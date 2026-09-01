#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <dirent.h>
#include <sys/stat.h>
#include <ctype.h>

#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "freertos/semphr.h"
#include "freertos/queue.h"
#include "nvs_flash.h"
#include "esp_system.h"
#include "esp_log.h"

#include "esp_vfs_fat.h"
#include "driver/sdspi_host.h"
#include "driver/spi_common.h"
#include "sdmmc_cmd.h"
#include "driver/uart.h"
#include "driver/i2s_std.h"
#include "driver/gpio.h"
#include "mp3dec.h"
#include "codec2.h"

#include "nimble/nimble_port.h"
#include "nimble/nimble_port_freertos.h"
#include "host/ble_hs.h"
#include "services/gap/ble_svc_gap.h"

#define TAG "WROOM_BLE"

#define I2S_BCLK_PIN        27
#define I2S_LRCK_PIN        33
#define I2S_DOUT_PIN        32

static i2s_chan_handle_t    s_tx_chan = NULL;
static SemaphoreHandle_t    s_i2s_mutex = NULL;
static uint32_t             s_current_sample_rate = 44100;

#define P4_UART_NUM         UART_NUM_2
#define P4_TX_PIN           22  
#define P4_RX_PIN           21  
#define UART_BUF_SIZE       1024

#define MAX_TRACKS          100
#define MAX_PATH_LEN        280
static char *s_track_list[MAX_TRACKS] = {NULL};
static int s_total_tracks = 0;

static volatile bool s_music_playing = false; 
static volatile float s_volume_factor = 0.04f; // 20% 지수형 시작 (0.2 * 0.2)
static volatile int s_current_volume = 20;        
static volatile int s_play_mode = 0;             
static volatile int s_target_track = 1;          
static volatile bool s_track_changed = false;    
static volatile bool s_voice_call_mode = false;
static volatile bool s_ble_connected = false;

static struct CODEC2 *s_c2_dec = NULL;

#define PIN_NUM_MISO        19
#define PIN_NUM_MOSI        23
#define PIN_NUM_CLK         18
#define PIN_NUM_CS          5
#define MOUNT_POINT         "/sdcard"

#define FILE_BUF_SIZE       (8 * 1024)
#define PCM_BUF_SIZE        (1152 * 2 * sizeof(int16_t))

typedef struct {
    uint8_t len;
    uint8_t data[64];
} voice_downlink_msg_t;

static QueueHandle_t s_voice_queue = NULL;

static const ble_uuid128_t S3_SVC_UUID = 
    BLE_UUID128_INIT(0x4b, 0x91, 0x31, 0xc3, 0xc9, 0xc5, 0xcc, 0x8f, 0x9e, 0x45, 0xb5, 0x1f, 0x01, 0xc2, 0xaf, 0x4f);
static const ble_uuid128_t S3_CHAR_EMERGENCY_UUID = 
    BLE_UUID128_INIT(0xa8, 0x26, 0x1b, 0x36, 0x07, 0xea, 0xf5, 0xb7, 0x88, 0x46, 0xe1, 0x36, 0x3e, 0x48, 0xb5, 0xbe);
static const ble_uuid128_t S3_CHAR_RADAR1_UUID = 
    BLE_UUID128_INIT(0x7e, 0xe8, 0x7b, 0x5d, 0x2e, 0x7a, 0x3d, 0xbf, 0x3a, 0x41, 0xf7, 0xd8, 0xe3, 0xd5, 0x95, 0x1c);
static const ble_uuid128_t S3_CHAR_RADAR2_UUID = 
    BLE_UUID128_INIT(0x20, 0x8e, 0x5d, 0x4a, 0x5c, 0x9e, 0x9a, 0x81, 0x9b, 0x4d, 0xeb, 0xe2, 0x58, 0x2b, 0x2d, 0xa2);
static const ble_uuid128_t S3_CHAR_AUDIO_UUID = 
    BLE_UUID128_INIT(0xbc, 0x9a, 0x78, 0x56, 0x34, 0x12, 0x7a, 0x83, 0x2e, 0x4a, 0x54, 0x6a, 0x3e, 0xb1, 0xa8, 0xd1);

#pragma pack(push, 1)
typedef struct {
    uint8_t  header1;
    uint8_t  header2;
    uint16_t in_count;
    uint16_t out_count;
    int16_t  r1_x[3];
    int16_t  r1_y[3];
    int16_t  r2_x[3];
    int16_t  r2_y[3];
    uint8_t  r1_detected;
    uint8_t  r2_detected;
    uint8_t  emergency_code;
    uint8_t  checksum;
} wroom_to_p4_pkt_t;
#pragma pack(pop)

static wroom_to_p4_pkt_t s_p4_pkt = {
    .header1 = 0xAA, .header2 = 0x55,
    .in_count = 0, .out_count = 0,
    .r1_x = {0}, .r1_y = {0}, .r2_x = {0}, .r2_y = {0},
    .r1_detected = 0, .r2_detected = 0, .emergency_code = 0, .checksum = 0
};

static SemaphoreHandle_t s_sensor_mutex = NULL;
static SemaphoreHandle_t s_uart_tx_mutex = NULL;
static uint16_t g_conn_handle = BLE_HS_CONN_HANDLE_NONE;

static uint16_t g_handle_emergency = 0;
static uint16_t g_handle_radar1 = 0;
static uint16_t g_handle_radar2 = 0;
static uint16_t g_handle_audio = 0;
static bool s_subscription_started = false;

static volatile uint32_t s_rx_r1_cnt = 0;
static volatile uint32_t s_rx_r2_cnt = 0;
static volatile uint32_t s_rx_em_cnt = 0;
static volatile uint32_t s_rx_audio_cnt = 0;
static uint32_t s_emergency_trigger_time = 0;

static volatile uint32_t s_last_play_time = 0; 

static void p4_uart_send_bytes(const void *data, size_t len) {
    if (s_uart_tx_mutex && xSemaphoreTake(s_uart_tx_mutex, pdMS_TO_TICKS(50)) == pdTRUE) {
        uart_write_bytes(P4_UART_NUM, (const char *)data, len);
        xSemaphoreGive(s_uart_tx_mutex);
    }
}

static void set_i2s_sample_rate_locked(uint32_t rate) {
    if (s_current_sample_rate != rate && s_tx_chan != NULL) {
        i2s_channel_disable(s_tx_chan);
        i2s_std_clk_config_t clk_cfg = I2S_STD_CLK_DEFAULT_CONFIG(rate);
        clk_cfg.clk_src = I2S_CLK_SRC_DEFAULT; 
        i2s_channel_reconfig_std_clock(s_tx_chan, &clk_cfg);
        i2s_channel_enable(s_tx_chan);
        s_current_sample_rate = rate;
        ESP_LOGI(TAG, "🎵 [I2S DAC] 샘플레이트 변경: %lu Hz", rate);
    }
}

static void parse_ld2450_frame(const uint8_t *data, uint16_t len, int16_t out_x[3], int16_t out_y[3], uint8_t *out_detected) {
    if (len < 30) return;
    if (data[0] != 0xAA || data[1] != 0xFF || data[2] != 0x03 || data[3] != 0x00) return;
    if (data[28] != 0x55 || data[29] != 0xCC) return;

    bool detected = false;
    for (int i = 0; i < 3; i++) {
        int base = 4 + (i * 8);
        uint16_t raw_x = (uint16_t)(data[base + 0] | (data[base + 1] << 8));
        uint16_t raw_y = (uint16_t)(data[base + 2] | (data[base + 3] << 8));
        uint16_t res   = (uint16_t)(data[base + 6] | (data[base + 7] << 8));

        int16_t x = (raw_x & 0x8000) ? -(int16_t)(raw_x & 0x7FFF) : (int16_t)raw_x;
        int16_t y = (raw_y & 0x8000) ? -(int16_t)(raw_y & 0x7FFF) : (int16_t)raw_y;

        if (abs(y) > 100 || abs(x) > 100 || res > 0) {
            out_x[i] = x; out_y[i] = y; detected = true;
        } else {
            out_x[i] = 0; out_y[i] = 0;
        }
    }
    *out_detected = detected ? 1 : 0;
}

static void scan_sd_mp3_files(void) {
    DIR *dir = opendir(MOUNT_POINT);
    if (!dir) return;

    for (int i = 0; i < s_total_tracks; i++) {
        if (s_track_list[i]) { free(s_track_list[i]); s_track_list[i] = NULL; }
    }
    s_total_tracks = 0;

    struct dirent *entry;
    char path_buf[MAX_PATH_LEN];
    while ((entry = readdir(dir)) != NULL && s_total_tracks < MAX_TRACKS) {
        if (entry->d_type == DT_REG || entry->d_type == DT_UNKNOWN) {
            char *ext = strrchr(entry->d_name, '.');
            if (ext && (strcasecmp(ext, ".mp3") == 0)) {
                snprintf(path_buf, sizeof(path_buf), "%s/%s", MOUNT_POINT, entry->d_name);
                s_track_list[s_total_tracks++] = strdup(path_buf);
            }
        }
    }
    closedir(dir);
}

static esp_err_t init_sd_card(void) {
    esp_vfs_fat_sdmmc_mount_config_t mount_config = {
        .format_if_mount_failed = false, .max_files = 5, .allocation_unit_size = 16 * 1024
    };
    sdmmc_card_t *card;
    spi_bus_config_t bus_cfg = {
        .mosi_io_num = PIN_NUM_MOSI, .miso_io_num = PIN_NUM_MISO, .sclk_io_num = PIN_NUM_CLK,
        .quadwp_io_num = -1, .quadhd_io_num = -1, .max_transfer_sz = 4000,
    };
    if (spi_bus_initialize(SPI2_HOST, &bus_cfg, SDSPI_DEFAULT_DMA) != ESP_OK) return ESP_FAIL;

    sdmmc_host_t host_config = SDSPI_HOST_DEFAULT();
    host_config.slot = SPI2_HOST;
    sdspi_device_config_t slot_config = SDSPI_DEVICE_CONFIG_DEFAULT();
    slot_config.gpio_cs = PIN_NUM_CS;
    slot_config.host_id = SPI2_HOST;

    esp_err_t ret = esp_vfs_fat_sdspi_mount(MOUNT_POINT, &host_config, &slot_config, &mount_config, &card);
    if (ret == ESP_OK) scan_sd_mp3_files();
    return ret;
}

static FILE* open_mp3_track_file(int track_num) {
    if (s_total_tracks > 0) {
        int index = (track_num - 1) % s_total_tracks;
        if (index < 0) index = 0;
        if (s_track_list[index]) {
            FILE *f = fopen(s_track_list[index], "rb");
            if (f) return f;
        }
    }
    char filepath[MAX_PATH_LEN];
    snprintf(filepath, sizeof(filepath), MOUNT_POINT "/music%d.mp3", track_num);
    FILE *f = fopen(filepath, "rb");
    if (!f && track_num != 1) f = fopen(MOUNT_POINT "/music1.mp3", "rb");
    return f;
}

static void ble_client_scan(void);
static int ble_gap_event(struct ble_gap_event *event, void *arg);

static void ble_subscribe_task(void *pvParameters) {
    uint16_t conn = (uint16_t)(uintptr_t)pvParameters;
    vTaskDelay(pdMS_TO_TICKS(150));
    uint8_t enable[2] = {0x01, 0x00};

    if (g_handle_emergency != 0) {
        ble_gattc_write_flat(conn, g_handle_emergency + 1, enable, sizeof(enable), NULL, NULL);
        vTaskDelay(pdMS_TO_TICKS(80));
    }
    if (g_handle_radar1 != 0) {
        ble_gattc_write_flat(conn, g_handle_radar1 + 1, enable, sizeof(enable), NULL, NULL);
        vTaskDelay(pdMS_TO_TICKS(80));
    }
    if (g_handle_radar2 != 0) {
        ble_gattc_write_flat(conn, g_handle_radar2 + 1, enable, sizeof(enable), NULL, NULL);
        vTaskDelay(pdMS_TO_TICKS(80));
    }
    if (g_handle_audio != 0) {
        ble_gattc_write_flat(conn, g_handle_audio + 1, enable, sizeof(enable), NULL, NULL);
        vTaskDelay(pdMS_TO_TICKS(80));
    }
    ESP_LOGI(TAG, "🔔 [GATT Subscribe] 센서 및 오디오 구독 완료");
    vTaskDelete(NULL);
}

static int on_disc_chr(uint16_t conn_handle, const struct ble_gatt_error *error,
                       const struct ble_gatt_chr *chr, void *arg) {
    if (error->status == 0 && chr != NULL) {
        if (ble_uuid_cmp(&chr->uuid.u, &S3_CHAR_EMERGENCY_UUID.u) == 0) g_handle_emergency = chr->val_handle;
        else if (ble_uuid_cmp(&chr->uuid.u, &S3_CHAR_RADAR1_UUID.u) == 0) g_handle_radar1 = chr->val_handle;
        else if (ble_uuid_cmp(&chr->uuid.u, &S3_CHAR_RADAR2_UUID.u) == 0) g_handle_radar2 = chr->val_handle;
        else if (ble_uuid_cmp(&chr->uuid.u, &S3_CHAR_AUDIO_UUID.u) == 0) g_handle_audio = chr->val_handle;

        if (!s_subscription_started && g_handle_emergency != 0 && g_handle_radar1 != 0 && 
            g_handle_radar2 != 0 && g_handle_audio != 0) {
            s_subscription_started = true;
            xTaskCreate(ble_subscribe_task, "sub_task", 3072, (void *)(uintptr_t)conn_handle, 5, NULL);
        }
    }
    return 0;
}

static int on_disc_svc(uint16_t conn_handle, const struct ble_gatt_error *error,
                       const struct ble_gatt_svc *svc, void *arg) {
    if (error->status == 0 && svc != NULL) {
        if (ble_uuid_cmp(&svc->uuid.u, &S3_SVC_UUID.u) == 0) {
            ble_gattc_disc_all_chrs(conn_handle, svc->start_handle, svc->end_handle, on_disc_chr, NULL);
        }
    }
    return 0;
}

static int on_mtu_exchange(uint16_t conn_handle, const struct ble_gatt_error *error,
                           uint16_t mtu, void *arg) {
    ble_gattc_disc_all_svcs(conn_handle, on_disc_svc, NULL);
    return 0;
}

static void ble_client_scan(void) {
    uint8_t own_addr_type;
    if (ble_hs_id_infer_auto(0, &own_addr_type) != 0) return;

    struct ble_gap_disc_params disc_params = {
        .filter_duplicates = 1, 
        .passive = 1,
        .itvl = 0x0100,
        .window = 0x0080,
        .filter_policy = 0, 
        .limited = 0
    };
    ble_gap_disc(own_addr_type, BLE_HS_FOREVER, &disc_params, ble_gap_event, NULL);
}

static int ble_gap_event(struct ble_gap_event *event, void *arg) {
    struct ble_hs_adv_fields fields;

    switch (event->type) {
    case BLE_GAP_EVENT_DISC:
        if (ble_hs_adv_parse_fields(&fields, event->disc.data, event->disc.length_data) == 0) {
            char dev_name[33] = {0};
            if (fields.name != NULL && fields.name_len > 0) {
                memcpy(dev_name, fields.name, fields.name_len < 32 ? fields.name_len : 32);
            }

            bool is_match = false;
            for (int i = 0; i < fields.num_uuids128; i++) {
                if (ble_uuid_cmp(&fields.uuids128[i].u, &S3_SVC_UUID.u) == 0) { is_match = true; break; }
            }
            if (!is_match && strlen(dev_name) > 0) {
                if (strstr(dev_name, "ESP32S3") != NULL || strstr(dev_name, "EMERGENCY") != NULL) is_match = true;
            }

            if (is_match) {
                ble_gap_disc_cancel();
                uint8_t own_addr_type;
                ble_hs_id_infer_auto(0, &own_addr_type);
                ble_gap_connect(own_addr_type, &event->disc.addr, 30000, NULL, ble_gap_event, NULL);
            }
        }
        break;

    case BLE_GAP_EVENT_CONNECT:
        if (event->connect.status == 0) {
            g_conn_handle = event->connect.conn_handle;
            s_ble_connected = true;
            s_subscription_started = false;
            ESP_LOGI(TAG, "🔗 S3 비상장치 BLE 연결 성공!");
            ble_gattc_exchange_mtu(g_conn_handle, on_mtu_exchange, NULL);
        } else {
            s_ble_connected = false;
            vTaskDelay(pdMS_TO_TICKS(1000));
            ble_client_scan();
        }
        break;

    case BLE_GAP_EVENT_DISCONNECT:
        s_ble_connected = false;
        s_subscription_started = false;
        g_conn_handle = BLE_HS_CONN_HANDLE_NONE;
        g_handle_emergency = 0; g_handle_radar1 = 0; g_handle_radar2 = 0; g_handle_audio = 0;
        ESP_LOGW(TAG, "⚡ S3 BLE 연결 해제 -> 재스캔");
        ble_client_scan();
        break;

    case BLE_GAP_EVENT_NOTIFY_RX: {
        uint16_t attr_handle = event->notify_rx.attr_handle;
        uint16_t pkt_len = OS_MBUF_PKTLEN(event->notify_rx.om);
        uint8_t rx_buf[128] = {0};
        os_mbuf_copydata(event->notify_rx.om, 0, pkt_len < sizeof(rx_buf) ? pkt_len : sizeof(rx_buf), rx_buf);

        if (attr_handle == g_handle_emergency) {
            char msg[32] = {0};
            memcpy(msg, rx_buf, pkt_len < sizeof(msg) ? pkt_len : sizeof(msg) - 1);

            if (xSemaphoreTake(s_sensor_mutex, pdMS_TO_TICKS(10)) == pdTRUE) {
                s_rx_em_cnt++;
                if (strstr(msg, "살려") != NULL) s_p4_pkt.emergency_code = 1;
                else if (strstr(msg, "도와") != NULL) s_p4_pkt.emergency_code = 2;
                else if (strstr(msg, "구해") != NULL) s_p4_pkt.emergency_code = 3;
                else if (strstr(msg, "CALL_START") != NULL) s_p4_pkt.emergency_code = 1;
                else if (strstr(msg, "CALL_END") != NULL) s_p4_pkt.emergency_code = 0;

                if (s_p4_pkt.emergency_code > 0) {
                    s_emergency_trigger_time = xTaskGetTickCount() * portTICK_PERIOD_MS;
                    s_voice_call_mode = true;
                    s_music_playing = false;
                    p4_uart_send_bytes("$CALL_START\n", 12);
                } else {
                    s_voice_call_mode = false;
                    p4_uart_send_bytes("$CALL_END\n", 10);
                }
                xSemaphoreGive(s_sensor_mutex);
            }
        }
        else if (attr_handle == g_handle_audio) {
            s_rx_audio_cnt++;
            if (s_voice_call_mode && pkt_len > 0) {
                uint32_t now = xTaskGetTickCount() * portTICK_PERIOD_MS;
                bool is_speaker_busy = (uxQueueMessagesWaiting(s_voice_queue) > 0) || (now - s_last_play_time < 350);
                
                if (!is_speaker_busy) {
                    uint8_t voice_pkt[64];
                    voice_pkt[0] = 0xA5; voice_pkt[1] = 0x5A; voice_pkt[2] = (uint8_t)pkt_len;
                    memcpy(&voice_pkt[3], rx_buf, pkt_len);
                    p4_uart_send_bytes(voice_pkt, pkt_len + 3);
                }
            }
        }
        else if (attr_handle == g_handle_radar1) {
            if (!s_voice_call_mode) {
                if (xSemaphoreTake(s_sensor_mutex, pdMS_TO_TICKS(10)) == pdTRUE) {
                    s_rx_r1_cnt++;
                    parse_ld2450_frame(rx_buf, pkt_len, s_p4_pkt.r1_x, s_p4_pkt.r1_y, &s_p4_pkt.r1_detected);
                    xSemaphoreGive(s_sensor_mutex);
                }
            }
        }
        else if (attr_handle == g_handle_radar2) {
            if (!s_voice_call_mode) {
                if (xSemaphoreTake(s_sensor_mutex, pdMS_TO_TICKS(10)) == pdTRUE) {
                    s_rx_r2_cnt++;
                    parse_ld2450_frame(rx_buf, pkt_len, s_p4_pkt.r2_x, s_p4_pkt.r2_y, &s_p4_pkt.r2_detected);
                    xSemaphoreGive(s_sensor_mutex);
                }
            }
        }
        break;
    }
    default:
        break;
    }
    return 0;
}

static void ble_host_task(void *param) {
    nimble_port_run();
    nimble_port_freertos_deinit();
}

static void radar_process_task(void *pvParameters) {
    bool prev_slot_active[3] = {false, false, false};
    uint8_t tx_frame[34];

    while (1) {
        if (s_voice_call_mode) {
            vTaskDelay(pdMS_TO_TICKS(100));
            continue;
        }

        uint32_t now = xTaskGetTickCount() * portTICK_PERIOD_MS;
        wroom_to_p4_pkt_t snap;

        if (xSemaphoreTake(s_sensor_mutex, pdMS_TO_TICKS(20)) == pdTRUE) {
            if (s_p4_pkt.emergency_code > 0 && (now - s_emergency_trigger_time > 3000)) {
                s_p4_pkt.emergency_code = 0;
            }

            for (int i = 0; i < 3; i++) {
                bool curr_active = (s_p4_pkt.r1_x[i] != 0 || s_p4_pkt.r1_y[i] != 0);
                if (curr_active && !prev_slot_active[i]) {
                    s_p4_pkt.in_count++;
                }
                prev_slot_active[i] = curr_active;
            }

            snap = s_p4_pkt;
            xSemaphoreGive(s_sensor_mutex);
        }

        tx_frame[0] = 0xAA; tx_frame[1] = 0x55;
        tx_frame[2] = (uint8_t)((snap.in_count >> 8) & 0xFF); tx_frame[3] = (uint8_t)(snap.in_count & 0xFF);
        tx_frame[4] = (uint8_t)((snap.out_count >> 8) & 0xFF); tx_frame[5] = (uint8_t)(snap.out_count & 0xFF);

        for (int i = 0; i < 3; i++) {
            tx_frame[6 + (i * 2)]   = (uint8_t)((snap.r1_x[i] >> 8) & 0xFF);
            tx_frame[7 + (i * 2)]   = (uint8_t)(snap.r1_x[i] & 0xFF);
            tx_frame[12 + (i * 2)]  = (uint8_t)((snap.r1_y[i] >> 8) & 0xFF);
            tx_frame[13 + (i * 2)]  = (uint8_t)(snap.r1_y[i] & 0xFF);
            tx_frame[18 + (i * 2)]  = (uint8_t)((snap.r2_x[i] >> 8) & 0xFF);
            tx_frame[19 + (i * 2)]  = (uint8_t)(snap.r2_x[i] & 0xFF);
            tx_frame[24 + (i * 2)]  = (uint8_t)((snap.r2_y[i] >> 8) & 0xFF);
            tx_frame[25 + (i * 2)]  = (uint8_t)(snap.r2_y[i] & 0xFF);
        }
        tx_frame[30] = snap.r1_detected; tx_frame[31] = snap.r2_detected; tx_frame[32] = snap.emergency_code;

        uint8_t chk = 0;
        for (int i = 2; i < 33; i++) chk ^= tx_frame[i];
        tx_frame[33] = chk;

        p4_uart_send_bytes(tx_frame, 34);
        vTaskDelay(pdMS_TO_TICKS(50));
    }
}

static uint8_t s_rx_acc_buf[512];
static int s_rx_acc_len = 0;
static uint8_t s_uart_temp[128];
static char s_line_buf[128];

static void p4_rx_task(void *pvParameters) {
    s_rx_acc_len = 0;

    while (1) {
        int len = uart_read_bytes(P4_UART_NUM, s_uart_temp, sizeof(s_uart_temp), pdMS_TO_TICKS(5));
        if (len > 0) {
            if (s_rx_acc_len + len <= (int)sizeof(s_rx_acc_buf)) {
                memcpy(&s_rx_acc_buf[s_rx_acc_len], s_uart_temp, len);
                s_rx_acc_len += len;
            } else {
                s_rx_acc_len = 0;
            }
        }

        if (s_rx_acc_len >= 9) {
            for (int i = 0; i <= s_rx_acc_len - 9; i++) {
                if (memcmp(&s_rx_acc_buf[i], "$CALL_END", 9) == 0) {
                    s_voice_call_mode = false;
                    xQueueReset(s_voice_queue);
                    if (g_conn_handle != BLE_HS_CONN_HANDLE_NONE && g_handle_emergency != 0) {
                        ble_gattc_write_no_rsp_flat(g_conn_handle, g_handle_emergency, "CALL_END", 8);
                    }
                    s_rx_acc_len = 0; break;
                }
            }
        }
        if (s_rx_acc_len >= 11) {
            for (int i = 0; i <= s_rx_acc_len - 11; i++) {
                if (memcmp(&s_rx_acc_buf[i], "$CALL_START", 11) == 0) {
                    s_voice_call_mode = true; s_music_playing = false; xQueueReset(s_voice_queue);
                    if (g_conn_handle != BLE_HS_CONN_HANDLE_NONE && g_handle_emergency != 0) {
                        ble_gattc_write_no_rsp_flat(g_conn_handle, g_handle_emergency, "CALL_START", 10);
                    }
                    s_rx_acc_len = 0; break;
                }
            }
        }

        while (s_rx_acc_len > 0) {
            if (s_rx_acc_buf[0] == 0x5A) {
                if (s_rx_acc_len < 3) break; 
                if (s_rx_acc_buf[1] != 0xA5) {
                    s_rx_acc_len--; memmove(s_rx_acc_buf, &s_rx_acc_buf[1], s_rx_acc_len); continue;
                }
                
                uint8_t c2_len = s_rx_acc_buf[2];
                if (s_rx_acc_len < 3 + c2_len) break; 

                if (s_voice_call_mode && c2_len <= 64) {
                    voice_downlink_msg_t msg;
                    msg.len = c2_len;
                    memcpy(msg.data, &s_rx_acc_buf[3], c2_len);
                    if (uxQueueSpacesAvailable(s_voice_queue) == 0) {
                        voice_downlink_msg_t dummy; xQueueReceive(s_voice_queue, &dummy, 0); 
                    }
                    xQueueSend(s_voice_queue, &msg, 0);
                }
                s_rx_acc_len -= (3 + c2_len);
                if (s_rx_acc_len > 0) memmove(s_rx_acc_buf, &s_rx_acc_buf[3 + c2_len], s_rx_acc_len);
                continue;
            } 
            else if (s_rx_acc_buf[0] == '$') {
                int nl_idx = -1;
                for (int j = 1; j < s_rx_acc_len; j++) {
                    if (s_rx_acc_buf[j] == '\n' || s_rx_acc_buf[j] == '\r') { nl_idx = j; break; }
                }
                if (nl_idx == -1) {
                    if (s_rx_acc_len >= (int)sizeof(s_rx_acc_buf)) { 
                        s_rx_acc_len--; memmove(s_rx_acc_buf, &s_rx_acc_buf[1], s_rx_acc_len); continue; 
                    }
                    break;
                }

                int copy_len = (nl_idx < (int)sizeof(s_line_buf) - 1) ? nl_idx : (int)sizeof(s_line_buf) - 1;
                memcpy(s_line_buf, s_rx_acc_buf, copy_len); s_line_buf[copy_len] = '\0';

                if (strstr(s_line_buf, "MUSIC,ON") != NULL) { if (!s_voice_call_mode) s_music_playing = true; } 
                else if (strstr(s_line_buf, "MUSIC,OFF") != NULL) s_music_playing = false;
                else if (strncmp(s_line_buf, "$VOL,", 5) == 0) {
                    int vol = atoi(s_line_buf + 5);
                    s_current_volume = (vol < 0) ? 0 : ((vol > 100) ? 100 : vol);
                    float ratio = (float)s_current_volume / 100.0f;
                    s_volume_factor = ratio * ratio; 
                }
                else if (strncmp(s_line_buf, "$PLAYMODE,", 10) == 0) {
                    s_play_mode = atoi(s_line_buf + 10);
                }
                else if (strncmp(s_line_buf, "$TRACK,", 7) == 0) {
                    int trk = atoi(s_line_buf + 7);
                    if (trk > 0 && s_target_track != trk) {
                        s_target_track = trk; s_play_mode = 2; s_track_changed = true; s_music_playing = true; 
                    }
                }
                else if (strncmp(s_line_buf, "$ACTION,NEXT", 12) == 0) {
                    if (s_total_tracks > 0) s_target_track = (s_target_track % s_total_tracks) + 1;
                    else s_target_track++;
                    s_track_changed = true; s_music_playing = true;
                }
                else if (strncmp(s_line_buf, "$ACTION,PREV", 12) == 0) {
                    if (s_total_tracks > 0) s_target_track = (s_target_track <= 1) ? s_total_tracks : (s_target_track - 1);
                    else if (s_target_track > 1) s_target_track--;
                    s_track_changed = true; s_music_playing = true;
                }

                s_rx_acc_len -= (nl_idx + 1);
                if (s_rx_acc_len > 0) memmove(s_rx_acc_buf, &s_rx_acc_buf[nl_idx + 1], s_rx_acc_len);
                continue;
            }
            else if (s_rx_acc_buf[0] == '\n' || s_rx_acc_buf[0] == '\r') {
                s_rx_acc_len--;
                if (s_rx_acc_len > 0) memmove(s_rx_acc_buf, &s_rx_acc_buf[1], s_rx_acc_len);
                continue;
            }

            s_rx_acc_len--;
            if (s_rx_acc_len > 0) memmove(s_rx_acc_buf, &s_rx_acc_buf[1], s_rx_acc_len);
        }
        vTaskDelay(1);
    }
}

static int16_t s_voice_pcm_8k[160];
static int16_t s_voice_stereo_8k[160 * 2];

static void voice_play_worker_task(void *pvParameters) {
    voice_downlink_msg_t msg;
    bool is_buffering = true;
    int silence_count = 0;

    while (1) {
        if (!s_voice_call_mode) {
            xQueueReset(s_voice_queue);
            is_buffering = true; silence_count = 0;
            vTaskDelay(pdMS_TO_TICKS(50));
            continue;
        }

        if (is_buffering) {
            if (uxQueueMessagesWaiting(s_voice_queue) >= 2 || (silence_count > 15 && uxQueueMessagesWaiting(s_voice_queue) > 0)) {
                is_buffering = false; silence_count = 0;
            } else {
                silence_count++; vTaskDelay(pdMS_TO_TICKS(10)); continue;
            }
        }

        if (xQueueReceive(s_voice_queue, &msg, pdMS_TO_TICKS(150)) == pdTRUE) {
            silence_count = 0;
            if (s_c2_dec != NULL && msg.len > 0) {
                s_last_play_time = xTaskGetTickCount() * portTICK_PERIOD_MS;
                
                if (xSemaphoreTake(s_i2s_mutex, portMAX_DELAY) == pdTRUE) {
                    set_i2s_sample_rate_locked(8000);
                    for (int c_idx = 0; c_idx < msg.len; c_idx += 6) {
                        if (msg.len - c_idx < 6) break;
                        codec2_decode(s_c2_dec, s_voice_pcm_8k, &msg.data[c_idx]);

                        for (int s = 0; s < 160; s++) {
                            int32_t val = (int32_t)(s_voice_pcm_8k[s] * s_volume_factor * 3.0f); 
                            if (val > 32767) val = 32767;
                            if (val < -32768) val = -32768;
                            s_voice_stereo_8k[s * 2]     = (int16_t)val;
                            s_voice_stereo_8k[s * 2 + 1] = (int16_t)val;
                        }
                        size_t written = 0;
                        i2s_channel_write(s_tx_chan, s_voice_stereo_8k, sizeof(s_voice_stereo_8k), &written, portMAX_DELAY);
                    }
                    xSemaphoreGive(s_i2s_mutex);
                }
            }
        } else {
            silence_count++;
            if (silence_count >= 2) {
                if (xSemaphoreTake(s_i2s_mutex, pdMS_TO_TICKS(10)) == pdTRUE) {
                    set_i2s_sample_rate_locked(8000);
                    memset(s_voice_stereo_8k, 0, sizeof(s_voice_stereo_8k));
                    size_t written = 0;
                    i2s_channel_write(s_tx_chan, s_voice_stereo_8k, sizeof(s_voice_stereo_8k), &written, pdMS_TO_TICKS(10));
                    xSemaphoreGive(s_i2s_mutex);
                }
                is_buffering = true;
            }
        }
    }
}

// 💡 [따발총/경운기 소리 완전 해결] 대기 시 지속 전송할 1024바이트 무음 버퍼
static int16_t s_idle_zero_buf[512] = {0}; 

static void mp3_player_task(void *pvParameters) {
    HMP3Decoder hMP3Decoder = MP3InitDecoder();
    if (!hMP3Decoder) vTaskDelete(NULL);

    uint8_t *file_buf = malloc(FILE_BUF_SIZE);
    int16_t *pcm_buf = malloc(PCM_BUF_SIZE);
    int16_t *stereo_buf = malloc(PCM_BUF_SIZE * 2); 
    
    if (!file_buf || !pcm_buf || !stereo_buf) {
        if (file_buf) free(file_buf);
        if (pcm_buf) free(pcm_buf);
        if (stereo_buf) free(stereo_buf);
        MP3FreeDecoder(hMP3Decoder);
        vTaskDelete(NULL);
    }

    uint32_t last_eq_send_time = 0;
    int current_playing_track = s_target_track;
    FILE *f = open_mp3_track_file(current_playing_track);

    int bytes_in_buffer = 0;
    uint8_t *read_ptr = file_buf;

    while (1) {
        if (s_track_changed) {
            s_track_changed = false;
            current_playing_track = s_target_track;
            if (f) fclose(f);
            f = open_mp3_track_file(current_playing_track);
            bytes_in_buffer = 0;
            read_ptr = file_buf;
        }

        // 💡 [핵심 수정] portMAX_DELAY를 사용하여 DMA 버퍼 빈자리에 맞춰 실시간 블로킹 전송 (vTaskDelay 제거)
        if (s_voice_call_mode || !s_music_playing) {
            if (!s_voice_call_mode) {
                if (xSemaphoreTake(s_i2s_mutex, pdMS_TO_TICKS(20)) == pdTRUE) {
                    set_i2s_sample_rate_locked(44100);
                    size_t bytes_written = 0;
                    i2s_channel_write(s_tx_chan, s_idle_zero_buf, sizeof(s_idle_zero_buf), &bytes_written, portMAX_DELAY);
                    xSemaphoreGive(s_i2s_mutex);
                } else {
                    vTaskDelay(pdMS_TO_TICKS(5));
                }
            } else {
                vTaskDelay(pdMS_TO_TICKS(20));
            }
            continue;
        }

        if (bytes_in_buffer < 2048 && f != NULL) {
            memmove(file_buf, read_ptr, bytes_in_buffer);
            int bytes_read = fread(file_buf + bytes_in_buffer, 1, FILE_BUF_SIZE - bytes_in_buffer, f);
            
            if (bytes_read <= 0 && bytes_in_buffer == 0) {
                if (s_play_mode == 0 || s_play_mode == 1) { 
                    int count = (s_total_tracks > 0) ? s_total_tracks : 5;
                    s_target_track = (rand() % count) + 1;
                    s_track_changed = true; 
                } else { 
                    rewind(f);
                }
                bytes_in_buffer = 0;
                read_ptr = file_buf;
                vTaskDelay(pdMS_TO_TICKS(10));
                continue;
            }
            bytes_in_buffer += bytes_read;
            read_ptr = file_buf;
        }

        if (bytes_in_buffer == 0 || f == NULL) {
            vTaskDelay(pdMS_TO_TICKS(100));
            continue;
        }

        int offset = MP3FindSyncWord(read_ptr, bytes_in_buffer);
        if (offset < 0) { 
            bytes_in_buffer = 0; 
            vTaskDelay(pdMS_TO_TICKS(10)); 
            continue; 
        }

        read_ptr += offset;
        bytes_in_buffer -= offset;

        int err = MP3Decode(hMP3Decoder, &read_ptr, &bytes_in_buffer, pcm_buf, 0);
        if (err == ERR_MP3_NONE) {
            MP3FrameInfo frameInfo;
            MP3GetLastFrameInfo(hMP3Decoder, &frameInfo);

            int sample_count = frameInfo.outputSamps;
            int channels = frameInfo.nChans;

            uint32_t now = xTaskGetTickCount() * portTICK_PERIOD_MS;
            if (s_music_playing && (now - last_eq_send_time >= 40)) {
                last_eq_send_time = now;
                int bands[8] = {0};
                int samples_per_band = sample_count / 8;
                for (int b = 0; b < 8; b++) {
                    int64_t sum = 0;
                    for (int i = 0; i < samples_per_band; i++) sum += abs(pcm_buf[b * samples_per_band + i]);
                    bands[b] = ((int)(sum / samples_per_band) * 4) / 12000; 
                    if (bands[b] > 4) bands[b] = 4;
                }
                char eq_pkt[64];
                int pkt_len = snprintf(eq_pkt, sizeof(eq_pkt), "$AUDIO,%d,%d,%d,%d,%d,%d,%d,%d\n",
                                       bands[0], bands[1], bands[2], bands[3],
                                       bands[4], bands[5], bands[6], bands[7]);
                p4_uart_send_bytes(eq_pkt, pkt_len);
            }

            for (int i = 0; i < sample_count; i++) {
                int32_t scaled = (int32_t)(pcm_buf[i] * s_volume_factor);
                pcm_buf[i] = (int16_t)(scaled > 32767 ? 32767 : (scaled < -32768 ? -32768 : scaled));
            }

            if (xSemaphoreTake(s_i2s_mutex, pdMS_TO_TICKS(20)) == pdTRUE) {
                if (!s_voice_call_mode && frameInfo.samprate > 0) {
                    set_i2s_sample_rate_locked(frameInfo.samprate); 
                    size_t bytes_written = 0;

                    if (channels == 1) {
                        for (int i = 0; i < sample_count; i++) {
                            stereo_buf[i * 2] = pcm_buf[i];
                            stereo_buf[i * 2 + 1] = pcm_buf[i];
                        }
                        i2s_channel_write(s_tx_chan, stereo_buf, sample_count * 2 * sizeof(int16_t), &bytes_written, portMAX_DELAY);
                    } else {
                        i2s_channel_write(s_tx_chan, pcm_buf, sample_count * sizeof(int16_t), &bytes_written, portMAX_DELAY);
                    }
                }
                xSemaphoreGive(s_i2s_mutex);
            }
        } else {
            vTaskDelay(1);
        }
    }
}

static esp_err_t init_i2s_driver(void) {
    i2s_chan_config_t chan_cfg = I2S_CHANNEL_DEFAULT_CONFIG(I2S_NUM_0, I2S_ROLE_MASTER);
    chan_cfg.dma_desc_num = 16;
    chan_cfg.dma_frame_num = 512;
    chan_cfg.auto_clear = true;

    ESP_ERROR_CHECK(i2s_new_channel(&chan_cfg, &s_tx_chan, NULL));

    i2s_std_config_t std_cfg = {
        .clk_cfg = I2S_STD_CLK_DEFAULT_CONFIG(44100), 
        .slot_cfg = I2S_STD_PHILIPS_SLOT_DEFAULT_CONFIG(I2S_DATA_BIT_WIDTH_16BIT, I2S_SLOT_MODE_STEREO),
        .gpio_cfg = {
            .mclk = I2S_GPIO_UNUSED, 
            .bclk = I2S_BCLK_PIN, 
            .ws = I2S_LRCK_PIN, 
            .dout = I2S_DOUT_PIN, 
            .din = I2S_GPIO_UNUSED,
            .invert_flags = { .mclk_inv = false, .bclk_inv = false, .ws_inv = false },
        },
    };
    
    std_cfg.clk_cfg.clk_src = I2S_CLK_SRC_DEFAULT;

    ESP_ERROR_CHECK(i2s_channel_init_std_mode(s_tx_chan, &std_cfg));
    ESP_ERROR_CHECK(i2s_channel_enable(s_tx_chan));
    return ESP_OK;
}

static void init_p4_uarts(void) {
    uart_config_t uart_ctrl_cfg = {
        .baud_rate = 115200, .data_bits = UART_DATA_8_BITS, .parity = UART_PARITY_DISABLE,
        .stop_bits = UART_STOP_BITS_1, .flow_ctrl = UART_HW_FLOWCTRL_DISABLE, .source_clk = UART_SCLK_DEFAULT,
    };
    ESP_ERROR_CHECK(uart_driver_install(P4_UART_NUM, UART_BUF_SIZE * 2, UART_BUF_SIZE * 2, 0, NULL, 0));
    ESP_ERROR_CHECK(uart_param_config(P4_UART_NUM, &uart_ctrl_cfg));
    ESP_ERROR_CHECK(uart_set_pin(P4_UART_NUM, P4_TX_PIN, P4_RX_PIN, UART_PIN_NO_CHANGE, UART_PIN_NO_CHANGE));
}

static void system_init_task(void *pvParameters) {
    ESP_LOGI(TAG, "🚀 WROOM 메인 초기화 워커 태스크 시작");

    s_c2_dec = codec2_create(CODEC2_MODE_2400);
    if (!s_c2_dec) {
        ESP_LOGE(TAG, "❌ Codec2 디코더 생성 실패!");
    }

    s_voice_queue = xQueueCreate(30, sizeof(voice_downlink_msg_t));

    nimble_port_init();
    ble_svc_gap_device_name_set("ESP32_WROOM_RECV");
    ble_hs_cfg.sync_cb = ble_client_scan;
    nimble_port_freertos_init(ble_host_task);

    init_p4_uarts();
    ESP_ERROR_CHECK(init_i2s_driver());

    xTaskCreatePinnedToCore(p4_rx_task, "p4_rx_task", 4096, NULL, 5, NULL, 1);
    xTaskCreatePinnedToCore(voice_play_worker_task, "voice_play_task", 24576, NULL, 5, NULL, 1);
    xTaskCreatePinnedToCore(radar_process_task, "radar_process_task", 3072, NULL, 4, NULL, 0);

    if (init_sd_card() == ESP_OK) {
        ESP_LOGI(TAG, "💾 SD 카드 마운트 성공! (%d곡 로드)", s_total_tracks);
        xTaskCreatePinnedToCore(mp3_player_task, "mp3_player_task", 8192, NULL, 4, NULL, 1);
    } else {
        ESP_LOGW(TAG, "⚠️ SD 카드가 없거나 마운트에 실패했습니다.");
    }

    ESP_LOGI(TAG, "🎉 WROOM 시스템 준비 완료");
    vTaskDelete(NULL);
}

void app_main(void) {
    esp_err_t ret = nvs_flash_init();
    if (ret == ESP_ERR_NVS_NO_FREE_PAGES || ret == ESP_ERR_NVS_NEW_VERSION_FOUND) {
        ESP_ERROR_CHECK(nvs_flash_erase());
        ret = nvs_flash_init();
    }
    ESP_ERROR_CHECK(ret);

    s_sensor_mutex = xSemaphoreCreateMutex();
    s_uart_tx_mutex = xSemaphoreCreateMutex();
    s_i2s_mutex = xSemaphoreCreateMutex();

    xTaskCreatePinnedToCore(system_init_task, "sys_init_task", 12288, NULL, 5, NULL, 0);
}