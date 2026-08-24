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
#include "nvs_flash.h"
#include "esp_system.h"
#include "esp_log.h"

// SD & I2S & UART
#include "esp_vfs_fat.h"
#include "driver/sdspi_host.h"
#include "driver/spi_common.h"
#include "sdmmc_cmd.h"
#include "driver/uart.h"
#include "driver/i2s_std.h"
#include "driver/gpio.h"
#include "mp3dec.h"

// NimBLE
#include "nimble/nimble_port.h"
#include "nimble/nimble_port_freertos.h"
#include "host/ble_hs.h"
#include "services/gap/ble_svc_gap.h"

#define TAG "WROOM_BLE"
static const char *TARGET_DEVICE_NAME = "ESP32S3_EMERGENCY_SYSTEM";

// ------------------- [I2S 핀 설정] -------------------
#define I2S_BCLK_PIN        27
#define I2S_LRCK_PIN        33
#define I2S_DOUT_PIN        32

static i2s_chan_handle_t    s_tx_chan = NULL;
static uint32_t             s_current_sample_rate = 44100;

// ------------------- [P4 통신 메인 통합 UART 설정] -------------------
#define P4_UART_NUM         UART_NUM_2
#define P4_TX_PIN           22  
#define P4_RX_PIN           21  
#define UART_BUF_SIZE       1024

#define MAX_TRACKS          100
#define MAX_PATH_LEN        280
static char *s_track_list[MAX_TRACKS] = {NULL};
static int s_total_tracks = 0;

static volatile bool s_music_playing = false; 
static volatile float s_volume_factor = 0.2f;
static volatile int s_current_volume = 20;        
static volatile int s_play_mode = 0;             
static volatile int s_target_track = 1;          
static volatile bool s_track_changed = false;     

// ------------------- [SD 카드 핀 설정] -------------------
#define PIN_NUM_MISO        19
#define PIN_NUM_MOSI        23
#define PIN_NUM_CLK         18
#define PIN_NUM_CS          5
#define MOUNT_POINT         "/sdcard"

#define FILE_BUF_SIZE       (2 * 1024)
#define PCM_BUF_SIZE        (1152 * 2 * sizeof(int16_t))

// ------------------- [S3 128-bit UUID (Little-Endian)] -------------------
static const ble_uuid128_t S3_SVC_UUID = 
    BLE_UUID128_INIT(0x4b, 0x91, 0x31, 0xc3, 0xc9, 0xc5, 0xcc, 0x8f, 0x9e, 0x45, 0xb5, 0x1f, 0x01, 0xc2, 0xaf, 0x4f);

static const ble_uuid128_t S3_CHAR_EMERGENCY_UUID = 
    BLE_UUID128_INIT(0xa8, 0x26, 0x1b, 0x36, 0x07, 0xea, 0xf5, 0xb7, 0x88, 0x46, 0xe1, 0x36, 0x3e, 0x48, 0xb5, 0xbe);

static const ble_uuid128_t S3_CHAR_RADAR1_UUID = 
    BLE_UUID128_INIT(0x7e, 0xe8, 0x7b, 0x5d, 0x2e, 0x7a, 0x3d, 0xbf, 0x3a, 0x41, 0xf7, 0xd8, 0xe3, 0xd5, 0x95, 0x1c);

static const ble_uuid128_t S3_CHAR_RADAR2_UUID = 
    BLE_UUID128_INIT(0x20, 0x8e, 0x5d, 0x4a, 0x5c, 0x9e, 0x9a, 0x81, 0x9b, 0x4d, 0xeb, 0xe2, 0x58, 0x2b, 0x2d, 0xa2);

// ------------------- [P4 송신용 구조체] -------------------
#pragma pack(push, 1)
typedef struct {
    uint8_t  header1;        // 0xAA
    uint8_t  header2;        // 0x55
    uint16_t in_count;       // 2B
    uint16_t out_count;      // 2B
    int16_t  r1_x[3];        // 6B
    int16_t  r1_y[3];        // 6B
    int16_t  r2_x[3];        // 6B
    int16_t  r2_y[3];        // 6B
    uint8_t  r1_detected;    // 1B
    uint8_t  r2_detected;    // 1B
    uint8_t  emergency_code; // 1B
    uint8_t  checksum;       // 1B
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
static bool s_subscription_started = false;

static volatile uint32_t s_rx_r1_cnt = 0;
static volatile uint32_t s_rx_r2_cnt = 0;
static volatile uint32_t s_rx_em_cnt = 0;
static volatile bool s_ble_connected = false;
static uint32_t s_emergency_trigger_time = 0;

static void p4_uart_send_bytes(const void *data, size_t len) {
    if (s_uart_tx_mutex && xSemaphoreTake(s_uart_tx_mutex, pdMS_TO_TICKS(50)) == pdTRUE) {
        uart_write_bytes(P4_UART_NUM, (const char *)data, len);
        xSemaphoreGive(s_uart_tx_mutex);
    }
}

// ------------------- [LD2450 30B 디코더] -------------------
static void parse_ld2450_frame(const uint8_t *data, uint16_t len, int16_t out_x[3], int16_t out_y[3], uint8_t *out_detected) {
    if (len < 30 || data[0] != 0xAA || data[1] != 0xFF || data[2] != 0x03 || data[3] != 0x00 ||
        data[28] != 0x55 || data[29] != 0xCC) {
        return;
    }

    bool detected = false;
    for (int i = 0; i < 3; i++) {
        int base = 4 + (i * 8);
        uint16_t raw_x = data[base + 0] | (data[base + 1] << 8);
        uint16_t raw_y = data[base + 2] | (data[base + 3] << 8);
        uint16_t res   = data[base + 6] | (data[base + 7] << 8);

        int16_t x = (raw_x & 0x8000) ? -(int16_t)(raw_x & 0x7FFF) : (int16_t)raw_x;
        int16_t y = (raw_y & 0x8000) ? -(int16_t)(raw_y & 0x7FFF) : (int16_t)raw_y;

        if (abs(y) > 50 || abs(x) > 50 || res > 0) {
            out_x[i] = x;
            out_y[i] = y;
            detected = true;
        } else {
            out_x[i] = 0;
            out_y[i] = 0;
        }
    }
    *out_detected = detected ? 1 : 0;
}

// ------------------- [순차 CCCD 활성화 태스크] -------------------
static void ble_client_scan(void);
static int ble_gap_event(struct ble_gap_event *event, void *arg);

static void ble_subscribe_task(void *pvParameters) {
    uint16_t conn = (uint16_t)(uintptr_t)pvParameters;
    vTaskDelay(pdMS_TO_TICKS(150));

    uint8_t enable[2] = {0x01, 0x00};

    // 1. Emergency 알림 활성화
    if (g_handle_emergency != 0) {
        ESP_LOGI(TAG, "📡 [1/3] Emergency CCCD 쓰기 (Handle: %d)", g_handle_emergency + 1);
        ble_gattc_write_flat(conn, g_handle_emergency + 1, enable, sizeof(enable), NULL, NULL);
        vTaskDelay(pdMS_TO_TICKS(80));
    }

    // 2. Radar 1 알림 활성화
    if (g_handle_radar1 != 0) {
        ESP_LOGI(TAG, "📡 [2/3] Radar 1 CCCD 쓰기 (Handle: %d)", g_handle_radar1 + 1);
        ble_gattc_write_flat(conn, g_handle_radar1 + 1, enable, sizeof(enable), NULL, NULL);
        vTaskDelay(pdMS_TO_TICKS(80));
    }

    // 3. Radar 2 알림 활성화
    if (g_handle_radar2 != 0) {
        ESP_LOGI(TAG, "📡 [3/3] Radar 2 CCCD 쓰기 (Handle: %d)", g_handle_radar2 + 1);
        ble_gattc_write_flat(conn, g_handle_radar2 + 1, enable, sizeof(enable), NULL, NULL);
        vTaskDelay(pdMS_TO_TICKS(80));
    }

    ESP_LOGI(TAG, "🚀 [모든 센서 CCCD 등록 완결] R1, R2, 비상 실시간 스트리밍 시작!");
    vTaskDelete(NULL);
}

static int on_disc_chr(uint16_t conn_handle, const struct ble_gatt_error *error,
                       const struct ble_gatt_chr *chr, void *arg) {
    if (error->status == 0 && chr != NULL) {
        if (ble_uuid_cmp(&chr->uuid.u, &S3_CHAR_EMERGENCY_UUID.u) == 0) {
            g_handle_emergency = chr->val_handle;
            ESP_LOGI(TAG, "📌 Emergency Char Handle: %d", g_handle_emergency);
        } else if (ble_uuid_cmp(&chr->uuid.u, &S3_CHAR_RADAR1_UUID.u) == 0) {
            g_handle_radar1 = chr->val_handle;
            ESP_LOGI(TAG, "📌 Radar1 Char Handle: %d", g_handle_radar1);
        } else if (ble_uuid_cmp(&chr->uuid.u, &S3_CHAR_RADAR2_UUID.u) == 0) {
            g_handle_radar2 = chr->val_handle;
            ESP_LOGI(TAG, "📌 Radar2 Char Handle: %d", g_handle_radar2);
        }

        // 3개 핵심 특성을 모두 발견하면 완료 이벤트를 기다리지 않고 즉시 CCCD 등록 태스크 가동
        if (!s_subscription_started && g_handle_emergency != 0 && g_handle_radar1 != 0 && g_handle_radar2 != 0) {
            s_subscription_started = true;
            ESP_LOGI(TAG, "🎉 [3개 특성 모두 발견] 즉시 CCCD 활성화 태스크 가동");
            xTaskCreate(ble_subscribe_task, "sub_task", 3072, (void *)(uintptr_t)conn_handle, 5, NULL);
        }
    }
    return 0;
}

static int on_disc_svc(uint16_t conn_handle, const struct ble_gatt_error *error,
                       const struct ble_gatt_svc *svc, void *arg) {
    if (error->status == 0 && svc != NULL) {
        if (ble_uuid_cmp(&svc->uuid.u, &S3_SVC_UUID.u) == 0) {
            ESP_LOGI(TAG, "🟢 [S3 서비스 발견] Start: %d, End: %d", svc->start_handle, svc->end_handle);
            ble_gattc_disc_all_chrs(conn_handle, svc->start_handle, svc->end_handle, on_disc_chr, NULL);
        }
    }
    return 0;
}

static int on_mtu_exchange(uint16_t conn_handle, const struct ble_gatt_error *error,
                          uint16_t mtu, void *arg) {
    if (error->status == 0) {
        ESP_LOGI(TAG, "🚀 [MTU 협상 성공] MTU: %d 바이트", mtu);
    } else {
        ESP_LOGW(TAG, "⚠️ [MTU 협상 기본값 유지] Code: %d", error->status);
    }
    ble_gattc_disc_all_svcs(conn_handle, on_disc_svc, NULL);
    return 0;
}

static void ble_client_scan(void) {
    uint8_t own_addr_type;
    if (ble_hs_id_infer_auto(0, &own_addr_type) != 0) return;

    struct ble_gap_disc_params disc_params = {
        .filter_duplicates = 0,
        .passive = 0,
        .itvl = 0x0040,
        .window = 0x0030,
        .filter_policy = 0,
        .limited = 0
    };
    ESP_LOGI(TAG, "🔍 S3 탐색 중... ('%s')", TARGET_DEVICE_NAME);
    ble_gap_disc(own_addr_type, BLE_HS_FOREVER, &disc_params, ble_gap_event, NULL);
}

static int ble_gap_event(struct ble_gap_event *event, void *arg) {
    struct ble_hs_adv_fields fields;

    switch (event->type) {
    case BLE_GAP_EVENT_DISC:
        if (ble_hs_adv_parse_fields(&fields, event->disc.data, event->disc.length_data) == 0) {
            bool is_match = false;
            for (int i = 0; i < fields.num_uuids128; i++) {
                if (ble_uuid_cmp(&fields.uuids128[i].u, &S3_SVC_UUID.u) == 0) {
                    is_match = true; break;
                }
            }
            if (!is_match && fields.name != NULL && fields.name_len > 0) {
                char dev_name[32] = {0};
                int len = (fields.name_len < 31) ? fields.name_len : 31;
                memcpy(dev_name, fields.name, len);
                if (strstr(dev_name, "ESP32S3") != NULL || strstr(dev_name, "EMERGENCY") != NULL) {
                    is_match = true;
                }
            }

            if (is_match) {
                ESP_LOGI(TAG, "🎯 타겟 S3 발견! 즉시 연결 시도...");
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
            ESP_LOGI(TAG, "🟢 S3 연결 성공 (Handle: %d) -> MTU 확장 요청...", g_conn_handle);
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
        ESP_LOGW(TAG, "🔴 S3 연결 끊김 -> 재스캔 시작");
        g_conn_handle = BLE_HS_CONN_HANDLE_NONE;
        g_handle_emergency = 0;
        g_handle_radar1 = 0;
        g_handle_radar2 = 0;
        ble_client_scan();
        break;

    case BLE_GAP_EVENT_NOTIFY_RX: {
        uint16_t attr_handle = event->notify_rx.attr_handle;
        uint16_t pkt_len = OS_MBUF_PKTLEN(event->notify_rx.om);
        uint8_t rx_buf[64] = {0};
        os_mbuf_copydata(event->notify_rx.om, 0, pkt_len < sizeof(rx_buf) ? pkt_len : sizeof(rx_buf), rx_buf);

        if (xSemaphoreTake(s_sensor_mutex, pdMS_TO_TICKS(10)) == pdTRUE) {
            if (attr_handle == g_handle_emergency) {
                s_rx_em_cnt++;
                char msg[32] = {0};
                memcpy(msg, rx_buf, pkt_len < sizeof(msg) ? pkt_len : sizeof(msg) - 1);

                if (strstr(msg, "살려") != NULL) s_p4_pkt.emergency_code = 1;
                else if (strstr(msg, "도와") != NULL) s_p4_pkt.emergency_code = 2;
                else if (strstr(msg, "구해") != NULL) s_p4_pkt.emergency_code = 3;
                else if (strstr(msg, "CALL_START") != NULL) s_p4_pkt.emergency_code = 1;
                else if (strstr(msg, "CALL_END") != NULL) s_p4_pkt.emergency_code = 0;

                if (s_p4_pkt.emergency_code > 0) {
                    s_emergency_trigger_time = xTaskGetTickCount() * portTICK_PERIOD_MS;
                }
                ESP_LOGW(TAG, "🚨 [비상 음성 감지] '%s' (Code: %d)", msg, s_p4_pkt.emergency_code);
            }
            else if (attr_handle == g_handle_radar1) {
                s_rx_r1_cnt++;
                parse_ld2450_frame(rx_buf, pkt_len, s_p4_pkt.r1_x, s_p4_pkt.r1_y, &s_p4_pkt.r1_detected);
            }
            else if (attr_handle == g_handle_radar2) {
                s_rx_r2_cnt++;
                parse_ld2450_frame(rx_buf, pkt_len, s_p4_pkt.r2_x, s_p4_pkt.r2_y, &s_p4_pkt.r2_detected);
            }
            xSemaphoreGive(s_sensor_mutex);
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

// ------------------- [1초 주기 진단 모니터링] -------------------
static void diagnostic_monitor_task(void *pvParameters) {
    while (1) {
        vTaskDelay(pdMS_TO_TICKS(1000));

        wroom_to_p4_pkt_t snap;
        if (xSemaphoreTake(s_sensor_mutex, pdMS_TO_TICKS(10)) == pdTRUE) {
            snap = s_p4_pkt;
            xSemaphoreGive(s_sensor_mutex);
        }

        const char *em_str = (snap.emergency_code == 1) ? "🚨 살려주세요 (1)" :
                             (snap.emergency_code == 2) ? "🚨 도와주세요 (2)" :
                             (snap.emergency_code == 3) ? "🚨 구해주세요 (3)" : "정상 (0)";

        ESP_LOGI(TAG, "===================== [S3 ➔ WROOM 수신 모니터] =====================");
        ESP_LOGI(TAG, "🔗 BLE 연결 : %s | 패킷 수신: R1(%lu) R2(%lu) 비상(%lu)",
                 s_ble_connected ? "🟢 정상 연결됨" : "🔴 탐색중...", 
                 s_rx_r1_cnt, s_rx_r2_cnt, s_rx_em_cnt);
        ESP_LOGI(TAG, "🎯 R1 (진입): %s | T1:(%5d,%5d) T2:(%5d,%5d) T3:(%5d,%5d)",
                 snap.r1_detected ? "🔴감지" : "⚪미감지",
                 snap.r1_x[0], snap.r1_y[0], snap.r1_x[1], snap.r1_y[1], snap.r1_x[2], snap.r1_y[2]);
        ESP_LOGI(TAG, "🎯 R2 (퇴장): %s | T1:(%5d,%5d) T2:(%5d,%5d) T3:(%5d,%5d)",
                 snap.r2_detected ? "🔴감지" : "⚪미감지",
                 snap.r2_x[0], snap.r2_y[0], snap.r2_x[1], snap.r2_y[1], snap.r2_x[2], snap.r2_y[2]);
        ESP_LOGI(TAG, "🎙️ 비상 상태: %s | 누적 인원: In %d명 / Out %d명",
                 em_str, snap.in_count, snap.out_count);
        ESP_LOGI(TAG, "=====================================================================");
    }
}

// ------------------- [P4 바이너리 전송] -------------------
static void radar_process_task(void *pvParameters) {
    int prev_primary_y = 0;
    int tracking_state = 0;
    uint8_t tx_frame[34];

    while (1) {
        uint32_t now = xTaskGetTickCount() * portTICK_PERIOD_MS;
        wroom_to_p4_pkt_t snap;

        if (xSemaphoreTake(s_sensor_mutex, pdMS_TO_TICKS(20)) == pdTRUE) {
            if (s_p4_pkt.emergency_code > 0 && (now - s_emergency_trigger_time > 3000)) {
                s_p4_pkt.emergency_code = 0;
            }

            int primary_y = 0;
            if (s_p4_pkt.r1_detected) {
                for (int i = 0; i < 3; i++) {
                    if (s_p4_pkt.r1_y[i] != 0) {
                        primary_y = abs(s_p4_pkt.r1_y[i]);
                        break;
                    }
                }
            }

            if (primary_y > 0) {
                if (prev_primary_y > 0) {
                    int delta = primary_y - prev_primary_y;
                    if (delta < -250 && tracking_state == 0) tracking_state = 1;
                    else if (delta > 250 && tracking_state == 0) tracking_state = 2;

                    if (tracking_state == 1 && primary_y < 800) {
                        s_p4_pkt.in_count++;
                        tracking_state = 0;
                    } else if (tracking_state == 2 && primary_y > 2500) {
                        s_p4_pkt.out_count++;
                        tracking_state = 0;
                    }
                }
                prev_primary_y = primary_y;
            } else {
                tracking_state = 0;
                prev_primary_y = 0;
            }

            snap = s_p4_pkt;
            xSemaphoreGive(s_sensor_mutex);
        }

        // 34바이트 패킷 조립
        tx_frame[0] = 0xAA;
        tx_frame[1] = 0x55;
        tx_frame[2] = (uint8_t)((snap.in_count >> 8) & 0xFF);
        tx_frame[3] = (uint8_t)(snap.in_count & 0xFF);
        tx_frame[4] = (uint8_t)((snap.out_count >> 8) & 0xFF);
        tx_frame[5] = (uint8_t)(snap.out_count & 0xFF);

        for (int i = 0; i < 3; i++) {
            tx_frame[6 + (i * 2)]  = (uint8_t)((snap.r1_x[i] >> 8) & 0xFF);
            tx_frame[7 + (i * 2)]  = (uint8_t)(snap.r1_x[i] & 0xFF);
            tx_frame[12 + (i * 2)] = (uint8_t)((snap.r1_y[i] >> 8) & 0xFF);
            tx_frame[13 + (i * 2)] = (uint8_t)(snap.r1_y[i] & 0xFF);
            tx_frame[18 + (i * 2)] = (uint8_t)((snap.r2_x[i] >> 8) & 0xFF);
            tx_frame[19 + (i * 2)] = (uint8_t)(snap.r2_x[i] & 0xFF);
            tx_frame[24 + (i * 2)] = (uint8_t)((snap.r2_y[i] >> 8) & 0xFF);
            tx_frame[25 + (i * 2)] = (uint8_t)(snap.r2_y[i] & 0xFF);
        }
        tx_frame[30] = snap.r1_detected;
        tx_frame[31] = snap.r2_detected;
        tx_frame[32] = snap.emergency_code;

        // 체크섬 계산 (인덱스 2~32 XOR)
        uint8_t chk = 0;
        for (int i = 2; i < 33; i++) {
            chk ^= tx_frame[i];
        }
        tx_frame[33] = chk;

        // 메인 통합 UART로 34B 전송
        p4_uart_send_bytes(tx_frame, 34);

        vTaskDelay(pdMS_TO_TICKS(50));
    }
}

// ------------------- [SD / I2S / UART 초기화] -------------------
static esp_err_t init_i2s_driver(void) {
    i2s_chan_config_t chan_cfg = I2S_CHANNEL_DEFAULT_CONFIG(I2S_NUM_0, I2S_ROLE_MASTER);
    chan_cfg.dma_desc_num = 8;
    chan_cfg.dma_frame_num = 256;
    chan_cfg.auto_clear = true;

    ESP_ERROR_CHECK(i2s_new_channel(&chan_cfg, &s_tx_chan, NULL));

    i2s_std_config_t std_cfg = {
        .clk_cfg = I2S_STD_CLK_DEFAULT_CONFIG(44100),
        .slot_cfg = I2S_STD_PHILIPS_SLOT_DEFAULT_CONFIG(I2S_DATA_BIT_WIDTH_16BIT, I2S_SLOT_MODE_STEREO),
        .gpio_cfg = {
            .mclk = I2S_GPIO_UNUSED,
            .bclk = I2S_BCLK_PIN,
            .ws   = I2S_LRCK_PIN,
            .dout = I2S_DOUT_PIN,
            .din  = I2S_GPIO_UNUSED,
            .invert_flags = { .mclk_inv = false, .bclk_inv = false, .ws_inv = false },
        },
    };

    ESP_ERROR_CHECK(i2s_channel_init_std_mode(s_tx_chan, &std_cfg));
    ESP_ERROR_CHECK(i2s_channel_enable(s_tx_chan));
    return ESP_OK;
}

static void init_p4_uarts(void) {
    uart_config_t uart_ctrl_cfg = {
        .baud_rate = 115200,
        .data_bits = UART_DATA_8_BITS,
        .parity    = UART_PARITY_DISABLE,
        .stop_bits = UART_STOP_BITS_1,
        .flow_ctrl = UART_HW_FLOWCTRL_DISABLE,
        .source_clk = UART_SCLK_DEFAULT,
    };
    ESP_ERROR_CHECK(uart_driver_install(P4_UART_NUM, UART_BUF_SIZE * 2, UART_BUF_SIZE * 2, 0, NULL, 0));
    ESP_ERROR_CHECK(uart_param_config(P4_UART_NUM, &uart_ctrl_cfg));
    ESP_ERROR_CHECK(uart_set_pin(P4_UART_NUM, P4_TX_PIN, P4_RX_PIN, UART_PIN_NO_CHANGE, UART_PIN_NO_CHANGE));
}

static void p4_rx_task(void *pvParameters) {
    uint8_t *data = (uint8_t *) malloc(UART_BUF_SIZE);
    if (!data) vTaskDelete(NULL);
    char line_buf[128];
    int line_pos = 0;

    while (1) {
        int len = uart_read_bytes(P4_UART_NUM, data, UART_BUF_SIZE - 1, pdMS_TO_TICKS(20));
        if (len > 0) {
            for (int i = 0; i < len; i++) {
                char ch = (char)data[i];
                if (ch == '\n' || ch == '\r') {
                    if (line_pos > 0) {
                        line_buf[line_pos] = '\0';
                        if (strstr(line_buf, "$MUSIC,ON") != NULL) {
                            s_music_playing = true;
                            p4_uart_send_bytes("$MUSIC,ACK\n", 11);
                        } else if (strstr(line_buf, "$MUSIC,OFF") != NULL) {
                            s_music_playing = false;
                            p4_uart_send_bytes("$MUSIC,OFF_ACK\n", 15);
                        } else if (strstr(line_buf, "$CTRL,") != NULL) {
                            int vol = 50, mode = 0, track = 1;
                            if (sscanf(line_buf, "$CTRL,%d,%d,%d", &vol, &mode, &track) == 3) {
                                if (vol < 0) vol = 0;
                                if (vol > 100) vol = 100;
                                s_current_volume = vol;
                                float ratio = (float)vol / 100.0f;
                                s_volume_factor = ratio * ratio;
                                s_play_mode = mode;
                                if (mode == 2 && track > 0 && s_target_track != track) {
                                    s_target_track = track;
                                    s_track_changed = true; 
                                }
                                p4_uart_send_bytes("$CTRL_ACK\n", 10);
                            }
                        }
                        line_pos = 0;
                    }
                } else {
                    if (line_pos < (int)sizeof(line_buf) - 1) line_buf[line_pos++] = ch;
                }
            }
        }
        vTaskDelay(pdMS_TO_TICKS(1));
    }
    free(data);
    vTaskDelete(NULL);
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
        .format_if_mount_failed = false,
        .max_files = 5,
        .allocation_unit_size = 16 * 1024
    };
    sdmmc_card_t *card;
    spi_bus_config_t bus_cfg = {
        .mosi_io_num = PIN_NUM_MOSI,
        .miso_io_num = PIN_NUM_MISO,
        .sclk_io_num = PIN_NUM_CLK,
        .quadwp_io_num = -1,
        .quadhd_io_num = -1,
        .max_transfer_sz = 4000,
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

static void mp3_player_task(void *pvParameters) {
    HMP3Decoder hMP3Decoder = MP3InitDecoder();
    if (!hMP3Decoder) vTaskDelete(NULL);

    uint8_t *file_buf = malloc(FILE_BUF_SIZE);
    int16_t *pcm_buf = malloc(PCM_BUF_SIZE);
    if (!file_buf || !pcm_buf) {
        if (file_buf) free(file_buf);
        if (pcm_buf) free(pcm_buf);
        MP3FreeDecoder(hMP3Decoder);
        vTaskDelete(NULL);
    }

    uint32_t last_eq_send_time = 0;
    int current_playing_track = s_target_track;
    FILE *f = open_mp3_track_file(current_playing_track);
    if (!f) {
        free(file_buf); free(pcm_buf);
        MP3FreeDecoder(hMP3Decoder);
        vTaskDelete(NULL);
    }

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

        if (!s_music_playing) {
            vTaskDelay(pdMS_TO_TICKS(20));
            continue;
        }

        if (bytes_in_buffer < 1024) {
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
                continue;
            }
            bytes_in_buffer += bytes_read;
            read_ptr = file_buf;
        }

        int offset = MP3FindSyncWord(read_ptr, bytes_in_buffer);
        if (offset < 0) { bytes_in_buffer = 0; continue; }

        read_ptr += offset;
        bytes_in_buffer -= offset;

        int err = MP3Decode(hMP3Decoder, &read_ptr, &bytes_in_buffer, pcm_buf, 0);
        if (err == ERR_MP3_NONE) {
            MP3FrameInfo frameInfo;
            MP3GetLastFrameInfo(hMP3Decoder, &frameInfo);
            
            if (frameInfo.samprate != s_current_sample_rate && frameInfo.samprate > 0) {
                s_current_sample_rate = frameInfo.samprate;
                i2s_std_clk_config_t clk_cfg = I2S_STD_CLK_DEFAULT_CONFIG(s_current_sample_rate);
                i2s_channel_reconfig_std_clock(s_tx_chan, &clk_cfg);
            }

            int sample_count = frameInfo.outputSamps;
            int pcm_bytes = sample_count * sizeof(int16_t);

            uint32_t now = xTaskGetTickCount() * portTICK_PERIOD_MS;
            if (s_music_playing && (now - last_eq_send_time >= 40)) {
                last_eq_send_time = now;
                int bands[8] = {0};
                int samples_per_band = sample_count / 8;
                for (int b = 0; b < 8; b++) {
                    int64_t sum = 0;
                    for (int i = 0; i < samples_per_band; i++) {
                        sum += abs(pcm_buf[b * samples_per_band + i]);
                    }
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

            size_t bytes_written = 0;
            i2s_channel_write(s_tx_chan, pcm_buf, pcm_bytes, &bytes_written, portMAX_DELAY);
        } else {
            vTaskDelay(pdMS_TO_TICKS(1));
        }
    }

    if (f) fclose(f);
    MP3FreeDecoder(hMP3Decoder);
    free(file_buf); free(pcm_buf);
    vTaskDelete(NULL);
}

// ------------------- [메인 진입점] -------------------
void app_main(void) {
    esp_err_t ret = nvs_flash_init();
    if (ret == ESP_ERR_NVS_NO_FREE_PAGES || ret == ESP_ERR_NVS_NEW_VERSION_FOUND) {
        ESP_ERROR_CHECK(nvs_flash_erase());
        ret = nvs_flash_init();
    }
    ESP_ERROR_CHECK(ret);

    s_sensor_mutex = xSemaphoreCreateMutex();
    s_uart_tx_mutex = xSemaphoreCreateMutex();

    // 1. NimBLE 시작
    nimble_port_init();
    ble_svc_gap_device_name_set("ESP32_WROOM_RECV");
    ble_hs_cfg.sync_cb = ble_client_scan;
    nimble_port_freertos_init(ble_host_task);

    // 2. UART 단일 채널 & I2S 초기화
    init_p4_uarts();
    ESP_ERROR_CHECK(init_i2s_driver());

    // 3. 태스크 실행
    xTaskCreatePinnedToCore(p4_rx_task, "p4_rx_task", 3072, NULL, 5, NULL, 0);
    xTaskCreatePinnedToCore(radar_process_task, "radar_process_task", 3072, NULL, 4, NULL, 0);
    xTaskCreatePinnedToCore(diagnostic_monitor_task, "diag_task", 3072, NULL, 1, NULL, 0);

    if (init_sd_card() == ESP_OK) {
        xTaskCreatePinnedToCore(mp3_player_task, "mp3_player_task", 8192, NULL, 5, NULL, 1);
    }
}