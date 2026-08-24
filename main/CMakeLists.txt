file(GLOB_RECURSE srcs "*.c" "src/*.c")

idf_component_register(
    SRCS "main.c" "${srcs}"
    INCLUDE_DIRS "." "include" "src"
    PRIV_REQUIRES 
        bt
        nvs_flash
        fatfs
        vfs
        sdmmc
        driver
        esp_driver_gpio
        esp_driver_uart
        esp_driver_i2s
        helix_mp3
        espressif__led_strip
)