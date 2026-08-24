#include <stdlib.h>

// helix 디코더가 내부적으로 호출하는 메모리 할당 함수 구현
void *helix_malloc(size_t size) {
    return malloc(size);
}

void helix_free(void *ptr) {
    free(ptr);
}