#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

extern uint8_t checked_byte(const uint8_t *, int64_t, int64_t);

_Noreturn void host_panic(const char *msg, int64_t len) {
    printf("host: %.*s\n", (int)len, msg);
    exit(7);
}

int main(void) {
    const uint8_t bytes[] = {4, 5, 6};
    printf("%d\n", checked_byte(bytes, 3, 2));
    checked_byte(bytes, 3, 3);
    return 0;
}
