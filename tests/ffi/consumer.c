#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

extern int64_t jihoo_add(int64_t, int64_t);
extern bool jihoo_flip(bool);
extern int8_t jihoo_small(int8_t);
extern double jihoo_float(double);

int main(void) {
    if (jihoo_add(20, 22) != 42 || !jihoo_flip(false) || jihoo_flip(true) ||
        jihoo_small(-100) != -101 || jihoo_float(1.5) != 3.0)
        return 1;
    puts("C called jihoo");
    return 0;
}
