#include <stdint.h>

int64_t c_loop(const int64_t *xs, int64_t n, int64_t scale,
               int64_t offset, int64_t limit) {
    int64_t total = 0;
    for (int64_t i = 0; i < n; ++i) {
        int64_t y = xs[i] * scale + offset;
        if (y > limit) total += y;
    }
    return total;
}
