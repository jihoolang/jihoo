#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

extern int64_t jihoo_add(int64_t, int64_t);
extern bool jihoo_flip(bool);
extern int8_t jihoo_small(int8_t);
extern double jihoo_float(double);

struct ExportPair { double x; int64_t y; };
struct ExportLarge { int64_t a, b, c; };
extern struct ExportPair jihoo_pair(struct ExportPair);
extern struct ExportLarge jihoo_large(struct ExportLarge);
extern __int128 jihoo_i128(__int128);

int main(void) {
    struct ExportPair p = jihoo_pair((struct ExportPair){1.5, 41});
    struct ExportLarge l = jihoo_large((struct ExportLarge){1, 2, 3});
    if (p.x != 3.0 || p.y != 42 || l.a != 2 || l.b != 4 || l.c != 6 ||
        jihoo_i128(-7) != (((__int128)1 << 100) - 7)) return 1;
    if (jihoo_add(20, 22) != 42 || !jihoo_flip(false) || jihoo_flip(true) ||
        jihoo_small(-100) != -101 || jihoo_float(1.5) != 3.0)
        return 1;
    puts("C called jihoo");
    return 0;
}
