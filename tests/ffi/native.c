#include <stdbool.h>
#include <stdint.h>
#include <stdarg.h>

int8_t ffi_i8(int8_t x) { return x - 1; }
uint8_t ffi_u8(uint8_t x) { return x + 1; }
int16_t ffi_i16(int16_t x) { return x - 1; }
uint16_t ffi_u16(uint16_t x) { return x + 1; }
bool ffi_bool(bool x) { return !x; }
float ffi_float(float x) { return x * 2; }
double ffi_double(double x) { return x * 2; }

struct Pair { int32_t first; int64_t second; };
void ffi_pair(struct Pair *p) { p->first += 1; p->second += 2; }

bool ffi_callback(bool (*f)(bool), bool x) { return f(x); }
int8_t ffi_small_callback(int8_t (*f)(int8_t), int8_t x) { return f(x); }

// Read the promoted types, rather than depending on printf's permissiveness.
int32_t ffi_promotions(int32_t tag, ...) {
    va_list ap;
    va_start(ap, tag);
    int a = va_arg(ap, int);
    int b = va_arg(ap, int);
    int c = va_arg(ap, int);
    double d = va_arg(ap, double);
    va_end(ap);
    return tag + a + b + c + (int)d;
}
