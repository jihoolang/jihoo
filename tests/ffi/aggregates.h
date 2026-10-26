#ifndef JIHOO_TEST_AGGREGATES_H
#define JIHOO_TEST_AGGREGATES_H
#include <stdint.h>
#include <stdbool.h>
struct Tiny { uint8_t bytes[3]; };
struct IntPair { int64_t a, b; };
struct Mixed { double x; int32_t y; };
struct Reverse { int32_t y; double x; };
struct FloatPair { float a, b; };
struct Float3 { float v[3]; };
struct Hfa4 { struct FloatPair p[2]; };
struct Double4 { double v[4]; };
struct Large { int64_t a, b, c; };
struct Wide { __int128 x; };
struct Aligned { uint8_t tag; __int128 x; };
struct Nested { struct IntPair pair; struct Tiny tiny; int16_t z; };
struct FloatInt { float f; int32_t i; };
struct Tail { double d; float f; };
struct Bytes17 { uint8_t v[17]; };
struct Flags { bool a, b; };
struct Node { int64_t (*apply)(struct Node); int64_t value; };
#endif
