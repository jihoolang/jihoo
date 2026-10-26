#include "aggregates.h"
#include <stdarg.h>

struct Tiny abi_tiny(struct Tiny v) { v.bytes[0]++; v.bytes[2] += 3; return v; }
struct IntPair abi_pair(struct IntPair v) { v.a += 10; v.b += 20; return v; }
struct Mixed abi_mixed(struct Mixed v) { v.x *= 2; v.y += 3; return v; }
struct Reverse abi_reverse(struct Reverse v) { v.x *= 2; v.y += 3; return v; }
struct FloatPair abi_floats(struct FloatPair v) { v.a += 1; v.b += 2; return v; }
struct Float3 abi_float3(struct Float3 v) { v.v[0] += 1; v.v[2] += 3; return v; }
struct Hfa4 abi_hfa4(struct Hfa4 v) { v.p[0].a += 1; v.p[1].b += 4; return v; }
struct Double4 abi_double4(struct Double4 v) { v.v[0] += 1; v.v[3] += 4; return v; }
struct Large abi_large(struct Large v) { v.a += 1; v.b += 2; v.c += 3; return v; }
struct Wide abi_wide(struct Wide v) { v.x += ((__int128)1 << 90) + 7; return v; }
struct Aligned abi_aligned(struct Aligned v) { v.tag += 1; v.x += ((__int128)1 << 90) + 7; return v; }
struct Nested abi_nested(struct Nested v) { v.pair.a += 1; v.tiny.bytes[2] += 3; v.z -= 4; return v; }
struct FloatInt abi_float_int(struct FloatInt v) { v.f += 1; v.i -= 2; return v; }
struct Tail abi_tail(struct Tail v) { v.d += 1; v.f += 2; return v; }
struct Bytes17 abi_bytes17(struct Bytes17 v) { v.v[0]++; v.v[16] += 2; return v; }
struct Flags abi_flags(struct Flags v) { v.a = !v.a; v.b = !v.b; return v; }
__int128 abi_i128(__int128 x) { return x + ((__int128)1 << 100) + 9; }
unsigned __int128 abi_u128(unsigned __int128 x) { return x ^ ((unsigned __int128)1 << 127); }

// All-or-nothing allocation: a mixed or two-register argument must spill
// together, leaving remaining registers available for later arguments.
int64_t abi_gp(int64_t a, int64_t b, int64_t c, int64_t d, int64_t e, struct IntPair p, int64_t z) {
    return a+b+c+d+e+p.a+p.b+z;
}
int64_t abi_gp_mixed(int64_t a, int64_t b, int64_t c, int64_t d, int64_t e, int64_t f, struct Mixed p, double z) {
    return a+b+c+d+e+f+(int64_t)p.x+p.y+(int64_t)z;
}
double abi_fp(double a, double b, double c, double d, double e, double f, double g, struct FloatPair p, double z) {
    return a+b+c+d+e+f+g+p.a+p.b+z;
}
double abi_fp_pair(double a, double b, double c, double d, double e, double f, double g, struct Tail p, double z) {
    return a+b+c+d+e+f+g+p.d+p.f+z;
}
__int128 abi_gp_i128(int64_t a, int64_t b, int64_t c, int64_t d, int64_t e, __int128 x, int64_t z) {
    return x + a+b+c+d+e+z;
}
struct Wide abi_gp_wide(int64_t a, int64_t b, int64_t c, int64_t d, int64_t e, struct Wide x, int64_t z) {
    x.x += a+b+c+d+e+z; return x;
}
struct Large abi_sret(int64_t a, int64_t b, int64_t c, int64_t d, struct IntPair p, int64_t z) {
    return (struct Large){a+b+c+d, p.a+p.b, z};
}
struct IntPair abi_callback(struct IntPair (*f)(struct IntPair), struct IntPair x) { return f(x); }
struct Float3 abi_callback_float3(struct Float3 (*f)(struct Float3), struct Float3 x) { return f(x); }
struct Large abi_callback_large(struct Large (*f)(struct Large), struct Large x) { return f(x); }
__int128 abi_callback_i128(__int128 (*f)(__int128), __int128 x) { return f(x); }

int64_t abi_varargs(int tag, ...) {
    va_list ap; va_start(ap, tag);
    struct IntPair p = va_arg(ap, struct IntPair);
    struct Mixed m = va_arg(ap, struct Mixed);
    struct Double4 h = va_arg(ap, struct Double4);
    struct Large l = va_arg(ap, struct Large);
    __int128 n = va_arg(ap, __int128);
    int small = va_arg(ap, int);
    double real = va_arg(ap, double);
    va_end(ap);
    return tag+p.a+p.b+(int64_t)m.x+m.y+(int64_t)h.v[3]+l.a+l.b+l.c+(int64_t)n+small+(int64_t)real;
}

extern struct IntPair jh_pair(struct IntPair);
extern struct Mixed jh_mixed(struct Mixed);
extern struct Float3 jh_float3(struct Float3);
extern struct Double4 jh_double4(struct Double4);
extern struct Large jh_large(struct Large);
extern struct Tiny jh_tiny(struct Tiny);
extern struct Aligned jh_aligned(struct Aligned);
extern __int128 jh_i128(__int128);
extern int64_t jh_gp(int64_t,int64_t,int64_t,int64_t,int64_t,struct IntPair,int64_t);
extern double jh_fp(double,double,double,double,double,double,double,struct Tail,double);
int abi_check_exports(void) {
    struct IntPair p = jh_pair((struct IntPair){1,2});
    struct Mixed m = jh_mixed((struct Mixed){1.5,4});
    struct Float3 f = jh_float3((struct Float3){{1,2,3}});
    struct Double4 h = jh_double4((struct Double4){{1,2,3,4}});
    struct Large l = jh_large((struct Large){1,2,3});
    struct Tiny t = jh_tiny((struct Tiny){{1,2,3}});
    struct Aligned a = jh_aligned((struct Aligned){5,(__int128)1 << 80});
    return p.a==11 && p.b==22 && m.x==3 && m.y==7 && f.v[0]==2 && f.v[2]==6 &&
        h.v[0]==2 && h.v[3]==8 && l.a==2 && l.b==4 && l.c==6 && t.bytes[0]==2 && t.bytes[2]==6 &&
        a.tag==6 && a.x==(((__int128)1 << 80)+((__int128)1 << 90)+7) &&
        jh_i128(-7)==(((__int128)1 << 100)+2) &&
        jh_gp(1,2,3,4,5,(struct IntPair){6,7},8)==36 &&
        jh_fp(1,2,3,4,5,6,7,(struct Tail){8,9},10)==55;
}

static int64_t node_value(struct Node n) { return n.value; }
struct Node abi_node(struct Node n) { n.apply = node_value; n.value++; return n; }
int64_t abi_stack(int64_t a, int64_t b, int64_t c, int64_t d, int64_t e, int64_t f, int64_t g, int64_t h,
                  struct Tiny t, struct Wide w, struct Float3 p, int64_t z) {
    return a+b+c+d+e+f+g+h+t.bytes[0]+t.bytes[1]+t.bytes[2]+(int64_t)w.x+(int64_t)(p.v[0]+p.v[1]+p.v[2])+z;
}
int64_t abi_varspill(int64_t a, int64_t b, int64_t c, int64_t d, int64_t e,
                     double f0, double f1, double f2, double f3, double f4, double f5, double f6, ...) {
    va_list ap; va_start(ap, f6);
    struct IntPair p = va_arg(ap, struct IntPair);
    struct Mixed m = va_arg(ap, struct Mixed);
    struct Float3 h = va_arg(ap, struct Float3);
    __int128 w = va_arg(ap, __int128);
    struct Large l = va_arg(ap, struct Large);
    int small = va_arg(ap, int);
    double real = va_arg(ap, double);
    va_end(ap);
    return a+b+c+d+e+(int64_t)(f0+f1+f2+f3+f4+f5+f6)+p.a+p.b+(int64_t)m.x+m.y+
        (int64_t)(h.v[0]+h.v[1]+h.v[2])+(int64_t)w+l.a+l.b+l.c+small+(int64_t)real;
}
