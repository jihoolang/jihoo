#define _POSIX_C_SOURCE 200809L
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef int64_t (*Kernel)(const int64_t *, int64_t, int64_t, int64_t, int64_t);
extern int64_t functional(const int64_t *, int64_t, int64_t, int64_t, int64_t);
extern int64_t iterator(const int64_t *, int64_t, int64_t, int64_t, int64_t);
extern int64_t staged(const int64_t *, int64_t, int64_t, int64_t, int64_t);
extern int64_t eager(const int64_t *, int64_t, int64_t, int64_t, int64_t);
extern int64_t handwritten(const int64_t *, int64_t, int64_t, int64_t, int64_t);
extern int64_t ordered(const int64_t *, int64_t, int64_t, int64_t, int64_t);
extern int64_t c_loop(const int64_t *, int64_t, int64_t, int64_t, int64_t);

static const char *names[] = {"functional", "staged", "iterator", "eager", "handwritten", "c"};
static Kernel kernels[] = {functional, staged, iterator, eager, handwritten, c_loop};
#define KERNEL_COUNT (sizeof(kernels) / sizeof(kernels[0]))
static int counting;
static uint64_t allocations, frees;
extern void *__real_malloc(size_t);
extern void *__real_realloc(void *, size_t);
extern void __real_free(void *);
void *__wrap_malloc(size_t n) {
    if (counting) ++allocations;
    return __real_malloc(n);
}
void *__wrap_realloc(void *p, size_t n) {
    if (counting) ++allocations;
    return __real_realloc(p, n);
}
void __wrap_free(void *p) {
    if (counting && p) ++frees;
    __real_free(p);
}

static uint64_t rng = 42;
static uint64_t random_word(void) {
    rng = rng * UINT64_C(6364136223846793005) + 1;
    return rng;
}

static void verify(int wrapping) {
    int64_t xs[65];
    for (int trial = 0; trial < 600; ++trial) {
        int64_t n = trial % 66;
        for (int64_t i = 0; i < n; ++i)
            xs[i] = (int64_t)(random_word() % 201) - 100;
        int64_t scale = trial % 9 - 4;
        int64_t offset = trial % 23 - 11;
        int64_t limit = trial % 401 - 200;
        if (wrapping && trial >= 300) {
            for (int64_t i = 0; i < n; ++i) xs[i] = (int64_t)random_word();
            scale = (int64_t)random_word();
            offset = (int64_t)random_word();
        }
        int64_t expected = c_loop(xs, n, scale, offset, limit);
        for (size_t k = 0; k < KERNEL_COUNT; ++k) {
            int64_t actual = kernels[k](xs, n, scale, offset, limit);
            if (actual != expected) {
                fprintf(stderr, "trial %d %s: got %" PRId64 ", expected %" PRId64 "\n",
                        trial, names[k], actual, expected);
                exit(1);
            }
        }
        // Small inputs keep this order-sensitive fold in range in checked mode.
        int64_t m = n % 6, acc = 7;
        for (int64_t i = 0; i < m; ++i) {
            int64_t y = xs[i] * scale + offset;
            if (y > limit) acc = acc * 31 + y;
        }
        if (ordered(xs, m, scale, offset, limit) != acc) abort();
    }
    puts("600 differential cases and 600 order-sensitive folds passed");
}

static double seconds(void) {
    struct timespec t;
    if (clock_gettime(CLOCK_MONOTONIC, &t)) abort();
    return (double)t.tv_sec + (double)t.tv_nsec * 1e-9;
}

int main(int argc, char **argv) {
    if (argc == 3 && strcmp(argv[1], "check") == 0) {
        verify(atoi(argv[2]));
        return 0;
    }
    if (argc != 4) return 2;
    size_t k = 0;
    while (k < KERNEL_COUNT && strcmp(argv[1], names[k])) ++k;
    if (k == KERNEL_COUNT) return 2;
    int64_t n = strtoll(argv[2], NULL, 10);
    int repetitions = atoi(argv[3]);
    if (n <= 0 || repetitions <= 0) return 2;
    int64_t *xs = malloc((size_t)n * sizeof(*xs));
    if (!xs) return 2;
    for (int64_t i = 0; i < n; ++i) xs[i] = (int64_t)(random_word() % 2001) - 1000;
    // Count one invocation independently of input setup and timing repetitions.
    counting = 1;
    int64_t sample = kernels[k](xs, n, 3, 1, 50);
    counting = 0;
    uint64_t checksum = 0;
    double start = seconds();
    for (int i = 0; i < repetitions; ++i)
        checksum += (uint64_t)kernels[k](xs, n, 3, i % 17, 50 + i % 13);
    double elapsed = seconds() - start;
    free(xs);
    printf("{\"seconds\":%.9f,\"checksum\":\"%" PRIu64 "\",\"sample\":\"%" PRId64
           "\",\"allocations\":%" PRIu64 ",\"frees\":%" PRIu64 "}\n",
           elapsed, checksum, sample, allocations, frees);
    return 0;
}
