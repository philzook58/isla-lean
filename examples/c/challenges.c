/* C corpus: lean-pcode's challenges/challenges.c functions, plus larger loops.
   Built once per optimization level; NAME appends the level so both coexist in one binary. */
#include <stddef.h>
#include <stdint.h>

#ifndef LEVEL
#define LEVEL O0
#endif
#define CAT2(a, b) a##_##b
#define CAT(a, b) CAT2(a, b)
#define NAME(f) CAT(f, LEVEL)
#define TARGET __attribute__((noinline, noclone))

/* lean-pcode's corpus. */
TARGET uint32_t NAME(inc_u32)(uint32_t x) { return x + 1u; }
TARGET uint32_t NAME(max_u32)(uint32_t x, uint32_t y) { return x < y ? y : x; }
TARGET uint32_t NAME(mix_u32)(uint32_t x, uint32_t y) {
    return ((x * 33u) ^ (y >> (x & 31u))) + (x << (y & 31u));
}
TARGET uint32_t NAME(sum_u32)(const uint32_t *a, uint32_t n) {
    uint32_t sum = 0;
    for (uint32_t i = 0; i < n; ++i) sum += a[i];
    return sum;
}
TARGET uint32_t NAME(find_u32)(const uint32_t *a, uint32_t n, uint32_t key) {
    for (uint32_t i = 0; i < n; ++i) if (a[i] == key) return i;
    return n;
}
TARGET uint32_t NAME(copy_bytes)(uint8_t *dst, const uint8_t *src, uint32_t n) {
    for (uint32_t i = 0; i < n; ++i) dst[i] = src[i];
    return n;
}

/* Larger: nested loops with loads and stores. */
TARGET void NAME(isort_u32)(uint32_t *a, uint32_t n) {
    for (uint32_t i = 1; i < n; ++i) {
        uint32_t v = a[i], j = i;
        while (j > 0 && a[j - 1] > v) { a[j] = a[j - 1]; --j; }
        a[j] = v;
    }
}
/* Division: remu, with a data-dependent trip count. */
TARGET uint64_t NAME(gcd_u64)(uint64_t a, uint64_t b) {
    while (b != 0) { uint64_t t = a % b; a = b; b = t; }
    return a;
}
/* Bitwise CRC-32 over a byte buffer: nested loop, shifts, xor, masks. */
TARGET uint32_t NAME(crc32_bytes)(const uint8_t *p, size_t n) {
    uint32_t crc = 0xffffffffu;
    for (size_t i = 0; i < n; ++i) {
        crc ^= p[i];
        for (int k = 0; k < 8; ++k) crc = (crc >> 1) ^ (0xedb88320u & (0u - (crc & 1u)));
    }
    return ~crc;
}
TARGET uint64_t NAME(popcount_u64)(uint64_t x) {
    uint64_t c = 0;
    while (x) { x &= x - 1; ++c; }
    return c;
}
TARGET size_t NAME(strlen_bytes)(const char *s) {
    size_t n = 0;
    while (s[n]) ++n;
    return n;
}
/* A dense switch: GCC may emit a jump table (an indirect jump through data). */
TARGET uint32_t NAME(classify)(uint32_t x) {
    switch (x) {
    case 0: return 11; case 1: return 23; case 2: return 37; case 3: return 41;
    case 4: return 53; case 5: return 67; case 6: return 79; case 7: return 83;
    default: return 0;
    }
}
