/* Generated C code from Oak */
#include <stdint.h>
#include <stddef.h>
#if !__STDC_HOSTED__ || defined(OAK_FREESTANDING)
/* freestanding host boundary (docs/spec/90-backend.md section 2a): a weak
   hook the kernel or firmware may define; diagnostics reach it, then trap */
extern int64_t oak_host_write(int64_t fd, const uint8_t *buf, size_t len) __attribute__((weak));
static void oak_report(const char *what, const char *file, uint32_t line) {
  if (&oak_host_write == 0) { return; }
  uint8_t buf[192]; size_t n = 0;
  const char *parts[4] = { "oak: ", what, " at ", file };
  for (int p = 0; p < 4; p++) { for (const char *c = parts[p]; *c != 0 && n < sizeof buf - 16; c++) { buf[n++] = (uint8_t)*c; } }
  buf[n++] = ':';
  uint8_t digits[10]; int d = 0;
  do { digits[d++] = (uint8_t)('0' + line % 10u); line /= 10u; } while (line != 0u);
  while (d > 0) { buf[n++] = digits[--d]; }
  buf[n++] = '\n';
  (void)oak_host_write(2, buf, n);
}
#endif
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
#include <math.h>
#else
#ifndef signbit
#define signbit(x) __builtin_signbit(x)
#endif
#ifndef isnan
#define isnan(x) __builtin_isnan(x)
#endif
#ifndef isinf
#define isinf(x) __builtin_isinf(x)
#endif
#ifndef isfinite
#define isfinite(x) __builtin_isfinite(x)
#endif
#endif
#include <float.h>
#if FLT_EVAL_METHOD != 0
#error "Oak floating point requires FLT_EVAL_METHOD == 0: every operation rounds to its own type"
#endif
#if defined(__clang__)
#pragma STDC FP_CONTRACT OFF
#endif

/* the test host's launch recorder (docs/spec/110-testing.md, "Launch targets"): defined by the oak test harness */
extern void oak_test_host_launch_begin(const char *kernel, uint32_t grid);
extern void oak_test_host_launch_arg(const char *name, const char *kind, const char *element, const void *base, uint32_t bytes);
extern void oak_test_host_launch_out(const char *name, const void *base, uint32_t bytes);
extern void oak_test_host_launch_end(void);
typedef uint8_t  u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;
#if defined(__SIZEOF_INT128__)
typedef unsigned __int128 u128;
#endif

typedef int8_t   i8;
typedef int16_t i16;
typedef int32_t i32;
typedef int64_t i64;

typedef u8  byte;
typedef u32 rune;   /* refined u32: docs/spec/70-strings.md section 9 */

typedef float  f32; /* IEEE 754 binary32: docs/spec/20-types.md section 11.3 */
typedef double f64; /* IEEE 754 binary64 */
typedef uint16_t f16;  /* binary16 storage: load, store, widen, round only */
typedef uint16_t bf16; /* bfloat16 storage */
typedef uint8_t f8e4m3; /* OCP FP8 E4M3 storage: no infinities, NaN is S.1111.111 */
typedef uint8_t f8e5m2; /* OCP FP8 E5M2 storage: IEEE-like */

/* floating point (docs/spec/20-types.md section 11.3): IEEE 754 binary32/64,
   round to nearest even, no contraction (see the FP_CONTRACT pragma above),
   no fast-math. min/max take the IEEE 754-2019 minimum/maximum semantics:
   a NaN operand yields NaN and -0.0 orders below +0.0; min_num/max_num are
   fmin/fmax. total_order is IEEE 754-2019 totalOrder over the bit patterns. */
static inline f32 oak_fmin_f32(f32 a, f32 b) { if (a != a || b != b) { return a + b; } if (a == b) { return signbit(a) ? a : b; } return a < b ? a : b; }
static inline f32 oak_fmax_f32(f32 a, f32 b) { if (a != a || b != b) { return a + b; } if (a == b) { return signbit(a) ? b : a; } return a > b ? a : b; }
static inline f64 oak_fmin_f64(f64 a, f64 b) { if (a != a || b != b) { return a + b; } if (a == b) { return signbit(a) ? a : b; } return a < b ? a : b; }
static inline f64 oak_fmax_f64(f64 a, f64 b) { if (a != a || b != b) { return a + b; } if (a == b) { return signbit(a) ? b : a; } return a > b ? a : b; }
static inline int32_t oak_total_key_f32(f32 x) { union { f32 f; int32_t i; } pun; pun.f = x; return pun.i < 0 ? (int32_t)(pun.i ^ 0x7FFFFFFF) : pun.i; }
static inline int64_t oak_total_key_f64(f64 x) { union { f64 f; int64_t i; } pun; pun.f = x; return pun.i < 0 ? (int64_t)(pun.i ^ 0x7FFFFFFFFFFFFFFFLL) : pun.i; }
static inline int oak_total_order_f32(f32 a, f32 b) { return oak_total_key_f32(a) <= oak_total_key_f32(b); }
static inline int oak_total_order_f64(f64 a, f64 b) { return oak_total_key_f64(a) <= oak_total_key_f64(b); }
/* storage formats (section 11.3.1): binary16 and bfloat16 as uint16_t carriers.
   Widening is exact; rounding from f32 is to nearest even with subnormals,
   overflow to infinity, and quiet NaN preserved — pure integer bit work over
   a union pun, no dependence on compiler half-precision support. */
static inline f32 oak_widen_f16(f16 h) {
  uint32_t sign = ((uint32_t)h & 0x8000u) << 16, exp = ((uint32_t)h >> 10) & 0x1Fu, mant = (uint32_t)h & 0x3FFu;
  union { uint32_t u; f32 f; } pun;
  if (exp == 0x1Fu) { pun.u = sign | 0x7F800000u | (mant << 13); return pun.f; }
  if (exp == 0u) {
    if (mant == 0u) { pun.u = sign; return pun.f; }
    exp = 1u; while ((mant & 0x400u) == 0u) { mant <<= 1; exp--; } mant &= 0x3FFu;
    pun.u = sign | ((exp + 112u) << 23) | (mant << 13); return pun.f;
  }
  pun.u = sign | ((exp + 112u) << 23) | (mant << 13); return pun.f;
}
static inline f16 oak_f16_round_f32(f32 x) {
  union { f32 f; uint32_t u; } pun; pun.f = x;
  uint32_t u = pun.u, sign = (u >> 16) & 0x8000u, exp = (u >> 23) & 0xFFu, mant = u & 0x7FFFFFu;
  if (exp == 0xFFu) { return (f16)(sign | 0x7C00u | (mant != 0u ? (0x200u | (mant >> 13)) : 0u)); }
  int32_t e = (int32_t)exp - 127 + 15;
  if (e >= 0x1F) { return (f16)(sign | 0x7C00u); }
  if (e <= 0) {
    if (e < -10) { return (f16)sign; }
    mant |= 0x800000u;
    uint32_t shift = (uint32_t)(14 - e), half = mant >> shift, rem = mant & ((1u << shift) - 1u), midpoint = 1u << (shift - 1u);
    if (rem > midpoint || (rem == midpoint && (half & 1u))) { half++; }
    return (f16)(sign | half);
  }
  uint32_t half = ((uint32_t)e << 10) | (mant >> 13), rem = mant & 0x1FFFu;
  if (rem > 0x1000u || (rem == 0x1000u && (half & 1u))) { half++; }
  return (f16)(sign | half);
}
static inline f32 oak_widen_bf16(bf16 h) { union { uint32_t u; f32 f; } pun; pun.u = (uint32_t)h << 16; return pun.f; }
static inline bf16 oak_bf16_round_f32(f32 x) {
  union { f32 f; uint32_t u; } pun; pun.f = x; uint32_t u = pun.u;
  if (((u >> 23) & 0xFFu) == 0xFFu && (u & 0x7FFFFFu) != 0u) { return (bf16)((u >> 16) | 0x40u); }
  uint32_t upper = u >> 16, rem = u & 0xFFFFu;
  if (rem > 0x8000u || (rem == 0x8000u && (upper & 1u))) { upper++; }
  return (bf16)upper;
}
/* OCP FP8 storage formats (docs/spec/20-types.md section 11.3.1). E4M3: bias 7,
   three fraction bits, no infinities, NaN is exponent and fraction all ones
   (0x7F), largest finite 448 (0x7E); rounding is nearest even on the format's
   grid, a result that would exceed 448 is NaN. E5M2: bias 15, two fraction
   bits, infinities and NaN as IEEE, largest finite 57344 (0x7B); overflow is
   infinity. NaN narrows to the format's quiet NaN without payload and widens
   quiet. The saturating forms clamp finite overflow to the largest finite
   value instead (NaN stays NaN; an E5M2 infinity stays infinite). */
static inline f32 oak_widen_f8e4m3(f8e4m3 h) {
  uint32_t sign = ((uint32_t)h & 0x80u) << 24, exp = ((uint32_t)h >> 3) & 0xFu, mant = (uint32_t)h & 0x7u;
  union { uint32_t u; f32 f; } pun;
  if (exp == 0xFu && mant == 0x7u) { pun.u = sign | 0x7FC00000u; return pun.f; }
  if (exp == 0u) {
    if (mant == 0u) { pun.u = sign; return pun.f; }
    exp = 1u; while ((mant & 0x8u) == 0u) { mant <<= 1; exp--; } mant &= 0x7u;
    pun.u = sign | ((exp + 120u) << 23) | (mant << 20); return pun.f;
  }
  pun.u = sign | ((exp + 120u) << 23) | (mant << 20); return pun.f;
}
static inline f8e4m3 oak_f8e4m3_round_f32(f32 x) {
  union { f32 f; uint32_t u; } pun; pun.f = x;
  uint32_t u = pun.u, sign = (u >> 24) & 0x80u, exp = (u >> 23) & 0xFFu, mant = u & 0x7FFFFFu;
  if (exp == 0xFFu) { return (f8e4m3)(sign | 0x7Fu); }
  int32_t e = (int32_t)exp - 127 + 7;
  if (e >= 16) { return (f8e4m3)(sign | 0x7Fu); }
  uint32_t enc;
  if (e <= 0) {
    if (e < -3) { return (f8e4m3)sign; }
    mant |= 0x800000u;
    uint32_t shift = (uint32_t)(21 - e), rem = mant & ((1u << shift) - 1u), midpoint = 1u << (shift - 1u);
    enc = mant >> shift;
    if (rem > midpoint || (rem == midpoint && (enc & 1u))) { enc++; }
  } else {
    uint32_t rem = mant & 0xFFFFFu;
    enc = ((uint32_t)e << 3) | (mant >> 20);
    if (rem > 0x80000u || (rem == 0x80000u && (enc & 1u))) { enc++; }
  }
  if (enc >= 0x7Fu) { return (f8e4m3)(sign | 0x7Fu); }
  return (f8e4m3)(sign | enc);
}
static inline f8e4m3 oak_f8e4m3_saturating_f32(f32 x) {
  f8e4m3 r = oak_f8e4m3_round_f32(x);
  if ((r & 0x7Fu) == 0x7Fu && x == x) { return (f8e4m3)((r & 0x80u) | 0x7Eu); }
  return r;
}
static inline f32 oak_widen_f8e5m2(f8e5m2 h) {
  uint32_t sign = ((uint32_t)h & 0x80u) << 24, exp = ((uint32_t)h >> 2) & 0x1Fu, mant = (uint32_t)h & 0x3u;
  union { uint32_t u; f32 f; } pun;
  if (exp == 0x1Fu) { pun.u = sign | 0x7F800000u | (mant != 0u ? 0x400000u : 0u) | (mant << 21); return pun.f; }
  if (exp == 0u) {
    if (mant == 0u) { pun.u = sign; return pun.f; }
    exp = 1u; while ((mant & 0x4u) == 0u) { mant <<= 1; exp--; } mant &= 0x3u;
    pun.u = sign | ((exp + 112u) << 23) | (mant << 21); return pun.f;
  }
  pun.u = sign | ((exp + 112u) << 23) | (mant << 21); return pun.f;
}
static inline f8e5m2 oak_f8e5m2_round_f32(f32 x) {
  union { f32 f; uint32_t u; } pun; pun.f = x;
  uint32_t u = pun.u, sign = (u >> 24) & 0x80u, exp = (u >> 23) & 0xFFu, mant = u & 0x7FFFFFu;
  if (exp == 0xFFu) { return (f8e5m2)(sign | (mant != 0u ? 0x7Eu : 0x7Cu)); }
  int32_t e = (int32_t)exp - 127 + 15;
  if (e >= 31) { return (f8e5m2)(sign | 0x7Cu); }
  uint32_t enc;
  if (e <= 0) {
    if (e < -2) { return (f8e5m2)sign; }
    mant |= 0x800000u;
    uint32_t shift = (uint32_t)(22 - e), rem = mant & ((1u << shift) - 1u), midpoint = 1u << (shift - 1u);
    enc = mant >> shift;
    if (rem > midpoint || (rem == midpoint && (enc & 1u))) { enc++; }
  } else {
    uint32_t rem = mant & 0x1FFFFFu;
    enc = ((uint32_t)e << 2) | (mant >> 21);
    if (rem > 0x100000u || (rem == 0x100000u && (enc & 1u))) { enc++; }
  }
  return (f8e5m2)(sign | enc);
}
static inline f8e5m2 oak_f8e5m2_saturating_f32(f32 x) {
  f8e5m2 r = oak_f8e5m2_round_f32(x);
  if ((r & 0x7Fu) == 0x7Cu && x == x && (x < 0 ? -x : x) <= 0x1.fffffep+127f) { return (f8e5m2)((r & 0x80u) | 0x7Bu); }
  return r;
}

typedef struct oak_string {
    u8* data;  /* UTF-8 bytes, not necessarily null-terminated */
    u32 len;   /* number of bytes */
} string;

typedef enum oak_Bool {
    oak_Bool_False = 0,
    oak_Bool_True  = 1
} Bool;

typedef enum oak_Comparison {
    oak_Comparison_Less    = -1,
    oak_Comparison_Equal    = 0,
    oak_Comparison_Greater  = 1
} Comparison;

/* assert: always compiled in (docs/spec/85-discipline.md section 5) */
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
#include <stdio.h>
static inline void oak_assert(Bool cond, const char *file, u32 line) {
  if (!cond) {
    fprintf(stderr, "oak: assertion failed at %s:%u\n", file, (unsigned)line);
    __builtin_trap();
  }
}
#else
static inline void oak_assert(Bool cond, const char *file, u32 line) {
  if (!cond) {
    oak_report("assertion failed", file, line);
    __builtin_trap();
  }
}
#endif

/* assert_eq / assert_ne: the failure names both values (85-discipline section 5) */
static inline void oak_assert_eq_u8(u8 got, u8 want, const char *file, u32 line) {
  if (!(got == want)) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %llu, want %llu\n", file, (unsigned)line, (unsigned long long)got, (unsigned long long)want);
#else
    oak_report("assertion failed (assert_eq; values need a hosted build)", file, line);
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_ne_u8(u8 got, u8 want, const char *file, u32 line) {
  if (got == want) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %llu, want anything but %llu\n", file, (unsigned)line, (unsigned long long)got, (unsigned long long)want);
#else
    oak_report("assertion failed (assert_ne; values need a hosted build)", file, line);
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_eq_u16(u16 got, u16 want, const char *file, u32 line) {
  if (!(got == want)) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %llu, want %llu\n", file, (unsigned)line, (unsigned long long)got, (unsigned long long)want);
#else
    oak_report("assertion failed (assert_eq; values need a hosted build)", file, line);
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_ne_u16(u16 got, u16 want, const char *file, u32 line) {
  if (got == want) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %llu, want anything but %llu\n", file, (unsigned)line, (unsigned long long)got, (unsigned long long)want);
#else
    oak_report("assertion failed (assert_ne; values need a hosted build)", file, line);
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_eq_u32(u32 got, u32 want, const char *file, u32 line) {
  if (!(got == want)) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %llu, want %llu\n", file, (unsigned)line, (unsigned long long)got, (unsigned long long)want);
#else
    oak_report("assertion failed (assert_eq; values need a hosted build)", file, line);
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_ne_u32(u32 got, u32 want, const char *file, u32 line) {
  if (got == want) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %llu, want anything but %llu\n", file, (unsigned)line, (unsigned long long)got, (unsigned long long)want);
#else
    oak_report("assertion failed (assert_ne; values need a hosted build)", file, line);
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_eq_u64(u64 got, u64 want, const char *file, u32 line) {
  if (!(got == want)) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %llu, want %llu\n", file, (unsigned)line, (unsigned long long)got, (unsigned long long)want);
#else
    oak_report("assertion failed (assert_eq; values need a hosted build)", file, line);
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_ne_u64(u64 got, u64 want, const char *file, u32 line) {
  if (got == want) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %llu, want anything but %llu\n", file, (unsigned)line, (unsigned long long)got, (unsigned long long)want);
#else
    oak_report("assertion failed (assert_ne; values need a hosted build)", file, line);
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_eq_i8(i8 got, i8 want, const char *file, u32 line) {
  if (!(got == want)) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %lld, want %lld\n", file, (unsigned)line, (long long)got, (long long)want);
#else
    oak_report("assertion failed (assert_eq; values need a hosted build)", file, line);
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_ne_i8(i8 got, i8 want, const char *file, u32 line) {
  if (got == want) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %lld, want anything but %lld\n", file, (unsigned)line, (long long)got, (long long)want);
#else
    oak_report("assertion failed (assert_ne; values need a hosted build)", file, line);
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_eq_i16(i16 got, i16 want, const char *file, u32 line) {
  if (!(got == want)) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %lld, want %lld\n", file, (unsigned)line, (long long)got, (long long)want);
#else
    oak_report("assertion failed (assert_eq; values need a hosted build)", file, line);
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_ne_i16(i16 got, i16 want, const char *file, u32 line) {
  if (got == want) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %lld, want anything but %lld\n", file, (unsigned)line, (long long)got, (long long)want);
#else
    oak_report("assertion failed (assert_ne; values need a hosted build)", file, line);
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_eq_i32(i32 got, i32 want, const char *file, u32 line) {
  if (!(got == want)) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %lld, want %lld\n", file, (unsigned)line, (long long)got, (long long)want);
#else
    oak_report("assertion failed (assert_eq; values need a hosted build)", file, line);
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_ne_i32(i32 got, i32 want, const char *file, u32 line) {
  if (got == want) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %lld, want anything but %lld\n", file, (unsigned)line, (long long)got, (long long)want);
#else
    oak_report("assertion failed (assert_ne; values need a hosted build)", file, line);
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_eq_i64(i64 got, i64 want, const char *file, u32 line) {
  if (!(got == want)) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %lld, want %lld\n", file, (unsigned)line, (long long)got, (long long)want);
#else
    oak_report("assertion failed (assert_eq; values need a hosted build)", file, line);
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_ne_i64(i64 got, i64 want, const char *file, u32 line) {
  if (got == want) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %lld, want anything but %lld\n", file, (unsigned)line, (long long)got, (long long)want);
#else
    oak_report("assertion failed (assert_ne; values need a hosted build)", file, line);
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_eq_f32(f32 got, f32 want, const char *file, u32 line) {
  if (!(got == want)) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %.9g, want %.9g\n", file, (unsigned)line, (double)got, (double)want);
#else
    oak_report("assertion failed (assert_eq; values need a hosted build)", file, line);
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_ne_f32(f32 got, f32 want, const char *file, u32 line) {
  if (got == want) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %.9g, want anything but %.9g\n", file, (unsigned)line, (double)got, (double)want);
#else
    oak_report("assertion failed (assert_ne; values need a hosted build)", file, line);
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_eq_f64(f64 got, f64 want, const char *file, u32 line) {
  if (!(got == want)) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %.17g, want %.17g\n", file, (unsigned)line, (double)got, (double)want);
#else
    oak_report("assertion failed (assert_eq; values need a hosted build)", file, line);
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_ne_f64(f64 got, f64 want, const char *file, u32 line) {
  if (got == want) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %.17g, want anything but %.17g\n", file, (unsigned)line, (double)got, (double)want);
#else
    oak_report("assertion failed (assert_ne; values need a hosted build)", file, line);
#endif
    __builtin_trap();
  }
}
#if defined(__SIZEOF_INT128__)
static inline void oak_assert_eq_u128(u128 got, u128 want, const char *file, u32 line) {
  if (!(got == want)) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got 0x%016llx%016llx, want 0x%016llx%016llx\n", file, (unsigned)line, (unsigned long long)(got >> 64), (unsigned long long)got, (unsigned long long)(want >> 64), (unsigned long long)want);
#else
    oak_report("assertion failed (assert_eq; values need a hosted build)", file, line);
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_ne_u128(u128 got, u128 want, const char *file, u32 line) {
  if (got == want) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got 0x%016llx%016llx, want anything but 0x%016llx%016llx\n", file, (unsigned)line, (unsigned long long)(got >> 64), (unsigned long long)got, (unsigned long long)(want >> 64), (unsigned long long)want);
#else
    oak_report("assertion failed (assert_ne; values need a hosted build)", file, line);
#endif
    __builtin_trap();
  }
}
#endif
static inline void oak_assert_eq_Bool(Bool got, Bool want, const char *file, u32 line) {
  if (!(got == want)) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %s, want %s\n", file, (unsigned)line, got ? "true" : "false", want ? "true" : "false");
#else
    oak_report(got ? "assertion failed: got true, want false" : "assertion failed: got false, want true", file, line);
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_ne_Bool(Bool got, Bool want, const char *file, u32 line) {
  if (got == want) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %s, want anything but %s\n", file, (unsigned)line, got ? "true" : "false", want ? "true" : "false");
#else
    oak_report(got ? "assertion failed: got true, want anything but true" : "assertion failed: got false, want anything but false", file, line);
#endif
    __builtin_trap();
  }
}

typedef struct oak_view_u8 {
    const u8* base;
    u32       len;
} oak_view_u8;

static inline u8 oak_view_index_u8(oak_view_u8 v, u64 i) {
  if (i >= (u64)v.len) { __builtin_trap(); }
  return v.base[i];
}

#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
#include <stdio.h>
static inline const char *oak_cstr_u8(oak_view_u8 v, const char *file, u32 line) {
  if (v.len == 0u || v.base[v.len - 1u] != 0u) {
    fprintf(stderr, "oak: c.cstr view is not NUL-terminated at %s:%u\n", file, (unsigned)line);
    __builtin_trap();
  }
  return (const char *)v.base;
}
#else
static inline const char *oak_cstr_u8(oak_view_u8 v, const char *file, u32 line) {
  if (v.len == 0u || v.base[v.len - 1u] != 0u) { oak_report("c.cstr view is not NUL-terminated", file, line); __builtin_trap(); }
  return (const char *)v.base;
}
#endif

static inline u32 oak_cstr_len(const void *p) {
  const unsigned char *s = (const unsigned char *)p;
  u64 n = 0;
  if (s == 0) { return 0u; }
  while (s[n] != 0u) { n++; if (n > 0xFFFFFFFFull) { __builtin_trap(); } }
  return (u32)n;
}

static inline oak_view_u8 oak_view_subslice_u8(oak_view_u8 v, u64 start, u64 n) {
  if (start > (u64)v.len || n > (u64)v.len - start) { __builtin_trap(); }
  return (oak_view_u8){ v.base + start, (u32)n };
}

/* core_slice: view construction as a brace initializer (declaration
   position); field order matches the view/span structs {base, len} */
#define core_slice(arr, lo, hi) { (arr) + (lo), (u32)((hi) - (lo)) }

/* bounds-checked owned-array indexing: out-of-range traps, never UB */
static inline u64 oak_bounds_trap(void) { __builtin_trap(); return 0; }
#define oak_index(base, len, i) ((u64)(i) < (u64)(len) ? (base)[(i)] : (base)[oak_bounds_trap()])
/* checked index in lvalue position: pool[ oak_lv_idx(i, len) ].field = v */
static inline u64 oak_lv_idx(u64 i, u64 len) { if (i >= len) { __builtin_trap(); } return i; }

/* checked shifts: a count reaching the operand width traps, never UB
   (docs/spec/10-syntax.md section 3b); constant counts fold the check away */
#define OAK_SHIFT_HELPERS(T, W) \
  static inline T oak_shl_##T(T v, T n) { if (n >= W) { __builtin_trap(); } return (T)(v << n); } \
  static inline T oak_shr_##T(T v, T n) { if (n >= W) { __builtin_trap(); } return (T)(v >> n); }
OAK_SHIFT_HELPERS(u8, 8u) OAK_SHIFT_HELPERS(u16, 16u) OAK_SHIFT_HELPERS(u32, 32u) OAK_SHIFT_HELPERS(u64, 64u)

/* total fixed-width arithmetic (docs/spec/20-types.md section 11.1, 90-backend.md
   section 7): results wrap mod 2^N, computed in unsigned space so no C
   promotion overflows; signed results come back through a union pun (defined
   since C99 TC3). Division by zero traps; MIN / -1 wraps. Never UB. */
#define OAK_ARITH_U(T) \
  static inline T oak_add_##T(T a, T b) { return (T)((u64)a + (u64)b); } \
  static inline T oak_sub_##T(T a, T b) { return (T)((u64)a - (u64)b); } \
  static inline T oak_neg_##T(T a) { return (T)(0u - (u64)a); } \
  static inline T oak_mul_##T(T a, T b) { return (T)((u64)a * (u64)b); } \
  static inline T oak_div_##T(T a, T b) { if (b == 0) { __builtin_trap(); } return (T)(a / b); } \
  static inline T oak_rem_##T(T a, T b) { if (b == 0) { __builtin_trap(); } return (T)(a % b); }
#define OAK_ARITH_I(T, U, MIN) \
  static inline T oak_pun_##T(U bits) { union { U from; T to; } pun; pun.from = bits; return pun.to; } \
  static inline T oak_add_##T(T a, T b) { return oak_pun_##T((U)((u64)(U)a + (u64)(U)b)); } \
  static inline T oak_sub_##T(T a, T b) { return oak_pun_##T((U)((u64)(U)a - (u64)(U)b)); } \
  static inline T oak_neg_##T(T a) { return oak_pun_##T((U)(0u - (u64)(U)a)); } \
  static inline T oak_mul_##T(T a, T b) { return oak_pun_##T((U)((u64)(U)a * (u64)(U)b)); } \
  static inline T oak_div_##T(T a, T b) { if (b == 0) { __builtin_trap(); } if (a == MIN && b == -1) { return a; } return (T)(a / b); } \
  static inline T oak_rem_##T(T a, T b) { if (b == 0) { __builtin_trap(); } if (b == -1) { return 0; } return (T)(a % b); }
OAK_ARITH_U(u8) OAK_ARITH_U(u16) OAK_ARITH_U(u32) OAK_ARITH_U(u64)
OAK_ARITH_I(i8, u8, INT8_MIN) OAK_ARITH_I(i16, u16, INT16_MIN) OAK_ARITH_I(i32, u32, INT32_MIN) OAK_ARITH_I(i64, u64, INT64_MIN)
#if defined(__SIZEOF_INT128__)
/* u128: unsigned __int128 arithmetic is defined mod 2^128 by C itself; the
   helpers keep the one shape (division by zero traps, shifts checked) */
OAK_SHIFT_HELPERS(u128, 128u)
static inline u128 oak_add_u128(u128 a, u128 b) { return a + b; }
static inline u128 oak_sub_u128(u128 a, u128 b) { return a - b; }
static inline u128 oak_neg_u128(u128 a) { return (u128)0 - a; }
static inline u128 oak_mul_u128(u128 a, u128 b) { return a * b; }
static inline u128 oak_div_u128(u128 a, u128 b) { if (b == 0) { __builtin_trap(); } return a / b; }
static inline u128 oak_rem_u128(u128 a, u128 b) { if (b == 0) { __builtin_trap(); } return a % b; }
#endif
#define oak_store(base, len, i, v) do { if ((u64)(i) >= (u64)(len)) { __builtin_trap(); } (base)[(i)] = (v); } while (0)

/* is_valid_utf8: Unicode Table 3-7, transliterated from Oak.Utf8Validity */
static Bool oak_is_valid_utf8(oak_view_u8 v) {
  u64 i = 0;
  u64 n = (u64)v.len;
  while (i < n) {
    u8 b0 = v.base[i];
    if (b0 <= 0x7F) { i += 1; continue; }
    if (0xC2 <= b0 && b0 <= 0xDF) {
      if (i + 1 >= n || v.base[i+1] < 0x80 || v.base[i+1] > 0xBF) { return oak_Bool_False; }
      i += 2; continue;
    }
    if (b0 == 0xE0) {
      if (i + 2 >= n || v.base[i+1] < 0xA0 || v.base[i+1] > 0xBF ||
          v.base[i+2] < 0x80 || v.base[i+2] > 0xBF) { return oak_Bool_False; }
      i += 3; continue;
    }
    if (0xE1 <= b0 && b0 <= 0xEC) {
      if (i + 2 >= n || v.base[i+1] < 0x80 || v.base[i+1] > 0xBF ||
          v.base[i+2] < 0x80 || v.base[i+2] > 0xBF) { return oak_Bool_False; }
      i += 3; continue;
    }
    if (b0 == 0xED) {
      if (i + 2 >= n || v.base[i+1] < 0x80 || v.base[i+1] > 0x9F ||
          v.base[i+2] < 0x80 || v.base[i+2] > 0xBF) { return oak_Bool_False; }
      i += 3; continue;
    }
    if (0xEE <= b0 && b0 <= 0xEF) {
      if (i + 2 >= n || v.base[i+1] < 0x80 || v.base[i+1] > 0xBF ||
          v.base[i+2] < 0x80 || v.base[i+2] > 0xBF) { return oak_Bool_False; }
      i += 3; continue;
    }
    if (b0 == 0xF0) {
      if (i + 3 >= n || v.base[i+1] < 0x90 || v.base[i+1] > 0xBF ||
          v.base[i+2] < 0x80 || v.base[i+2] > 0xBF ||
          v.base[i+3] < 0x80 || v.base[i+3] > 0xBF) { return oak_Bool_False; }
      i += 4; continue;
    }
    if (0xF1 <= b0 && b0 <= 0xF3) {
      if (i + 3 >= n || v.base[i+1] < 0x80 || v.base[i+1] > 0xBF ||
          v.base[i+2] < 0x80 || v.base[i+2] > 0xBF ||
          v.base[i+3] < 0x80 || v.base[i+3] > 0xBF) { return oak_Bool_False; }
      i += 4; continue;
    }
    if (b0 == 0xF4) {
      if (i + 3 >= n || v.base[i+1] < 0x80 || v.base[i+1] > 0x8F ||
          v.base[i+2] < 0x80 || v.base[i+2] > 0xBF ||
          v.base[i+3] < 0x80 || v.base[i+3] > 0xBF) { return oak_Bool_False; }
      i += 4; continue;
    }
    return oak_Bool_False;
  }
  return oak_Bool_True;
}

/* explicit integer conversions: total, two's complement, no
   implementation-defined C (signed results via union punning) */
static inline u32 oak_conv_u32_bits_f32( f32 x ) { union { f32 from; u32 to; } pun; pun.from = x; return pun.to; }

/* forward declarations; OAK_INLINE marks private leaf helpers the C
   compiler must inline at every optimization level (the external
   definition is still emitted: C99 extern inline) */
#define OAK_INLINE extern inline __attribute__((always_inline))
OAK_INLINE f32 oak_norm( f32 x, f32 y );
i32 oak_main( void );

// @source: unknown.oak:1:0-3:0
// @package: main
// @kind: function
// @identifier: norm
// @signature: fn norm(x: f32, y: f32) -> f32
OAK_INLINE f32 oak_norm( f32 x, f32 y ) {
    return sqrtf( (f32)( ( ( x * x ) + ( y * y ) ) ) )  ;
}

// @source: unknown.oak:5:0-10:0
// @package: main
// @kind: function
// @identifier: main
// @signature: fn main() -> i32
i32 oak_main(  ) {
    f32 n   = oak_norm( ((f32)0x1.8p+01f), ((f32)0x1p+02f) )  ;
    u32 bits   = oak_conv_u32_bits_f32( n )  ;
    f64 half   = ( ((f64)( n )) * ((f64)0x1p-01) )  ;
    if ( ( bits == ((u32)( 1084227584 )) ) && ( half == ((f64)0x1.4p+01) ) ) {
      return 0    ;
    } else {
      return 1    ;
    }
}

int main(void) {
  return (int)oak_main();
}
