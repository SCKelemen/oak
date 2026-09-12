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

typedef uint8_t  u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

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

typedef struct oak_view_i32 {
    const i32* base;
    u32       len;
} oak_view_i32;

static inline i32 oak_view_index_i32(oak_view_i32 v, u64 i) {
  if (i >= (u64)v.len) { __builtin_trap(); }
  return v.base[i];
}

static inline oak_view_i32 oak_view_subslice_i32(oak_view_i32 v, u64 start, u64 n) {
  if (start > (u64)v.len || n > (u64)v.len - start) { __builtin_trap(); }
  return (oak_view_i32){ v.base + start, (u32)n };
}

/* forward declarations; OAK_INLINE marks private leaf helpers the C
   compiler must inline at every optimization level (the external
   definition is still emitted: C99 extern inline) */
#define OAK_INLINE extern inline __attribute__((always_inline))
OAK_INLINE i32 oak_total( i32 base, oak_view_i32 rest );
i32 oak_caller( void );

// @source: unknown.oak:1:0-3:0
// @package: main
// @kind: function
// @identifier: total
// @signature: fn total(base: i32, rest: i32) -> i32
OAK_INLINE i32 oak_total( i32 base, oak_view_i32 rest ) {
    return base  ;
}

// @source: unknown.oak:5:0-7:0
// @package: main
// @kind: function
// @identifier: caller
// @signature: fn caller() -> i32
i32 oak_caller(  ) {
    return oak_total( 1, (oak_view_i32){ (i32[]){ 2, 3 }, 2 } )  ;
}

