/* Generated C code from Oak */
#include <stdint.h>
#include <stddef.h>

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
  (void)file; (void)line;
  if (!cond) {
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
    (void)file; (void)line;
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_ne_u8(u8 got, u8 want, const char *file, u32 line) {
  if (got == want) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %llu, want anything but %llu\n", file, (unsigned)line, (unsigned long long)got, (unsigned long long)want);
#else
    (void)file; (void)line;
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_eq_u16(u16 got, u16 want, const char *file, u32 line) {
  if (!(got == want)) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %llu, want %llu\n", file, (unsigned)line, (unsigned long long)got, (unsigned long long)want);
#else
    (void)file; (void)line;
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_ne_u16(u16 got, u16 want, const char *file, u32 line) {
  if (got == want) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %llu, want anything but %llu\n", file, (unsigned)line, (unsigned long long)got, (unsigned long long)want);
#else
    (void)file; (void)line;
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_eq_u32(u32 got, u32 want, const char *file, u32 line) {
  if (!(got == want)) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %llu, want %llu\n", file, (unsigned)line, (unsigned long long)got, (unsigned long long)want);
#else
    (void)file; (void)line;
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_ne_u32(u32 got, u32 want, const char *file, u32 line) {
  if (got == want) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %llu, want anything but %llu\n", file, (unsigned)line, (unsigned long long)got, (unsigned long long)want);
#else
    (void)file; (void)line;
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_eq_u64(u64 got, u64 want, const char *file, u32 line) {
  if (!(got == want)) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %llu, want %llu\n", file, (unsigned)line, (unsigned long long)got, (unsigned long long)want);
#else
    (void)file; (void)line;
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_ne_u64(u64 got, u64 want, const char *file, u32 line) {
  if (got == want) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %llu, want anything but %llu\n", file, (unsigned)line, (unsigned long long)got, (unsigned long long)want);
#else
    (void)file; (void)line;
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_eq_i8(i8 got, i8 want, const char *file, u32 line) {
  if (!(got == want)) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %lld, want %lld\n", file, (unsigned)line, (long long)got, (long long)want);
#else
    (void)file; (void)line;
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_ne_i8(i8 got, i8 want, const char *file, u32 line) {
  if (got == want) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %lld, want anything but %lld\n", file, (unsigned)line, (long long)got, (long long)want);
#else
    (void)file; (void)line;
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_eq_i16(i16 got, i16 want, const char *file, u32 line) {
  if (!(got == want)) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %lld, want %lld\n", file, (unsigned)line, (long long)got, (long long)want);
#else
    (void)file; (void)line;
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_ne_i16(i16 got, i16 want, const char *file, u32 line) {
  if (got == want) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %lld, want anything but %lld\n", file, (unsigned)line, (long long)got, (long long)want);
#else
    (void)file; (void)line;
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_eq_i32(i32 got, i32 want, const char *file, u32 line) {
  if (!(got == want)) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %lld, want %lld\n", file, (unsigned)line, (long long)got, (long long)want);
#else
    (void)file; (void)line;
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_ne_i32(i32 got, i32 want, const char *file, u32 line) {
  if (got == want) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %lld, want anything but %lld\n", file, (unsigned)line, (long long)got, (long long)want);
#else
    (void)file; (void)line;
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_eq_i64(i64 got, i64 want, const char *file, u32 line) {
  if (!(got == want)) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %lld, want %lld\n", file, (unsigned)line, (long long)got, (long long)want);
#else
    (void)file; (void)line;
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_ne_i64(i64 got, i64 want, const char *file, u32 line) {
  if (got == want) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %lld, want anything but %lld\n", file, (unsigned)line, (long long)got, (long long)want);
#else
    (void)file; (void)line;
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_eq_f32(f32 got, f32 want, const char *file, u32 line) {
  if (!(got == want)) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %.9g, want %.9g\n", file, (unsigned)line, (double)got, (double)want);
#else
    (void)file; (void)line;
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_ne_f32(f32 got, f32 want, const char *file, u32 line) {
  if (got == want) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %.9g, want anything but %.9g\n", file, (unsigned)line, (double)got, (double)want);
#else
    (void)file; (void)line;
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_eq_f64(f64 got, f64 want, const char *file, u32 line) {
  if (!(got == want)) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %.17g, want %.17g\n", file, (unsigned)line, (double)got, (double)want);
#else
    (void)file; (void)line;
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_ne_f64(f64 got, f64 want, const char *file, u32 line) {
  if (got == want) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %.17g, want anything but %.17g\n", file, (unsigned)line, (double)got, (double)want);
#else
    (void)file; (void)line;
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_eq_Bool(Bool got, Bool want, const char *file, u32 line) {
  if (!(got == want)) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %s, want %s\n", file, (unsigned)line, got ? "true" : "false", want ? "true" : "false");
#else
    (void)file; (void)line;
#endif
    __builtin_trap();
  }
}
static inline void oak_assert_ne_Bool(Bool got, Bool want, const char *file, u32 line) {
  if (got == want) {
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
    fprintf(stderr, "oak: assertion failed at %s:%u: got %s, want anything but %s\n", file, (unsigned)line, got ? "true" : "false", want ? "true" : "false");
#else
    (void)file; (void)line;
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
  (void)file; (void)line;
  if (v.len == 0u || v.base[v.len - 1u] != 0u) { __builtin_trap(); }
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
/* is_valid_utf8: lowered to the standard library's vector validator utf8.valid
   (stdlib/utf8.oak), which Oak.Utf8Blocks.program_valid proves decides Oak.Utf8Validity.Valid */
Bool oak_utf8__valid( oak_view_u8 bytes );
static inline Bool oak_is_valid_utf8(oak_view_u8 v) { return oak_utf8__valid( v ); }

/* portable SIMD vectors: docs/spec/93-simd.md */
#if defined(__aarch64__) && defined(__ARM_NEON) && !defined(OAK_SCALAR_SIMD) && !defined(OAK_PORTABLE_INTRINSICS)
#include <arm_neon.h>
#endif
typedef struct oak_u8x16 { u8 lanes[16]; } u8x16;
typedef struct oak_u16x8 { u16 lanes[8]; } u16x8;
typedef struct oak_u32x4 { u32 lanes[4]; } u32x4;
typedef struct oak_u64x2 { u64 lanes[2]; } u64x2;
typedef struct oak_f32x4 { f32 lanes[4]; } f32x4;
typedef struct oak_f64x2 { f64 lanes[2]; } f64x2;

static inline u8x16 oak_simd_and_u8x16( u8x16 a, u8x16 b ) {
  u8x16 r;
#if defined(__aarch64__) && defined(__ARM_NEON) && !defined(OAK_SCALAR_SIMD) && !defined(OAK_PORTABLE_INTRINSICS)
  vst1q_u8(r.lanes, vandq_u8(vld1q_u8(a.lanes), vld1q_u8(b.lanes)));
#else
  for (int i = 0; i < 16; i++) {
    u8 x = a.lanes[i]; u8 y = b.lanes[i];
    r.lanes[i] = (u8)(x & y);
  }
#endif
  return r;
}

static inline Bool oak_simd_any_u8x16( u8x16 v ) {
#if defined(__aarch64__) && defined(__ARM_NEON) && !defined(OAK_SCALAR_SIMD) && !defined(OAK_PORTABLE_INTRINSICS)
  return vmaxvq_u8(vld1q_u8(v.lanes)) != 0u ? oak_Bool_True : oak_Bool_False;
#else
  for (int i = 0; i < 16; i++) { if (v.lanes[i] != 0) { return oak_Bool_True; } }
  return oak_Bool_False;
#endif
}

static inline u8x16 oak_simd_load_u8x16( oak_view_u8 v, u32 off ) {
  if ((u64)off + 16u > (u64)v.len) { __builtin_trap(); }
  u8x16 r;
#if defined(__aarch64__) && defined(__ARM_NEON) && !defined(OAK_SCALAR_SIMD) && !defined(OAK_PORTABLE_INTRINSICS)
  vst1q_u8(r.lanes, vld1q_u8(v.base + off));
#else
  for (int i = 0; i < 16; i++) { r.lanes[i] = v.base[off + (u32)i]; }
#endif
  return r;
}
static inline u8x16 oak_simd_load_u8x16_proven( oak_view_u8 v, u32 off ) {
  u8x16 r;
#if defined(__aarch64__) && defined(__ARM_NEON) && !defined(OAK_SCALAR_SIMD) && !defined(OAK_PORTABLE_INTRINSICS)
  vst1q_u8(r.lanes, vld1q_u8(v.base + off));
#else
  for (int i = 0; i < 16; i++) { r.lanes[i] = v.base[off + (u32)i]; }
#endif
  return r;
}

static inline u8x16 oak_simd_or_u8x16( u8x16 a, u8x16 b ) {
  u8x16 r;
#if defined(__aarch64__) && defined(__ARM_NEON) && !defined(OAK_SCALAR_SIMD) && !defined(OAK_PORTABLE_INTRINSICS)
  vst1q_u8(r.lanes, vorrq_u8(vld1q_u8(a.lanes), vld1q_u8(b.lanes)));
#else
  for (int i = 0; i < 16; i++) {
    u8 x = a.lanes[i]; u8 y = b.lanes[i];
    r.lanes[i] = (u8)(x | y);
  }
#endif
  return r;
}

static inline u8x16 oak_simd_prev_u8x16( u8x16 prev, u8x16 cur, u32 n ) {
  if (n > 16u) { __builtin_trap(); }
  u8x16 r;
#if defined(__aarch64__) && defined(__ARM_NEON) && !defined(OAK_SCALAR_SIMD) && !defined(OAK_PORTABLE_INTRINSICS)
  uint8x16_t p = vld1q_u8(prev.lanes), c = vld1q_u8(cur.lanes);
  switch (n) {
    case 0: vst1q_u8(r.lanes, c); break;
    case 1: vst1q_u8(r.lanes, vextq_u8(p, c, 15)); break;
    case 2: vst1q_u8(r.lanes, vextq_u8(p, c, 14)); break;
    case 3: vst1q_u8(r.lanes, vextq_u8(p, c, 13)); break;
    case 4: vst1q_u8(r.lanes, vextq_u8(p, c, 12)); break;
    case 5: vst1q_u8(r.lanes, vextq_u8(p, c, 11)); break;
    case 6: vst1q_u8(r.lanes, vextq_u8(p, c, 10)); break;
    case 7: vst1q_u8(r.lanes, vextq_u8(p, c, 9)); break;
    case 8: vst1q_u8(r.lanes, vextq_u8(p, c, 8)); break;
    case 9: vst1q_u8(r.lanes, vextq_u8(p, c, 7)); break;
    case 10: vst1q_u8(r.lanes, vextq_u8(p, c, 6)); break;
    case 11: vst1q_u8(r.lanes, vextq_u8(p, c, 5)); break;
    case 12: vst1q_u8(r.lanes, vextq_u8(p, c, 4)); break;
    case 13: vst1q_u8(r.lanes, vextq_u8(p, c, 3)); break;
    case 14: vst1q_u8(r.lanes, vextq_u8(p, c, 2)); break;
    case 15: vst1q_u8(r.lanes, vextq_u8(p, c, 1)); break;
    case 16: vst1q_u8(r.lanes, p); break;
    default: __builtin_trap();
  }
#else
  for (int i = 0; i < 16; i++) { r.lanes[i] = (u32)i < n ? prev.lanes[16u - n + (u32)i] : cur.lanes[(u32)i - n]; }
#endif
  return r;
}

static inline u8x16 oak_simd_shr_u8x16( u8x16 v, u32 n ) {
  if (n >= 8u) { __builtin_trap(); }
  u8x16 r;
#if defined(__aarch64__) && defined(__ARM_NEON) && !defined(OAK_SCALAR_SIMD) && !defined(OAK_PORTABLE_INTRINSICS)
  vst1q_u8(r.lanes, vshlq_u8(vld1q_u8(v.lanes), vdupq_n_s8(-(int8_t)n)));
#else
  for (int i = 0; i < 16; i++) { r.lanes[i] = (u8)(v.lanes[i] >> n); }
#endif
  return r;
}

static inline u8x16 oak_simd_splat_u8x16( u8 x ) {
  u8x16 r;
#if defined(__aarch64__) && defined(__ARM_NEON) && !defined(OAK_SCALAR_SIMD) && !defined(OAK_PORTABLE_INTRINSICS)
  vst1q_u8(r.lanes, vdupq_n_u8(x));
#else
  for (int i = 0; i < 16; i++) { r.lanes[i] = x; }
#endif
  return r;
}

static inline u8x16 oak_simd_subs_u8x16( u8x16 a, u8x16 b ) {
  u8x16 r;
#if defined(__aarch64__) && defined(__ARM_NEON) && !defined(OAK_SCALAR_SIMD) && !defined(OAK_PORTABLE_INTRINSICS)
  vst1q_u8(r.lanes, vqsubq_u8(vld1q_u8(a.lanes), vld1q_u8(b.lanes)));
#else
  for (int i = 0; i < 16; i++) {
    u8 x = a.lanes[i]; u8 y = b.lanes[i];
    r.lanes[i] = (x > y ? (u8)(x - y) : (u8)0);
  }
#endif
  return r;
}

static inline u8x16 oak_simd_tbl_u8x16( u8x16 table, u8x16 idx ) {
  u8x16 r;
#if defined(__aarch64__) && defined(__ARM_NEON) && !defined(OAK_SCALAR_SIMD) && !defined(OAK_PORTABLE_INTRINSICS)
  vst1q_u8(r.lanes, vqtbl1q_u8(vld1q_u8(table.lanes), vld1q_u8(idx.lanes)));
#else
  for (int i = 0; i < 16; i++) { r.lanes[i] = idx.lanes[i] < 16 ? table.lanes[idx.lanes[i]] : (u8)0; }
#endif
  return r;
}

static inline u8x16 oak_simd_xor_u8x16( u8x16 a, u8x16 b ) {
  u8x16 r;
#if defined(__aarch64__) && defined(__ARM_NEON) && !defined(OAK_SCALAR_SIMD) && !defined(OAK_PORTABLE_INTRINSICS)
  vst1q_u8(r.lanes, veorq_u8(vld1q_u8(a.lanes), vld1q_u8(b.lanes)));
#else
  for (int i = 0; i < 16; i++) {
    u8 x = a.lanes[i]; u8 y = b.lanes[i];
    r.lanes[i] = (u8)(x ^ y);
  }
#endif
  return r;
}

typedef struct oak_RingCursor {
  u32 head;
  u32 count;
} oak_RingCursor;
typedef char oak_layout_size_RingCursor[ (sizeof(oak_RingCursor) == 8u) ? 1 : -1 ];
typedef char oak_layout_off_RingCursor_head[ (offsetof(oak_RingCursor, head) == 0u) ? 1 : -1 ];
typedef char oak_layout_off_RingCursor_count[ (offsetof(oak_RingCursor, count) == 4u) ? 1 : -1 ];

typedef struct oak_ByteBufferCursor {
  u32 start;
  u32 end;
} oak_ByteBufferCursor;
typedef char oak_layout_size_ByteBufferCursor[ (sizeof(oak_ByteBufferCursor) == 8u) ? 1 : -1 ];
typedef char oak_layout_off_ByteBufferCursor_start[ (offsetof(oak_ByteBufferCursor, start) == 0u) ? 1 : -1 ];
typedef char oak_layout_off_ByteBufferCursor_end[ (offsetof(oak_ByteBufferCursor, end) == 4u) ? 1 : -1 ];

typedef struct oak_ByteBuilder {
  u32 length;
  Bool failed;
} oak_ByteBuilder;
typedef char oak_layout_size_ByteBuilder[ (sizeof(oak_ByteBuilder) == 8u) ? 1 : -1 ];
typedef char oak_layout_off_ByteBuilder_length[ (offsetof(oak_ByteBuilder, length) == 0u) ? 1 : -1 ];
typedef char oak_layout_off_ByteBuilder_failed[ (offsetof(oak_ByteBuilder, failed) == 4u) ? 1 : -1 ];

typedef struct oak_ArrayListCursor {
  u32 length;
} oak_ArrayListCursor;
typedef char oak_layout_size_ArrayListCursor[ (sizeof(oak_ArrayListCursor) == 4u) ? 1 : -1 ];
typedef char oak_layout_off_ArrayListCursor_length[ (offsetof(oak_ArrayListCursor, length) == 0u) ? 1 : -1 ];

typedef struct oak_SListHook {
  u32 next;
  u32 owner;
} oak_SListHook;
typedef char oak_layout_size_SListHook[ (sizeof(oak_SListHook) == 8u) ? 1 : -1 ];
typedef char oak_layout_off_SListHook_next[ (offsetof(oak_SListHook, next) == 0u) ? 1 : -1 ];
typedef char oak_layout_off_SListHook_owner[ (offsetof(oak_SListHook, owner) == 4u) ? 1 : -1 ];

typedef struct oak_DListHook {
  u32 next;
  u32 prev;
  u32 owner;
} oak_DListHook;
typedef char oak_layout_size_DListHook[ (sizeof(oak_DListHook) == 12u) ? 1 : -1 ];
typedef char oak_layout_off_DListHook_next[ (offsetof(oak_DListHook, next) == 0u) ? 1 : -1 ];
typedef char oak_layout_off_DListHook_prev[ (offsetof(oak_DListHook, prev) == 4u) ? 1 : -1 ];
typedef char oak_layout_off_DListHook_owner[ (offsetof(oak_DListHook, owner) == 8u) ? 1 : -1 ];

typedef struct oak_IntrusiveCursor {
  u32 head;
  u32 tail;
  u32 count;
  u32 id;
} oak_IntrusiveCursor;
typedef char oak_layout_size_IntrusiveCursor[ (sizeof(oak_IntrusiveCursor) == 16u) ? 1 : -1 ];
typedef char oak_layout_off_IntrusiveCursor_head[ (offsetof(oak_IntrusiveCursor, head) == 0u) ? 1 : -1 ];
typedef char oak_layout_off_IntrusiveCursor_tail[ (offsetof(oak_IntrusiveCursor, tail) == 4u) ? 1 : -1 ];
typedef char oak_layout_off_IntrusiveCursor_count[ (offsetof(oak_IntrusiveCursor, count) == 8u) ? 1 : -1 ];
typedef char oak_layout_off_IntrusiveCursor_id[ (offsetof(oak_IntrusiveCursor, id) == 12u) ? 1 : -1 ];

typedef struct oak_MinHeapCursor {
  u32 length;
} oak_MinHeapCursor;
typedef char oak_layout_size_MinHeapCursor[ (sizeof(oak_MinHeapCursor) == 4u) ? 1 : -1 ];
typedef char oak_layout_off_MinHeapCursor_length[ (offsetof(oak_MinHeapCursor, length) == 0u) ? 1 : -1 ];

typedef struct oak_DequeCursor {
  u32 head;
  u32 count;
} oak_DequeCursor;
typedef char oak_layout_size_DequeCursor[ (sizeof(oak_DequeCursor) == 8u) ? 1 : -1 ];
typedef char oak_layout_off_DequeCursor_head[ (offsetof(oak_DequeCursor, head) == 0u) ? 1 : -1 ];
typedef char oak_layout_off_DequeCursor_count[ (offsetof(oak_DequeCursor, count) == 4u) ? 1 : -1 ];

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:3:4-3:23
// @package: main
// @kind: ADT
// @identifier: Overflow
typedef enum oak_Overflow_tag {
    oak_Overflow_tag_Overflow
} oak_Overflow_tag;

typedef struct oak_Overflow {
    u32 tag;
} oak_Overflow;

typedef char oak_union_layout_Overflow[ (sizeof(oak_Overflow) == 4u && _Alignof(oak_Overflow) == 4u && offsetof(oak_Overflow, tag) == 0u) ? 1 : -1 ];

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:3:23
// @package: main
// @kind: constructor
// @identifier: oak_Overflow::Overflow
static inline oak_Overflow oak_Overflow_Overflow(  ) {
    oak_Overflow res;
    res.tag = oak_Overflow_tag_Overflow;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:15:4-15:32
// @package: main
// @kind: ADT
// @identifier: RingPush
typedef enum oak_RingPush_tag {
    oak_RingPush_tag_Inserted  ,
    oak_RingPush_tag_Full
} oak_RingPush_tag;

typedef struct oak_RingPush {
    u32 tag;
} oak_RingPush;

typedef char oak_union_layout_RingPush[ (sizeof(oak_RingPush) == 4u && _Alignof(oak_RingPush) == 4u && offsetof(oak_RingPush, tag) == 0u) ? 1 : -1 ];

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:15:21
// @package: main
// @kind: constructor
// @identifier: oak_RingPush::Inserted
static inline oak_RingPush oak_RingPush_Inserted(  ) {
    oak_RingPush res;
    res.tag = oak_RingPush_tag_Inserted;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:15:32
// @package: main
// @kind: constructor
// @identifier: oak_RingPush::Full
static inline oak_RingPush oak_RingPush_Full(  ) {
    oak_RingPush res;
    res.tag = oak_RingPush_tag_Full;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:54:4-54:24
// @package: main
// @kind: ADT
// @identifier: CopyError
typedef enum oak_CopyError_tag {
    oak_CopyError_tag_DestinationTooSmall
} oak_CopyError_tag;

typedef struct oak_CopyError {
    u32 tag;
} oak_CopyError;

typedef char oak_union_layout_CopyError[ (sizeof(oak_CopyError) == 4u && _Alignof(oak_CopyError) == 4u && offsetof(oak_CopyError, tag) == 0u) ? 1 : -1 ];

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:54:24
// @package: main
// @kind: constructor
// @identifier: oak_CopyError::DestinationTooSmall
static inline oak_CopyError oak_CopyError_DestinationTooSmall(  ) {
    oak_CopyError res;
    res.tag = oak_CopyError_tag_DestinationTooSmall;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:97:4-97:42
// @package: main
// @kind: ADT
// @identifier: BitSetError
typedef enum oak_BitSetError_tag {
    oak_BitSetError_tag_StorageTooSmall  ,
    oak_BitSetError_tag_BitOutOfRange
} oak_BitSetError_tag;

typedef struct oak_BitSetError {
    u32 tag;
} oak_BitSetError;

typedef char oak_union_layout_BitSetError[ (sizeof(oak_BitSetError) == 4u && _Alignof(oak_BitSetError) == 4u && offsetof(oak_BitSetError, tag) == 0u) ? 1 : -1 ];

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:97:24
// @package: main
// @kind: constructor
// @identifier: oak_BitSetError::StorageTooSmall
static inline oak_BitSetError oak_BitSetError_StorageTooSmall(  ) {
    oak_BitSetError res;
    res.tag = oak_BitSetError_tag_StorageTooSmall;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:97:42
// @package: main
// @kind: constructor
// @identifier: oak_BitSetError::BitOutOfRange
static inline oak_BitSetError oak_BitSetError_BitOutOfRange(  ) {
    oak_BitSetError res;
    res.tag = oak_BitSetError_tag_BitOutOfRange;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:156:4-156:26
// @package: main
// @kind: ADT
// @identifier: EndianError
typedef enum oak_EndianError_tag {
    oak_EndianError_tag_BufferTooSmall
} oak_EndianError_tag;

typedef struct oak_EndianError {
    u32 tag;
} oak_EndianError;

typedef char oak_union_layout_EndianError[ (sizeof(oak_EndianError) == 4u && _Alignof(oak_EndianError) == 4u && offsetof(oak_EndianError, tag) == 0u) ? 1 : -1 ];

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:156:26
// @package: main
// @kind: constructor
// @identifier: oak_EndianError::BufferTooSmall
static inline oak_EndianError oak_EndianError_BufferTooSmall(  ) {
    oak_EndianError res;
    res.tag = oak_EndianError_tag_BufferTooSmall;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:320:4-320:29
// @package: main
// @kind: ADT
// @identifier: ByteRangeError
typedef enum oak_ByteRangeError_tag {
    oak_ByteRangeError_tag_OutOfBounds
} oak_ByteRangeError_tag;

typedef struct oak_ByteRangeError {
    u32 tag;
} oak_ByteRangeError;

typedef char oak_union_layout_ByteRangeError[ (sizeof(oak_ByteRangeError) == 4u && _Alignof(oak_ByteRangeError) == 4u && offsetof(oak_ByteRangeError, tag) == 0u) ? 1 : -1 ];

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:320:29
// @package: main
// @kind: constructor
// @identifier: oak_ByteRangeError::OutOfBounds
static inline oak_ByteRangeError oak_ByteRangeError_OutOfBounds(  ) {
    oak_ByteRangeError res;
    res.tag = oak_ByteRangeError_tag_OutOfBounds;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:384:4-384:31
// @package: main
// @kind: ADT
// @identifier: BufferError
typedef enum oak_BufferError_tag {
    oak_BufferError_tag_Full  ,
    oak_BufferError_tag_InsufficientData
} oak_BufferError_tag;

typedef struct oak_BufferError {
    u32 tag;
} oak_BufferError;

typedef char oak_union_layout_BufferError[ (sizeof(oak_BufferError) == 4u && _Alignof(oak_BufferError) == 4u && offsetof(oak_BufferError, tag) == 0u) ? 1 : -1 ];

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:384:24
// @package: main
// @kind: constructor
// @identifier: oak_BufferError::Full
static inline oak_BufferError oak_BufferError_Full(  ) {
    oak_BufferError res;
    res.tag = oak_BufferError_tag_Full;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:384:31
// @package: main
// @kind: constructor
// @identifier: oak_BufferError::InsufficientData
static inline oak_BufferError oak_BufferError_InsufficientData(  ) {
    oak_BufferError res;
    res.tag = oak_BufferError_tag_InsufficientData;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:520:4-520:73
// @package: main
// @kind: ADT
// @identifier: CollectionError
typedef enum oak_CollectionError_tag {
    oak_CollectionError_tag_Full  ,
    oak_CollectionError_tag_Empty  ,
    oak_CollectionError_tag_OutOfBounds  ,
    oak_CollectionError_tag_AlreadyLinked  ,
    oak_CollectionError_tag_NotMember
} oak_CollectionError_tag;

typedef struct oak_CollectionError {
    u32 tag;
} oak_CollectionError;

typedef char oak_union_layout_CollectionError[ (sizeof(oak_CollectionError) == 4u && _Alignof(oak_CollectionError) == 4u && offsetof(oak_CollectionError, tag) == 0u) ? 1 : -1 ];

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:520:28
// @package: main
// @kind: constructor
// @identifier: oak_CollectionError::Full
static inline oak_CollectionError oak_CollectionError_Full(  ) {
    oak_CollectionError res;
    res.tag = oak_CollectionError_tag_Full;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:520:35
// @package: main
// @kind: constructor
// @identifier: oak_CollectionError::Empty
static inline oak_CollectionError oak_CollectionError_Empty(  ) {
    oak_CollectionError res;
    res.tag = oak_CollectionError_tag_Empty;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:520:43
// @package: main
// @kind: constructor
// @identifier: oak_CollectionError::OutOfBounds
static inline oak_CollectionError oak_CollectionError_OutOfBounds(  ) {
    oak_CollectionError res;
    res.tag = oak_CollectionError_tag_OutOfBounds;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:520:57
// @package: main
// @kind: constructor
// @identifier: oak_CollectionError::AlreadyLinked
static inline oak_CollectionError oak_CollectionError_AlreadyLinked(  ) {
    oak_CollectionError res;
    res.tag = oak_CollectionError_tag_AlreadyLinked;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:520:73
// @package: main
// @kind: constructor
// @identifier: oak_CollectionError::NotMember
static inline oak_CollectionError oak_CollectionError_NotMember(  ) {
    oak_CollectionError res;
    res.tag = oak_CollectionError_tag_NotMember;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:890:4-890:55
// @package: main
// @kind: ADT
// @identifier: ListTransferError
typedef enum oak_ListTransferError_tag {
    oak_ListTransferError_tag_SameList  ,
    oak_ListTransferError_tag_OutOfBounds  ,
    oak_ListTransferError_tag_NotMember
} oak_ListTransferError_tag;

typedef struct oak_ListTransferError {
    u32 tag;
} oak_ListTransferError;

typedef char oak_union_layout_ListTransferError[ (sizeof(oak_ListTransferError) == 4u && _Alignof(oak_ListTransferError) == 4u && offsetof(oak_ListTransferError, tag) == 0u) ? 1 : -1 ];

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:890:30
// @package: main
// @kind: constructor
// @identifier: oak_ListTransferError::SameList
static inline oak_ListTransferError oak_ListTransferError_SameList(  ) {
    oak_ListTransferError res;
    res.tag = oak_ListTransferError_tag_SameList;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:890:41
// @package: main
// @kind: constructor
// @identifier: oak_ListTransferError::OutOfBounds
static inline oak_ListTransferError oak_ListTransferError_OutOfBounds(  ) {
    oak_ListTransferError res;
    res.tag = oak_ListTransferError_tag_OutOfBounds;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:890:55
// @package: main
// @kind: constructor
// @identifier: oak_ListTransferError::NotMember
static inline oak_ListTransferError oak_ListTransferError_NotMember(  ) {
    oak_ListTransferError res;
    res.tag = oak_ListTransferError_tag_NotMember;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:1324:4-1324:82
// @package: main
// @kind: ADT
// @identifier: IdPoolError
typedef enum oak_IdPoolError_tag {
    oak_IdPoolError_tag_StorageTooSmall  ,
    oak_IdPoolError_tag_Full  ,
    oak_IdPoolError_tag_OutOfBounds  ,
    oak_IdPoolError_tag_AlreadyAllocated  ,
    oak_IdPoolError_tag_NotAllocated
} oak_IdPoolError_tag;

typedef struct oak_IdPoolError {
    u32 tag;
} oak_IdPoolError;

typedef char oak_union_layout_IdPoolError[ (sizeof(oak_IdPoolError) == 4u && _Alignof(oak_IdPoolError) == 4u && offsetof(oak_IdPoolError, tag) == 0u) ? 1 : -1 ];

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:1324:24
// @package: main
// @kind: constructor
// @identifier: oak_IdPoolError::StorageTooSmall
static inline oak_IdPoolError oak_IdPoolError_StorageTooSmall(  ) {
    oak_IdPoolError res;
    res.tag = oak_IdPoolError_tag_StorageTooSmall;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:1324:42
// @package: main
// @kind: constructor
// @identifier: oak_IdPoolError::Full
static inline oak_IdPoolError oak_IdPoolError_Full(  ) {
    oak_IdPoolError res;
    res.tag = oak_IdPoolError_tag_Full;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:1324:49
// @package: main
// @kind: constructor
// @identifier: oak_IdPoolError::OutOfBounds
static inline oak_IdPoolError oak_IdPoolError_OutOfBounds(  ) {
    oak_IdPoolError res;
    res.tag = oak_IdPoolError_tag_OutOfBounds;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:1324:63
// @package: main
// @kind: constructor
// @identifier: oak_IdPoolError::AlreadyAllocated
static inline oak_IdPoolError oak_IdPoolError_AlreadyAllocated(  ) {
    oak_IdPoolError res;
    res.tag = oak_IdPoolError_tag_AlreadyAllocated;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:1324:82
// @package: main
// @kind: constructor
// @identifier: oak_IdPoolError::NotAllocated
static inline oak_IdPoolError oak_IdPoolError_NotAllocated(  ) {
    oak_IdPoolError res;
    res.tag = oak_IdPoolError_tag_NotAllocated;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:-1:19--1:15
// @package: main
// @kind: ADT
// @identifier: Utf8State
typedef enum oak_Utf8State_tag {
    oak_Utf8State_tag_Accept   = 0  ,
    oak_Utf8State_tag_Two   = 6  ,
    oak_Utf8State_tag_ThreeE0   = 12  ,
    oak_Utf8State_tag_Three   = 18  ,
    oak_Utf8State_tag_ThreeED   = 24  ,
    oak_Utf8State_tag_FourF0   = 30  ,
    oak_Utf8State_tag_Four   = 36  ,
    oak_Utf8State_tag_FourF4   = 42
} oak_Utf8State_tag;

typedef struct oak_Utf8State {
    u32 tag;
} oak_Utf8State;

typedef char oak_union_layout_Utf8State[ (sizeof(oak_Utf8State) == 4u && _Alignof(oak_Utf8State) == 4u && offsetof(oak_Utf8State, tag) == 0u) ? 1 : -1 ];

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:-1:0
// @package: main
// @kind: constructor
// @identifier: oak_Utf8State::Accept
static inline oak_Utf8State oak_Utf8State_Accept(  ) {
    oak_Utf8State res;
    res.tag = oak_Utf8State_tag_Accept;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:-1:2
// @package: main
// @kind: constructor
// @identifier: oak_Utf8State::Two
static inline oak_Utf8State oak_Utf8State_Two(  ) {
    oak_Utf8State res;
    res.tag = oak_Utf8State_tag_Two;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:-1:4
// @package: main
// @kind: constructor
// @identifier: oak_Utf8State::ThreeE0
static inline oak_Utf8State oak_Utf8State_ThreeE0(  ) {
    oak_Utf8State res;
    res.tag = oak_Utf8State_tag_ThreeE0;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:-1:6
// @package: main
// @kind: constructor
// @identifier: oak_Utf8State::Three
static inline oak_Utf8State oak_Utf8State_Three(  ) {
    oak_Utf8State res;
    res.tag = oak_Utf8State_tag_Three;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:-1:8
// @package: main
// @kind: constructor
// @identifier: oak_Utf8State::ThreeED
static inline oak_Utf8State oak_Utf8State_ThreeED(  ) {
    oak_Utf8State res;
    res.tag = oak_Utf8State_tag_ThreeED;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:-1:10
// @package: main
// @kind: constructor
// @identifier: oak_Utf8State::FourF0
static inline oak_Utf8State oak_Utf8State_FourF0(  ) {
    oak_Utf8State res;
    res.tag = oak_Utf8State_tag_FourF0;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:-1:12
// @package: main
// @kind: constructor
// @identifier: oak_Utf8State::Four
static inline oak_Utf8State oak_Utf8State_Four(  ) {
    oak_Utf8State res;
    res.tag = oak_Utf8State_tag_Four;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:-1:14
// @package: main
// @kind: constructor
// @identifier: oak_Utf8State::FourF4
static inline oak_Utf8State oak_Utf8State_FourF4(  ) {
    oak_Utf8State res;
    res.tag = oak_Utf8State_tag_FourF4;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:-1:22--1:17
// @package: main
// @kind: ADT
// @identifier: Utf8Step
typedef enum oak_Utf8Step_tag {
    oak_Utf8Step_tag_Byte
} oak_Utf8Step_tag;

typedef struct oak_Utf8Step {
    u32 tag;
    union {
        u8 Byte;
    } payload;
} oak_Utf8Step;

typedef char oak_union_layout_Utf8Step[ (sizeof(oak_Utf8Step) == 8u && _Alignof(oak_Utf8Step) == 4u && offsetof(oak_Utf8Step, tag) == 0u && offsetof(oak_Utf8Step, payload) == 4u) ? 1 : -1 ];

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:-1:16
// @package: main
// @kind: constructor
// @identifier: oak_Utf8Step::Byte
static inline oak_Utf8Step oak_Utf8Step_Byte( u8 value ) {
    oak_Utf8Step res;
    res.tag = oak_Utf8Step_tag_Byte;
    res.payload.Byte = value;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:1:4-1:32
// @package: main
// @kind: ADT
// @identifier: Option_u32
typedef enum oak_Option_u32_tag {
    oak_Option_u32_tag_Some  ,
    oak_Option_u32_tag_None
} oak_Option_u32_tag;

typedef struct oak_Option_u32 {
    u32 tag;
    union {
        u32 Some;
    } payload;
} oak_Option_u32;

typedef char oak_union_layout_Option_u32[ (sizeof(oak_Option_u32) == 8u && _Alignof(oak_Option_u32) == 4u && offsetof(oak_Option_u32, tag) == 0u && offsetof(oak_Option_u32, payload) == 4u) ? 1 : -1 ];

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:1:22
// @package: main
// @kind: constructor
// @identifier: oak_Option_u32::Some
static inline oak_Option_u32 oak_Option_u32_Some( u32 value ) {
    oak_Option_u32 res;
    res.tag = oak_Option_u32_tag_Some;
    res.payload.Some = value;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:1:32
// @package: main
// @kind: constructor
// @identifier: oak_Option_u32::None
static inline oak_Option_u32 oak_Option_u32_None(  ) {
    oak_Option_u32 res;
    res.tag = oak_Option_u32_tag_None;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:4-2:33
// @package: main
// @kind: ADT
// @identifier: Result_Bool_BitSetError
typedef enum oak_Result_Bool_BitSetError_tag {
    oak_Result_Bool_BitSetError_tag_Ok  ,
    oak_Result_Bool_BitSetError_tag_Err
} oak_Result_Bool_BitSetError_tag;

typedef struct oak_Result_Bool_BitSetError {
    u32 tag;
    union {
        Bool Ok;
        oak_BitSetError Err;
    } payload;
} oak_Result_Bool_BitSetError;

typedef char oak_union_layout_Result_Bool_BitSetError[ (sizeof(oak_Result_Bool_BitSetError) == 8u && _Alignof(oak_Result_Bool_BitSetError) == 4u && offsetof(oak_Result_Bool_BitSetError, tag) == 0u && offsetof(oak_Result_Bool_BitSetError, payload) == 4u) ? 1 : -1 ];

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:25
// @package: main
// @kind: constructor
// @identifier: oak_Result_Bool_BitSetError::Ok
static inline oak_Result_Bool_BitSetError oak_Result_Bool_BitSetError_Ok( Bool value ) {
    oak_Result_Bool_BitSetError res;
    res.tag = oak_Result_Bool_BitSetError_tag_Ok;
    res.payload.Ok = value;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:33
// @package: main
// @kind: constructor
// @identifier: oak_Result_Bool_BitSetError::Err
static inline oak_Result_Bool_BitSetError oak_Result_Bool_BitSetError_Err( oak_BitSetError value ) {
    oak_Result_Bool_BitSetError res;
    res.tag = oak_Result_Bool_BitSetError_tag_Err;
    res.payload.Err = value;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:4-2:33
// @package: main
// @kind: ADT
// @identifier: Result_Bool_IdPoolError
typedef enum oak_Result_Bool_IdPoolError_tag {
    oak_Result_Bool_IdPoolError_tag_Ok  ,
    oak_Result_Bool_IdPoolError_tag_Err
} oak_Result_Bool_IdPoolError_tag;

typedef struct oak_Result_Bool_IdPoolError {
    u32 tag;
    union {
        Bool Ok;
        oak_IdPoolError Err;
    } payload;
} oak_Result_Bool_IdPoolError;

typedef char oak_union_layout_Result_Bool_IdPoolError[ (sizeof(oak_Result_Bool_IdPoolError) == 8u && _Alignof(oak_Result_Bool_IdPoolError) == 4u && offsetof(oak_Result_Bool_IdPoolError, tag) == 0u && offsetof(oak_Result_Bool_IdPoolError, payload) == 4u) ? 1 : -1 ];

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:25
// @package: main
// @kind: constructor
// @identifier: oak_Result_Bool_IdPoolError::Ok
static inline oak_Result_Bool_IdPoolError oak_Result_Bool_IdPoolError_Ok( Bool value ) {
    oak_Result_Bool_IdPoolError res;
    res.tag = oak_Result_Bool_IdPoolError_tag_Ok;
    res.payload.Ok = value;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:33
// @package: main
// @kind: constructor
// @identifier: oak_Result_Bool_IdPoolError::Err
static inline oak_Result_Bool_IdPoolError oak_Result_Bool_IdPoolError_Err( oak_IdPoolError value ) {
    oak_Result_Bool_IdPoolError res;
    res.tag = oak_Result_Bool_IdPoolError_tag_Err;
    res.payload.Err = value;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:4-2:33
// @package: main
// @kind: ADT
// @identifier: Result_u16_EndianError
typedef enum oak_Result_u16_EndianError_tag {
    oak_Result_u16_EndianError_tag_Ok  ,
    oak_Result_u16_EndianError_tag_Err
} oak_Result_u16_EndianError_tag;

typedef struct oak_Result_u16_EndianError {
    u32 tag;
    union {
        u16 Ok;
        oak_EndianError Err;
    } payload;
} oak_Result_u16_EndianError;

typedef char oak_union_layout_Result_u16_EndianError[ (sizeof(oak_Result_u16_EndianError) == 8u && _Alignof(oak_Result_u16_EndianError) == 4u && offsetof(oak_Result_u16_EndianError, tag) == 0u && offsetof(oak_Result_u16_EndianError, payload) == 4u) ? 1 : -1 ];

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:25
// @package: main
// @kind: constructor
// @identifier: oak_Result_u16_EndianError::Ok
static inline oak_Result_u16_EndianError oak_Result_u16_EndianError_Ok( u16 value ) {
    oak_Result_u16_EndianError res;
    res.tag = oak_Result_u16_EndianError_tag_Ok;
    res.payload.Ok = value;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:33
// @package: main
// @kind: constructor
// @identifier: oak_Result_u16_EndianError::Err
static inline oak_Result_u16_EndianError oak_Result_u16_EndianError_Err( oak_EndianError value ) {
    oak_Result_u16_EndianError res;
    res.tag = oak_Result_u16_EndianError_tag_Err;
    res.payload.Err = value;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:4-2:33
// @package: main
// @kind: ADT
// @identifier: Result_u32_BitSetError
typedef enum oak_Result_u32_BitSetError_tag {
    oak_Result_u32_BitSetError_tag_Ok  ,
    oak_Result_u32_BitSetError_tag_Err
} oak_Result_u32_BitSetError_tag;

typedef struct oak_Result_u32_BitSetError {
    u32 tag;
    union {
        u32 Ok;
        oak_BitSetError Err;
    } payload;
} oak_Result_u32_BitSetError;

typedef char oak_union_layout_Result_u32_BitSetError[ (sizeof(oak_Result_u32_BitSetError) == 8u && _Alignof(oak_Result_u32_BitSetError) == 4u && offsetof(oak_Result_u32_BitSetError, tag) == 0u && offsetof(oak_Result_u32_BitSetError, payload) == 4u) ? 1 : -1 ];

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:25
// @package: main
// @kind: constructor
// @identifier: oak_Result_u32_BitSetError::Ok
static inline oak_Result_u32_BitSetError oak_Result_u32_BitSetError_Ok( u32 value ) {
    oak_Result_u32_BitSetError res;
    res.tag = oak_Result_u32_BitSetError_tag_Ok;
    res.payload.Ok = value;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:33
// @package: main
// @kind: constructor
// @identifier: oak_Result_u32_BitSetError::Err
static inline oak_Result_u32_BitSetError oak_Result_u32_BitSetError_Err( oak_BitSetError value ) {
    oak_Result_u32_BitSetError res;
    res.tag = oak_Result_u32_BitSetError_tag_Err;
    res.payload.Err = value;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:4-2:33
// @package: main
// @kind: ADT
// @identifier: Result_u32_BufferError
typedef enum oak_Result_u32_BufferError_tag {
    oak_Result_u32_BufferError_tag_Ok  ,
    oak_Result_u32_BufferError_tag_Err
} oak_Result_u32_BufferError_tag;

typedef struct oak_Result_u32_BufferError {
    u32 tag;
    union {
        u32 Ok;
        oak_BufferError Err;
    } payload;
} oak_Result_u32_BufferError;

typedef char oak_union_layout_Result_u32_BufferError[ (sizeof(oak_Result_u32_BufferError) == 8u && _Alignof(oak_Result_u32_BufferError) == 4u && offsetof(oak_Result_u32_BufferError, tag) == 0u && offsetof(oak_Result_u32_BufferError, payload) == 4u) ? 1 : -1 ];

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:25
// @package: main
// @kind: constructor
// @identifier: oak_Result_u32_BufferError::Ok
static inline oak_Result_u32_BufferError oak_Result_u32_BufferError_Ok( u32 value ) {
    oak_Result_u32_BufferError res;
    res.tag = oak_Result_u32_BufferError_tag_Ok;
    res.payload.Ok = value;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:33
// @package: main
// @kind: constructor
// @identifier: oak_Result_u32_BufferError::Err
static inline oak_Result_u32_BufferError oak_Result_u32_BufferError_Err( oak_BufferError value ) {
    oak_Result_u32_BufferError res;
    res.tag = oak_Result_u32_BufferError_tag_Err;
    res.payload.Err = value;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:4-2:33
// @package: main
// @kind: ADT
// @identifier: Result_u32_ByteRangeError
typedef enum oak_Result_u32_ByteRangeError_tag {
    oak_Result_u32_ByteRangeError_tag_Ok  ,
    oak_Result_u32_ByteRangeError_tag_Err
} oak_Result_u32_ByteRangeError_tag;

typedef struct oak_Result_u32_ByteRangeError {
    u32 tag;
    union {
        u32 Ok;
        oak_ByteRangeError Err;
    } payload;
} oak_Result_u32_ByteRangeError;

typedef char oak_union_layout_Result_u32_ByteRangeError[ (sizeof(oak_Result_u32_ByteRangeError) == 8u && _Alignof(oak_Result_u32_ByteRangeError) == 4u && offsetof(oak_Result_u32_ByteRangeError, tag) == 0u && offsetof(oak_Result_u32_ByteRangeError, payload) == 4u) ? 1 : -1 ];

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:25
// @package: main
// @kind: constructor
// @identifier: oak_Result_u32_ByteRangeError::Ok
static inline oak_Result_u32_ByteRangeError oak_Result_u32_ByteRangeError_Ok( u32 value ) {
    oak_Result_u32_ByteRangeError res;
    res.tag = oak_Result_u32_ByteRangeError_tag_Ok;
    res.payload.Ok = value;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:33
// @package: main
// @kind: constructor
// @identifier: oak_Result_u32_ByteRangeError::Err
static inline oak_Result_u32_ByteRangeError oak_Result_u32_ByteRangeError_Err( oak_ByteRangeError value ) {
    oak_Result_u32_ByteRangeError res;
    res.tag = oak_Result_u32_ByteRangeError_tag_Err;
    res.payload.Err = value;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:4-2:33
// @package: main
// @kind: ADT
// @identifier: Result_u32_CollectionError
typedef enum oak_Result_u32_CollectionError_tag {
    oak_Result_u32_CollectionError_tag_Ok  ,
    oak_Result_u32_CollectionError_tag_Err
} oak_Result_u32_CollectionError_tag;

typedef struct oak_Result_u32_CollectionError {
    u32 tag;
    union {
        u32 Ok;
        oak_CollectionError Err;
    } payload;
} oak_Result_u32_CollectionError;

typedef char oak_union_layout_Result_u32_CollectionError[ (sizeof(oak_Result_u32_CollectionError) == 8u && _Alignof(oak_Result_u32_CollectionError) == 4u && offsetof(oak_Result_u32_CollectionError, tag) == 0u && offsetof(oak_Result_u32_CollectionError, payload) == 4u) ? 1 : -1 ];

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:25
// @package: main
// @kind: constructor
// @identifier: oak_Result_u32_CollectionError::Ok
static inline oak_Result_u32_CollectionError oak_Result_u32_CollectionError_Ok( u32 value ) {
    oak_Result_u32_CollectionError res;
    res.tag = oak_Result_u32_CollectionError_tag_Ok;
    res.payload.Ok = value;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:33
// @package: main
// @kind: constructor
// @identifier: oak_Result_u32_CollectionError::Err
static inline oak_Result_u32_CollectionError oak_Result_u32_CollectionError_Err( oak_CollectionError value ) {
    oak_Result_u32_CollectionError res;
    res.tag = oak_Result_u32_CollectionError_tag_Err;
    res.payload.Err = value;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:4-2:33
// @package: main
// @kind: ADT
// @identifier: Result_u32_CopyError
typedef enum oak_Result_u32_CopyError_tag {
    oak_Result_u32_CopyError_tag_Ok  ,
    oak_Result_u32_CopyError_tag_Err
} oak_Result_u32_CopyError_tag;

typedef struct oak_Result_u32_CopyError {
    u32 tag;
    union {
        u32 Ok;
        oak_CopyError Err;
    } payload;
} oak_Result_u32_CopyError;

typedef char oak_union_layout_Result_u32_CopyError[ (sizeof(oak_Result_u32_CopyError) == 8u && _Alignof(oak_Result_u32_CopyError) == 4u && offsetof(oak_Result_u32_CopyError, tag) == 0u && offsetof(oak_Result_u32_CopyError, payload) == 4u) ? 1 : -1 ];

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:25
// @package: main
// @kind: constructor
// @identifier: oak_Result_u32_CopyError::Ok
static inline oak_Result_u32_CopyError oak_Result_u32_CopyError_Ok( u32 value ) {
    oak_Result_u32_CopyError res;
    res.tag = oak_Result_u32_CopyError_tag_Ok;
    res.payload.Ok = value;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:33
// @package: main
// @kind: constructor
// @identifier: oak_Result_u32_CopyError::Err
static inline oak_Result_u32_CopyError oak_Result_u32_CopyError_Err( oak_CopyError value ) {
    oak_Result_u32_CopyError res;
    res.tag = oak_Result_u32_CopyError_tag_Err;
    res.payload.Err = value;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:4-2:33
// @package: main
// @kind: ADT
// @identifier: Result_u32_EndianError
typedef enum oak_Result_u32_EndianError_tag {
    oak_Result_u32_EndianError_tag_Ok  ,
    oak_Result_u32_EndianError_tag_Err
} oak_Result_u32_EndianError_tag;

typedef struct oak_Result_u32_EndianError {
    u32 tag;
    union {
        u32 Ok;
        oak_EndianError Err;
    } payload;
} oak_Result_u32_EndianError;

typedef char oak_union_layout_Result_u32_EndianError[ (sizeof(oak_Result_u32_EndianError) == 8u && _Alignof(oak_Result_u32_EndianError) == 4u && offsetof(oak_Result_u32_EndianError, tag) == 0u && offsetof(oak_Result_u32_EndianError, payload) == 4u) ? 1 : -1 ];

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:25
// @package: main
// @kind: constructor
// @identifier: oak_Result_u32_EndianError::Ok
static inline oak_Result_u32_EndianError oak_Result_u32_EndianError_Ok( u32 value ) {
    oak_Result_u32_EndianError res;
    res.tag = oak_Result_u32_EndianError_tag_Ok;
    res.payload.Ok = value;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:33
// @package: main
// @kind: constructor
// @identifier: oak_Result_u32_EndianError::Err
static inline oak_Result_u32_EndianError oak_Result_u32_EndianError_Err( oak_EndianError value ) {
    oak_Result_u32_EndianError res;
    res.tag = oak_Result_u32_EndianError_tag_Err;
    res.payload.Err = value;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:4-2:33
// @package: main
// @kind: ADT
// @identifier: Result_u32_IdPoolError
typedef enum oak_Result_u32_IdPoolError_tag {
    oak_Result_u32_IdPoolError_tag_Ok  ,
    oak_Result_u32_IdPoolError_tag_Err
} oak_Result_u32_IdPoolError_tag;

typedef struct oak_Result_u32_IdPoolError {
    u32 tag;
    union {
        u32 Ok;
        oak_IdPoolError Err;
    } payload;
} oak_Result_u32_IdPoolError;

typedef char oak_union_layout_Result_u32_IdPoolError[ (sizeof(oak_Result_u32_IdPoolError) == 8u && _Alignof(oak_Result_u32_IdPoolError) == 4u && offsetof(oak_Result_u32_IdPoolError, tag) == 0u && offsetof(oak_Result_u32_IdPoolError, payload) == 4u) ? 1 : -1 ];

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:25
// @package: main
// @kind: constructor
// @identifier: oak_Result_u32_IdPoolError::Ok
static inline oak_Result_u32_IdPoolError oak_Result_u32_IdPoolError_Ok( u32 value ) {
    oak_Result_u32_IdPoolError res;
    res.tag = oak_Result_u32_IdPoolError_tag_Ok;
    res.payload.Ok = value;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:33
// @package: main
// @kind: constructor
// @identifier: oak_Result_u32_IdPoolError::Err
static inline oak_Result_u32_IdPoolError oak_Result_u32_IdPoolError_Err( oak_IdPoolError value ) {
    oak_Result_u32_IdPoolError res;
    res.tag = oak_Result_u32_IdPoolError_tag_Err;
    res.payload.Err = value;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:4-2:33
// @package: main
// @kind: ADT
// @identifier: Result_u32_ListTransferError
typedef enum oak_Result_u32_ListTransferError_tag {
    oak_Result_u32_ListTransferError_tag_Ok  ,
    oak_Result_u32_ListTransferError_tag_Err
} oak_Result_u32_ListTransferError_tag;

typedef struct oak_Result_u32_ListTransferError {
    u32 tag;
    union {
        u32 Ok;
        oak_ListTransferError Err;
    } payload;
} oak_Result_u32_ListTransferError;

typedef char oak_union_layout_Result_u32_ListTransferError[ (sizeof(oak_Result_u32_ListTransferError) == 8u && _Alignof(oak_Result_u32_ListTransferError) == 4u && offsetof(oak_Result_u32_ListTransferError, tag) == 0u && offsetof(oak_Result_u32_ListTransferError, payload) == 4u) ? 1 : -1 ];

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:25
// @package: main
// @kind: constructor
// @identifier: oak_Result_u32_ListTransferError::Ok
static inline oak_Result_u32_ListTransferError oak_Result_u32_ListTransferError_Ok( u32 value ) {
    oak_Result_u32_ListTransferError res;
    res.tag = oak_Result_u32_ListTransferError_tag_Ok;
    res.payload.Ok = value;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:33
// @package: main
// @kind: constructor
// @identifier: oak_Result_u32_ListTransferError::Err
static inline oak_Result_u32_ListTransferError oak_Result_u32_ListTransferError_Err( oak_ListTransferError value ) {
    oak_Result_u32_ListTransferError res;
    res.tag = oak_Result_u32_ListTransferError_tag_Err;
    res.payload.Err = value;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:4-2:33
// @package: main
// @kind: ADT
// @identifier: Result_u64_EndianError
typedef enum oak_Result_u64_EndianError_tag {
    oak_Result_u64_EndianError_tag_Ok  ,
    oak_Result_u64_EndianError_tag_Err
} oak_Result_u64_EndianError_tag;

typedef struct oak_Result_u64_EndianError {
    u32 tag;
    union {
        u64 Ok;
        oak_EndianError Err;
    } payload;
} oak_Result_u64_EndianError;

typedef char oak_union_layout_Result_u64_EndianError[ (sizeof(oak_Result_u64_EndianError) == 16u && _Alignof(oak_Result_u64_EndianError) == 8u && offsetof(oak_Result_u64_EndianError, tag) == 0u && offsetof(oak_Result_u64_EndianError, payload) == 8u) ? 1 : -1 ];

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:25
// @package: main
// @kind: constructor
// @identifier: oak_Result_u64_EndianError::Ok
static inline oak_Result_u64_EndianError oak_Result_u64_EndianError_Ok( u64 value ) {
    oak_Result_u64_EndianError res;
    res.tag = oak_Result_u64_EndianError_tag_Ok;
    res.payload.Ok = value;
    return res;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:2:33
// @package: main
// @kind: constructor
// @identifier: oak_Result_u64_EndianError::Err
static inline oak_Result_u64_EndianError oak_Result_u64_EndianError_Err( oak_EndianError value ) {
    oak_Result_u64_EndianError res;
    res.tag = oak_Result_u64_EndianError_tag_Err;
    res.payload.Err = value;
    return res;
}

typedef struct oak_span_oak_RingCursor {
    oak_RingCursor* base;
    u32 len;
} oak_span_oak_RingCursor;

static inline oak_RingCursor oak_span_index_oak_RingCursor(oak_span_oak_RingCursor v, u64 i) {
  if (i >= (u64)v.len) { __builtin_trap(); }
  return v.base[i];
}

static inline void oak_span_store_oak_RingCursor(oak_span_oak_RingCursor v, u64 i, oak_RingCursor value) {
  if (i >= (u64)v.len) { __builtin_trap(); }
  v.base[i] = value;
}

static inline oak_span_oak_RingCursor oak_span_subslice_oak_RingCursor(oak_span_oak_RingCursor v, u64 start, u64 n) {
  if (start > (u64)v.len || n > (u64)v.len - start) { __builtin_trap(); }
  return (oak_span_oak_RingCursor){ v.base + start, (u32)n };
}

typedef struct oak_span_u8 {
    u8* base;
    u32 len;
} oak_span_u8;

static inline u8 oak_span_index_u8(oak_span_u8 v, u64 i) {
  if (i >= (u64)v.len) { __builtin_trap(); }
  return v.base[i];
}

static inline void oak_span_store_u8(oak_span_u8 v, u64 i, u8 value) {
  if (i >= (u64)v.len) { __builtin_trap(); }
  v.base[i] = value;
}

static inline oak_span_u8 oak_span_subslice_u8(oak_span_u8 v, u64 start, u64 n) {
  if (start > (u64)v.len || n > (u64)v.len - start) { __builtin_trap(); }
  return (oak_span_u8){ v.base + start, (u32)n };
}

typedef struct oak_span_oak_ByteBufferCursor {
    oak_ByteBufferCursor* base;
    u32 len;
} oak_span_oak_ByteBufferCursor;

static inline oak_ByteBufferCursor oak_span_index_oak_ByteBufferCursor(oak_span_oak_ByteBufferCursor v, u64 i) {
  if (i >= (u64)v.len) { __builtin_trap(); }
  return v.base[i];
}

static inline void oak_span_store_oak_ByteBufferCursor(oak_span_oak_ByteBufferCursor v, u64 i, oak_ByteBufferCursor value) {
  if (i >= (u64)v.len) { __builtin_trap(); }
  v.base[i] = value;
}

static inline oak_span_oak_ByteBufferCursor oak_span_subslice_oak_ByteBufferCursor(oak_span_oak_ByteBufferCursor v, u64 start, u64 n) {
  if (start > (u64)v.len || n > (u64)v.len - start) { __builtin_trap(); }
  return (oak_span_oak_ByteBufferCursor){ v.base + start, (u32)n };
}

typedef struct oak_span_oak_ArrayListCursor {
    oak_ArrayListCursor* base;
    u32 len;
} oak_span_oak_ArrayListCursor;

static inline oak_ArrayListCursor oak_span_index_oak_ArrayListCursor(oak_span_oak_ArrayListCursor v, u64 i) {
  if (i >= (u64)v.len) { __builtin_trap(); }
  return v.base[i];
}

static inline void oak_span_store_oak_ArrayListCursor(oak_span_oak_ArrayListCursor v, u64 i, oak_ArrayListCursor value) {
  if (i >= (u64)v.len) { __builtin_trap(); }
  v.base[i] = value;
}

static inline oak_span_oak_ArrayListCursor oak_span_subslice_oak_ArrayListCursor(oak_span_oak_ArrayListCursor v, u64 start, u64 n) {
  if (start > (u64)v.len || n > (u64)v.len - start) { __builtin_trap(); }
  return (oak_span_oak_ArrayListCursor){ v.base + start, (u32)n };
}

typedef struct oak_span_oak_IntrusiveCursor {
    oak_IntrusiveCursor* base;
    u32 len;
} oak_span_oak_IntrusiveCursor;

static inline oak_IntrusiveCursor oak_span_index_oak_IntrusiveCursor(oak_span_oak_IntrusiveCursor v, u64 i) {
  if (i >= (u64)v.len) { __builtin_trap(); }
  return v.base[i];
}

static inline void oak_span_store_oak_IntrusiveCursor(oak_span_oak_IntrusiveCursor v, u64 i, oak_IntrusiveCursor value) {
  if (i >= (u64)v.len) { __builtin_trap(); }
  v.base[i] = value;
}

static inline oak_span_oak_IntrusiveCursor oak_span_subslice_oak_IntrusiveCursor(oak_span_oak_IntrusiveCursor v, u64 start, u64 n) {
  if (start > (u64)v.len || n > (u64)v.len - start) { __builtin_trap(); }
  return (oak_span_oak_IntrusiveCursor){ v.base + start, (u32)n };
}

typedef struct oak_span_oak_MinHeapCursor {
    oak_MinHeapCursor* base;
    u32 len;
} oak_span_oak_MinHeapCursor;

static inline oak_MinHeapCursor oak_span_index_oak_MinHeapCursor(oak_span_oak_MinHeapCursor v, u64 i) {
  if (i >= (u64)v.len) { __builtin_trap(); }
  return v.base[i];
}

static inline void oak_span_store_oak_MinHeapCursor(oak_span_oak_MinHeapCursor v, u64 i, oak_MinHeapCursor value) {
  if (i >= (u64)v.len) { __builtin_trap(); }
  v.base[i] = value;
}

static inline oak_span_oak_MinHeapCursor oak_span_subslice_oak_MinHeapCursor(oak_span_oak_MinHeapCursor v, u64 start, u64 n) {
  if (start > (u64)v.len || n > (u64)v.len - start) { __builtin_trap(); }
  return (oak_span_oak_MinHeapCursor){ v.base + start, (u32)n };
}

typedef struct oak_span_oak_DequeCursor {
    oak_DequeCursor* base;
    u32 len;
} oak_span_oak_DequeCursor;

static inline oak_DequeCursor oak_span_index_oak_DequeCursor(oak_span_oak_DequeCursor v, u64 i) {
  if (i >= (u64)v.len) { __builtin_trap(); }
  return v.base[i];
}

static inline void oak_span_store_oak_DequeCursor(oak_span_oak_DequeCursor v, u64 i, oak_DequeCursor value) {
  if (i >= (u64)v.len) { __builtin_trap(); }
  v.base[i] = value;
}

static inline oak_span_oak_DequeCursor oak_span_subslice_oak_DequeCursor(oak_span_oak_DequeCursor v, u64 start, u64 n) {
  if (start > (u64)v.len || n > (u64)v.len - start) { __builtin_trap(); }
  return (oak_span_oak_DequeCursor){ v.base + start, (u32)n };
}

typedef struct oak_arr_u8_16 { u8 v[ 16 ]; } oak_arr_u8_16;

typedef struct oak_arr_u8_4 { u8 v[ 4 ]; } oak_arr_u8_4;

/* static globals: constant-initialized, zero otherwise */
static u8 utf8__too_ushort = ((u8)( 1 ));
static u8 utf8__too_ulong = ((u8)( 2 ));
static u8 utf8__overlong_u3 = ((u8)( 4 ));
static u8 utf8__too_ularge = ((u8)( 8 ));
static u8 utf8__surrogate = ((u8)( 16 ));
static u8 utf8__overlong_u2 = ((u8)( 32 ));
static u8 utf8__too_ularge_u1000 = ((u8)( 64 ));
static u8 utf8__overlong_u4 = ((u8)( 64 ));
static u8 utf8__two_uconts = ((u8)( 128 ));
static u8 utf8__carry = ((u8)( 131 ));
static oak_arr_u8_16 utf8__table_uhigh1 = { { ((u8)( 2 )), ((u8)( 2 )), ((u8)( 2 )), ((u8)( 2 )), ((u8)( 2 )), ((u8)( 2 )), ((u8)( 2 )), ((u8)( 2 )), ((u8)( 128 )), ((u8)( 128 )), ((u8)( 128 )), ((u8)( 128 )), ((u8)( 33 )), ((u8)( 1 )), ((u8)( 21 )), ((u8)( 73 )) } };
static oak_arr_u8_16 utf8__table_ulow1 = { { ((u8)( 231 )), ((u8)( 163 )), ((u8)( 131 )), ((u8)( 131 )), ((u8)( 139 )), ((u8)( 203 )), ((u8)( 203 )), ((u8)( 203 )), ((u8)( 203 )), ((u8)( 203 )), ((u8)( 203 )), ((u8)( 203 )), ((u8)( 203 )), ((u8)( 219 )), ((u8)( 203 )), ((u8)( 203 )) } };
static oak_arr_u8_16 utf8__table_uhigh2 = { { ((u8)( 1 )), ((u8)( 1 )), ((u8)( 1 )), ((u8)( 1 )), ((u8)( 1 )), ((u8)( 1 )), ((u8)( 1 )), ((u8)( 1 )), ((u8)( 230 )), ((u8)( 174 )), ((u8)( 186 )), ((u8)( 186 )), ((u8)( 1 )), ((u8)( 1 )), ((u8)( 1 )), ((u8)( 1 )) } };
static oak_arr_u8_16 utf8__incomplete_umax = { { ((u8)( 255 )), ((u8)( 255 )), ((u8)( 255 )), ((u8)( 255 )), ((u8)( 255 )), ((u8)( 255 )), ((u8)( 255 )), ((u8)( 255 )), ((u8)( 255 )), ((u8)( 255 )), ((u8)( 255 )), ((u8)( 255 )), ((u8)( 255 )), ((u8)( 239 )), ((u8)( 223 )), ((u8)( 191 )) } };

/* explicit integer conversions: total, two's complement, no
   implementation-defined C (signed results via union punning) */
static inline u8 oak_conv_u8_trunc_u16( u16 x ) {
  return (u8)( x );
}

static inline u8 oak_conv_u8_trunc_u32( u32 x ) {
  return (u8)( x );
}

static inline u8 oak_conv_u8_trunc_u64( u64 x ) {
  return (u8)( x );
}

/* forward declarations; OAK_INLINE marks private leaf helpers the C
   compiler must inline at every optimization level (the external
   definition is still emitted: C99 extern inline) */
#define OAK_INLINE extern inline __attribute__((always_inline))
void oak_ring_check( oak_span_oak_RingCursor cursor, u32 capacity );
oak_Result_u32_CopyError oak_bytes_copy_into( oak_span_u8 dst, oak_view_u8 src );
Bool oak_bytes_equal( oak_view_u8 left, oak_view_u8 right );
oak_Option_u32 oak_bytes_find( oak_view_u8 src, u8 needle );
u32 oak_bitset_storage_bytes( u32 bits );
oak_Result_Bool_BitSetError oak_bitset_contains( oak_view_u8 storage, u32 bits, u32 index );
oak_Result_Bool_BitSetError oak_bitset_set( oak_span_u8 storage, u32 bits, u32 index, Bool value );
oak_Result_u32_BitSetError oak_bitset_count( oak_view_u8 storage, u32 bits );
Bool oak_bytes_range_fits( u32 length, u32 offset, u32 width );
oak_Result_u16_EndianError oak_bytes_read_u16_le( oak_view_u8 src, u32 offset );
oak_Result_u32_EndianError oak_bytes_write_u16_le( oak_span_u8 dst, u32 offset, u16 value );
oak_Result_u16_EndianError oak_bytes_read_u16_be( oak_view_u8 src, u32 offset );
oak_Result_u32_EndianError oak_bytes_write_u16_be( oak_span_u8 dst, u32 offset, u16 value );
oak_Result_u32_EndianError oak_bytes_read_u32_le( oak_view_u8 src, u32 offset );
oak_Result_u32_EndianError oak_bytes_write_u32_le( oak_span_u8 dst, u32 offset, u32 value );
oak_Result_u32_EndianError oak_bytes_read_u32_be( oak_view_u8 src, u32 offset );
oak_Result_u32_EndianError oak_bytes_write_u32_be( oak_span_u8 dst, u32 offset, u32 value );
oak_Result_u64_EndianError oak_bytes_read_u64_le( oak_view_u8 src, u32 offset );
oak_Result_u32_EndianError oak_bytes_write_u64_le( oak_span_u8 dst, u32 offset, u64 value );
oak_Result_u64_EndianError oak_bytes_read_u64_be( oak_view_u8 src, u32 offset );
oak_Result_u32_EndianError oak_bytes_write_u64_be( oak_span_u8 dst, u32 offset, u64 value );
void oak_bytes_fill( oak_span_u8 dst, u8 value );
oak_Result_u32_ByteRangeError oak_bytes_copy_at( oak_span_u8 dst, u32 offset, oak_view_u8 src );
oak_Result_u32_ByteRangeError oak_bytes_move_within( oak_span_u8 storage, u32 dst, u32 src, u32 count );
i32 oak_bytes_compare( oak_view_u8 left, oak_view_u8 right );
void oak_buffer_check( oak_span_oak_ByteBufferCursor cursor, u32 capacity );
u32 oak_buffer_len( oak_span_oak_ByteBufferCursor cursor, u32 capacity );
u32 oak_buffer_tail_space( oak_span_oak_ByteBufferCursor cursor, u32 capacity );
oak_Result_u32_BufferError oak_buffer_append( oak_span_oak_ByteBufferCursor cursor, oak_span_u8 storage, oak_view_u8 src );
oak_Result_u32_BufferError oak_buffer_peek_into( oak_span_oak_ByteBufferCursor cursor, oak_view_u8 storage, oak_span_u8 dst );
oak_Result_u32_BufferError oak_buffer_consume( oak_span_oak_ByteBufferCursor cursor, u32 capacity, u32 count );
oak_Result_u32_BufferError oak_buffer_read_into( oak_span_oak_ByteBufferCursor cursor, oak_view_u8 storage, oak_span_u8 dst );
u32 oak_buffer_compact( oak_span_oak_ByteBufferCursor cursor, oak_span_u8 storage );
void oak_buffer_reset( oak_span_oak_ByteBufferCursor cursor );
oak_ByteBuilder oak_byte_builder( void );
oak_ByteBuilder oak_append_bytes( oak_ByteBuilder builder, oak_span_u8 storage, oak_view_u8 src );
oak_ByteBuilder oak_append_byte( oak_ByteBuilder builder, oak_span_u8 storage, u8 value );
oak_Result_u32_BufferError oak_finish_bytes( oak_ByteBuilder builder );
void oak_array_list_check( oak_span_oak_ArrayListCursor cursor, u32 capacity );
void oak_array_list_clear( oak_span_oak_ArrayListCursor cursor, u32 capacity );
void oak_intrusive_init( oak_span_oak_IntrusiveCursor cursor, u32 id );
void oak_intrusive_check( oak_span_oak_IntrusiveCursor cursor, u32 capacity );
void oak_min_heap_check( oak_span_oak_MinHeapCursor cursor, u32 capacity );
void oak_min_heap_clear( oak_span_oak_MinHeapCursor cursor, u32 capacity );
void oak_deque_check( oak_span_oak_DequeCursor cursor, u32 capacity );
u32 oak_deque_offset( u32 head, u32 capacity, u32 offset );
void oak_deque_clear( oak_span_oak_DequeCursor cursor, u32 capacity );
oak_Result_Bool_IdPoolError oak_id_pool_contains( oak_view_u8 storage, u32 limit, u32 id );
oak_Result_u32_IdPoolError oak_id_pool_reserve( oak_span_u8 storage, u32 limit, u32 id );
oak_Result_u32_IdPoolError oak_id_pool_release( oak_span_u8 storage, u32 limit, u32 id );
oak_Result_u32_IdPoolError oak_id_pool_allocate( oak_span_u8 storage, u32 limit );
oak_Result_u32_IdPoolError oak_id_pool_clear( oak_span_u8 storage, u32 limit );
OAK_INLINE u8x16 oak_utf8__special_ucases( u8x16 high1, u8x16 low1, u8x16 high2, u8x16 input, u8x16 prev1 );
u8x16 oak_utf8__check_ublock( u8x16 high1, u8x16 low1, u8x16 high2, u8x16 prev_input, u8x16 input );
u8x16 oak_utf8__check_ublocks( u8x16 high1, u8x16 low1, u8x16 high2, u8x16 prev_input, u8x16 a, u8x16 b, u8x16 c, u8x16 d );
Bool oak_utf8__valid( oak_view_u8 bytes );
oak_Utf8State oak_utf8_initial( void );
Bool oak_utf8_legal( oak_Utf8State state, oak_Utf8Step step );
oak_Utf8State oak_utf8_next( oak_Utf8State state, oak_Utf8Step step );
oak_Utf8State oak_utf8_run( oak_Utf8State state, oak_view_u8 bytes );
OAK_INLINE Bool oak_utf8_cont( u8 b );
Bool oak_utf8_second3( u8 b0, u8 b1 );
Bool oak_utf8_second4( u8 b0, u8 b1 );
Bool oak_utf8_scalar( oak_view_u8 v );
Bool oak_scalar_valid( oak_view_u8 bytes );
Bool oak_simd_valid( oak_view_u8 bytes );
u32 oak_main( void );

/* function literals lifted to plain functions: a literal is a code
   pointer, never an environment (docs/spec/10-syntax.md section 3c) */
  /* shift-DFA rows of protocol Utf8: field 6*s of rows[symbol] is 6*next(s, symbol) */
  static const u64 oak_utf8_transitions[256] = {
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL, 0x0030c30c30c30c00ULL,
    0x0030492c061b0030ULL, 0x0030492c061b0030ULL, 0x0030492c061b0030ULL, 0x0030492c061b0030ULL,
    0x0030492c061b0030ULL, 0x0030492c061b0030ULL, 0x0030492c061b0030ULL, 0x0030492c061b0030ULL,
    0x0030492c061b0030ULL, 0x0030492c061b0030ULL, 0x0030492c061b0030ULL, 0x0030492c061b0030ULL,
    0x0030492c061b0030ULL, 0x0030492c061b0030ULL, 0x0030492c061b0030ULL, 0x0030492c061b0030ULL,
    0x0030c124861b0030ULL, 0x0030c124861b0030ULL, 0x0030c124861b0030ULL, 0x0030c124861b0030ULL,
    0x0030c124861b0030ULL, 0x0030c124861b0030ULL, 0x0030c124861b0030ULL, 0x0030c124861b0030ULL,
    0x0030c124861b0030ULL, 0x0030c124861b0030ULL, 0x0030c124861b0030ULL, 0x0030c124861b0030ULL,
    0x0030c124861b0030ULL, 0x0030c124861b0030ULL, 0x0030c124861b0030ULL, 0x0030c124861b0030ULL,
    0x0030c124b0186030ULL, 0x0030c124b0186030ULL, 0x0030c124b0186030ULL, 0x0030c124b0186030ULL,
    0x0030c124b0186030ULL, 0x0030c124b0186030ULL, 0x0030c124b0186030ULL, 0x0030c124b0186030ULL,
    0x0030c124b0186030ULL, 0x0030c124b0186030ULL, 0x0030c124b0186030ULL, 0x0030c124b0186030ULL,
    0x0030c124b0186030ULL, 0x0030c124b0186030ULL, 0x0030c124b0186030ULL, 0x0030c124b0186030ULL,
    0x0030c124b0186030ULL, 0x0030c124b0186030ULL, 0x0030c124b0186030ULL, 0x0030c124b0186030ULL,
    0x0030c124b0186030ULL, 0x0030c124b0186030ULL, 0x0030c124b0186030ULL, 0x0030c124b0186030ULL,
    0x0030c124b0186030ULL, 0x0030c124b0186030ULL, 0x0030c124b0186030ULL, 0x0030c124b0186030ULL,
    0x0030c124b0186030ULL, 0x0030c124b0186030ULL, 0x0030c124b0186030ULL, 0x0030c124b0186030ULL,
    0x0030c30c30c30c30ULL, 0x0030c30c30c30c30ULL, 0x0030c30c30c30c06ULL, 0x0030c30c30c30c06ULL,
    0x0030c30c30c30c06ULL, 0x0030c30c30c30c06ULL, 0x0030c30c30c30c06ULL, 0x0030c30c30c30c06ULL,
    0x0030c30c30c30c06ULL, 0x0030c30c30c30c06ULL, 0x0030c30c30c30c06ULL, 0x0030c30c30c30c06ULL,
    0x0030c30c30c30c06ULL, 0x0030c30c30c30c06ULL, 0x0030c30c30c30c06ULL, 0x0030c30c30c30c06ULL,
    0x0030c30c30c30c06ULL, 0x0030c30c30c30c06ULL, 0x0030c30c30c30c06ULL, 0x0030c30c30c30c06ULL,
    0x0030c30c30c30c06ULL, 0x0030c30c30c30c06ULL, 0x0030c30c30c30c06ULL, 0x0030c30c30c30c06ULL,
    0x0030c30c30c30c06ULL, 0x0030c30c30c30c06ULL, 0x0030c30c30c30c06ULL, 0x0030c30c30c30c06ULL,
    0x0030c30c30c30c06ULL, 0x0030c30c30c30c06ULL, 0x0030c30c30c30c06ULL, 0x0030c30c30c30c06ULL,
    0x0030c30c30c30c0cULL, 0x0030c30c30c30c12ULL, 0x0030c30c30c30c12ULL, 0x0030c30c30c30c12ULL,
    0x0030c30c30c30c12ULL, 0x0030c30c30c30c12ULL, 0x0030c30c30c30c12ULL, 0x0030c30c30c30c12ULL,
    0x0030c30c30c30c12ULL, 0x0030c30c30c30c12ULL, 0x0030c30c30c30c12ULL, 0x0030c30c30c30c12ULL,
    0x0030c30c30c30c12ULL, 0x0030c30c30c30c18ULL, 0x0030c30c30c30c12ULL, 0x0030c30c30c30c12ULL,
    0x0030c30c30c30c1eULL, 0x0030c30c30c30c24ULL, 0x0030c30c30c30c24ULL, 0x0030c30c30c30c24ULL,
    0x0030c30c30c30c2aULL, 0x0030c30c30c30c30ULL, 0x0030c30c30c30c30ULL, 0x0030c30c30c30c30ULL,
    0x0030c30c30c30c30ULL, 0x0030c30c30c30c30ULL, 0x0030c30c30c30c30ULL, 0x0030c30c30c30c30ULL,
    0x0030c30c30c30c30ULL, 0x0030c30c30c30c30ULL, 0x0030c30c30c30c30ULL, 0x0030c30c30c30c30ULL
  };
// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:17:4-22:0
// @package: main
// @kind: function
// @identifier: ring_check
// @signature: fn ring_check(cursor: /* type */, capacity: u32) -> ()
void oak_ring_check( oak_span_oak_RingCursor cursor, u32 capacity ) {
oak_assert( ( ((u32)( cursor ).len) == ((u32)( 1 )) ), "stdlib.oak", 19 )  ;
oak_assert( ( capacity > ((u32)( 0 )) ), "stdlib.oak", 20 )  ;
oak_assert( ( oak_span_index_oak_RingCursor( cursor, (u64)( 0 ) ).head < capacity ), "stdlib.oak", 21 )  ;
    return oak_assert( ( oak_span_index_oak_RingCursor( cursor, (u64)( 0 ) ).count <= capacity ), "stdlib.oak", 22 )  ;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:55:4-67:0
// @package: main
// @kind: function
// @identifier: bytes_copy_into
// @signature: fn bytes_copy_into(dst: /* type */, src: /* type */) -> /* type */
oak_Result_u32_CopyError oak_bytes_copy_into( oak_span_u8 dst, oak_view_u8 src ) {
    u32 n   = ((u32)( src ).len)  ;
    if ( ( ((u32)( dst ).len) < n ) ) {
      return oak_Result_u32_CopyError_Err(oak_CopyError_DestinationTooSmall())    ;
    } else {
      u32 i     = 0    ;
      while ( ( i < n )     ) {
        oak_span_store_u8( dst, (u64)( i ), ( src ).base[ i ] );
        i       = oak_add_u32( i, ((u32)( 1 )) )      ;
      }
      return oak_Result_u32_CopyError_Ok(n)    ;
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:69:4-82:0
// @package: main
// @kind: function
// @identifier: bytes_equal
// @signature: fn bytes_equal(left: /* type */, right: /* type */) -> Bool
Bool oak_bytes_equal( oak_view_u8 left, oak_view_u8 right ) {
    u32 n   = ((u32)( left ).len)  ;
    if ( ( n == ((u32)( right ).len) ) ) {
      Bool same     = oak_Bool_True    ;
      u32 i     = 0    ;
      while ( ( i < n )     ) {
        same       = ( same && ( ( left ).base[ i ] == oak_view_index_u8( right, (u64)( i ) ) ) )      ;
        i       = oak_add_u32( i, ((u32)( 1 )) )      ;
      }
      return same    ;
    } else {
      return oak_Bool_False    ;
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:84:4-93:0
// @package: main
// @kind: function
// @identifier: bytes_find
// @signature: fn bytes_find(src: /* type */, needle: u8) -> /* type */
oak_Option_u32 oak_bytes_find( oak_view_u8 src, u8 needle ) {
    u32 n   = ((u32)( src ).len)  ;
    u32 index   = n  ;
    u32 i   = 0  ;
    while ( ( i < n )   ) {
      if ( ( ( index == n ) && ( ( src ).base[ i ] == needle ) )     ) {
        index       = i      ;
      }
      i     = oak_add_u32( i, ((u32)( 1 )) )    ;
    }
    if ( ( index == n ) ) {
      return oak_Option_u32_None()    ;
    } else {
      return oak_Option_u32_Some(index)    ;
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:99:4-102:0
// @package: main
// @kind: function
// @identifier: bitset_storage_bytes
// @signature: fn bitset_storage_bytes(bits: u32) -> u32
u32 oak_bitset_storage_bytes( u32 bits ) {
    u32 whole   = oak_div_u32( bits, ((u32)( 8 )) )  ;
    if ( ( oak_rem_u32( bits, ((u32)( 8 )) ) == ((u32)( 0 )) ) ) {
      return whole    ;
    } else {
      return oak_add_u32( whole, ((u32)( 1 )) )    ;
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:104:4-115:0
// @package: main
// @kind: function
// @identifier: bitset_contains
// @signature: fn bitset_contains(storage: /* type */, bits: u32, index: u32) -> /* type */
oak_Result_Bool_BitSetError oak_bitset_contains( oak_view_u8 storage, u32 bits, u32 index ) {
    if ( ( ((u32)( storage ).len) < oak_bitset_storage_bytes( bits ) ) ) {
      return oak_Result_Bool_BitSetError_Err(oak_BitSetError_StorageTooSmall())    ;
    } else {
      if ( ( index >= bits ) ) {
        return oak_Result_Bool_BitSetError_Err(oak_BitSetError_BitOutOfRange())      ;
      } else {
        u8 mask       = oak_shl_u8( ((u8)( 1 )), oak_conv_u8_trunc_u32( oak_rem_u32( index, ((u32)( 8 )) ) ) )      ;
        return oak_Result_Bool_BitSetError_Ok(( ( oak_view_index_u8( storage, (u64)( oak_div_u32( index, ((u32)( 8 )) ) ) ) & mask ) != ((u8)( 0 )) ))      ;
      }
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:118:4-136:0
// @package: main
// @kind: function
// @identifier: bitset_set
// @signature: fn bitset_set(storage: /* type */, bits: u32, index: u32, value: Bool) -> /* type */
oak_Result_Bool_BitSetError oak_bitset_set( oak_span_u8 storage, u32 bits, u32 index, Bool value ) {
    if ( ( ((u32)( storage ).len) < oak_bitset_storage_bytes( bits ) ) ) {
      return oak_Result_Bool_BitSetError_Err(oak_BitSetError_StorageTooSmall())    ;
    } else {
      if ( ( index >= bits ) ) {
        return oak_Result_Bool_BitSetError_Err(oak_BitSetError_BitOutOfRange())      ;
      } else {
        u32 byte_index       = oak_div_u32( index, ((u32)( 8 )) )      ;
        u8 mask       = oak_shl_u8( ((u8)( 1 )), oak_conv_u8_trunc_u32( oak_rem_u32( index, ((u32)( 8 )) ) ) )      ;
        Bool previous       = ( ( oak_span_index_u8( storage, (u64)( byte_index ) ) & mask ) != ((u8)( 0 )) )      ;
        if ( value       ) {
          oak_span_store_u8( storage, (u64)( byte_index ), ( oak_span_index_u8( storage, (u64)( byte_index ) ) | mask ) );
        } else {
          oak_span_store_u8( storage, (u64)( byte_index ), ( oak_span_index_u8( storage, (u64)( byte_index ) ) & ( mask ^ ((u8)( 255 )) ) ) );
        }
        return oak_Result_Bool_BitSetError_Ok(previous)      ;
      }
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:139:4-153:0
// @package: main
// @kind: function
// @identifier: bitset_count
// @signature: fn bitset_count(storage: /* type */, bits: u32) -> /* type */
oak_Result_u32_BitSetError oak_bitset_count( oak_view_u8 storage, u32 bits ) {
    if ( ( ((u32)( storage ).len) < oak_bitset_storage_bytes( bits ) ) ) {
      return oak_Result_u32_BitSetError_Err(oak_BitSetError_StorageTooSmall())    ;
    } else {
      u32 count     = 0    ;
      u32 i     = 0    ;
      while ( ( i < bits )     ) {
        u8 mask       = oak_shl_u8( ((u8)( 1 )), oak_conv_u8_trunc_u32( oak_rem_u32( i, ((u32)( 8 )) ) ) )      ;
        Bool present       = ( ( oak_view_index_u8( storage, (u64)( oak_div_u32( i, ((u32)( 8 )) ) ) ) & mask ) != ((u8)( 0 )) )      ;
        if ( present       ) {
          count         = oak_add_u32( count, ((u32)( 1 )) )        ;
        }
        i       = oak_add_u32( i, ((u32)( 1 )) )      ;
      }
      return oak_Result_u32_BitSetError_Ok(count)    ;
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:157:4-159:0
// @package: main
// @kind: function
// @identifier: bytes_range_fits
// @signature: fn bytes_range_fits(length: u32, offset: u32, width: u32) -> Bool
Bool oak_bytes_range_fits( u32 length, u32 offset, u32 width ) {
    if ( ( offset > length ) ) {
      return oak_Bool_False    ;
    } else {
      return ( width <= oak_sub_u32( length, offset ) )    ;
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:161:4-170:0
// @package: main
// @kind: function
// @identifier: bytes_read_u16_le
// @signature: fn bytes_read_u16_le(src: /* type */, offset: u32) -> /* type */
oak_Result_u16_EndianError oak_bytes_read_u16_le( oak_view_u8 src, u32 offset ) {
    if ( oak_bytes_range_fits( ((u32)( src ).len), offset, ((u32)( 2 )) ) ) {
      u16 value     = 0    ;
      value     = ( value | oak_shl_u16( ((u16)( oak_view_index_u8( src, (u64)( oak_add_u32( offset, ((u32)( 0 )) ) ) ) )), ((u16)( 0 )) ) )    ;
      value     = ( value | oak_shl_u16( ((u16)( oak_view_index_u8( src, (u64)( oak_add_u32( offset, ((u32)( 1 )) ) ) ) )), ((u16)( 8 )) ) )    ;
      return oak_Result_u16_EndianError_Ok(value)    ;
    } else {
      return oak_Result_u16_EndianError_Err(oak_EndianError_BufferTooSmall())    ;
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:172:4-180:0
// @package: main
// @kind: function
// @identifier: bytes_write_u16_le
// @signature: fn bytes_write_u16_le(dst: /* type */, offset: u32, value: u16) -> /* type */
oak_Result_u32_EndianError oak_bytes_write_u16_le( oak_span_u8 dst, u32 offset, u16 value ) {
    if ( oak_bytes_range_fits( ((u32)( dst ).len), offset, ((u32)( 2 )) ) ) {
      oak_span_store_u8( dst, (u64)( oak_add_u32( offset, ((u32)( 0 )) ) ), oak_conv_u8_trunc_u16( oak_shr_u16( value, ((u16)( 0 )) ) ) );
      oak_span_store_u8( dst, (u64)( oak_add_u32( offset, ((u32)( 1 )) ) ), oak_conv_u8_trunc_u16( oak_shr_u16( value, ((u16)( 8 )) ) ) );
      return oak_Result_u32_EndianError_Ok(((u32)( 2 )))    ;
    } else {
      return oak_Result_u32_EndianError_Err(oak_EndianError_BufferTooSmall())    ;
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:182:4-191:0
// @package: main
// @kind: function
// @identifier: bytes_read_u16_be
// @signature: fn bytes_read_u16_be(src: /* type */, offset: u32) -> /* type */
oak_Result_u16_EndianError oak_bytes_read_u16_be( oak_view_u8 src, u32 offset ) {
    if ( oak_bytes_range_fits( ((u32)( src ).len), offset, ((u32)( 2 )) ) ) {
      u16 value     = 0    ;
      value     = ( value | oak_shl_u16( ((u16)( oak_view_index_u8( src, (u64)( oak_add_u32( offset, ((u32)( 0 )) ) ) ) )), ((u16)( 8 )) ) )    ;
      value     = ( value | oak_shl_u16( ((u16)( oak_view_index_u8( src, (u64)( oak_add_u32( offset, ((u32)( 1 )) ) ) ) )), ((u16)( 0 )) ) )    ;
      return oak_Result_u16_EndianError_Ok(value)    ;
    } else {
      return oak_Result_u16_EndianError_Err(oak_EndianError_BufferTooSmall())    ;
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:193:4-201:0
// @package: main
// @kind: function
// @identifier: bytes_write_u16_be
// @signature: fn bytes_write_u16_be(dst: /* type */, offset: u32, value: u16) -> /* type */
oak_Result_u32_EndianError oak_bytes_write_u16_be( oak_span_u8 dst, u32 offset, u16 value ) {
    if ( oak_bytes_range_fits( ((u32)( dst ).len), offset, ((u32)( 2 )) ) ) {
      oak_span_store_u8( dst, (u64)( oak_add_u32( offset, ((u32)( 0 )) ) ), oak_conv_u8_trunc_u16( oak_shr_u16( value, ((u16)( 8 )) ) ) );
      oak_span_store_u8( dst, (u64)( oak_add_u32( offset, ((u32)( 1 )) ) ), oak_conv_u8_trunc_u16( oak_shr_u16( value, ((u16)( 0 )) ) ) );
      return oak_Result_u32_EndianError_Ok(((u32)( 2 )))    ;
    } else {
      return oak_Result_u32_EndianError_Err(oak_EndianError_BufferTooSmall())    ;
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:203:4-214:0
// @package: main
// @kind: function
// @identifier: bytes_read_u32_le
// @signature: fn bytes_read_u32_le(src: /* type */, offset: u32) -> /* type */
oak_Result_u32_EndianError oak_bytes_read_u32_le( oak_view_u8 src, u32 offset ) {
    if ( oak_bytes_range_fits( ((u32)( src ).len), offset, ((u32)( 4 )) ) ) {
      u32 value     = 0    ;
      value     = ( value | oak_shl_u32( ((u32)( oak_view_index_u8( src, (u64)( oak_add_u32( offset, ((u32)( 0 )) ) ) ) )), ((u32)( 0 )) ) )    ;
      value     = ( value | oak_shl_u32( ((u32)( oak_view_index_u8( src, (u64)( oak_add_u32( offset, ((u32)( 1 )) ) ) ) )), ((u32)( 8 )) ) )    ;
      value     = ( value | oak_shl_u32( ((u32)( oak_view_index_u8( src, (u64)( oak_add_u32( offset, ((u32)( 2 )) ) ) ) )), ((u32)( 16 )) ) )    ;
      value     = ( value | oak_shl_u32( ((u32)( oak_view_index_u8( src, (u64)( oak_add_u32( offset, ((u32)( 3 )) ) ) ) )), ((u32)( 24 )) ) )    ;
      return oak_Result_u32_EndianError_Ok(value)    ;
    } else {
      return oak_Result_u32_EndianError_Err(oak_EndianError_BufferTooSmall())    ;
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:216:4-226:0
// @package: main
// @kind: function
// @identifier: bytes_write_u32_le
// @signature: fn bytes_write_u32_le(dst: /* type */, offset: u32, value: u32) -> /* type */
oak_Result_u32_EndianError oak_bytes_write_u32_le( oak_span_u8 dst, u32 offset, u32 value ) {
    if ( oak_bytes_range_fits( ((u32)( dst ).len), offset, ((u32)( 4 )) ) ) {
      oak_span_store_u8( dst, (u64)( oak_add_u32( offset, ((u32)( 0 )) ) ), oak_conv_u8_trunc_u32( oak_shr_u32( value, ((u32)( 0 )) ) ) );
      oak_span_store_u8( dst, (u64)( oak_add_u32( offset, ((u32)( 1 )) ) ), oak_conv_u8_trunc_u32( oak_shr_u32( value, ((u32)( 8 )) ) ) );
      oak_span_store_u8( dst, (u64)( oak_add_u32( offset, ((u32)( 2 )) ) ), oak_conv_u8_trunc_u32( oak_shr_u32( value, ((u32)( 16 )) ) ) );
      oak_span_store_u8( dst, (u64)( oak_add_u32( offset, ((u32)( 3 )) ) ), oak_conv_u8_trunc_u32( oak_shr_u32( value, ((u32)( 24 )) ) ) );
      return oak_Result_u32_EndianError_Ok(((u32)( 4 )))    ;
    } else {
      return oak_Result_u32_EndianError_Err(oak_EndianError_BufferTooSmall())    ;
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:228:4-239:0
// @package: main
// @kind: function
// @identifier: bytes_read_u32_be
// @signature: fn bytes_read_u32_be(src: /* type */, offset: u32) -> /* type */
oak_Result_u32_EndianError oak_bytes_read_u32_be( oak_view_u8 src, u32 offset ) {
    if ( oak_bytes_range_fits( ((u32)( src ).len), offset, ((u32)( 4 )) ) ) {
      u32 value     = 0    ;
      value     = ( value | oak_shl_u32( ((u32)( oak_view_index_u8( src, (u64)( oak_add_u32( offset, ((u32)( 0 )) ) ) ) )), ((u32)( 24 )) ) )    ;
      value     = ( value | oak_shl_u32( ((u32)( oak_view_index_u8( src, (u64)( oak_add_u32( offset, ((u32)( 1 )) ) ) ) )), ((u32)( 16 )) ) )    ;
      value     = ( value | oak_shl_u32( ((u32)( oak_view_index_u8( src, (u64)( oak_add_u32( offset, ((u32)( 2 )) ) ) ) )), ((u32)( 8 )) ) )    ;
      value     = ( value | oak_shl_u32( ((u32)( oak_view_index_u8( src, (u64)( oak_add_u32( offset, ((u32)( 3 )) ) ) ) )), ((u32)( 0 )) ) )    ;
      return oak_Result_u32_EndianError_Ok(value)    ;
    } else {
      return oak_Result_u32_EndianError_Err(oak_EndianError_BufferTooSmall())    ;
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:241:4-251:0
// @package: main
// @kind: function
// @identifier: bytes_write_u32_be
// @signature: fn bytes_write_u32_be(dst: /* type */, offset: u32, value: u32) -> /* type */
oak_Result_u32_EndianError oak_bytes_write_u32_be( oak_span_u8 dst, u32 offset, u32 value ) {
    if ( oak_bytes_range_fits( ((u32)( dst ).len), offset, ((u32)( 4 )) ) ) {
      oak_span_store_u8( dst, (u64)( oak_add_u32( offset, ((u32)( 0 )) ) ), oak_conv_u8_trunc_u32( oak_shr_u32( value, ((u32)( 24 )) ) ) );
      oak_span_store_u8( dst, (u64)( oak_add_u32( offset, ((u32)( 1 )) ) ), oak_conv_u8_trunc_u32( oak_shr_u32( value, ((u32)( 16 )) ) ) );
      oak_span_store_u8( dst, (u64)( oak_add_u32( offset, ((u32)( 2 )) ) ), oak_conv_u8_trunc_u32( oak_shr_u32( value, ((u32)( 8 )) ) ) );
      oak_span_store_u8( dst, (u64)( oak_add_u32( offset, ((u32)( 3 )) ) ), oak_conv_u8_trunc_u32( oak_shr_u32( value, ((u32)( 0 )) ) ) );
      return oak_Result_u32_EndianError_Ok(((u32)( 4 )))    ;
    } else {
      return oak_Result_u32_EndianError_Err(oak_EndianError_BufferTooSmall())    ;
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:253:4-268:0
// @package: main
// @kind: function
// @identifier: bytes_read_u64_le
// @signature: fn bytes_read_u64_le(src: /* type */, offset: u32) -> /* type */
oak_Result_u64_EndianError oak_bytes_read_u64_le( oak_view_u8 src, u32 offset ) {
    if ( oak_bytes_range_fits( ((u32)( src ).len), offset, ((u32)( 8 )) ) ) {
      u64 value     = 0    ;
      value     = ( value | oak_shl_u64( ((u64)( oak_view_index_u8( src, (u64)( oak_add_u32( offset, ((u32)( 0 )) ) ) ) )), ((u64)( 0 )) ) )    ;
      value     = ( value | oak_shl_u64( ((u64)( oak_view_index_u8( src, (u64)( oak_add_u32( offset, ((u32)( 1 )) ) ) ) )), ((u64)( 8 )) ) )    ;
      value     = ( value | oak_shl_u64( ((u64)( oak_view_index_u8( src, (u64)( oak_add_u32( offset, ((u32)( 2 )) ) ) ) )), ((u64)( 16 )) ) )    ;
      value     = ( value | oak_shl_u64( ((u64)( oak_view_index_u8( src, (u64)( oak_add_u32( offset, ((u32)( 3 )) ) ) ) )), ((u64)( 24 )) ) )    ;
      value     = ( value | oak_shl_u64( ((u64)( oak_view_index_u8( src, (u64)( oak_add_u32( offset, ((u32)( 4 )) ) ) ) )), ((u64)( 32 )) ) )    ;
      value     = ( value | oak_shl_u64( ((u64)( oak_view_index_u8( src, (u64)( oak_add_u32( offset, ((u32)( 5 )) ) ) ) )), ((u64)( 40 )) ) )    ;
      value     = ( value | oak_shl_u64( ((u64)( oak_view_index_u8( src, (u64)( oak_add_u32( offset, ((u32)( 6 )) ) ) ) )), ((u64)( 48 )) ) )    ;
      value     = ( value | oak_shl_u64( ((u64)( oak_view_index_u8( src, (u64)( oak_add_u32( offset, ((u32)( 7 )) ) ) ) )), ((u64)( 56 )) ) )    ;
      return oak_Result_u64_EndianError_Ok(value)    ;
    } else {
      return oak_Result_u64_EndianError_Err(oak_EndianError_BufferTooSmall())    ;
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:270:4-284:0
// @package: main
// @kind: function
// @identifier: bytes_write_u64_le
// @signature: fn bytes_write_u64_le(dst: /* type */, offset: u32, value: u64) -> /* type */
oak_Result_u32_EndianError oak_bytes_write_u64_le( oak_span_u8 dst, u32 offset, u64 value ) {
    if ( oak_bytes_range_fits( ((u32)( dst ).len), offset, ((u32)( 8 )) ) ) {
      oak_span_store_u8( dst, (u64)( oak_add_u32( offset, ((u32)( 0 )) ) ), oak_conv_u8_trunc_u64( oak_shr_u64( value, ((u64)( 0 )) ) ) );
      oak_span_store_u8( dst, (u64)( oak_add_u32( offset, ((u32)( 1 )) ) ), oak_conv_u8_trunc_u64( oak_shr_u64( value, ((u64)( 8 )) ) ) );
      oak_span_store_u8( dst, (u64)( oak_add_u32( offset, ((u32)( 2 )) ) ), oak_conv_u8_trunc_u64( oak_shr_u64( value, ((u64)( 16 )) ) ) );
      oak_span_store_u8( dst, (u64)( oak_add_u32( offset, ((u32)( 3 )) ) ), oak_conv_u8_trunc_u64( oak_shr_u64( value, ((u64)( 24 )) ) ) );
      oak_span_store_u8( dst, (u64)( oak_add_u32( offset, ((u32)( 4 )) ) ), oak_conv_u8_trunc_u64( oak_shr_u64( value, ((u64)( 32 )) ) ) );
      oak_span_store_u8( dst, (u64)( oak_add_u32( offset, ((u32)( 5 )) ) ), oak_conv_u8_trunc_u64( oak_shr_u64( value, ((u64)( 40 )) ) ) );
      oak_span_store_u8( dst, (u64)( oak_add_u32( offset, ((u32)( 6 )) ) ), oak_conv_u8_trunc_u64( oak_shr_u64( value, ((u64)( 48 )) ) ) );
      oak_span_store_u8( dst, (u64)( oak_add_u32( offset, ((u32)( 7 )) ) ), oak_conv_u8_trunc_u64( oak_shr_u64( value, ((u64)( 56 )) ) ) );
      return oak_Result_u32_EndianError_Ok(((u32)( 8 )))    ;
    } else {
      return oak_Result_u32_EndianError_Err(oak_EndianError_BufferTooSmall())    ;
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:286:4-301:0
// @package: main
// @kind: function
// @identifier: bytes_read_u64_be
// @signature: fn bytes_read_u64_be(src: /* type */, offset: u32) -> /* type */
oak_Result_u64_EndianError oak_bytes_read_u64_be( oak_view_u8 src, u32 offset ) {
    if ( oak_bytes_range_fits( ((u32)( src ).len), offset, ((u32)( 8 )) ) ) {
      u64 value     = 0    ;
      value     = ( value | oak_shl_u64( ((u64)( oak_view_index_u8( src, (u64)( oak_add_u32( offset, ((u32)( 0 )) ) ) ) )), ((u64)( 56 )) ) )    ;
      value     = ( value | oak_shl_u64( ((u64)( oak_view_index_u8( src, (u64)( oak_add_u32( offset, ((u32)( 1 )) ) ) ) )), ((u64)( 48 )) ) )    ;
      value     = ( value | oak_shl_u64( ((u64)( oak_view_index_u8( src, (u64)( oak_add_u32( offset, ((u32)( 2 )) ) ) ) )), ((u64)( 40 )) ) )    ;
      value     = ( value | oak_shl_u64( ((u64)( oak_view_index_u8( src, (u64)( oak_add_u32( offset, ((u32)( 3 )) ) ) ) )), ((u64)( 32 )) ) )    ;
      value     = ( value | oak_shl_u64( ((u64)( oak_view_index_u8( src, (u64)( oak_add_u32( offset, ((u32)( 4 )) ) ) ) )), ((u64)( 24 )) ) )    ;
      value     = ( value | oak_shl_u64( ((u64)( oak_view_index_u8( src, (u64)( oak_add_u32( offset, ((u32)( 5 )) ) ) ) )), ((u64)( 16 )) ) )    ;
      value     = ( value | oak_shl_u64( ((u64)( oak_view_index_u8( src, (u64)( oak_add_u32( offset, ((u32)( 6 )) ) ) ) )), ((u64)( 8 )) ) )    ;
      value     = ( value | oak_shl_u64( ((u64)( oak_view_index_u8( src, (u64)( oak_add_u32( offset, ((u32)( 7 )) ) ) ) )), ((u64)( 0 )) ) )    ;
      return oak_Result_u64_EndianError_Ok(value)    ;
    } else {
      return oak_Result_u64_EndianError_Err(oak_EndianError_BufferTooSmall())    ;
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:303:4-317:0
// @package: main
// @kind: function
// @identifier: bytes_write_u64_be
// @signature: fn bytes_write_u64_be(dst: /* type */, offset: u32, value: u64) -> /* type */
oak_Result_u32_EndianError oak_bytes_write_u64_be( oak_span_u8 dst, u32 offset, u64 value ) {
    if ( oak_bytes_range_fits( ((u32)( dst ).len), offset, ((u32)( 8 )) ) ) {
      oak_span_store_u8( dst, (u64)( oak_add_u32( offset, ((u32)( 0 )) ) ), oak_conv_u8_trunc_u64( oak_shr_u64( value, ((u64)( 56 )) ) ) );
      oak_span_store_u8( dst, (u64)( oak_add_u32( offset, ((u32)( 1 )) ) ), oak_conv_u8_trunc_u64( oak_shr_u64( value, ((u64)( 48 )) ) ) );
      oak_span_store_u8( dst, (u64)( oak_add_u32( offset, ((u32)( 2 )) ) ), oak_conv_u8_trunc_u64( oak_shr_u64( value, ((u64)( 40 )) ) ) );
      oak_span_store_u8( dst, (u64)( oak_add_u32( offset, ((u32)( 3 )) ) ), oak_conv_u8_trunc_u64( oak_shr_u64( value, ((u64)( 32 )) ) ) );
      oak_span_store_u8( dst, (u64)( oak_add_u32( offset, ((u32)( 4 )) ) ), oak_conv_u8_trunc_u64( oak_shr_u64( value, ((u64)( 24 )) ) ) );
      oak_span_store_u8( dst, (u64)( oak_add_u32( offset, ((u32)( 5 )) ) ), oak_conv_u8_trunc_u64( oak_shr_u64( value, ((u64)( 16 )) ) ) );
      oak_span_store_u8( dst, (u64)( oak_add_u32( offset, ((u32)( 6 )) ) ), oak_conv_u8_trunc_u64( oak_shr_u64( value, ((u64)( 8 )) ) ) );
      oak_span_store_u8( dst, (u64)( oak_add_u32( offset, ((u32)( 7 )) ) ), oak_conv_u8_trunc_u64( oak_shr_u64( value, ((u64)( 0 )) ) ) );
      return oak_Result_u32_EndianError_Ok(((u32)( 8 )))    ;
    } else {
      return oak_Result_u32_EndianError_Err(oak_EndianError_BufferTooSmall())    ;
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:321:4-327:0
// @package: main
// @kind: function
// @identifier: bytes_fill
// @signature: fn bytes_fill(dst: /* type */, value: u8) -> ()
void oak_bytes_fill( oak_span_u8 dst, u8 value ) {
    u32 i   = 0  ;
    while ( ( i < ((u32)( dst ).len) )   ) {
      ( dst ).base[ i ] = value;
      i     = oak_add_u32( i, ((u32)( 1 )) )    ;
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:329:4-339:0
// @package: main
// @kind: function
// @identifier: bytes_copy_at
// @signature: fn bytes_copy_at(dst: /* type */, offset: u32, src: /* type */) -> /* type */
oak_Result_u32_ByteRangeError oak_bytes_copy_at( oak_span_u8 dst, u32 offset, oak_view_u8 src ) {
    u32 n   = ((u32)( src ).len)  ;
    if ( oak_bytes_range_fits( ((u32)( dst ).len), offset, n ) ) {
      u32 i     = 0    ;
      while ( ( i < n )     ) {
        oak_span_store_u8( dst, (u64)( oak_add_u32( offset, i ) ), ( src ).base[ i ] );
        i       = oak_add_u32( i, ((u32)( 1 )) )      ;
      }
      return oak_Result_u32_ByteRangeError_Ok(n)    ;
    } else {
      return oak_Result_u32_ByteRangeError_Err(oak_ByteRangeError_OutOfBounds())    ;
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:342:4-360:0
// @package: main
// @kind: function
// @identifier: bytes_move_within
// @signature: fn bytes_move_within(storage: /* type */, dst: u32, src: u32, count: u32) -> /* type */
oak_Result_u32_ByteRangeError oak_bytes_move_within( oak_span_u8 storage, u32 dst, u32 src, u32 count ) {
    Bool valid   = ( oak_bytes_range_fits( ((u32)( storage ).len), dst, count ) && oak_bytes_range_fits( ((u32)( storage ).len), src, count ) )  ;
    if ( valid ) {
      if ( ( dst > src )     ) {
        u32 remaining       = count      ;
        while ( ( remaining > ((u32)( 0 )) )       ) {
          remaining         = oak_sub_u32( remaining, ((u32)( 1 )) )        ;
          oak_span_store_u8( storage, (u64)( oak_add_u32( dst, remaining ) ), oak_span_index_u8( storage, (u64)( oak_add_u32( src, remaining ) ) ) );
        }
      } else {
        u32 i       = 0      ;
        while ( ( i < count )       ) {
          oak_span_store_u8( storage, (u64)( oak_add_u32( dst, i ) ), oak_span_index_u8( storage, (u64)( oak_add_u32( src, i ) ) ) );
          i         = oak_add_u32( i, ((u32)( 1 )) )        ;
        }
      }
      return oak_Result_u32_ByteRangeError_Ok(count)    ;
    } else {
      return oak_Result_u32_ByteRangeError_Err(oak_ByteRangeError_OutOfBounds())    ;
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:363:4-377:0
// @package: main
// @kind: function
// @identifier: bytes_compare
// @signature: fn bytes_compare(left: /* type */, right: /* type */) -> i32
i32 oak_bytes_compare( oak_view_u8 left, oak_view_u8 right ) {
    u32 limit   = ( ( ( ((u32)( left ).len) < ((u32)( right ).len) ) ) ? ((u32)( left ).len) : ((u32)( right ).len) )  ;
    i32 order   = 0  ;
    u32 i   = 0  ;
    while ( ( ( i < limit ) && ( order == 0 ) )   ) {
      if ( ( oak_view_index_u8( left, (u64)( i ) ) < oak_view_index_u8( right, (u64)( i ) ) )     ) {
        order       = -( 1 )      ;
      }
      if ( ( oak_view_index_u8( left, (u64)( i ) ) > oak_view_index_u8( right, (u64)( i ) ) )     ) {
        order       = 1      ;
      }
      i     = oak_add_u32( i, ((u32)( 1 )) )    ;
    }
    if ( ( order == 0 )   ) {
      if ( ( ((u32)( left ).len) < ((u32)( right ).len) )     ) {
        order       = -( 1 )      ;
      }
      if ( ( ((u32)( left ).len) > ((u32)( right ).len) ) ) {
        order       = 1      ;
      } else {
      }
    }
    return order  ;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:386:4-390:0
// @package: main
// @kind: function
// @identifier: buffer_check
// @signature: fn buffer_check(cursor: /* type */, capacity: u32) -> ()
void oak_buffer_check( oak_span_oak_ByteBufferCursor cursor, u32 capacity ) {
oak_assert( ( ((u32)( cursor ).len) == ((u32)( 1 )) ), "stdlib.oak", 388 )  ;
oak_assert( ( oak_span_index_oak_ByteBufferCursor( cursor, (u64)( 0 ) ).start <= oak_span_index_oak_ByteBufferCursor( cursor, (u64)( 0 ) ).end ), "stdlib.oak", 389 )  ;
    return oak_assert( ( oak_span_index_oak_ByteBufferCursor( cursor, (u64)( 0 ) ).end <= capacity ), "stdlib.oak", 390 )  ;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:392:4-395:0
// @package: main
// @kind: function
// @identifier: buffer_len
// @signature: fn buffer_len(cursor: /* type */, capacity: u32) -> u32
u32 oak_buffer_len( oak_span_oak_ByteBufferCursor cursor, u32 capacity ) {
oak_buffer_check( cursor, capacity )  ;
    return oak_sub_u32( oak_span_index_oak_ByteBufferCursor( cursor, (u64)( 0 ) ).end, oak_span_index_oak_ByteBufferCursor( cursor, (u64)( 0 ) ).start )  ;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:397:4-400:0
// @package: main
// @kind: function
// @identifier: buffer_tail_space
// @signature: fn buffer_tail_space(cursor: /* type */, capacity: u32) -> u32
u32 oak_buffer_tail_space( oak_span_oak_ByteBufferCursor cursor, u32 capacity ) {
oak_buffer_check( cursor, capacity )  ;
    return oak_sub_u32( capacity, oak_span_index_oak_ByteBufferCursor( cursor, (u64)( 0 ) ).end )  ;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:403:4-415:0
// @package: main
// @kind: function
// @identifier: buffer_append
// @signature: fn buffer_append(cursor: /* type */, storage: /* type */, src: /* type */) -> /* type */
oak_Result_u32_BufferError oak_buffer_append( oak_span_oak_ByteBufferCursor cursor, oak_span_u8 storage, oak_view_u8 src ) {
oak_buffer_check( cursor, ((u32)( storage ).len) )  ;
    u32 n   = ((u32)( src ).len)  ;
    if ( ( n <= oak_sub_u32( ((u32)( storage ).len), oak_span_index_oak_ByteBufferCursor( cursor, (u64)( 0 ) ).end ) ) ) {
      u32 i     = 0    ;
      while ( ( i < n )     ) {
        oak_span_store_u8( storage, (u64)( oak_add_u32( oak_span_index_oak_ByteBufferCursor( cursor, (u64)( 0 ) ).end, i ) ), ( src ).base[ i ] );
        i       = oak_add_u32( i, ((u32)( 1 )) )      ;
      }
      cursor.base[ oak_lv_idx( (u64)( 0 ), (u64)(cursor.len) ) ].end = oak_add_u32( oak_span_index_oak_ByteBufferCursor( cursor, (u64)( 0 ) ).end, n );
      return oak_Result_u32_BufferError_Ok(n)    ;
    } else {
      return oak_Result_u32_BufferError_Err(oak_BufferError_Full())    ;
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:418:4-429:0
// @package: main
// @kind: function
// @identifier: buffer_peek_into
// @signature: fn buffer_peek_into(cursor: /* type */, storage: /* type */, dst: /* type */) -> /* type */
oak_Result_u32_BufferError oak_buffer_peek_into( oak_span_oak_ByteBufferCursor cursor, oak_view_u8 storage, oak_span_u8 dst ) {
oak_buffer_check( cursor, ((u32)( storage ).len) )  ;
    u32 n   = ((u32)( dst ).len)  ;
    if ( ( n <= oak_sub_u32( oak_span_index_oak_ByteBufferCursor( cursor, (u64)( 0 ) ).end, oak_span_index_oak_ByteBufferCursor( cursor, (u64)( 0 ) ).start ) ) ) {
      u32 i     = 0    ;
      while ( ( i < n )     ) {
        ( dst ).base[ i ] = oak_view_index_u8( storage, (u64)( oak_add_u32( oak_span_index_oak_ByteBufferCursor( cursor, (u64)( 0 ) ).start, i ) ) );
        i       = oak_add_u32( i, ((u32)( 1 )) )      ;
      }
      return oak_Result_u32_BufferError_Ok(n)    ;
    } else {
      return oak_Result_u32_BufferError_Err(oak_BufferError_InsufficientData())    ;
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:432:4-442:0
// @package: main
// @kind: function
// @identifier: buffer_consume
// @signature: fn buffer_consume(cursor: /* type */, capacity: u32, count: u32) -> /* type */
oak_Result_u32_BufferError oak_buffer_consume( oak_span_oak_ByteBufferCursor cursor, u32 capacity, u32 count ) {
oak_buffer_check( cursor, capacity )  ;
    if ( ( count <= oak_sub_u32( oak_span_index_oak_ByteBufferCursor( cursor, (u64)( 0 ) ).end, oak_span_index_oak_ByteBufferCursor( cursor, (u64)( 0 ) ).start ) ) ) {
      cursor.base[ oak_lv_idx( (u64)( 0 ), (u64)(cursor.len) ) ].start = oak_add_u32( oak_span_index_oak_ByteBufferCursor( cursor, (u64)( 0 ) ).start, count );
      if ( ( oak_span_index_oak_ByteBufferCursor( cursor, (u64)( 0 ) ).start == oak_span_index_oak_ByteBufferCursor( cursor, (u64)( 0 ) ).end )     ) {
        cursor.base[ oak_lv_idx( (u64)( 0 ), (u64)(cursor.len) ) ].start = ((u32)( 0 ));
        cursor.base[ oak_lv_idx( (u64)( 0 ), (u64)(cursor.len) ) ].end = ((u32)( 0 ));
      }
      return oak_Result_u32_BufferError_Ok(count)    ;
    } else {
      return oak_Result_u32_BufferError_Err(oak_BufferError_InsufficientData())    ;
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:444:4-449:0
// @package: main
// @kind: function
// @identifier: buffer_read_into
// @signature: fn buffer_read_into(cursor: /* type */, storage: /* type */, dst: /* type */) -> /* type */
oak_Result_u32_BufferError oak_buffer_read_into( oak_span_oak_ByteBufferCursor cursor, oak_view_u8 storage, oak_span_u8 dst ) {
    oak_Result_u32_BufferError copied   = oak_buffer_peek_into( cursor, storage, dst )  ;
    if ( copied.tag == oak_Result_u32_BufferError_tag_Ok ) {
      u32 count = copied.payload.Ok;
    return oak_buffer_consume( cursor, ((u32)( storage ).len), count )  ;
    }
    if ( copied.tag == oak_Result_u32_BufferError_tag_Err ) {
      oak_BufferError reason = copied.payload.Err;
    return oak_Result_u32_BufferError_Err(reason)  ;
    }
    __builtin_trap(); /* unreachable: exhaustive match */
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:452:4-465:0
// @package: main
// @kind: function
// @identifier: buffer_compact
// @signature: fn buffer_compact(cursor: /* type */, storage: /* type */) -> u32
u32 oak_buffer_compact( oak_span_oak_ByteBufferCursor cursor, oak_span_u8 storage ) {
oak_buffer_check( cursor, ((u32)( storage ).len) )  ;
    u32 n   = oak_sub_u32( oak_span_index_oak_ByteBufferCursor( cursor, (u64)( 0 ) ).end, oak_span_index_oak_ByteBufferCursor( cursor, (u64)( 0 ) ).start )  ;
    if ( ( oak_span_index_oak_ByteBufferCursor( cursor, (u64)( 0 ) ).start > ((u32)( 0 )) )   ) {
      u32 i     = 0    ;
      while ( ( i < n )     ) {
        oak_span_store_u8( storage, (u64)( i ), oak_span_index_u8( storage, (u64)( oak_add_u32( oak_span_index_oak_ByteBufferCursor( cursor, (u64)( 0 ) ).start, i ) ) ) );
        i       = oak_add_u32( i, ((u32)( 1 )) )      ;
      }
    }
    cursor.base[ oak_lv_idx( (u64)( 0 ), (u64)(cursor.len) ) ].start = ((u32)( 0 ));
    cursor.base[ oak_lv_idx( (u64)( 0 ), (u64)(cursor.len) ) ].end = n;
    return n  ;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:468:4-472:0
// @package: main
// @kind: function
// @identifier: buffer_reset
// @signature: fn buffer_reset(cursor: /* type */) -> ()
void oak_buffer_reset( oak_span_oak_ByteBufferCursor cursor ) {
oak_assert( ( ((u32)( cursor ).len) == ((u32)( 1 )) ), "stdlib.oak", 470 )  ;
    cursor.base[ oak_lv_idx( (u64)( 0 ), (u64)(cursor.len) ) ].start = ((u32)( 0 ));
    cursor.base[ oak_lv_idx( (u64)( 0 ), (u64)(cursor.len) ) ].end = ((u32)( 0 ));
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:481:4-484:0
// @package: main
// @kind: function
// @identifier: byte_builder
// @signature: fn byte_builder() -> ByteBuilder
oak_ByteBuilder oak_byte_builder(  ) {
    oak_ByteBuilder initial   = ((oak_ByteBuilder){ .length = ((u32)( 0 )), .failed = oak_Bool_False })  ;
    return initial  ;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:486:4-501:0
// @package: main
// @kind: function
// @identifier: append_bytes
// @signature: fn append_bytes(builder: ByteBuilder, storage: /* type */, src: /* type */) -> ByteBuilder
oak_ByteBuilder oak_append_bytes( oak_ByteBuilder builder, oak_span_u8 storage, oak_view_u8 src ) {
    oak_ByteBuilder next   = builder  ;
    if ( builder.failed ) {
      return next    ;
    } else {
oak_assert( ( builder.length <= ((u32)( storage ).len) ), "stdlib.oak", 490 )    ;
      u32 n     = ((u32)( src ).len)    ;
      if ( ( n <= oak_sub_u32( ((u32)( storage ).len), builder.length ) )     ) {
        u32 i       = 0      ;
        while ( ( i < n )       ) {
          oak_span_store_u8( storage, (u64)( oak_add_u32( builder.length, i ) ), ( src ).base[ i ] );
          i         = oak_add_u32( i, ((u32)( 1 )) )        ;
        }
        next.length = oak_add_u32( builder.length, n );
      } else {
        next.failed = oak_Bool_True;
      }
      return next    ;
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:503:4-513:0
// @package: main
// @kind: function
// @identifier: append_byte
// @signature: fn append_byte(builder: ByteBuilder, storage: /* type */, value: u8) -> ByteBuilder
oak_ByteBuilder oak_append_byte( oak_ByteBuilder builder, oak_span_u8 storage, u8 value ) {
    oak_ByteBuilder next   = builder  ;
    if ( builder.failed ) {
      return next    ;
    } else {
oak_assert( ( builder.length <= ((u32)( storage ).len) ), "stdlib.oak", 507 )    ;
      if ( ( builder.length < ((u32)( storage ).len) )     ) {
        ( storage ).base[ builder.length ] = value;
        next.length = oak_add_u32( builder.length, ((u32)( 1 )) );
      } else {
        next.failed = oak_Bool_True;
      }
      return next    ;
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:515:4-517:0
// @package: main
// @kind: function
// @identifier: finish_bytes
// @signature: fn finish_bytes(builder: ByteBuilder) -> /* type */
oak_Result_u32_BufferError oak_finish_bytes( oak_ByteBuilder builder ) {
    if ( builder.failed ) {
      return oak_Result_u32_BufferError_Err(oak_BufferError_Full())    ;
    } else {
      return oak_Result_u32_BufferError_Ok(builder.length)    ;
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:523:4-526:0
// @package: main
// @kind: function
// @identifier: array_list_check
// @signature: fn array_list_check(cursor: /* type */, capacity: u32) -> ()
void oak_array_list_check( oak_span_oak_ArrayListCursor cursor, u32 capacity ) {
oak_assert( ( ((u32)( cursor ).len) == ((u32)( 1 )) ), "stdlib.oak", 525 )  ;
    return oak_assert( ( oak_span_index_oak_ArrayListCursor( cursor, (u64)( 0 ) ).length <= capacity ), "stdlib.oak", 526 )  ;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:602:4-605:0
// @package: main
// @kind: function
// @identifier: array_list_clear
// @signature: fn array_list_clear(cursor: /* type */, capacity: u32) -> ()
void oak_array_list_clear( oak_span_oak_ArrayListCursor cursor, u32 capacity ) {
oak_array_list_check( cursor, capacity )  ;
    cursor.base[ oak_lv_idx( (u64)( 0 ), (u64)(cursor.len) ) ].length = ((u32)( 0 ));
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:613:4-618:0
// @package: main
// @kind: function
// @identifier: intrusive_init
// @signature: fn intrusive_init(cursor: /* type */, id: u32) -> ()
void oak_intrusive_init( oak_span_oak_IntrusiveCursor cursor, u32 id ) {
oak_assert( ( ((u32)( cursor ).len) == ((u32)( 1 )) ), "stdlib.oak", 615 )  ;
oak_assert( ( id != ((u32)( 0 )) ), "stdlib.oak", 616 )  ;
oak_assert( ( ( ( oak_span_index_oak_IntrusiveCursor( cursor, (u64)( 0 ) ).count == ((u32)( 0 )) ) && ( oak_span_index_oak_IntrusiveCursor( cursor, (u64)( 0 ) ).head == ((u32)( 0 )) ) ) && ( oak_span_index_oak_IntrusiveCursor( cursor, (u64)( 0 ) ).tail == ((u32)( 0 )) ) ), "stdlib.oak", 617 )  ;
    cursor.base[ oak_lv_idx( (u64)( 0 ), (u64)(cursor.len) ) ].id = id;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:620:4-631:0
// @package: main
// @kind: function
// @identifier: intrusive_check
// @signature: fn intrusive_check(cursor: /* type */, capacity: u32) -> ()
void oak_intrusive_check( oak_span_oak_IntrusiveCursor cursor, u32 capacity ) {
oak_assert( ( ((u32)( cursor ).len) == ((u32)( 1 )) ), "stdlib.oak", 622 )  ;
oak_assert( ( oak_span_index_oak_IntrusiveCursor( cursor, (u64)( 0 ) ).id != ((u32)( 0 )) ), "stdlib.oak", 623 )  ;
oak_assert( ( oak_span_index_oak_IntrusiveCursor( cursor, (u64)( 0 ) ).count <= capacity ), "stdlib.oak", 624 )  ;
    if ( ( oak_span_index_oak_IntrusiveCursor( cursor, (u64)( 0 ) ).count == ((u32)( 0 )) ) ) {
      return oak_assert( ( ( oak_span_index_oak_IntrusiveCursor( cursor, (u64)( 0 ) ).head == ((u32)( 0 )) ) && ( oak_span_index_oak_IntrusiveCursor( cursor, (u64)( 0 ) ).tail == ((u32)( 0 )) ) ), "stdlib.oak", 626 )    ;
    } else {
oak_assert( ( ( oak_span_index_oak_IntrusiveCursor( cursor, (u64)( 0 ) ).head > ((u32)( 0 )) ) && ( oak_span_index_oak_IntrusiveCursor( cursor, (u64)( 0 ) ).head <= capacity ) ), "stdlib.oak", 628 )    ;
oak_assert( ( ( oak_span_index_oak_IntrusiveCursor( cursor, (u64)( 0 ) ).tail > ((u32)( 0 )) ) && ( oak_span_index_oak_IntrusiveCursor( cursor, (u64)( 0 ) ).tail <= capacity ) ), "stdlib.oak", 629 )    ;
      if ( ( oak_span_index_oak_IntrusiveCursor( cursor, (u64)( 0 ) ).count == ((u32)( 1 )) ) ) {
        return oak_assert( ( oak_span_index_oak_IntrusiveCursor( cursor, (u64)( 0 ) ).head == oak_span_index_oak_IntrusiveCursor( cursor, (u64)( 0 ) ).tail ), "stdlib.oak", 630 )      ;
      } else {
      }
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:1110:4-1113:0
// @package: main
// @kind: function
// @identifier: min_heap_check
// @signature: fn min_heap_check(cursor: /* type */, capacity: u32) -> ()
void oak_min_heap_check( oak_span_oak_MinHeapCursor cursor, u32 capacity ) {
oak_assert( ( ((u32)( cursor ).len) == ((u32)( 1 )) ), "stdlib.oak", 1112 )  ;
    return oak_assert( ( oak_span_index_oak_MinHeapCursor( cursor, (u64)( 0 ) ).length <= capacity ), "stdlib.oak", 1113 )  ;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:1208:4-1211:0
// @package: main
// @kind: function
// @identifier: min_heap_clear
// @signature: fn min_heap_clear(cursor: /* type */, capacity: u32) -> ()
void oak_min_heap_clear( oak_span_oak_MinHeapCursor cursor, u32 capacity ) {
oak_min_heap_check( cursor, capacity )  ;
    cursor.base[ oak_lv_idx( (u64)( 0 ), (u64)(cursor.len) ) ].length = ((u32)( 0 ));
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:1227:4-1233:0
// @package: main
// @kind: function
// @identifier: deque_check
// @signature: fn deque_check(cursor: /* type */, capacity: u32) -> ()
void oak_deque_check( oak_span_oak_DequeCursor cursor, u32 capacity ) {
oak_assert( ( ((u32)( cursor ).len) == ((u32)( 1 )) ), "stdlib.oak", 1229 )  ;
oak_assert( ( oak_span_index_oak_DequeCursor( cursor, (u64)( 0 ) ).count <= capacity ), "stdlib.oak", 1230 )  ;
    if ( ( capacity == ((u32)( 0 )) ) ) {
      return oak_assert( ( oak_span_index_oak_DequeCursor( cursor, (u64)( 0 ) ).head == ((u32)( 0 )) ), "stdlib.oak", 1231 )    ;
    } else {
      return oak_assert( ( oak_span_index_oak_DequeCursor( cursor, (u64)( 0 ) ).head < capacity ), "stdlib.oak", 1232 )    ;
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:1236:4-1240:0
// @package: main
// @kind: function
// @identifier: deque_offset
// @signature: fn deque_offset(head: u32, capacity: u32, offset: u32) -> u32
u32 oak_deque_offset( u32 head, u32 capacity, u32 offset ) {
oak_assert( ( ( head < capacity ) && ( offset < capacity ) ), "stdlib.oak", 1238 )  ;
    u32 remaining   = oak_sub_u32( capacity, head )  ;
    if ( ( offset < remaining ) ) {
      return oak_add_u32( head, offset )    ;
    } else {
      return oak_sub_u32( offset, remaining )    ;
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:1316:4-1320:0
// @package: main
// @kind: function
// @identifier: deque_clear
// @signature: fn deque_clear(cursor: /* type */, capacity: u32) -> ()
void oak_deque_clear( oak_span_oak_DequeCursor cursor, u32 capacity ) {
oak_deque_check( cursor, capacity )  ;
    cursor.base[ oak_lv_idx( (u64)( 0 ), (u64)(cursor.len) ) ].head = ((u32)( 0 ));
    cursor.base[ oak_lv_idx( (u64)( 0 ), (u64)(cursor.len) ) ].count = ((u32)( 0 ));
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:1326:4-1333:0
// @package: main
// @kind: function
// @identifier: id_pool_contains
// @signature: fn id_pool_contains(storage: /* type */, limit: u32, id: u32) -> /* type */
oak_Result_Bool_IdPoolError oak_id_pool_contains( oak_view_u8 storage, u32 limit, u32 id ) {
    if ( ( ((u32)( storage ).len) < oak_bitset_storage_bytes( limit ) ) ) {
      return oak_Result_Bool_IdPoolError_Err(oak_IdPoolError_StorageTooSmall())    ;
    } else {
      if ( ( id >= limit ) ) {
        return oak_Result_Bool_IdPoolError_Err(oak_IdPoolError_OutOfBounds())      ;
      } else {
        u8 mask       = oak_shl_u8( ((u8)( 1 )), oak_conv_u8_trunc_u32( oak_rem_u32( id, ((u32)( 8 )) ) ) )      ;
        return oak_Result_Bool_IdPoolError_Ok(( ( oak_view_index_u8( storage, (u64)( oak_div_u32( id, ((u32)( 8 )) ) ) ) & mask ) != ((u8)( 0 )) ))      ;
      }
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:1335:4-1347:0
// @package: main
// @kind: function
// @identifier: id_pool_reserve
// @signature: fn id_pool_reserve(storage: /* type */, limit: u32, id: u32) -> /* type */
oak_Result_u32_IdPoolError oak_id_pool_reserve( oak_span_u8 storage, u32 limit, u32 id ) {
    if ( ( ((u32)( storage ).len) < oak_bitset_storage_bytes( limit ) ) ) {
      return oak_Result_u32_IdPoolError_Err(oak_IdPoolError_StorageTooSmall())    ;
    } else {
      if ( ( id >= limit ) ) {
        return oak_Result_u32_IdPoolError_Err(oak_IdPoolError_OutOfBounds())      ;
      } else {
        u32 index       = oak_div_u32( id, ((u32)( 8 )) )      ;
        u8 mask       = oak_shl_u8( ((u8)( 1 )), oak_conv_u8_trunc_u32( oak_rem_u32( id, ((u32)( 8 )) ) ) )      ;
        Bool occupied       = ( ( oak_span_index_u8( storage, (u64)( index ) ) & mask ) != ((u8)( 0 )) )      ;
        if ( occupied ) {
          return oak_Result_u32_IdPoolError_Err(oak_IdPoolError_AlreadyAllocated())        ;
        } else {
          oak_span_store_u8( storage, (u64)( index ), ( oak_span_index_u8( storage, (u64)( index ) ) | mask ) );
          return oak_Result_u32_IdPoolError_Ok(id)        ;
        }
      }
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:1349:4-1361:0
// @package: main
// @kind: function
// @identifier: id_pool_release
// @signature: fn id_pool_release(storage: /* type */, limit: u32, id: u32) -> /* type */
oak_Result_u32_IdPoolError oak_id_pool_release( oak_span_u8 storage, u32 limit, u32 id ) {
    if ( ( ((u32)( storage ).len) < oak_bitset_storage_bytes( limit ) ) ) {
      return oak_Result_u32_IdPoolError_Err(oak_IdPoolError_StorageTooSmall())    ;
    } else {
      if ( ( id >= limit ) ) {
        return oak_Result_u32_IdPoolError_Err(oak_IdPoolError_OutOfBounds())      ;
      } else {
        u32 index       = oak_div_u32( id, ((u32)( 8 )) )      ;
        u8 mask       = oak_shl_u8( ((u8)( 1 )), oak_conv_u8_trunc_u32( oak_rem_u32( id, ((u32)( 8 )) ) ) )      ;
        Bool vacant       = ( ( oak_span_index_u8( storage, (u64)( index ) ) & mask ) == ((u8)( 0 )) )      ;
        if ( vacant ) {
          return oak_Result_u32_IdPoolError_Err(oak_IdPoolError_NotAllocated())        ;
        } else {
          oak_span_store_u8( storage, (u64)( index ), ( oak_span_index_u8( storage, (u64)( index ) ) & ( mask ^ ((u8)( 255 )) ) ) );
          return oak_Result_u32_IdPoolError_Ok(id)        ;
        }
      }
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:1364:4-1383:0
// @package: main
// @kind: function
// @identifier: id_pool_allocate
// @signature: fn id_pool_allocate(storage: /* type */, limit: u32) -> /* type */
oak_Result_u32_IdPoolError oak_id_pool_allocate( oak_span_u8 storage, u32 limit ) {
    u32 needed   = oak_bitset_storage_bytes( limit )  ;
    if ( ( ((u32)( storage ).len) < needed ) ) {
      return oak_Result_u32_IdPoolError_Err(oak_IdPoolError_StorageTooSmall())    ;
    } else {
      u32 byte_index     = 0    ;
      u32 id     = limit    ;
      while ( ( ( byte_index < needed ) && ( id == limit ) )     ) {
        if ( ( oak_span_index_u8( storage, (u64)( byte_index ) ) != ((u8)( 255 )) )       ) {
          u32 bit         = 0        ;
          while ( ( ( bit < ((u32)( 8 )) ) && ( id == limit ) )         ) {
            u32 candidate           = oak_add_u32( oak_mul_u32( byte_index, ((u32)( 8 )) ), bit )          ;
            u8 mask           = oak_shl_u8( ((u8)( 1 )), oak_conv_u8_trunc_u32( bit ) )          ;
            if ( ( ( candidate < limit ) && ( ( oak_span_index_u8( storage, (u64)( byte_index ) ) & mask ) == ((u8)( 0 )) ) )           ) {
              id             = candidate            ;
            }
            bit           = oak_add_u32( bit, ((u32)( 1 )) )          ;
          }
        }
        byte_index       = oak_add_u32( byte_index, ((u32)( 1 )) )      ;
      }
      if ( ( id == limit ) ) {
        return oak_Result_u32_IdPoolError_Err(oak_IdPoolError_Full())      ;
      } else {
        return oak_id_pool_reserve( storage, limit, id )      ;
      }
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:1386:4-1400:0
// @package: main
// @kind: function
// @identifier: id_pool_clear
// @signature: fn id_pool_clear(storage: /* type */, limit: u32) -> /* type */
oak_Result_u32_IdPoolError oak_id_pool_clear( oak_span_u8 storage, u32 limit ) {
    if ( ( ((u32)( storage ).len) < oak_bitset_storage_bytes( limit ) ) ) {
      return oak_Result_u32_IdPoolError_Err(oak_IdPoolError_StorageTooSmall())    ;
    } else {
      u32 whole     = oak_div_u32( limit, ((u32)( 8 )) )    ;
      u32 i     = 0    ;
      while ( ( i < whole )     ) {
        oak_span_store_u8( storage, (u64)( i ), ((u8)( 0 )) );
        i       = oak_add_u32( i, ((u32)( 1 )) )      ;
      }
      u32 tail     = oak_rem_u32( limit, ((u32)( 8 )) )    ;
      if ( ( tail != ((u32)( 0 )) )     ) {
        u8 mask       = oak_sub_u8( oak_shl_u8( ((u8)( 1 )), oak_conv_u8_trunc_u32( tail ) ), ((u8)( 1 )) )      ;
        oak_span_store_u8( storage, (u64)( whole ), ( oak_span_index_u8( storage, (u64)( whole ) ) & ( mask ^ ((u8)( 255 )) ) ) );
      }
      return oak_Result_u32_IdPoolError_Ok(limit)    ;
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:65:0-70:0
// @package: main
// @kind: function
// @identifier: utf8__special_ucases
// @signature: fn utf8__special_ucases(high1: simd.U8x16, low1: simd.U8x16, high2: simd.U8x16, input: simd.U8x16, prev1: simd.U8x16) -> simd.U8x16
OAK_INLINE u8x16 oak_utf8__special_ucases( u8x16 high1, u8x16 low1, u8x16 high2, u8x16 input, u8x16 prev1 ) {
    u8x16 byte_1_high   = oak_simd_tbl_u8x16( high1, oak_simd_shr_u8x16( prev1, ((u32)( 4 )) ) )  ;
    u8x16 byte_1_low   = oak_simd_tbl_u8x16( low1, oak_simd_and_u8x16( prev1, oak_simd_splat_u8x16( ((u8)( 15 )) ) ) )  ;
    u8x16 byte_2_high   = oak_simd_tbl_u8x16( high2, oak_simd_shr_u8x16( input, ((u32)( 4 )) ) )  ;
    return oak_simd_and_u8x16( oak_simd_and_u8x16( byte_1_high, byte_1_low ), byte_2_high )  ;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:75:0-88:0
// @package: main
// @kind: function
// @identifier: utf8__check_ublock
// @signature: fn utf8__check_ublock(high1: simd.U8x16, low1: simd.U8x16, high2: simd.U8x16, prev_input: simd.U8x16, input: simd.U8x16) -> simd.U8x16
u8x16 oak_utf8__check_ublock( u8x16 high1, u8x16 low1, u8x16 high2, u8x16 prev_input, u8x16 input ) {
    u8x16 prev1   = oak_simd_prev_u8x16( prev_input, input, ((u32)( 1 )) )  ;
    u8x16 prev2   = oak_simd_prev_u8x16( prev_input, input, ((u32)( 2 )) )  ;
    u8x16 prev3   = oak_simd_prev_u8x16( prev_input, input, ((u32)( 3 )) )  ;
    u8x16 sc   = oak_utf8__special_ucases( high1, low1, high2, input, prev1 )  ;
    u8x16 third   = oak_simd_subs_u8x16( prev2, oak_simd_splat_u8x16( ((u8)( 96 )) ) )  ;
    u8x16 fourth   = oak_simd_subs_u8x16( prev3, oak_simd_splat_u8x16( ((u8)( 112 )) ) )  ;
    u8x16 must23   = oak_simd_and_u8x16( oak_simd_or_u8x16( third, fourth ), oak_simd_splat_u8x16( ((u8)( 128 )) ) )  ;
    return oak_simd_xor_u8x16( must23, sc )  ;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:95:0-101:0
// @package: main
// @kind: function
// @identifier: utf8__check_ublocks
// @signature: fn utf8__check_ublocks(high1: simd.U8x16, low1: simd.U8x16, high2: simd.U8x16, prev_input: simd.U8x16, a: simd.U8x16, b: simd.U8x16, c: simd.U8x16, d: simd.U8x16) -> simd.U8x16
u8x16 oak_utf8__check_ublocks( u8x16 high1, u8x16 low1, u8x16 high2, u8x16 prev_input, u8x16 a, u8x16 b, u8x16 c, u8x16 d ) {
    u8x16 ea   = oak_utf8__check_ublock( high1, low1, high2, prev_input, a )  ;
    u8x16 eb   = oak_utf8__check_ublock( high1, low1, high2, a, b )  ;
    u8x16 ec   = oak_utf8__check_ublock( high1, low1, high2, b, c )  ;
    u8x16 ed   = oak_utf8__check_ublock( high1, low1, high2, c, d )  ;
    return oak_simd_or_u8x16( oak_simd_or_u8x16( ea, eb ), oak_simd_or_u8x16( ec, ed ) )  ;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:115:4-172:0
// @package: main
// @kind: function
// @identifier: utf8__valid
// @signature: fn utf8__valid(bytes: /* type */) -> Bool
Bool oak_utf8__valid( oak_view_u8 bytes ) {
    u8x16 high1   = oak_simd_load_u8x16( (oak_view_u8){ utf8__table_uhigh1.v, 16 }, ((u32)( 0 )) )  ;
    u8x16 low1   = oak_simd_load_u8x16( (oak_view_u8){ utf8__table_ulow1.v, 16 }, ((u32)( 0 )) )  ;
    u8x16 high2   = oak_simd_load_u8x16( (oak_view_u8){ utf8__table_uhigh2.v, 16 }, ((u32)( 0 )) )  ;
    u8x16 maxima   = oak_simd_load_u8x16( (oak_view_u8){ utf8__incomplete_umax.v, 16 }, ((u32)( 0 )) )  ;
    u8x16 high_bit   = oak_simd_splat_u8x16( ((u8)( 128 )) )  ;
    u8x16 zero   = oak_simd_splat_u8x16( ((u8)( 0 )) )  ;
    u8x16 error   = zero  ;
    u8x16 prev_input   = zero  ;
    u8x16 prev_incomplete   = zero  ;
    u32 n   = ((u32)( bytes ).len)  ;
    u32 off   = ((u32)( 0 ))  ;
    while ( ( ( ((u32)( bytes ).len) >= ((u32)( 64 )) ) && ( off <= oak_sub_u32( ((u32)( bytes ).len), ((u32)( 64 )) ) ) )   ) {
      u8x16 a     = oak_simd_load_u8x16_proven( bytes, off )    ;
      u8x16 b     = oak_simd_load_u8x16_proven( bytes, oak_add_u32( off, ((u32)( 16 )) ) )    ;
      u8x16 c     = oak_simd_load_u8x16_proven( bytes, oak_add_u32( off, ((u32)( 32 )) ) )    ;
      u8x16 d     = oak_simd_load_u8x16_proven( bytes, oak_add_u32( off, ((u32)( 48 )) ) )    ;
      u8x16 step_bits     = oak_simd_or_u8x16( oak_simd_or_u8x16( a, b ), oak_simd_or_u8x16( c, d ) )    ;
      if ( oak_simd_any_u8x16( oak_simd_and_u8x16( step_bits, high_bit ) )     ) {
        error       = oak_simd_or_u8x16( error, oak_utf8__check_ublocks( high1, low1, high2, prev_input, a, b, c, d ) )      ;
        prev_incomplete       = oak_simd_subs_u8x16( d, maxima )      ;
      } else {
        error       = oak_simd_or_u8x16( error, prev_incomplete )      ;
        prev_incomplete       = zero      ;
      }
      prev_input     = d    ;
      off     = oak_add_u32( off, ((u32)( 64 )) )    ;
    }
    while ( ( ( ((u32)( bytes ).len) >= ((u32)( 16 )) ) && ( off <= oak_sub_u32( ((u32)( bytes ).len), ((u32)( 16 )) ) ) )   ) {
      u8x16 input     = oak_simd_load_u8x16_proven( bytes, off )    ;
      if ( oak_simd_any_u8x16( oak_simd_and_u8x16( input, high_bit ) )     ) {
        error       = oak_simd_or_u8x16( error, oak_utf8__check_ublock( high1, low1, high2, prev_input, input ) )      ;
        prev_incomplete       = oak_simd_subs_u8x16( input, maxima )      ;
      } else {
        error       = oak_simd_or_u8x16( error, prev_incomplete )      ;
        prev_incomplete       = zero      ;
      }
      prev_input     = input    ;
      off     = oak_add_u32( off, ((u32)( 16 )) )    ;
    }
    oak_arr_u8_16 tail = { { ((u8)( 0 )), ((u8)( 0 )), ((u8)( 0 )), ((u8)( 0 )), ((u8)( 0 )), ((u8)( 0 )), ((u8)( 0 )), ((u8)( 0 )), ((u8)( 0 )), ((u8)( 0 )), ((u8)( 0 )), ((u8)( 0 )), ((u8)( 0 )), ((u8)( 0 )), ((u8)( 0 )), ((u8)( 0 )) } };
    u32 i   = ((u32)( 0 ))  ;
    while ( ( oak_add_u32( off, i ) < n )   ) {
      oak_store( tail.v, 16, (u64)( i ), oak_view_index_u8( bytes, (u64)( oak_add_u32( off, i ) ) ) );
      i     = oak_add_u32( i, ((u32)( 1 )) )    ;
    }
    u8x16 last   = oak_simd_load_u8x16( (oak_view_u8){ tail.v, 16 }, ((u32)( 0 )) )  ;
    if ( oak_simd_any_u8x16( oak_simd_and_u8x16( last, high_bit ) )   ) {
      error     = oak_simd_or_u8x16( error, oak_utf8__check_ublock( high1, low1, high2, prev_input, last ) )    ;
      prev_incomplete     = oak_simd_subs_u8x16( last, maxima )    ;
    } else {
      error     = oak_simd_or_u8x16( error, prev_incomplete )    ;
      prev_incomplete     = zero    ;
    }
    return !( oak_simd_any_u8x16( oak_simd_or_u8x16( error, prev_incomplete ) ) )  ;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:-1:28
// @package: main
// @kind: function
// @identifier: utf8_initial
// @signature: fn utf8_initial() -> Utf8State
oak_Utf8State oak_utf8_initial(  ) {
    return oak_Utf8State_Accept()  ;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:-1:791
// @package: main
// @kind: function
// @identifier: utf8_legal
// @signature: fn utf8_legal(state: Utf8State, step: Utf8Step) -> Bool
Bool oak_utf8_legal( oak_Utf8State state, oak_Utf8Step step ) {
    return (u32)( ( oak_utf8_transitions[ step.payload.Byte ] >> state.tag ) & 63u ) != 48u ? oak_Bool_True : oak_Bool_False;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:-1:819
// @package: main
// @kind: function
// @identifier: utf8_next
// @signature: fn utf8_next(state: Utf8State, step: Utf8Step) -> Utf8State
oak_Utf8State oak_utf8_next( oak_Utf8State state, oak_Utf8Step step ) {
    u32 next = (u32)( ( oak_utf8_transitions[ step.payload.Byte ] >> state.tag ) & 63u );
    oak_assert( next != 48u ? oak_Bool_True : oak_Bool_False, "Utf8", 0 );
    oak_Utf8State result;
    result.tag = next;
    return result;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:-1:869
// @package: main
// @kind: function
// @identifier: utf8_run
// @signature: fn utf8_run(state: Utf8State, bytes: /* type */) -> Utf8State
oak_Utf8State oak_utf8_run( oak_Utf8State state, oak_view_u8 bytes ) {
    u32 current = state.tag;
    const u8 *symbols = bytes.base;
    u64 count = (u64)bytes.len;
    for (u64 i = 0; i < count; i++) {
      current = (u32)( ( oak_utf8_transitions[ symbols[ i ] ] >> current ) & 63u );
    }
    oak_assert( current != 48u ? oak_Bool_True : oak_Bool_False, "Utf8", 0 );
    oak_Utf8State result;
    result.tag = current;
    return result;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:27:0-27:54
// @package: main
// @kind: function
// @identifier: utf8_cont
// @signature: fn utf8_cont(b: u8) -> Bool
OAK_INLINE Bool oak_utf8_cont( u8 b ) {
    return ( ( b >= ((u8)( 128 )) ) && ( b <= ((u8)( 191 )) ) )  ;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:28:0-31:16
// @package: main
// @kind: function
// @identifier: utf8_second3
// @signature: fn utf8_second3(b0: u8, b1: u8) -> Bool
Bool oak_utf8_second3( u8 b0, u8 b1 ) {
    if ( ( b0 == ((u8)( 224 )) ) ) {
      return ( ( b1 >= ((u8)( 160 )) ) && ( b1 <= ((u8)( 191 )) ) )    ;
    } else {
      if ( ( b0 == ((u8)( 237 )) ) ) {
        return ( ( b1 >= ((u8)( 128 )) ) && ( b1 <= ((u8)( 159 )) ) )      ;
      } else {
        return oak_utf8_cont( b1 )      ;
      }
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:32:0-35:16
// @package: main
// @kind: function
// @identifier: utf8_second4
// @signature: fn utf8_second4(b0: u8, b1: u8) -> Bool
Bool oak_utf8_second4( u8 b0, u8 b1 ) {
    if ( ( b0 == ((u8)( 240 )) ) ) {
      return ( ( b1 >= ((u8)( 144 )) ) && ( b1 <= ((u8)( 191 )) ) )    ;
    } else {
      if ( ( b0 == ((u8)( 244 )) ) ) {
        return ( ( b1 >= ((u8)( 128 )) ) && ( b1 <= ((u8)( 143 )) ) )      ;
      } else {
        return oak_utf8_cont( b1 )      ;
      }
    }
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:36:0-55:0
// @package: main
// @kind: function
// @identifier: utf8_scalar
// @signature: fn utf8_scalar(v: /* type */) -> Bool
Bool oak_utf8_scalar( oak_view_u8 v ) {
    u32 n   = ((u32)( v ).len)  ;
    u32 i   = ((u32)( 0 ))  ;
    Bool ok   = oak_Bool_True  ;
    while ( ( ok && ( i < n ) )   ) {
      u8 b0     = ( v ).base[ i ]    ;
      if ( ( b0 <= ((u8)( 127 )) )     ) {
        i       = oak_add_u32( i, ((u32)( 1 )) )      ;
      } else {
        if ( ( ( b0 >= ((u8)( 194 )) ) && ( b0 <= ((u8)( 223 )) ) ) ) {
          if ( ( ( oak_add_u32( i, ((u32)( 1 )) ) < n ) && oak_utf8_cont( oak_view_index_u8( v, (u64)( oak_add_u32( i, ((u32)( 1 )) ) ) ) ) ) ) {
            i           = oak_add_u32( i, ((u32)( 2 )) )          ;
          } else {
            ok           = oak_Bool_False          ;
          }
        } else {
          if ( ( ( b0 >= ((u8)( 224 )) ) && ( b0 <= ((u8)( 239 )) ) ) ) {
            if ( ( ( ( oak_add_u32( i, ((u32)( 2 )) ) < n ) && oak_utf8_second3( b0, oak_view_index_u8( v, (u64)( oak_add_u32( i, ((u32)( 1 )) ) ) ) ) ) && oak_utf8_cont( oak_view_index_u8( v, (u64)( oak_add_u32( i, ((u32)( 2 )) ) ) ) ) ) ) {
              i             = oak_add_u32( i, ((u32)( 3 )) )            ;
            } else {
              ok             = oak_Bool_False            ;
            }
          } else {
            if ( ( ( b0 >= ((u8)( 240 )) ) && ( b0 <= ((u8)( 244 )) ) ) ) {
              if ( ( ( ( ( oak_add_u32( i, ((u32)( 3 )) ) < n ) && oak_utf8_second4( b0, oak_view_index_u8( v, (u64)( oak_add_u32( i, ((u32)( 1 )) ) ) ) ) ) && oak_utf8_cont( oak_view_index_u8( v, (u64)( oak_add_u32( i, ((u32)( 2 )) ) ) ) ) ) && oak_utf8_cont( oak_view_index_u8( v, (u64)( oak_add_u32( i, ((u32)( 3 )) ) ) ) ) ) ) {
                i               = oak_add_u32( i, ((u32)( 4 )) )              ;
              } else {
                ok               = oak_Bool_False              ;
              }
            } else {
              ok             = oak_Bool_False            ;
            }
          }
        }
      }
    }
    return ok  ;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:56:4-56:57
// @package: main
// @kind: function
// @identifier: scalar_valid
// @signature: fn scalar_valid(bytes: /* type */) -> Bool
Bool oak_scalar_valid( oak_view_u8 bytes ) {
    return oak_utf8_scalar( bytes )  ;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:57:4-57:54
// @package: main
// @kind: function
// @identifier: simd_valid
// @signature: fn simd_valid(bytes: /* type */) -> Bool
Bool oak_simd_valid( oak_view_u8 bytes ) {
    return oak_utf8__valid( bytes )  ;
}

// @source: /var/folders/h4/7zdg3m7s02j_ym20ys_0h0b00000gn/T/TestEmitStateMachineBenchmarkSource3120498031/001:58:0-61:0
// @package: main
// @kind: function
// @identifier: main
// @signature: fn main() -> u32
u32 oak_main(  ) {
    oak_arr_u8_4 text = { { ((u8)( 104 )), ((u8)( 105 )), ((u8)( 195 )), ((u8)( 169 )) } };
    if ( ( oak_scalar_valid( (oak_view_u8){ text.v, 4 } ) && oak_simd_valid( (oak_view_u8){ text.v, 4 } ) ) ) {
      return ((u32)( 0 ))    ;
    } else {
      return ((u32)( 1 ))    ;
    }
}

int main(void) {
  return (int)oak_main();
}
