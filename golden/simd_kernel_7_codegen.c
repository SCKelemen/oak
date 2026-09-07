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
static inline void oak_assert(Bool cond) {
  if (!cond) {
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

/* portable SIMD vectors: docs/spec/93-simd.md */
#if defined(__aarch64__) && !defined(OAK_PORTABLE_INTRINSICS)
#include <arm_neon.h>
#endif
typedef struct oak_u8x16 { u8 lanes[16]; } u8x16;
typedef struct oak_u16x8 { u16 lanes[8]; } u16x8;
typedef struct oak_u32x4 { u32 lanes[4]; } u32x4;
typedef struct oak_u64x2 { u64 lanes[2]; } u64x2;

static inline Bool oak_simd_any_u8x16( u8x16 v ) {
#if defined(__aarch64__) && !defined(OAK_PORTABLE_INTRINSICS)
  return vmaxvq_u8(vld1q_u8(v.lanes)) != 0u ? oak_Bool_True : oak_Bool_False;
#else
  for (int i = 0; i < 16; i++) { if (v.lanes[i] != 0) { return oak_Bool_True; } }
  return oak_Bool_False;
#endif
}

static inline u8x16 oak_simd_eq_u8x16( u8x16 a, u8x16 b ) {
  u8x16 r;
#if defined(__aarch64__) && !defined(OAK_PORTABLE_INTRINSICS)
  vst1q_u8(r.lanes, vceqq_u8(vld1q_u8(a.lanes), vld1q_u8(b.lanes)));
#else
  for (int i = 0; i < 16; i++) {
    u8 x = a.lanes[i]; u8 y = b.lanes[i];
    r.lanes[i] = (u8)(x == y ? (u8)~(u8)0 : (u8)0);
  }
#endif
  return r;
}

static inline u8x16 oak_simd_load_u8x16( oak_view_u8 v, u32 off ) {
  if ((u64)off + 16u > (u64)v.len) { __builtin_trap(); }
  u8x16 r;
#if defined(__aarch64__) && !defined(OAK_PORTABLE_INTRINSICS)
  vst1q_u8(r.lanes, vld1q_u8(v.base + off));
#else
  for (int i = 0; i < 16; i++) { r.lanes[i] = v.base[off + (u32)i]; }
#endif
  return r;
}

static inline u8x16 oak_simd_splat_u8x16( u8 x ) {
  u8x16 r;
#if defined(__aarch64__) && !defined(OAK_PORTABLE_INTRINSICS)
  vst1q_u8(r.lanes, vdupq_n_u8(x));
#else
  for (int i = 0; i < 16; i++) { r.lanes[i] = x; }
#endif
  return r;
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

static inline void oak_simd_store_u8x16( oak_span_u8 s, u32 off, u8x16 val ) {
  if ((u64)off + 16u > (u64)s.len) { __builtin_trap(); }
#if defined(__aarch64__) && !defined(OAK_PORTABLE_INTRINSICS)
  vst1q_u8(s.base + off, vld1q_u8(val.lanes));
#else
  for (int i = 0; i < 16; i++) { s.base[off + (u32)i] = val.lanes[i]; }
#endif
}

static inline u32 oak_arm64_uaddlv_u8x16( u8x16 x ) {
#if defined(__aarch64__) && !defined(OAK_PORTABLE_INTRINSICS)
  return (u32)vaddlvq_u8(vld1q_u8(x.lanes));
#else
  u32 sum = 0;
  for (int i = 0; i < 16; i++) { sum += x.lanes[i]; }
  return sum;
#endif
}

/* forward declarations */
Bool oak_contains16( oak_view_u8 v, u8 needle );
i32 oak_main( void );

// @source: unknown.oak:1:0-5:0
// @package: main
// @kind: function
// @identifier: contains16
// @signature: fn contains16(v: /* type */, needle: u8) -> Bool
Bool oak_contains16( oak_view_u8 v, u8 needle ) {
    u8x16 chunk   = oak_simd_load_u8x16( v, ((u32)( 0 )) )  ;
    u8x16 hits   = oak_simd_eq_u8x16( chunk, oak_simd_splat_u8x16( needle ) )  ;
    return oak_simd_any_u8x16( hits )  ;
}

// @source: unknown.oak:7:0-13:0
// @package: main
// @kind: function
// @identifier: main
// @signature: fn main() -> i32
i32 oak_main(  ) {
    u8 out[16] = {0};
    oak_span_u8 s   = (oak_span_u8){ out, 16 }  ;
oak_simd_store_u8x16( s, ((u32)( 0 )), oak_simd_splat_u8x16( ((u8)( 66 )) ) )  ;
oak_assert( ( oak_arm64_uaddlv_u8x16( oak_simd_splat_u8x16( ((u8)( 1 )) ) ) == ((u32)( 16 )) ) )  ;
    return ((i32)( oak_span_index_u8( s, (u64)( 0 ) ) ))  ;
}

int main(void) {
  return (int)oak_main();
}
