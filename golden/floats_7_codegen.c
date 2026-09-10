/* Generated C code from Oak */
#include <stdint.h>
#include <stddef.h>
#include <math.h>
#pragma STDC FP_CONTRACT OFF

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
    if ( ( ( bits == ((u32)( 1084227584 )) ) && ( half == ((f64)0x1.4p+01) ) ) ) {
      return 0    ;
    } else {
      return 1    ;
    }
}

int main(void) {
  return (int)oak_main();
}
