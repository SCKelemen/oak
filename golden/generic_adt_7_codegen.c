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

// @source: unknown.oak:1:0-1:19
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

// @source: unknown.oak:1:19
// @package: main
// @kind: constructor
// @identifier: oak_Overflow::Overflow
static inline oak_Overflow oak_Overflow_Overflow(  ) {
    oak_Overflow res;
    res.tag = oak_Overflow_tag_Overflow;
    return res;
}

// @source: unknown.oak:5:0-5:28
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

// @source: unknown.oak:5:18
// @package: main
// @kind: constructor
// @identifier: oak_Option_u32::Some
static inline oak_Option_u32 oak_Option_u32_Some( u32 value ) {
    oak_Option_u32 res;
    res.tag = oak_Option_u32_tag_Some;
    res.payload.Some = value;
    return res;
}

// @source: unknown.oak:5:28
// @package: main
// @kind: constructor
// @identifier: oak_Option_u32::None
static inline oak_Option_u32 oak_Option_u32_None(  ) {
    oak_Option_u32 res;
    res.tag = oak_Option_u32_tag_None;
    return res;
}

// @source: unknown.oak:3:0-3:29
// @package: main
// @kind: ADT
// @identifier: Result_u8_Overflow
typedef enum oak_Result_u8_Overflow_tag {
    oak_Result_u8_Overflow_tag_Ok  ,
    oak_Result_u8_Overflow_tag_Err
} oak_Result_u8_Overflow_tag;

typedef struct oak_Result_u8_Overflow {
    u32 tag;
    union {
        u8 Ok;
        oak_Overflow Err;
    } payload;
} oak_Result_u8_Overflow;

typedef char oak_union_layout_Result_u8_Overflow[ (sizeof(oak_Result_u8_Overflow) == 8u && _Alignof(oak_Result_u8_Overflow) == 4u && offsetof(oak_Result_u8_Overflow, tag) == 0u && offsetof(oak_Result_u8_Overflow, payload) == 4u) ? 1 : -1 ];

// @source: unknown.oak:3:21
// @package: main
// @kind: constructor
// @identifier: oak_Result_u8_Overflow::Ok
static inline oak_Result_u8_Overflow oak_Result_u8_Overflow_Ok( u8 value ) {
    oak_Result_u8_Overflow res;
    res.tag = oak_Result_u8_Overflow_tag_Ok;
    res.payload.Ok = value;
    return res;
}

// @source: unknown.oak:3:29
// @package: main
// @kind: constructor
// @identifier: oak_Result_u8_Overflow::Err
static inline oak_Result_u8_Overflow oak_Result_u8_Overflow_Err( oak_Overflow value ) {
    oak_Result_u8_Overflow res;
    res.tag = oak_Result_u8_Overflow_tag_Err;
    res.payload.Err = value;
    return res;
}

/* explicit integer conversions: total, two's complement, no
   implementation-defined C (signed results via union punning) */
static inline i32 oak_conv_i32_bits_u32( u32 x ) {
  union { u32 from; i32 to; } pun;
  pun.from = x;
  return pun.to;
}

static inline oak_Result_u8_Overflow oak_conv_u8_checked_u32( u32 x ) {
  if (x > (u32)255u) { return oak_Result_u8_Overflow_Err(oak_Overflow_Overflow()); }
  return oak_Result_u8_Overflow_Ok((u8)x);
}

/* forward declarations; OAK_INLINE marks private leaf helpers the C
   compiler must inline at every optimization level (the external
   definition is still emitted: C99 extern inline) */
#define OAK_INLINE extern inline __attribute__((always_inline))
OAK_INLINE oak_Option_u32 oak_first_even( u32 a, u32 b );
i32 oak_main( void );

// @source: unknown.oak:7:0-11:0
// @package: main
// @kind: function
// @identifier: first_even
// @signature: fn first_even(a: u32, b: u32) -> /* type */
OAK_INLINE oak_Option_u32 oak_first_even( u32 a, u32 b ) {
    if ( ( oak_sub_u32( a, oak_mul_u32( oak_div_u32( a, ((u32)( 2 )) ), ((u32)( 2 )) ) ) == ((u32)( 0 )) ) ) {
      return oak_Option_u32_Some(a)    ;
    } else {
      if ( ( oak_sub_u32( b, oak_mul_u32( oak_div_u32( b, ((u32)( 2 )) ), ((u32)( 2 )) ) ) == ((u32)( 0 )) ) ) {
        return oak_Option_u32_Some(b)      ;
      } else {
        return oak_Option_u32_None()      ;
      }
    }
}

// @source: unknown.oak:13:0-21:0
// @package: main
// @kind: function
// @identifier: main
// @signature: fn main() -> i32
i32 oak_main(  ) {
    oak_Option_u32 found   = oak_first_even( ((u32)( 3 )), ((u32)( 8 )) )  ;
    i32 byteRange  ;
    oak_Result_u8_Overflow oak__scrutinee_0 = oak_conv_u8_checked_u32( ((u32)( 300 )) );
    if ( oak__scrutinee_0.tag == oak_Result_u8_Overflow_tag_Ok ) {
      u8 v = oak__scrutinee_0.payload.Ok;
      byteRange     = ((i32)( v ))    ;
    }
    else if ( oak__scrutinee_0.tag == oak_Result_u8_Overflow_tag_Err ) {
      oak_Overflow e = oak__scrutinee_0.payload.Err;
      byteRange     = ( 0 - 1 )    ;
    }
    else { __builtin_trap(); /* unreachable: exhaustive match */ }
    if ( found.tag == oak_Option_u32_tag_Some ) {
      u32 n = found.payload.Some;
    return oak_add_i32( oak_conv_i32_bits_u32( n ), byteRange )  ;
    }
    if ( found.tag == oak_Option_u32_tag_None ) {
    return byteRange  ;
    }
    __builtin_trap(); /* unreachable: exhaustive match */
}

int main(void) {
  return (int)oak_main();
}
