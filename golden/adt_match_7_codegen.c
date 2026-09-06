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

// @source: unknown.oak:1:0-4:4
// @package: main
// @kind: ADT
// @identifier: Shape
typedef enum oak_Shape_tag {
    oak_Shape_tag_Circle  ,
    oak_Shape_tag_Square  ,
    oak_Shape_tag_Empty
} oak_Shape_tag;

typedef struct oak_Shape {
    oak_Shape_tag tag;
    union {
        i32 Circle;
        i32 Square;
    } payload;
} oak_Shape;

// @source: unknown.oak:2:4
// @package: main
// @kind: constructor
// @identifier: oak_Shape::Circle
static inline oak_Shape oak_Shape_Circle( i32 value ) {
    oak_Shape res;
    res.tag = oak_Shape_tag_Circle;
    res.payload.Circle = value;
    return res;
}

// @source: unknown.oak:3:4
// @package: main
// @kind: constructor
// @identifier: oak_Shape::Square
static inline oak_Shape oak_Shape_Square( i32 value ) {
    oak_Shape res;
    res.tag = oak_Shape_tag_Square;
    res.payload.Square = value;
    return res;
}

// @source: unknown.oak:4:4
// @package: main
// @kind: constructor
// @identifier: oak_Shape::Empty
static inline oak_Shape oak_Shape_Empty(  ) {
    oak_Shape res;
    res.tag = oak_Shape_tag_Empty;
    return res;
}

/* forward declarations */
i32 oak_area2( oak_Shape s );
i32 oak_main( void );

// @source: unknown.oak:6:0-9:14
// @package: main
// @kind: function
// @identifier: area2
// @signature: fn area2(s: Shape) -> i32
i32 oak_area2( oak_Shape s ) {
    if ( s.tag == oak_Shape_tag_Circle ) {
      i32 r = s.payload.Circle;
    return ( r * 3 )  ;
    }
    if ( s.tag == oak_Shape_tag_Square ) {
      i32 w = s.payload.Square;
    return ( w * w )  ;
    }
    if ( s.tag == oak_Shape_tag_Empty ) {
    return 0  ;
    }
}

// @source: unknown.oak:11:0-15:0
// @package: main
// @kind: function
// @identifier: main
// @signature: fn main() -> i32
i32 oak_main(  ) {
    oak_Shape c   = oak_Shape_Circle(5)  ;
    oak_Shape q   = oak_Shape_Square(4)  ;
    return ( oak_area2( c ) + oak_area2( q ) )  ;
}

int main(void) {
  return (int)oak_main();
}
