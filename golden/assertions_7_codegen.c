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

// @source: unknown.oak:1:0-4:0
// @package: main
// @kind: function
// @identifier: checked_double
// @signature: fn checked_double(n: i32) -> i32
i32 oak_checked_double( i32 n ) {
oak_assert( ( n < 100 ) )  ;
    return ( n * 2 )  ;
}

