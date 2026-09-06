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

/* trampoline for mutual tail recursion: ping, pong */
typedef enum {
    oak_tramp_ping_pong_ping,
    oak_tramp_ping_pong_pong
} oak_tramp_ping_pong_state;

static i32 oak_tramp_ping_pong( oak_tramp_ping_pong_state __oak_state, i32 n ) {
  while (1) {
  switch (__oak_state) {
  case oak_tramp_ping_pong_ping: {
  i32 x = ( n + 1 );
  {
    i32 __oak_tail_0 = x;
    n = __oak_tail_0;
    __oak_state = oak_tramp_ping_pong_pong;
    continue;
  }
  }
  case oak_tramp_ping_pong_pong: {
  i32 y = ( n * 2 );
  {
    i32 __oak_tail_0 = y;
    n = __oak_tail_0;
    __oak_state = oak_tramp_ping_pong_ping;
    continue;
  }
  }
  }
  }
}

i32 oak_ping( i32 n ) {
  return oak_tramp_ping_pong( oak_tramp_ping_pong_ping, n );
}

i32 oak_pong( i32 n ) {
  return oak_tramp_ping_pong( oak_tramp_ping_pong_pong, n );
}

