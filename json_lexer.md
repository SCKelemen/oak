# Lexing and Parsing

Design notes for Oak’s lexing/parsing layer, the language features it relies on, and how it maps to the C backend. Includes:

* Language features needed for efficient lexing and parsing.
* A byte-oriented `ByteLexer` abstraction.
* A JSON lexer written in Oak.
* Corresponding C output that a firmware engineer would be happy to debug.
* Reader/Writer/Closer abstractions for I/O.
* A sketch of a jq-like tool built on top.
* An architecture decision log capturing trade-offs and rejected alternatives.

All of this is MCU-focused and heap-less by default.

---

## 0. Goals

1. **MCU-friendly**

   * No heap allocation in core lexing/parsing libraries.
   * All buffers are caller-owned; lexers hold spans/views into those buffers.
   * Target devices like STM32 and RP2350.

2. **C-backend friendly**

   * Oak code for lexers/parsers should compile to C that:

     * Has simple structs and functions.
     * Uses clear whitespace and comments.
     * Is pleasant to read and debug in firmware workflows.

3. **State-machine friendly**

   * Lexers and parsers should compose into deterministic state machines.
   * Easy to apply to streams (e.g., JSON + jq-like command language) without building large heaps of AST objects.

4. **Predictable performance and semantics**

   * No hidden allocations.
   * No implicit integer widening/downcasting.
   * Strict control over pointer usage.

---

## 1. Language features used by lexers/parsers

We only depend on a small subset of Oak features for lexing/parsing. This keeps the compiler surface small and the generated C predictable.

### 1.1 Primitive aliases and core types

```oak
// Primitive aliases
byte: type = u8
rune: type = i32

// Sentinel rune for end-of-input in in-memory lexers.
const EOF: rune = rune(-1)

// Immutable string as a pointer+length into some buffer.
string: type =
  { data: *byte
  , len:  u32
  }

// Generic span / slice (non-owning window over contiguous memory).
Span[T]: type =
  { base: *T
  , len:  u32
  }
```

Notes:

* `EOF` is a **sentinel only at the lexing layer** (e.g., JSON lexer over a `string`).
* For I/O streams, we use `Reader` and error ADTs instead (see §6).

### 1.2 Pattern matching

Oak has expression-based pattern matching; lexers lean on it heavily:

```oak
scrutinee ?
  | pattern1 -> expr1
  | pattern2 -> expr2
  | _        -> fallback
```

Inline form:

```oak
scrutinee ? | pattern1 -> expr1 | pattern2 -> expr2 | _ -> exprN
```

We also allow optional braces around the arms:

```oak
scrutinee ? { pattern1 -> expr1 | pattern2 -> expr2 }
```

Match is an expression; the last expression in each arm is the value.

* **No if statement** – pattern matching and the `?` form are the primary conditional.
* Evaluation order is left-to-right.
* Functions return the last expression in their body.

### 1.3 Array and byte-pattern sugar

Lexers need concise ways to look at several bytes at once. We introduce a small amount of pattern sugar for fixed-size byte windows.

#### `Bytes4` helper type

```oak
// 4-byte window over bytes at the current index.
Bytes4: type =
  { len:  u8       // 0..4
  , data: [4]byte
  }
```

We pattern-match on `Bytes4` in JSON lexing.

Patterns allowed for a `Bytes4` scrutinee:

1. **Exact string literal** (length ≤ 4):

   ```oak
   chunk: Bytes4 = lx.peek_bytes4()

   chunk ?
     | "true" -> ...
     | "null" -> ...
   ```

   Semantics:

   * String literal must be ASCII for now.
   * The compiler encodes it as a `Bytes4` constant `{ len: 4, data: [...] }` if length is 4.
   * Match checks both `len` and byte contents.

2. **Array of byte literals**:

   ```oak
   chunk ?
     | [ '{', _, _, _ ] -> ...
     | [ '0'..'9', _, _, _ ] -> ...
   ```

   Where:

   * Character literals like `'{'` are bytes.
   * `_` is a wildcard (matches any byte).
   * A range like `'0'..'9'` is shorthand for `b >= '0' && b <= '9'` at that position.

3. **Mixed string and array patterns**

   The following is valid and common in lexers:

   ```oak
   chunk ?
     | "true"              -> ...   // full literal
     | "null"              -> ...
     | [ 'f', 'a', 'l', 's' ] -> ... // prefix of "false"
     | [ '{', _, _, _ ]      -> ...
   ```

This sugar is deliberately limited:

* Only available when scrutinee is a `Bytes4` or `[4]byte`.
* Only fixed-size arrays; no variadic array patterns.
* Ranges (`'a'..'z'`) only occur in element position, not spanning indices.

This keeps matching logic simple and easy to map to C.

### 1.4 EOF sentinel vs I/O errors

We distinguish two layers:

1. **In-memory lexers** (e.g., JSON over a `string`):

   * Use `rune` + `EOF` sentinel for `next_rune()`.
   * Use `is_eof()` / `index` vs `len` for window-based helpers.

2. **I/O layer** (e.g., reading from UART or file):

   * Uses `Reader` with `ReadResult` and `ReadError` ADTs (see §6).
   * EOF is represented as a `ReadError.EOF` in that layer.

Lexers are typically fed from an in-memory buffer; bridging from `Reader` to `ByteLexer` is handled by a small adapter that fills fixed-size buffers.

---

## 2. Byte lexer model

A `ByteLexer` reads from a `string` (pointer+length) with a single cursor index.

```oak
ByteLexer: type =
  { input: string
  , index: u32
  }

fn mk_lexer( input: string ) -> ByteLexer
  ByteLexer { input: input, index: u32(0) }

fn (lx: *ByteLexer) pos() -> u32
  lx.index

fn (lx: *ByteLexer) is_eof() -> Bool
  (lx.index >= lx.input.len) ?
    | .True  -> .True
    | .False -> .False
```

### 2.1 `next_rune` (byte-level, sentinel EOF)

```oak
fn (lx: *ByteLexer) next_rune() -> rune
  lx.is_eof() ?
    | .True  -> EOF
    | .False ->
        b: byte = lx.input.data[lx.index]
        lx.index = lx.index + u32(1)
        rune(u32(b))      // widen 0..255 to rune
```

### 2.2 `peek_bytes4`

```oak
fn (lx: *ByteLexer) peek_bytes4() -> Bytes4
  rem: u32 =
    (lx.input.len > lx.index) ?
      | .True  -> lx.input.len - lx.index
      | .False -> u32(0)

  take32: u32 =
    (rem >= u32(4)) ?
      | .True  -> u32(4)
      | .False -> rem

  take: u8 = u8(take32)

  buf: [4]byte = [ u8(0), u8(0), u8(0), u8(0) ]
  i: u32 = 0

  while i < take32 {
    buf[i] = lx.input.data[lx.index + i]
    i      = i + u32(1)
  }

  Bytes4 { len: take, data: buf }
```

### 2.3 Advancing and whitespace skipping

```oak
// Advance by at most n bytes, clamping at end of input.
fn (lx: *ByteLexer) advance( n: u32 ) -> ()
  rem: u32 =
    (lx.input.len > lx.index) ?
      | .True  -> lx.input.len - lx.index
      | .False -> u32(0)

  step: u32 =
    (n > rem) ?
      | .True  -> rem
      | .False -> n

  lx.index = lx.index + step


fn (lx: *ByteLexer) skip_ws() -> ()
  while !lx.is_eof() {
    b: byte = lx.input.data[lx.index]

    (b == u8(' ') || b == u8('\t') || b == u8('\r') || b == u8('\n')) ?
      | .True  ->
          lx.index = lx.index + u32(1)
      | .False ->
          break
  }
```

### 2.4 `skip_until_byte`

A Go-like `strings` helper: advance until a given byte or EOF.

```oak
// Advance until we see `target` or hit EOF.
// Returns the number of bytes skipped before stopping.
//
// Postconditions:
//   let start = original lx.index
//   let skipped = return value
//
//   lx.index == start + skipped
//
//   if !lx.is_eof() && lx.input.data[lx.index] == target:
//       we stopped before target (caller may now consume it).
//   else:
//       we reached EOF without seeing target.
fn (lx: *ByteLexer) skip_until_byte( target: byte ) -> u32
  start: u32 = lx.index

  while !lx.is_eof() {
    b: byte = lx.input.data[lx.index]

    (b == target) ?
      | .True  ->
          return lx.index - start

      | .False ->
          lx.index = lx.index + u32(1)
  }

  lx.index - start
```

### 2.5 `try_consume_byte`

```oak
// If the next byte equals `target`, consume it and return True; otherwise False.
fn (lx: *ByteLexer) try_consume_byte( target: byte ) -> Bool
  lx.is_eof() ?
    | .True  -> .False
    | .False ->
        (lx.input.data[lx.index] == target) ?
          | .True  ->
              lx.index = lx.index + u32(1)
              .True
          | .False ->
              .False
```

These primitives are enough to build lexers for JSON and for small DSLs.

---

## 3. JSON token model

We design a minimal token model suitable for both a classic parser and for streaming/event-style handling.

```oak
JsonTokenKind: type =
  | LBrace | RBrace
  | LBracket | RBracket
  | Colon | Comma
  | TrueKw | FalseKw | NullKw
  | Number | String
  | EndOfFile
  | Error

Span: type =
  { start: u32
  , len:   u32
  }

JsonToken: type =
  { kind: JsonTokenKind
  , span: Span
  }

fn mk_token( kind: JsonTokenKind, start: u32, end: u32 ) -> JsonToken
  JsonToken {
    kind: kind,
    span: { start: start, len: end - start },
  }
```

The `span` always refers to the original input buffer (no copies). A parser can later create higher-level structures by holding spans or pointers into the same underlying data.

---

## 4. JSON lexer in Oak

### 4.1 High-level `next_token`

We bring together the byte-level primitives, pattern-matching sugar, and token model.

```oak
fn next_token( lx: *ByteLexer ) -> JsonToken
  lx.skip_ws()
  start: u32 = lx.pos()

  lx.is_eof() ?
    | .True  ->
        mk_token(.EndOfFile, start, start)

    | .False ->
        chunk: Bytes4 = lx.peek_bytes4()

        chunk ?
          | "true" ->
              lx.advance(u32(4))
              mk_token(.TrueKw, start, lx.pos())

          | "null" ->
              lx.advance(u32(4))
              mk_token(.NullKw, start, lx.pos())

          | [ 'f', 'a', 'l', 's' ] ->
              lex_false(lx, start)

          | [ '{', _, _, _ ] ->
              lx.advance(u32(1))
              mk_token(.LBrace, start, lx.pos())

          | [ '}', _, _, _ ] ->
              lx.advance(u32(1))
              mk_token(.RBrace, start, lx.pos())

          | [ '[', _, _, _ ] ->
              lx.advance(u32(1))
              mk_token(.LBracket, start, lx.pos())

          | [ ']', _, _, _ ] ->
              lx.advance(u32(1))
              mk_token(.RBracket, start, lx.pos())

          | [ ':', _, _, _ ] ->
              lx.advance(u32(1))
              mk_token(.Colon, start, lx.pos())

          | [ ',', _, _, _ ] ->
              lx.advance(u32(1))
              mk_token(.Comma, start, lx.pos())

          | [ '"', _, _, _ ] ->
              lex_string(lx, start)

          | [ '-', '0'..'9', _, _ ] ->
              lex_number(lx, start)

          | [ '0'..'9', _, _, _ ] ->
              lex_number(lx, start)

          | [ _, _, _, _ ] ->
              // Unknown byte → error token consuming one byte.
              lx.advance(u32(1))
              mk_token(.Error, start, lx.pos())
```

### 4.2 `lex_false`

Efficient handling of `false` using `Bytes4` prefix and `next_rune` for the 5th character.

```oak
fn lex_false( lx: *ByteLexer, start: u32 ) -> JsonToken
  // We matched "fals" already via Bytes4; consume it.
  lx.advance(u32(4))

  ch: rune = lx.next_rune()

  (ch == EOF) ?
    | .True ->
        // Input ended after "fals".
        mk_token(.Error, start, lx.pos())

    | .False ->
        (ch == rune(u32('e'))) ?
          | .True ->
              // "false"
              mk_token(.FalseKw, start, lx.pos())

          | .False ->
              // "falsX"
              mk_token(.Error, start, lx.pos())
```

### 4.3 `lex_string` using `skip_until_byte`

For now, this ignores escape sequences; those can be layered on later.

```oak
fn lex_string( lx: *ByteLexer, start: u32 ) -> JsonToken
  // We are at the opening '"'; consume it.
  _ = lx.next_rune()

  _ = lx.skip_until_byte(u8('"'))

  lx.is_eof() ?
    | .True ->
        // Unterminated string.
        mk_token(.Error, start, lx.pos())

    | .False ->
        // Now at the closing '"'; consume it.
        _ = lx.next_rune()
        mk_token(.String, start, lx.pos())
```

### 4.4 `lex_number` (sketch)

A number lexer would use the same primitives and `peek_bytes4`/`next_rune` to implement JSON number rules. For brevity, only the shape:

```oak
fn lex_number( lx: *ByteLexer, start: u32 ) -> JsonToken
  // Consume digits, optional '.', exponent, etc.
  // Use lx.next_rune() and/or direct byte access from lx.input.
  // Ensure we only accept valid JSON numbers.

  // For now, just scan digits and optional '.', without validation.
  while !lx.is_eof() {
    b: byte = lx.input.data[lx.index]

    ((b >= u8('0') && b <= u8('9')) || b == u8('.') || b == u8('e') || b == u8('E') || b == u8('+') || b == u8('-')) ?
      | .True  -> lx.index = lx.index + u32(1)
      | .False -> break
  }

  mk_token(.Number, start, lx.pos())
```

The full JSON number rules can be enforced later, but the structure is compatible with the lexing primitives.

---

## 5. C backend mapping for lexers

This section describes how the Oak code above is lowered to C, following our C backend style:

* `u8`, `u16`, `u32`, `u64`, `i8`, `i16`, `i32`, `i64` typedefs.
* Pointer asterisks attached to the type (`u8* base;`).
* Braces opened on the same line as control statements/functions.
* Spaces inside parentheses and braces: `if ( cond ) { ... }`.
* Doxygen-style comments for functions.

### 5.1 Core C typedefs

```c
typedef uint8_t  u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

typedef int8_t   i8;
typedef int16_t  i16;
typedef int32_t  i32;
typedef int64_t  i64;

typedef u8   byte;
typedef i32  rune;

#define OAK_EOF_RUNE ( ( rune )-1 )

typedef struct {
  byte* data;
  u32   len;
} oak_string;

typedef struct {
  byte  data[ 4 ];
  u8    len; /* 0..4 */
} oak_bytes4;

typedef struct {
  oak_string input;
  u32        index;
} oak_byte_lexer;
```

### 5.2 `next_rune`

```c
/**
 * @brief Return the next byte as a rune, or OAK_EOF_RUNE on end-of-input.
 *
 * Advances the lexer index by one byte when not at EOF.
 */
static rune
oak_next_rune( oak_byte_lexer* lx )
{
  if ( lx->index >= lx->input.len ) {
    return OAK_EOF_RUNE;
  }

  byte b = lx->input.data[ lx->index ];
  lx->index += 1u;
  return ( rune )b;
}
```

### 5.3 `peek_bytes4`

```c
/**
 * @brief Peek up to 4 bytes from the current position.
 *
 * Does not advance the lexer index. The returned struct contains
 * the number of valid bytes in len (0..4) and the bytes in data[0..len).
 */
static oak_bytes4
oak_peek_bytes4( const oak_byte_lexer* lx )
{
  oak_bytes4 out;
  u32 rem = 0u;

  if ( lx->input.len > lx->index ) {
    rem = lx->input.len - lx->index;
  }

  u32 take32 = ( rem >= 4u ) ? 4u : rem;
  out.len    = ( u8 )take32;

  out.data[ 0 ] = 0u;
  out.data[ 1 ] = 0u;
  out.data[ 2 ] = 0u;
  out.data[ 3 ] = 0u;

  for ( u32 i = 0u; i < take32; ++i ) {
    out.data[ i ] = lx->input.data[ lx->index + i ];
  }

  return out;
}
```

### 5.4 `advance`, `skip_ws`, `skip_until_byte`

```c
/**
 * @brief Advance the lexer index by at most n bytes.
 */
static void
oak_advance( oak_byte_lexer* lx, u32 n )
{
  u32 rem = 0u;

  if ( lx->input.len > lx->index ) {
    rem = lx->input.len - lx->index;
  }

  u32 step = ( n > rem ) ? rem : n;
  lx->index += step;
}

/**
 * @brief Skip ASCII whitespace: space, tab, CR, LF.
 */
static void
oak_skip_ws( oak_byte_lexer* lx )
{
  while ( lx->index < lx->input.len ) {
    byte b = lx->input.data[ lx->index ];

    if ( b == ( byte )' ' || b == ( byte )'\t' ||
         b == ( byte )'\r' || b == ( byte )'\n' ) {
      lx->index += 1u;
    } else {
      break;
    }
  }
}

/**
 * @brief Advance until target byte or EOF.
 *
 * Returns the number of bytes skipped before stopping.
 * If !EOF and input.data[index] == target, we stopped before target.
 */
static u32
oak_skip_until_byte( oak_byte_lexer* lx, byte target )
{
  u32 start = lx->index;

  while ( lx->index < lx->input.len ) {
    byte b = lx->input.data[ lx->index ];

    if ( b == target ) {
      return lx->index - start;
    }

    lx->index += 1u;
  }

  return lx->index - start;
}
```

### 5.5 JSON tokens in C

```c
typedef enum {
  JSON_LBRACE,
  JSON_RBRACE,
  JSON_LBRACKET,
  JSON_RBRACKET,
  JSON_COLON,
  JSON_COMMA,
  JSON_TRUE,
  JSON_FALSE,
  JSON_NULL,
  JSON_NUMBER,
  JSON_STRING,
  JSON_EOF,
  JSON_ERROR
} json_token_kind;

typedef struct {
  u32 start;
  u32 len;
} oak_span_u32;

typedef struct {
  json_token_kind kind;
  oak_span_u32    span;
} json_token;

static json_token
oak_mk_token( json_token_kind kind, u32 start, u32 end )
{
  json_token tok;
  tok.kind      = kind;
  tok.span.start = start;
  tok.span.len   = end - start;
  return tok;
}
```

### 5.6 `lex_false` in C

```c
/**
 * @brief Lex the keyword "false" after seeing the prefix "fals".
 */
static json_token
oak_lex_false( oak_byte_lexer* lx, u32 start )
{
  /* We already matched "fals" via peek_bytes4; consume it. */
  oak_advance( lx, 4u );

  rune ch = oak_next_rune( lx );

  if ( ch == OAK_EOF_RUNE ) {
    return oak_mk_token( JSON_ERROR, start, lx->index );
  }

  if ( ch == ( rune )'e' ) {
    return oak_mk_token( JSON_FALSE, start, lx->index );
  }

  /* "falsX" */
  return oak_mk_token( JSON_ERROR, start, lx->index );
}
```

### 5.7 `lex_string` in C

```c
/**
 * @brief Lex a JSON string starting at the opening quote.
 */
static json_token
oak_lex_string( oak_byte_lexer* lx, u32 start )
{
  /* Consume opening '"'. */
  ( void )oak_next_rune( lx );

  ( void )oak_skip_until_byte( lx, ( byte )'"' );

  if ( lx->index >= lx->input.len ) {
    /* Unterminated string. */
    return oak_mk_token( JSON_ERROR, start, lx->index );
  }

  /* Consume closing '"'. */
  ( void )oak_next_rune( lx );
  return oak_mk_token( JSON_STRING, start, lx->index );
}
```

### 5.8 `next_token` in C (partial)

The full `next_token` function mirrors the Oak match; the key idea is that `Bytes4` patterns compile into a sequence of `if`/`else` checks on `oak_bytes4`.

```c
/**
 * @brief Lex the next JSON token from the input.
 */
static json_token
oak_next_token( oak_byte_lexer* lx )
{
  oak_skip_ws( lx );
  u32 start = lx->index;

  if ( lx->index >= lx->input.len ) {
    return oak_mk_token( JSON_EOF, start, start );
  }

  oak_bytes4 chunk = oak_peek_bytes4( lx );

  /* String literal cases: "true" and "null". */
  if ( chunk.len == 4u &&
       chunk.data[ 0 ] == ( byte )'t' &&
       chunk.data[ 1 ] == ( byte )'r' &&
       chunk.data[ 2 ] == ( byte )'u' &&
       chunk.data[ 3 ] == ( byte )'e' ) {
    oak_advance( lx, 4u );
    return oak_mk_token( JSON_TRUE, start, lx->index );
  }

  if ( chunk.len == 4u &&
       chunk.data[ 0 ] == ( byte )'n' &&
       chunk.data[ 1 ] == ( byte )'u' &&
       chunk.data[ 2 ] == ( byte )'l' &&
       chunk.data[ 3 ] == ( byte )'l' ) {
    oak_advance( lx, 4u );
    return oak_mk_token( JSON_NULL, start, lx->index );
  }

  /* Prefix "fals". */
  if ( chunk.len == 4u &&
       chunk.data[ 0 ] == ( byte )'f' &&
       chunk.data[ 1 ] == ( byte )'a' &&
       chunk.data[ 2 ] == ( byte )'l' &&
       chunk.data[ 3 ] == ( byte )'s' ) {
    return oak_lex_false( lx, start );
  }

  /* Single-character tokens. */
  if ( chunk.len >= 1u ) {
    byte b0 = chunk.data[ 0 ];

    if ( b0 == ( byte )'{' ) {
      oak_advance( lx, 1u );
      return oak_mk_token( JSON_LBRACE, start, lx->index );
    }
    if ( b0 == ( byte )'}' ) {
      oak_advance( lx, 1u );
      return oak_mk_token( JSON_RBRACE, start, lx->index );
    }
    if ( b0 == ( byte )'[' ) {
      oak_advance( lx, 1u );
      return oak_mk_token( JSON_LBRACKET, start, lx->index );
    }
    if ( b0 == ( byte )']' ) {
      oak_advance( lx, 1u );
      return oak_mk_token( JSON_RBRACKET, start, lx->index );
    }
    if ( b0 == ( byte )':' ) {
      oak_advance( lx, 1u );
      return oak_mk_token( JSON_COLON, start, lx->index );
    }
    if ( b0 == ( byte )',' ) {
      oak_advance( lx, 1u );
      return oak_mk_token( JSON_COMMA, start, lx->index );
    }
    if ( b0 == ( byte )'"' ) {
      return oak_lex_string( lx, start );
    }

    if ( ( b0 >= ( byte )'0' && b0 <= ( byte )'9' ) || b0 == ( byte )'-' ) {
      /* Call into number lexer (not shown here). */
      /* ... */
    }
  }

  /* Unknown byte -> error token consuming one byte. */
  oak_advance( lx, 1u );
  return oak_mk_token( JSON_ERROR, start, lx->index );
}
```

The C matches the Oak code closely, making debugging straightforward.

---

## 6. Reader / Writer / Closer interfaces

Lexers typically operate on in-memory buffers, but we still need a streaming I/O layer for MCU integration (UART, SPI, files, etc.). We follow Go’s `io.Reader` model, adapted to Oak’s ADTs.

### 6.1 Read errors and results

```oak
ReadError: type =
  | EOF            // graceful end of input
  | UnexpectedEOF  // EOF in the middle of a structured read
  | NoProgress     // repeated 0-byte reads without error
  | Other(u16)     // small numeric code for platform-specific errors

ReadResult: type =
  { n:   u32              // bytes read into buffer
  , err: Option[ReadError]
  }
```

### 6.2 Reader interface

```oak
Reader: interface =
  fn (self: *Self) read( buf: Span[byte] ) -> ReadResult
```

Semantics mirror Go’s `Read`:

* `n > 0` and `err == None` → some data read; continue.
* `n > 0` and `err == Some(.EOF)` → data read, plus EOF; caller must still process data.
* `n == 0` and `err == Some(.EOF)` → no more data.
* `n == 0` and `err == None` → nothing happened (e.g., non-blocking read); caller may retry or treat as `NoProgress` if repeated.
* `UnexpectedEOF` is for helper functions (e.g., `read_full`) that expected more bytes.

### 6.3 Writer and Closer (sketch)

```oak
WriteError: type =
  | ShortWrite
  | NoProgress
  | Other(u16)

WriteResult: type =
  { n:   u32
  , err: Option[WriteError]
  }

Writer: interface =
  fn (self: *Self) write( buf: Span[byte] ) -> WriteResult

Closer: interface =
  fn (self: *Self) close() -> Option[u16]  // optional small error code
```

Higher-level helpers (e.g., `read_full`, `copy`) are defined in terms of `Reader`/`Writer` but do not allocate; they operate on caller-provided buffers.

Lexers use `ByteLexer` over `string`/`Span[byte]`. Adapters bridge a `Reader` into a `ByteLexer` by filling fixed-size buffers.

---

## 7. jq-style pipeline sketch

A jq-like tool is a good stress-test for state machines on an MCU:

* **JSON parser**: turns bytes → tokens → a stream of events.
* **jq expression parser**: parses command syntax (no heap; fixed-size AST or bytecode).
* **Executor**: runs a state machine over JSON events, applying the jq expression and emitting filtered JSON.

### 7.1 JSON events

Instead of building a full object tree, we can use a streaming event model:

```oak
JsonEvent: type =
  | StartObject
  | EndObject
  | StartArray
  | EndArray
  | FieldName(Span[byte])  // view into input buffer
  | String(Span[byte])
  | Number(Span[byte])
  | Bool(Bool)
  | Null
```

The parser:

* Consumes `JsonToken`s from the lexer.
* Emits `JsonEvent`s into a small ring buffer or directly into a consumer callback.
* Never allocates; all `Span[byte]` values refer into the original input buffer.

### 7.2 Minimal jq expression language

For a first pass, keep jq syntax small:

```oak
JqExpr: type =
  | Identity                     // .
  | Field(Span[byte])            // .foo
  | Index(u32)                   // .[0]
  | Pipe(JqExpr, JqExpr)         // lhs | rhs
```

Parsing `JqExpr` can reuse the same lexing patterns:

* A small byte-oriented lexer over the jq command string.
* Tokens: `Dot`, `Identifier`, `Number`, `LBracket`, `RBracket`, `Pipe`, `EOF`.
* The parser runs as a simple recursive descent, storing an AST in a caller-provided buffer or as a tiny bytecode.

### 7.3 jq executor state machine

The executor consumes `JsonEvent`s and applies the `JqExpr`.

For a tiny subset:

* `Identity` → re-emit the JSON unchanged.
* `Field("foo")` → track current object path; only emit values when the path matches `.foo`.
* `Index(0)` → similar, but for array indices.
* `Pipe(lhs, rhs)` → implement as two-phase state machine:

  * Run `lhs` over the event stream → intermediate events.
  * Feed intermediate events into `rhs`.

In a constrained MCU:

* Intermediate events for `Pipe` can be handled one-by-one (streamed), not stored.
* The executor’s state is just a small struct with:

  * current path stack (fixed-size array of field names/indices),
  * current jq expression program counter,
  * output writer.

All of this can be implemented without heap allocation, as long as maximum nesting depth is bounded.

---

## 8. Architecture decision log

This section records the major design decisions and alternatives considered for lexing and parsing.

### 8.1 EOF representation

**Options considered:**

* A `Result`-style ADT for `next_byte`: `ByteOrEOF = EOF | Byte(byte)`.
* A sentinel integer (like Go’s `rune` with `-1` for EOF).

**Decision:**

* For in-memory lexers, use `rune` with `EOF = -1`.
* For streams, represent EOF as `ReadError.EOF` in `Reader`.

**Rationale:**

* ADTs are expressive but add a tag field; in the hot lexing loop, a single integer is simpler and easier to optimize.
* Sentinel `EOF` is a well-understood pattern (Go’s template lexer does something similar).
* Keeping a separate `Reader` layer gives us a clean place to model EOF as an error when appropriate.

### 8.2 `skip_until` return type

**Options considered:**

* `ReadUntilResult = Found(u32) | EOF(u32)`.
* A plain `u32` (bytes skipped) plus checking `is_eof()` afterwards.

**Decision:**

* `skip_until_byte` returns only `u32`.
* Caller inspects `is_eof()` and the next byte to distinguish “found vs EOF”.

**Rationale:**

* Matches `strings`-style APIs (index/len semantics) familiar from Go.
* Keeps the hot path signature tiny (`u32` return), no extra tag.
* Semantics are still clear when documented.

### 8.3 Fixed-size byte windows (`Bytes4`, `Bytes8`)

**Options considered:**

* General array patterns of arbitrary size.
* Fixed-size 4- or 8-byte windows for lexing keywords/punctuation.

**Decision:**

* Introduce `Bytes4` (and later `Bytes8` if needed) as explicit types.
* Restrict pattern sugar to these fixed sizes.

**Rationale:**

* 4-byte windows are enough for JSON keywords (`true`, `null`, `fals` prefix).
* Fixed size simplifies pattern compilation and keeps `peek_bytes4` trivial.
* Straightforward mapping to tight C code, easy to reason about alignment.

### 8.4 Pattern sugar for byte arrays

**Options considered:**

* Complex pattern language with nested arrays, arbitrary wildcards, etc.
* A small set of patterns: string literals, fixed-size arrays, `_` wildcard, and simple ranges.

**Decision:**

* Limit to:

  * string literals of length ≤ 4 as `Bytes4` patterns.
  * array patterns like `[ '{', _, _, _ ]`.
  * ranges like `'0'..'9'` at element positions.

**Rationale:**

* Enough expressivity for lexers without exploding language/implementation complexity.
* Easy to desugar into simple `if`/`else` sequences in C.

### 8.5 Reader vs direct buffer for lexers

**Options considered:**

* Make lexers operate directly on a `Reader` interface.
* Make lexers operate on `string`/`Span[byte]` and have a separate adapter from `Reader`.

**Decision:**

* Lexers operate on `string` / `Span[byte]` via `ByteLexer`.
* A separate adapter fills buffers from `Reader` if streaming is needed.

**Rationale:**

* Simpler mental model for lexers; they only worry about indices into a buffer.
* Avoids partial-read complexity in the lexing code.
* Works naturally with both static buffers and pre-fetched chunks from I/O.

### 8.6 Heap avoidance

**Decision:**

* No heap allocations in lexing/parsing core.
* All ownership is explicit: caller owns buffers; lexers and parsers operate via spans/views.

**Rationale:**

* MCU-focused design: easier to reason about memory usage and failure modes.
* Encourages streaming designs (JSON event stream, jq state machines) over building large trees.

### 8.7 ADTs vs interfaces for behavior

**Context:**

* For I/O, we use `Reader`, `Writer`, `Closer` interfaces.
* For token and event modeling, we use ADTs (`JsonTokenKind`, `JsonEvent`, etc.).

**Decision:**

* Use interfaces for pluggable behaviors (I/O, sinks, etc.).
* Use ADTs for closed sets of variants (tokens, events, expression kinds).

**Rationale:**

* ADTs give exhaustiveness checking in pattern matches.
* Interfaces let different devices and transports implement the same protocol with no extra type layers.

---

This document captures the current design for Oak’s lexing/parsing stack and its C mapping. Future work (e.g., full JSON parser, complete jq subset, more language-level sugar) should build on these foundations without introducing hidden costs or heap dependencies.
