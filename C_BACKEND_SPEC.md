# C Backend Specification (Draft)

> **Target:** Readable, idiomatic C suitable for firmware engineers

> **Goal:** Oak code must lower to simple, auditable C that matches how an experienced embedded engineer would structure code by hand.

---

## 1. Overall Goals and Constraints

1. **Readability first**

   * Generated C must be easy to inspect, debug, and code-review.
   * No macro metaprogramming, no exotic tricks.

2. **Predictable mapping**

   * Oak constructs map to a small set of familiar C idioms:

     * records → `struct`
     * ADTs → `enum + union`
     * slices/spans → `{ T* base; u32 len; }`

3. **Style consistency**

   * The backend must emit C that strictly follows the style rules below.

4. **No hidden runtime**

   * No exceptions, GC, or hidden allocations.
   * Code is compatible with freestanding MCU environments.

---

## 2. C Style Rules

These are **hard** constraints for the backend.

### 2.1 Pointer style

* Pointer asterisk belongs to the **type**, not the identifier.

```c
u8* ptr;
string* s;
oak_span_u8* span;
```

* Never emit `u8 * ptr` or `u8*ptr` or `ptr *u8`.

### 2.2 Braces

* **Opening brace** on the **same line** as the header.
* **Closing brace** on its own line, aligned with the start of the header.

Examples:

```c
u8 oak_example_func( u8* recv, u8 value ) {
  /* ... */
}

typedef struct oak_span_u8 {
  u8* base;
  u32 len;
} oak_span_u8;

if ( cond ) {
  /* ... */
} else {
  /* ... */
}
```

### 2.3 Spacing

* Space inside all parentheses, brackets, and braces:

```c
foo( x, y );
if ( x == 0 ) {
  buf[ 0 ] = 1;
}
```

* One space between type and identifier (when not a pointer): `u8 value;`.
* No trailing spaces at end of lines.

### 2.4 Function signatures

* Return type, name, and parameter list are on the **same line**:

```c
u8 oak_example_func( u8* recv, u8 value ) {
  /* ... */
}
```

---

## 3. Primitive Type Aliases

Every generated C module must include (directly or via a shared header):

```c
#include <stdint.h>
#include <stddef.h>

typedef uint8_t  u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

typedef int8_t   i8;
typedef int16_t  i16;
typedef int32_t  i32;
typedef int64_t  i64;

typedef u8  byte;
typedef i32 rune;
```

* These aliases mirror Oak's primitive integer types.
* `byte` and `rune` are semantic aliases for clarity.

---

## 4. Strings

Oak `string` is an immutable byte-sequence abstraction; in C it is represented as:

```c
typedef struct oak_string {
  u8* data;  /* UTF-8 bytes, not necessarily null-terminated */
  u32 len;   /* number of bytes */
} string;
```

Notes:

* No implicit null-termination.
* C interop helpers (`oak_string_to_cstr`, etc.) are emitted separately if needed.

---

## 5. Arrays, Views, Spans

### 5.1 Arrays `[N]T`

Oak fixed-size arrays are values, carried by a wrapper struct so that C's
struct semantics supply parameter, return, and assignment copies
(docs/spec/90-backend.md section 10). The wrapper has the raw array's size
and alignment:

```oak
buf: [256]u8
```

→ C:

```c
typedef struct oak_arr_u8_256 { u8 v[ 256 ]; } oak_arr_u8_256;
oak_arr_u8_256 buf = {0};
```

Element access spells the member: `buf.v[ i ]` under the bounds check.

### 5.2 View and Span types

Conceptual Oak definitions:

```oak
View[T]: type =
  { base: *T
  , len:  u32
  }

Span[T]: type =
  { base: *T
  , len:  u32
  }

[]T  == View[T]
[*]T == Span[T]
```

For each instantiated element type `T`, the backend emits specialized structs:

```c
typedef struct oak_view_u8 {
  const u8* base;
  u32       len;
} oak_view_u8;

typedef struct oak_span_u8 {
  u8* base;
  u32 len;
} oak_span_u8;
```

Example translation:

```oak
buf: [256]u8
v: []u8  = buf[0:128]
s: [*]u8 = buf[128:256]
```

→ C:

```c
u8 buf[ 256 ];

oak_view_u8 v = {
  .base = &buf[ 0 ],
  .len  = 128
};

oak_span_u8 s = {
  .base = &buf[ 128 ],
  .len  = 128
};
```

---

## 6. Records (Structs)

Oak record:

```oak
Config: type =
  { enabled: Bool
  , threshold: u8
  }
```

→ C struct (assuming `Bool` lowers to an integer-like type):

```c
typedef struct oak_Config {
  u8 enabled;    /* Bool encoded as 0/1 */
  u8 threshold;
} oak_Config;
```

Rules:

* Field order in C matches Oak declaration order.
* Field names are preserved (with minimal mangling if they collide with C keywords).

---

## 7. ADTs (Sum Types: Option, Result, User ADTs)

### 7.1 Representation pattern

All algebraic data types (ADTs) are represented as:

* A tag `enum` identifying the active variant.
* A `struct` holding the tag and, when needed, a `union` for variant payloads.

#### Example: Simple ADT

Oak:

```oak
Error: type
  = Eof
  | Io
```

→ C:

```c
typedef enum oak_Error_tag {
  oak_Error_tag_Eof,
  oak_Error_tag_Io
} oak_Error_tag;

typedef struct oak_Error {
  oak_Error_tag tag;
} oak_Error;
```

#### Example: ADT with payloads (Option)

Oak:

```oak
Option[T]: type
  = None
  | Some(T)
```

Instantiated for `T = u8`:

```c
typedef enum oak_Option_u8_tag {
  oak_Option_u8_tag_None,
  oak_Option_u8_tag_Some
} oak_Option_u8_tag;

typedef struct oak_Option_u8 {
  oak_Option_u8_tag tag;
  union {
    u8 Some;
  } payload;
} oak_Option_u8;
```

#### Example: Result

Oak:

```oak
Result[T, E]: type
  = Ok(T)
  | Err(E)
```

Instantiated for `T = u8`, `E = Error`:

```c
typedef enum oak_Result_u8_Error_tag {
  oak_Result_u8_Error_tag_Ok,
  oak_Result_u8_Error_tag_Err
} oak_Result_u8_Error_tag;

typedef struct oak_Result_u8_Error {
  oak_Result_u8_Error_tag tag;
  union {
    u8        Ok;
    oak_Error Err;
  } payload;
} oak_Result_u8_Error;
```

### 7.2 Constructors (helpers)

The backend emits small inline constructors for convenience and readability:

```c
static inline oak_Result_u8_Error oak_Result_u8_Error_Ok( u8 value ) {
  oak_Result_u8_Error res;
  res.tag = oak_Result_u8_Error_tag_Ok;
  res.payload.Ok = value;
  return res;
}

static inline oak_Result_u8_Error oak_Result_u8_Error_Err( oak_Error err ) {
  oak_Result_u8_Error res;
  res.tag = oak_Result_u8_Error_tag_Err;
  res.payload.Err = err;
  return res;
}
```

Similar constructors are generated for `Error` (if needed) and other ADTs.

### 7.3 Bool and Comparison

Oak:

```oak
Bool: type
  = False
  | True

Comparison: type
  = Less
  | Equal
  | Greater
```

→ C:

```c
typedef enum oak_Bool {
  oak_Bool_False = 0,
  oak_Bool_True  = 1
} Bool;

typedef enum oak_Comparison {
  oak_Comparison_Less,
  oak_Comparison_Equal,
  oak_Comparison_Greater
} Comparison;
```

These typedefs ensure user-facing C code uses `Bool` and `Comparison` directly.

---

## 8. Functions and Methods

### 8.1 Plain functions

Oak:

```oak
fn add_u8( a: u8, b: u8 ) -> u8
  a + b
```

→ C:

```c
u8 oak_add_u8( u8 a, u8 b ) {
  return (u8)( a + b );
}
```

Naming:

* Non-method functions are prefixed with `oak_` and, optionally, a package component (e.g., `oak_http_FromCode`).

### 8.2 Methods (receiver functions)

Oak:

```oak
fn (t: Token) lexeme() -> string
  /* ... */
```

→ C (one possible mangling):

```c
string oak_Token_lexeme( Token t ) {
  /* ... */
}
```

* First parameter is the receiver.
* No vtables; these are plain C functions.

---

## 9. Pattern Matching (`?`) Lowering

Oak's `scrutinee ? | pattern -> expr` constructs are lowered to `switch` or `if` chains.

### 9.1 ADT matches

Oak:

```oak
opt: Result[u8, Error] = ...

opt ?
  | .Ok(v)  -> v
  | .Err(e) ->
      e ?
        | .Eof -> 0
        | .Io  -> 1
```

→ C:

```c
u8 oak_status_code( oak_Result_u8_Error res ) {
  switch ( res.tag ) {
    case oak_Result_u8_Error_tag_Ok: {
      u8 v = res.payload.Ok;
      return v;
    } break;

    case oak_Result_u8_Error_tag_Err: {
      oak_Error e = res.payload.Err;

      switch ( e.tag ) {
        case oak_Error_tag_Eof: {
          return 0;
        } break;

        case oak_Error_tag_Io: {
          return 1;
        } break;
      }
    } break;
  }
}
```

Lowering rules:

* Each `?` on an ADT:

  * Introduces a `switch ( value.tag )`.
  * Each variant arm becomes a `case` block.
  * Pattern bindings (e.g. `.Ok(v)`) become locals extracted from `payload`.

### 9.2 Scalar matches

Oak:

```oak
fn FromCode( code: u16 ) -> Status
  code ?
    | 200 -> Status::Ok
    | 404 -> Status::NotFound
    | _   -> Status::InternalServerError
```

→ C (sketch):

```c
Status oak_http_FromCode( u16 code ) {
  if ( code == 200 ) {
    return oak_Status_Ok();
  } else if ( code == 404 ) {
    return oak_Status_NotFound();
  } else {
    return oak_Status_InternalServerError();
  }
}
```

* Scalar `?` lowers to an `if`/`else if` chain with equality checks.
* Constructors like `oak_Status_Ok()` are generated helpers.

---

## 10. Example: Result-returning Reader Function

### 10.1 Oak code

Assume:

```oak
Error: type
  = Eof
  | Io
  | ShortRead

Reader: type =
  interface
    fn (self) read( buf: [*]Byte ) -> Result[u32, Error]

fn read_exact[T: Reader]( reader: T, buf: [*]Byte ) -> Result[u32, Error]
  res: Result[u32, Error] = reader.read( buf )

  res ?
    | .Ok(n) ->
        (n == buf.len) ?
          | .True  -> .Ok(n)
          | .False -> .Err(.ShortRead)
    | .Err(e) -> .Err(e)
```

Suppose `Uart` is a concrete type implementing `Reader`. The compiler monomorphizes this for `Uart`, producing:

### 10.2 C types

Error ADT:

```c
typedef enum oak_Error_tag {
  oak_Error_tag_Eof,
  oak_Error_tag_Io,
  oak_Error_tag_ShortRead
} oak_Error_tag;

typedef struct oak_Error {
  oak_Error_tag tag;
} oak_Error;

static inline oak_Error oak_Error_Eof( void ) {
  oak_Error e;
  e.tag = oak_Error_tag_Eof;
  return e;
}

static inline oak_Error oak_Error_Io( void ) {
  oak_Error e;
  e.tag = oak_Error_tag_Io;
  return e;
}

static inline oak_Error oak_Error_ShortRead( void ) {
  oak_Error e;
  e.tag = oak_Error_tag_ShortRead;
  return e;
}
```

Result[u32, Error]:

```c
typedef enum oak_Result_u32_Error_tag {
  oak_Result_u32_Error_tag_Ok,
  oak_Result_u32_Error_tag_Err
} oak_Result_u32_Error_tag;

typedef struct oak_Result_u32_Error {
  oak_Result_u32_Error_tag tag;
  union {
    u32        Ok;
    oak_Error  Err;
  } payload;
} oak_Result_u32_Error;

static inline oak_Result_u32_Error oak_Result_u32_Error_Ok( u32 value ) {
  oak_Result_u32_Error res;
  res.tag = oak_Result_u32_Error_tag_Ok;
  res.payload.Ok = value;
  return res;
}

static inline oak_Result_u32_Error oak_Result_u32_Error_Err( oak_Error err ) {
  oak_Result_u32_Error res;
  res.tag = oak_Result_u32_Error_tag_Err;
  res.payload.Err = err;
  return res;
}
```

Span type for `Byte`/`u8`:

```c
typedef struct oak_span_u8 {
  u8* base;
  u32 len;
} oak_span_u8;
```

Uart type and its `read` method (simplified):

```c
typedef struct oak_Uart {
  /* hardware registers, etc. */
  void* regs;
} oak_Uart;

oak_Result_u32_Error oak_Uart_read( oak_Uart* self, oak_span_u8 buf );
```

### 10.3 Generated `read_exact` specialization

The monomorphized function for `Uart` is:

```c
oak_Result_u32_Error oak_read_exact_Uart( oak_Uart* reader, oak_span_u8 buf ) {
  oak_Result_u32_Error res = oak_Uart_read( reader, buf );

  switch ( res.tag ) {
    case oak_Result_u32_Error_tag_Ok: {
      u32 n = res.payload.Ok;

      /* inner Bool match: (n == buf.len) ? ... */
      if ( n == buf.len ) {
        return oak_Result_u32_Error_Ok( n );
      } else {
        return oak_Result_u32_Error_Err( oak_Error_ShortRead() );
      }
    } break;

    case oak_Result_u32_Error_tag_Err: {
      oak_Error e = res.payload.Err;
      return oak_Result_u32_Error_Err( e );
    } break;
  }
}
```

Notes:

* The outer `res ?` becomes `switch ( res.tag ) { ... }`.
* The `.Ok(n)` arm binds `n` from `res.payload.Ok`.
* The inner `(n == buf.len) ?` becomes a simple `if`:

  * `True` branch returns `Ok(n)` via the constructor.
  * `False` branch returns `Err(ShortRead)`.
* The `.Err(e)` arm simply propagates the error using the `Err` constructor.

The resulting C is clear, idiomatic, and straightforward to step through in a debugger.

---

## 11. Packages and Files

For each Oak package `pkg`:

* Emit `oak_pkg.h` and `oak_pkg.c`.
* Exported Oak symbols are mapped to C identifiers like `oak_pkg_Name`.
* `package main` becomes a special case:

  * For hosted environments: generate a C `int main( void )` that calls Oak's `main`.
  * For freestanding MCUs: generate an `oak_main( void )` entry and leave integration to the build system/startup code.

Example:

Oak:

```oak
package http

Status: type = ...

fn FromCode( code: u16 ) -> Status
  ...

fn ToString( status: Status ) -> string
  ...
```

C headers (simplified):

```c
/* oak_http.h */

#ifndef OAK_HTTP_H
#define OAK_HTTP_H

#include "oak_core.h"

/* Forward/type definitions for Status, string, etc. */

Status oak_http_FromCode( u16 code );
string oak_http_ToString( Status status );

#endif /* OAK_HTTP_H */
```

Implementation:

```c
/* oak_http.c */

#include "oak_http.h"

Status oak_http_FromCode( u16 code ) {
  /* ... */
}

string oak_http_ToString( Status status ) {
  /* ... */
}
```

---

## 12. Documentation Comments and Debuggability

To support better integration with IDEs, debuggers, and documentation tools, the C backend MUST emit structured comments for public functions and types.

### 12.1 Comment style

* Use Doxygen-compatible block comments immediately preceding declarations:

```c
/**
 * @brief Read exactly buf.len bytes from reader.
 *
 * @param reader Concrete reader instance (e.g. UART handle).
 * @param buf    Span over destination buffer (base pointer and length).
 * @return oak_Result_u32_Error
 *         - Ok(n)   when n == buf.len
 *         - Err(e)  on error or short read
 */
oak_Result_u32_Error oak_read_exact_Uart( oak_Uart* reader, oak_span_u8 buf ) {
  /* ... */
}
```

* For types (structs, enums, typedefs), emit a short `@brief` comment summarizing purpose.

```c
/**
 * @brief Result of operations returning either a u32 value or an Error.
 */
typedef struct oak_Result_u32_Error {
  oak_Result_u32_Error_tag tag;
  union {
    u32       Ok;
    oak_Error Err;
  } payload;
} oak_Result_u32_Error;
```

### 12.2 Mapping Oak docs to C comments

* Oak doc comments (line comments immediately preceding declarations) are propagated into the generated Doxygen block where possible.
* When Oak docs do not exist, the backend emits a minimal, auto-generated comment:

  * `@brief` derived from the symbol name and kind (e.g. "Oak function read_exact_Uart").
  * `@param` entries for each parameter with at least the parameter name and type.
  * `@return` entry for non-`void` functions.

Example for a function without explicit Oak docs:

```c
/**
 * @brief Oak function oak_status_code.
 *
 * @param res  Result[u8, Error] value to convert.
 * @return u8  Status code derived from res.
 */
u8 oak_status_code( oak_Result_u8_Error res ) {
  /* ... */
}
```

* The backend should err on the side of generating comments, even if minimal, so that all public-facing symbols are documented and easy to navigate in tooling.

### 12.3 Debuggability considerations

* Generated symbol names must be stable and predictable so debuggers (and humans) can correlate Oak functions to C frames.
* Comments should clearly describe:

  * Ownership/borrowing semantics for pointers and spans where non-obvious.
  * Units (e.g. bytes, milliseconds) for numeric parameters and return values.
* Where Oak code is inlined or specialized (e.g. generics), the backend should indicate the original Oak function and type parameters in the `@brief` text when useful.

---

## 13. Status and Future Work

This backend spec intentionally focuses on:

* Type representations (primitives, strings, arrays, views/spans, ADTs).
* Pattern matching lowering.
* Naming and file layout.
* Style constraints for generated C.

Still to be fully specified:

* Exact mapping of Oak `string` APIs to C helpers.
* FFI surface (`extern "C" fn` in Oak → C signatures).
* Mapping of Oak interfaces and generic constraints to C (beyond monomorphized examples).
* Support code for panics, asserts, and fatal errors in freestanding environments.

The guiding principle remains: **every Oak construct must lower to clean, unsurprising C that an embedded engineer can read, reason about, and debug without needing to understand Oak.**

