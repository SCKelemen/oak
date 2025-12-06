# Strings Encoding System Integration

## Overview

This document describes how the strings encoding system integrates with Oak's existing borrow checker, view/span system, and type system.

## Integration with View/Span System

### String Construction from Arrays

The `strings.string_from_utf8` function is conceptually a thin wrapper around `view_as`:

```oak
fn string_from_utf8(bytes: []u8) -> string =
    // Conceptually: view_as[string](bytes)
    // But since string = Str[utf8] = { bytes: []u8 },
    // this is just wrapping the slice
    { bytes: bytes }
```

### String Buffers from Spans

The `strings.buf_from_span` function wraps existing spans:

```oak
fn buf_from_span[E: Encoding](span: [*]u8) -> StrBuf[E] =
    // This is essentially a reinterpret cast of a span
    // Conceptually: span_as[StrBuf[E]](span)
    // But StrBuf[E] = { bytes: [*]u8 }, so it's just wrapping
    { bytes: span }
```

### Example: Creating String from Array

```oak
// User owns a buffer
buf: [1024]u8 = zero_init()

// Create a view of the first 64 bytes
view: []u8 = buf[0:64]

// Wrap as a UTF-8 string (no copy, just type-level reinterpret)
msg: string = strings.string_from_utf8(view)

// Or directly from the array slice
msg2: string = strings.string_from_utf8(buf[0:64])
```

### Example: Mutable String Buffer

```oak
// User owns a buffer
buf: [1024]u8 = zero_init()

// Create a mutable span
span: [*]u8 = span(&buf[0:64])

// Wrap as a mutable string buffer
str_buf: string_buf = strings.buf_from_span[utf8](span)

// Now can modify through str_buf, which modifies buf
// (implementation would provide mutation APIs)
```

## Borrow Checker Integration

### Str[E] as Views

- `Str[E]` contains `bytes: []u8` (read-only view)
- Borrow checker treats this as a regular `[]u8` view
- No special borrow rules needed - follows standard view rules

### StrBuf[E] as Spans

- `StrBuf[E]` contains `bytes: [*]u8` (mutable span)
- Borrow checker treats this as a regular `[*]u8` span
- Follows standard span rules (unique write, region disjointness)

### Example Borrow Checker Behavior

```oak
buf: [1024]u8 = zero_init()

// Create string view (creates a view borrow)
msg: string = strings.string_from_utf8(buf[0:64])
// borrow checker: buf has SharedRead state

// Try to create mutable buffer (should fail - view exists)
str_buf: string_buf = strings.buf_from_span[utf8](span(&buf[0:64]))
// borrow checker: ERROR - cannot create span while view exists

// After msg goes out of scope, buf returns to Free
// Then str_buf creation would be allowed
```

## Type System Integration

### Current State

- `StringType` exists as a simple type
- Generic types (`Str[E]`, `StrBuf[E]`) require full generics support
- Encoding tags require type-level values

### Required Implementation

1. **Encoding Type**
   - Add `EncodingType` to type system (zero-size marker)
   - Similar to `UnitType` but for encoding tags

2. **Generic String Types**
   - `StrType[E]` - parameterized by encoding
   - `StrBufType[E]` - parameterized by encoding
   - Type aliases: `string = StrType[utf8]`

3. **Type Constraints**
   - `E: Encoding` constraint checking
   - Ensure encoding parameters satisfy Encoding constraint

4. **Parser Support**
   - Generic type syntax: `Str[E]`, `StrBuf[E]`
   - Generic function syntax: `fn write[E: Encoding](...)`
   - Type constraint syntax: `E: Encoding`

## Code Generation Integration

### String Literals

Current: String literals are hoisted to static arrays.

With encoding system:
- String literals are UTF-8 by default
- Can be reinterpreted to other encodings at compile time if possible
- Runtime conversion for incompatible encodings

### String Types in C

```c
// Str[utf8] / string
typedef struct {
    u8* data;  // points to []u8.data
    u32 len;   // length in bytes
} oak_string;

// StrBuf[utf8] / string_buf
typedef struct {
    u8* data;  // points to [*]u8.base
    u32 len;   // length in bytes
} oak_string_buf;
```

### Encoding Tags

Encoding tags are compile-time only (phantom types):
- No runtime representation
- Used only for type checking and function dispatch
- Zero overhead in generated C

## Migration Path

### Phase 1: Foundation (Current)
- ✅ Design specification
- ✅ Package structure
- ⏳ Type system support (requires generics)

### Phase 2: Basic Support
- Parser: Generic type syntax
- Type checker: Encoding types and constraints
- Codegen: String type emission

### Phase 3: Full Integration
- Borrow checker: Recognize Str/StrBuf types
- Lowering: Connect to view_as/span_as
- Standard library: Implement encoding packages

## Example: Full Integration

```oak
// User code
buf: [1024]u8 = zero_init()

// Create string view (borrow checker sees []u8 view)
msg: string = strings.string_from_utf8(buf[0:64])

// Use encoding-tagged function
strings.write[ascii](ascii_writer, msg)

// After msg scope ends, can create mutable buffer
{
    span: [*]u8 = span(&buf[0:64])
    str_buf: string_buf = strings.buf_from_span[utf8](span)
    // Modify through str_buf...
}
```

## Next Steps

1. **Parser**: Add generic syntax support
2. **Type System**: Add Encoding type and generic string types
3. **Type Checker**: Implement constraint checking
4. **Codegen**: Emit string types correctly
5. **Borrow Checker**: Recognize string types (already works via []u8 / [*]u8)
6. **Lowering**: Connect string construction to view_as/span_as
