# UTF-16 and UTF-32 String Encoding Support

This document describes the implementation of UTF-16 and UTF-32 string encoding support in Oak, building on the canonical UTF-8 string system.

## Overview

The string encoding system has been generalized to support:
- **Different code unit widths**: `u8`, `u16`, `u32`/`rune`
- **Multiple encoding tags**: `Utf8`, `Ascii`, `Utf16`, `Utf32`
- **Fixed-width string forms**: `utf16_string`, `rune_string`

## Core Types

### Primitive Types

```oak
StrViewUnit[E, Unit]: type = {
    units: []Unit
}

StrBufUnit[E, Unit]: type = {
    units: [*]Unit
}
```

These are the fundamental types that support any encoding tag `E` and any code unit type `Unit`.

### Byte-Based Specializations

```oak
StrView[E]: type = StrViewUnit[E, u8]
StrBuf[E]: type = StrBufUnit[E, u8]
```

These provide the familiar byte-based string types for UTF-8 and ASCII.

### Wide String Types

```oak
rune: type = u32

utf16_string: type = StrViewUnit[Utf16, u16]
utf16_string_buf: type = StrBufUnit[Utf16, u16]

rune_string: type = StrViewUnit[Utf32, rune]
rune_string_buf: type = StrBufUnit[Utf32, rune]
```

## Key Design Principles

1. **Canonical UTF-8**: `string` remains `StrViewUnit[Utf8, u8]`
2. **No runtime overhead**: All string types are thin records over slices/spans
3. **Borrow semantics unchanged**: Still uses `[]Unit` / `[*]Unit` under the hood
4. **User-extensible**: Libraries can define new encoding tags

## Packages

### `package strings`

Core string types and utilities:
- Encoding tags: `Utf8`, `Ascii`, `Utf16`, `Utf32`
- Generic types: `StrViewUnit[E, Unit]`, `StrBufUnit[E, Unit]`
- Type aliases: `string`, `utf16_string`, `rune_string`
- Core utilities: `len_units`, `as_units`, `into`, `buf_from_span`, `view_from_buf`
- Writer abstraction: `Writer[E]` for encoding-tagged IO

### `package encoding/utf16`

UTF-16 specific operations:
- Conversion: `from_string`, `to_string`, `to_runes`, `from_runes`
- Code-unit operations: `len_units`, `unit_at`, `slice_units`
- Scalar-aware operations: `len_runes`, `rune_at`
- IO encoding: `Utf16LE`, `Utf16BE`, `encode_le`, `encode_be`, `write_le`, `write_be`

### `package encoding/utf32`

UTF-32/rune string operations:
- Conversion: `from_string`, `to_string`, `from_utf16`, `to_utf16`
- Scalar operations: `len_runes`, `at`, `slice`

## Implementation Status

### Completed

- ✅ Updated `strings.oak` with generalized `StrViewUnit` and `StrBufUnit` types
- ✅ Added UTF-16 and UTF-32 encoding tags
- ✅ Created `encoding/utf16.oak` package
- ✅ Created `encoding/utf32.oak` package
- ✅ Added parser support for multi-parameter generics (nested `IndexExpression`)

### Pending

- ⚠️ Parser routing for `Name: type = ...` syntax (blocking parsing)
- ⚠️ Type system support for `StrViewUnit[E, Unit]` and `StrBufUnit[E, Unit]`
- ⚠️ Type checker support for generic type applications with multiple parameters
- ⚠️ Codegen for UTF-16 and UTF-32 string types
- ⚠️ Borrow checker integration (should work automatically via underlying slices/spans)

## Parser Issues

The parser currently has issues with:
1. **Type definition routing**: `Name: type = ...` syntax isn't being routed to `parseADTType()` correctly
2. **Multi-parameter generics**: While the code supports nested `IndexExpression` for `StrViewUnit[E, Unit]`, the parsing may need refinement

## Next Steps

1. Fix parser routing for `Name: type = ...` syntax
2. Add type system support for multi-parameter generic types
3. Implement type checking for `StrViewUnit[E, Unit]` and related types
4. Add codegen support for UTF-16 and UTF-32 string types
5. Test the full encoding conversion pipeline

## Files

- `/examples/strings/strings.oak` - Core string types and utilities
- `/examples/strings/encoding/utf16.oak` - UTF-16 encoding operations
- `/examples/strings/encoding/utf32.oak` - UTF-32/rune string operations
- `/examples/strings/encoding/utf8.oak` - UTF-8 encoding operations (existing)
- `/examples/strings/encoding/ascii.oak` - ASCII encoding operations (existing)
