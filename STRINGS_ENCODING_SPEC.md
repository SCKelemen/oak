# Strings Encoding System Specification

## Overview

This document specifies the string encoding system for Oak, which treats encodings as first-class, extensible type-level capabilities.

## Core Design Principles

1. **Encoding as a capability kind**: `strings.Encoding` is a base type that can be extended
2. **Immutable strings by default**: `string` (UTF-8) is the canonical immutable representation
3. **Mutable strings as explicit buffers**: `StrBuf[E]` represents borrowed mutable views
4. **Tag-based APIs**: Functions use encoding tags as type parameters: `write[ascii](val: string)`
5. **Extensibility**: Libraries can define new encodings using the same pattern

## Type System

### Base Encoding Type

```oak
package strings

Encoding: type = {}
```

This is a zero-size marker type (like `Unit`) that serves as the base kind for all encodings.

### Built-in Encodings

```oak
utf8: Encoding = {}
ascii: Encoding = {}
utf16: Encoding = {}
utf32: Encoding = {}
```

These are pure, zero-size marker types that extend `strings.Encoding`.

### Generic String Types

```oak
// Immutable string view in encoding E
Str[E: Encoding]: type = {
    bytes: []u8
}

// Mutable string buffer (borrowed span) in encoding E
StrBuf[E: Encoding]: type = {
    bytes: [*]u8
}
```

### Type Aliases

```oak
// Canonical UTF-8 string (the default)
string: type = Str[utf8]

// Named variants for protocols
ascii_string: type = Str[ascii]

// Mutable buffers
string_buf: type = StrBuf[utf8]
ascii_buf: type = StrBuf[ascii]
```

## Function APIs

### Encoding-Tagged Functions

Functions can quantify over encodings:

```oak
fn write[E: Encoding](val: string) -> () {
    // E is the target encoding
    // Convert val (utf8) to bytes in encoding E
    // Push to some E-specific sink
}
```

Usage:
```oak
write[ascii](msg)   // converts utf8 -> ascii and writes
write[utf8](msg)    // writes utf8 directly
```

### Transformation Functions

```oak
// Convert canonical utf8 string into an E-encoded view
fn into[E: Encoding](s: string) -> Str[E]

// Parse bytes as E-encoded text
fn from_bytes[E: Encoding](b: []u8) -> Str[E]

// Recode between encodings
fn recode[E: Encoding, F: Encoding](s: Str[E]) -> Str[F]
```

## Extensibility

Libraries can define new encodings:

```oak
package encoding/shiftjis

import strings

shiftjis: strings.Encoding = {}

ShiftJisStr: type = strings.Str[shiftjis]

fn to_shiftjis(s: string) -> ShiftJisStr {
    strings.into[shiftjis](s)
}
```

## Implementation Requirements

### Type System Support

1. **Encoding type**: Zero-size marker type (like `Unit`)
2. **Generic types**: `Str[E]` and `StrBuf[E]` with encoding parameter
3. **Type constraints**: `E: Encoding` constraint in generics
4. **Type aliases**: `string = Str[utf8]` support

### Parser Support

1. Generic type syntax: `Str[E]`, `StrBuf[E]`
2. Type constraint syntax: `E: Encoding`
3. Generic function syntax: `fn write[E: Encoding](...)`
4. Encoding instances: `utf8: Encoding = {}`

### Type Checker Support

1. Encoding type checking
2. Generic type instantiation with encoding parameters
3. Constraint checking for encoding bounds
4. Type alias resolution

### Code Generator Support

1. Encoding-aware string emission
2. Encoding conversion functions
3. Generic function specialization

## Current Status

- ✅ Design specification complete
- ✅ Example code created
- ⏳ Type system implementation (requires generics)
- ⏳ Parser support (requires generic syntax)
- ⏳ Type checker support (requires constraint checking)
- ⏳ Code generator support

## Next Steps

1. Implement generic type syntax in parser
2. Add encoding types to type system
3. Implement constraint checking for encodings
4. Update code generator for encoding-aware strings
5. Create standard library `strings` package
