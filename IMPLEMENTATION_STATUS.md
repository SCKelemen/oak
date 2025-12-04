# Oak Language Implementation Status

## Overview

This document tracks the implementation progress of the Oak programming language, a MCU-friendly language designed to compile to simple C.

## Completed ✅

### 1. Language Specification
- ✅ Complete specification document (`SPEC.md`)
- ✅ ADT literal tags design documented
- ✅ Ownership, slices, and spans design documented
- ✅ Error handling, unsafe blocks, and compile-time evaluation sections

### 2. Token System
- ✅ Extended token definitions for new syntax:
  - `STRING` - string literals
  - `QMARK` - pattern matching operator `?`
  - `ARROW` - pattern matching arrow `->`
  - `PACKAGE`, `IMPORT`, `WHILE`, `UNSAFE`, `FN` keywords

### 3. Scanner/Lexer
- ✅ String literal parsing
- ✅ `?` token recognition
- ✅ `->` token recognition (handles `-` followed by `>`)
- ✅ All new keywords recognized

### 4. AST Extensions
- ✅ `StringLiteral` - string literal expressions
- ✅ `MatchExpression` - pattern matching with `?`
- ✅ `MatchArm` - pattern matching arms
- ✅ Pattern types:
  - `WildcardPattern` - `_`
  - `BindingPattern` - variable binding
  - `LiteralPattern` - literal values
  - `VariantPattern` - ADT variants (`.Ok`, `.Some(x)`)
- ✅ `ADTType` - ADT type definitions
- ✅ `ADTVariant` - ADT variant definitions with optional literal tags
- ✅ `PackageStatement` - package declarations
- ✅ `ImportStatement` - import statements
- ✅ `FunctionStatement` - top-level function declarations
- ✅ `FunctionParameter` - function parameters
- ✅ `WhileStatement` - while loops
- ✅ `UnsafeBlock` - unsafe blocks

## In Progress 🚧

### 5. Parser
- ✅ ADT type parsing
- ✅ Pattern matching expression parsing
- ✅ Function declaration parsing (new `fn` syntax)
- ✅ Package and import parsing
- ✅ While loop parsing
- ✅ Unsafe block parsing
- ✅ Record literal parsing
- ✅ Array literal parsing
- ⏳ Complex type expression parsing (array types, record types in annotations)

## Pending 📋

### 6. Type System
- ✅ Type checker implementation
- ✅ ADT type checking
- ✅ Pattern matching exhaustiveness checking
- ✅ Type inference for locals
- ✅ Type narrowing for ADT literal tags (TypeScript-style)
- ✅ Record type definition checking
- ✅ Intersection types for interfaces
- ✅ Enhanced type expression parsing (arrays, records, intersections)
- ⏳ Generic type support (`Option[T]`, `Result[T, E]`)
- ⏳ Interface type checking (structural typing)
- ⏳ Method lookup and interface implementation checking

### 7. Evaluator
- ✅ Arithmetic operations (`+`, `-`, `*`, `/`)
- ✅ Comparisons (`==`, `!=`, `<`, `>`)
- ✅ Pattern matching evaluation
- ✅ Function calls
- ✅ Variable bindings (declarations and assignments)
- ✅ ADT construction and matching
- ✅ Record literal evaluation
- ✅ Array literal evaluation
- ✅ Field access (record.field)
- ✅ Array indexing (array[index])

### 8. Borrow Checker
- ⏳ Slice/span alias analysis
- ⏳ Borrow rule enforcement (many readers OR one writer)
- ⏳ Bounds checking for array/slice access

### 9. Code Generation
- ⏳ C code generation
- ⏳ ADT lowering to C enums/structs
- ⏳ Pattern matching lowering to switch statements
- ⏳ Function lowering
- ⏳ Slice/span lowering to C structs

### 10. Standard Library
- ⏳ Core types (`Option`, `Result`, `Bool`)
- ⏳ Slice operations (`get`, `try_slice`, `len`)
- ⏳ Built-in functions (`zero_init`, `sizeof`)

## Test Files

- `test_examples.oak` - Example Oak programs for testing

## Next Steps

1. **Implement Parser** - Extend parser to handle new AST nodes
2. **Basic Type System** - Start with primitive types and ADTs
3. **Expression Evaluator** - Implement arithmetic and pattern matching
4. **Test Suite** - Create comprehensive test cases

## Architecture Notes

The implementation follows a traditional compiler pipeline:

```
Source Code
    ↓
Scanner (Lexer) ✅
    ↓
Parser ✅ (most features)
    ↓
AST ✅
    ↓
Type Checker ✅ (core features)
    ↓
Evaluator ✅ (core features)
    ↓
Code Generator ⏳
    ↓
C Output
```

## Design Decisions

1. **Expression-oriented**: Everything is an expression, no separate statements
2. **Pattern matching first**: No `if` statements, use `?` pattern matching
3. **Simple borrow checker**: Local analysis only, no explicit lifetimes
4. **MCU-focused**: Zero-cost abstractions, no hidden allocations
5. **Go-like compile times**: Simple type system, no macros, no CTFE beyond constants

