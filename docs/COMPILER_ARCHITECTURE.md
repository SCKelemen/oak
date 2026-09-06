# Oak Compiler Architecture

The compiler follows Oak's language priorities in order:

1. **Correctness**
2. **Performance**
3. **Simplicity**

Safety and ergonomics constrain all three. Internal convenience must not discard semantic or source information that later phases need to be correct.

## Source identity

Canonical source locations are half-open UTF-8 byte spans:

```text
SourceID + [ByteStart, ByteEnd)
```

Human/editor coordinates are projections from the owning source file, never the source of truth.

```text
byte span
  +-> path:line:column
  +-> vscode://file/...:line:column
  +-> LSP Range
  +-> source excerpt
```

Oak records editor columns in UTF-16 code units because LSP and VS Code use UTF-16 positions. Tokens also retain UTF-8 byte offsets so diagnostics, parsing, refactoring, and future incremental compilation do not confuse bytes with editor characters.

A span whose endpoint lands inside a UTF-8 code point is invalid.

Synthetic layout tokens are zero-width spans anchored at a real source position.

## Token pipeline

```text
SourceFile
   |
Scanner
   |
LayoutNormalizer
   |
token.Cursor
   |
Parser
```

`Scanner` and `LayoutNormalizer` preserve source identity through `token.LocatedSource`.

`token.Cursor` adds bounded-on-demand buffering for non-consuming lookahead. Parsing remains a forward pass; lookahead never re-lexes source or mutates parser state.

This exists primarily to make ambiguous prefixes mechanically safe. For example, `[N]T{...}` and `[x, y]` can be distinguished by inspection without consuming input and trying to reconstruct parser state afterward.

## One delimited sequence contract

All delimiter-contained sequences should converge on:

```go
parseDelimited[T](open, close, separator, allowTrailing, parseItem)
```

The invariant is:

```text
pre:    currentToken == open
success post: currentToken == close
```

`parseItem` starts on the first token of an item and leaves `currentToken` on the item's final token.

The same contract covers:

- invocation arguments;
- function parameters;
- type parameters;
- generic type arguments;
- array elements;
- other future comma-separated syntax.

Grammar-specific code decides *what an item is*. Cursor movement around delimiters and separators is shared.

## Ordered syntax

Source order is semantic input whenever representation, formatting, diagnostics, or tooling may depend on it.

Records therefore retain both:

```text
ordered field sequence   authoritative source order
field-name lookup map    fast compatibility lookup
```

The lookup map may never be used to reconstruct source order. A map-only legacy AST has unknown source order and semantic/layout projection must fail closed if order is required.

Preserving source order still does not imply that ABI field offsets are known. Size, alignment, padding, and offsets belong to a target-specific representation/layout pass.

## Allocation inside the host compiler

The Oak compiler is currently implemented in Go. We do not introduce custom host arenas/slabs merely to resemble generated Oak code. Host allocation strategy must be justified by profiles and measured compiler behavior.

This is separate from Oak-the-language, where allocation is explicit semantic behavior and hidden allocation is not permitted.
