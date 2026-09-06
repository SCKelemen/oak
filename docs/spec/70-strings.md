# Strings and Text Encodings

Oak treats text encoding as a semantic type distinction over explicit borrowed storage.

## 1. Bytes are not text

Arbitrary bytes are not automatically valid text.

```oak
[]u8
```

is a read-only byte view.

A UTF-8 string is conceptually:

```oak
Str[Utf8]
```

with an invariant that the referenced code units are valid for the declared encoding.

`string` is the canonical alias for validated UTF-8 text:

```oak
string: type = Str[Utf8]
```

This may have the same machine representation as `[]u8`, but it is not semantically interchangeable with arbitrary bytes.

## 2. Representation

An immutable encoded string view contains non-owning storage plus length. A mutable text buffer contains writable borrowed storage plus length.

Conceptually:

```oak
Str[E, Unit]: type = {
  units: []Unit
}

StrBuf[E, Unit]: type = {
  units: [*]Unit
}
```

Convenience aliases may fix the code-unit type for known encodings.

Examples:

```text
UTF-8 / ASCII  -> u8 code units
UTF-16         -> u16 code units
UTF-32         -> u32/rune code units
```

Encoding and code-unit type are semantic/representation parameters; there is no hidden allocation or runtime encoding object.

## 3. Phantom encoding identity

Encoding tags are zero-runtime semantic types when no runtime data is required.

```oak
Utf8: type = {}
Utf16: type = {}
Ascii: type = {}
```

The type checker distinguishes `Str[Utf8]` from `Str[Ascii]` even when both use byte storage.

Libraries may define additional encoding tags.

## 4. Validation

Converting arbitrary bytes/code units to validated text is a fallible operation unless validity is already proved by context.

Conceptually:

```oak
fn validate[E](units: []CodeUnit[E]): Result[Str[E], EncodingError]
```

A safe API must not expose:

```oak
fn from_bytes[E](b: []u8): Str[E]
```

without either validation or a proof/unsafe precondition.

When external protocol guarantees establish validity, an explicit unsafe/proof-bearing conversion may exist.

## 5. Borrowing

A string view preserves the provenance/lifetime of its underlying view. Wrapping bytes as text does not extend storage lifetime.

A mutable `StrBuf` follows the same unique-write rules as its underlying span.

No string-specific aliasing escape hatch exists.

## 6. Conversion

Re-encoding may require new storage because the output can differ in code-unit width/length.

Therefore allocation is never hidden.

Preferred forms are caller-provided or explicit allocator APIs:

```oak
fn recode[E, F](dst: [*]CodeUnit[F], src: Str[E]): Result[Str[F], Error]
```

or an explicitly allocator/effect-bearing variant.

Conversions that are representation-preserving and validity-preserving may be zero-copy.

## 7. Indexing

String indexing semantics must distinguish:

- code-unit index;
- Unicode scalar/rune index;
- grapheme-cluster index.

Oak must not pretend these are the same operation.

Low-level encoded strings should expose code-unit operations explicitly. Scalar/grapheme iteration belongs to encoding/Unicode libraries and may have different complexity.

A generic `len` or indexing operator should not hide an O(n) scan where programmers expect O(1) code-unit access.

## 8. Literals

Ordinary source string literals are UTF-8 semantic strings after the source decoder validates them. This is enforced: compilation validates the entire source file against the well-formed byte sequences of `Oak.Utf8Validity` (Unicode Table 3-7) before scanning, via `source.ValidateUTF8`, so no literal can carry invalid bytes into `string` values. Runtime byte validation exists as `is_valid_utf8(v: []u8) -> Bool`, a zero-allocation builtin lowered to a C helper transliterating the same brackets — one fact, three projections (Lean model, Go ingestion validator, C runtime).

The compiler may emit their bytes in readonly static storage.

Other encoding literals should be compile-time conversions/projections when possible rather than runtime allocation.

## 9. Canonical `rune`

A Unicode scalar value should use an unsigned value domain capable of representing Unicode scalar values; exact alias (`u32` vs a refined `u32`) should be specified explicitly rather than inheriting older conflicting `i32`/`u32` notes.

The preferred semantic model is a refined scalar type excluding surrogate code points and values above `0x10FFFF`, with `u32` representation.

## 10. Writer/reader APIs

Encoding-specific I/O should use ordinary generic constraints/types rather than special syntax.

A writer that accepts `Str[E]` is explicit about its input encoding. Transcoding is a separate operation/effect when needed.

## 11. Formal verification targets

Initial proof targets:

- validated `Str[E]` construction implies the encoding validity predicate;
- zero-copy retyping is allowed only when representation and validity implications hold;
- slicing preserves borrow provenance;
- UTF-8 decoding never reads beyond the input span;
- successful decode consumes a valid code-unit sequence and returns a valid scalar;
- UTF-16 surrogate-pair rules are respected;
- encoding conversion never writes beyond destination capacity;
- reported output length equals produced code units.

Encoding algorithm proofs can be added independently of the language type-system proofs and then connected through refinement tests.