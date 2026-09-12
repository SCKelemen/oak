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

The runtime validator behind `is_valid_utf8` and `str_from_utf8` is, in
every module build, the standard library's `utf8.valid` (`93-simd.md`
§1.5): the Keiser–Lemire lookup validator written in Oak over the portable
vectors, sixty-four bytes a step, at simdutf's speed. It is used on a
proof, not a test: `Oak.Utf8Blocks.program_valid` states that the program
as written — blocks shifted against their predecessors, the
sixty-four-byte step, both ASCII shortcuts, the zero-padded tail — accepts
exactly the byte lists that are `Oak.Utf8Validity.Valid`, the Table 3-7
model this section's guarantees rest on. A program that reaches either
spelling loads `utf8` implicitly (`compiler/modules.go`), and the runtime
helper `oak_is_valid_utf8` is a call to the compiled validator. A bare
source build has no packages and keeps the scalar C transliteration of
the same brackets; the interpreter's builtin stays scalar as the
reference the differential tests run against.

### 4a. Error positions

A validator that only answers `Bool` cannot say where; the position is
what a negative test asserts and what a user is shown. The text library
reports it as a typed value, never as a count whose meaning flips on error
(the checklist's rule against in-band sentinels):

- `strings.utf8_first_error_at(src, start): u32` is the offset of the first
  ill-formed byte at or after `start` — the lead of the sequence that
  fails: truncated, overlong, a surrogate, above U+10FFFF, or a stray
  continuation — or `len(src)` when the bytes from `start` on are
  well-formed. `utf8_first_error(src)` starts at zero. Both are total and
  walk the bounds-checked scalar decoder one sequence at a time.
- `strings.utf8_check(src): Result[u32, TextFault]` is the scalar count on
  success and, on failure, `TextFault { error: .InvalidEncoding, at }`.
  `TextFault` pairs a `TextError` with the offset it was detected at.
- `utf8.locate(bytes): u32` (`93-simd.md` §1.5) is the vector twin of
  `utf8_first_error`: it rejects fast, step by step, and locates slow — the
  first step whose error lanes are nonzero hands over to the scalar decoder
  from a sequence boundary just before it. It agrees with
  `utf8_first_error` byte for byte, which the differential tests check
  under both lowerings against a third, independent scalar oracle;
  `utf8.valid` stays the fast path when only the verdict is wanted.

The position is the first ill-formed byte in Unicode's sense (Table 3-7,
maximal subparts): the lead of the failing sequence, not the byte inside
it that failed to continue it. Go's `utf8.DecodeRune` reports the same
offset, which is how the differential test computes its expectation.

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

Ordinary source string literals are UTF-8 semantic strings after the source decoder validates them. This is enforced: compilation validates the entire source file against the well-formed byte sequences of `Oak.Utf8Validity` (Unicode Table 3-7) before scanning, via `source.ValidateUTF8`, so no literal can carry invalid bytes into `string` values. Runtime byte validation exists as `is_valid_utf8(v: []u8) -> Bool`, a zero-allocation builtin. In a module build it lowers to the standard library's `utf8.valid` (`93-simd.md` §1.5), the same predicate over the portable vectors at simdutf's speed, whose program is proved to accept exactly the valid streams of `Oak.Utf8Validity` (`Oak.Utf8Blocks.program_valid`); a program that reaches the builtin, or `str_from_utf8`, loads `utf8` implicitly. A bare source build keeps a C helper transliterating the same brackets — one fact, three projections (Lean model, Go ingestion validator, C runtime).

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


## 12. Executable bootstrap library

The current `import(std)` text implementation is documented in
[`stdlib/STRINGS.md`](../../stdlib/STRINGS.md). It operates on explicitly borrowed
code-unit views and uses fallible validation/transcoding plus caller-owned output
spans. UTF-8 read helpers validate and trap on invalid bytes; their fallible input
boundary counterparts report `TextError`. `text_literal` constructs static UTF-8
byte storage through ordinary borrowing. It is not a runtime `[]u8 -> Str[Utf8]`
cast and does not expose a representation-preserving validity bypass. It
performs no escape processing of its own: the scanner has already decoded the
literal's escape sequences (`10-syntax.md` §2a), so `text_literal("a\n")` is
two bytes, and the same holds for every string literal in every position.

Unicode default full case conversion/folding is pinned to Unicode 17.0.0. Byte
search results, scalar search results and grapheme counts remain explicitly
distinct. Scalar-boundary slicing returns ranges whose actual views are created
by the caller. No normalization, collation, grapheme segmentation, locale tailoring
or hidden allocator is implied. General encoding-polymorphic `Str[E]` and writer
interfaces above remain target interfaces.

Binary-to-text codecs — hexadecimal, RFC 4648 base64 and base32, RFC 3986
percent-encoding — live in the `encoding` package (`stdlib/encoding.oak`,
`import("encoding")`, also in the flat prelude) on the same contract: borrowed
byte views in, caller-owned spans out, `Result[u32, EncodingError]` with the
count written, `_size` functions that validate without writing, and strict
decoders that reject unknown symbols, wrong lengths, misplaced padding and
non-canonical trailing bits. They operate on bytes, not on `Str[E]`; text
validity of the decoded bytes is the caller's separate step.

## 13. Scoped runtime UTF-8 views

`str_from_utf8(named_view)` validates a read-only `[]u8` and returns a borrowed
`string` (`Str[Utf8]`) over the same bytes. Invalid input traps; callers needing
recoverable validation use `is_valid_utf8` before construction. `str_bytes` maps a
named UTF-8 string or literal back to a read-only byte view in constant time.
Both results require explicit new bindings. Neither operation allocates, copies
bytes, or appends a terminator. Other encoding tags are rejected by `str_bytes`.

The borrow checker tracks the owner and region across view/string aliases and
parameters. String rebinding, unproved borrow returns, and storage in aggregates
are rejected. Direct literal-string returns remain legal because their data has
static lifetime. No region-aware aggregate or closure capture support is implied.
The executable restrictions and examples are in `stdlib/STRINGS.md`.

