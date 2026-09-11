# Strings and text

The executable strings library is included by `import(std)`. It is implemented
in `strings.oak` with generated Unicode 17.0.0 data in `unicode.oak`. The examples
under `examples/strings/` are executable programs, not package/module definitions.

## Storage and validity

Runtime input is an explicit borrowed `[]u8`, `[]u16`, or `[]u32`. These remain
code-unit views: no unchecked conversion to the compiler's semantic `string` or
`Str[E]` type is performed. UTF-8 reads validate their input and trap if invalid;
fallible transforms and codecs return `InvalidEncoding`. Use `utf8_validate` at
an external input boundary if a trap is not an appropriate error policy.

`text_literal("héllo")` is compile-time syntax available with `import(std)`. It
creates a view of UTF-8 bytes in static storage, with identical literals sharing
storage within a compilation. Nonliteral arguments and wrong arity are rejected.
It lowers through ordinary `view(&owner)` and does not relax borrowing rules.
The generated `__oak_text_literal_*` bindings and `unicode_*_table` bindings are
implementation storage and must not be mutated by application code.

All transforms write to caller-provided spans and return the number of code units
written. They validate input, ranges, overflow and destination capacity **before
writing**, so failure leaves the destination unchanged. Source and destination
must be disjoint under the ordinary borrow checker; overlapping in-place text
transforms are not this API's contract. NUL is an ordinary scalar/byte, never a
terminator. Output is not NUL-terminated.

Lengths, ranges and search positions are u32 code-unit offsets unless explicitly
stated otherwise. Text ranges are half-open byte offsets. They carry no borrow,
provenance, or validity proof: keep them paired with the unchanged source. Use a
source view slice such as `src[range.start:range.end]` to construct the actual
borrow. View/span slicing now uses bounds-checked C helpers; explicit operands
are evaluated once, and reversed or out-of-range bounds trap.

## Validation, scalars and transcoding

| API | Result / meaning |
| --- | --- |
| `unicode_is_scalar(value)` | Excludes surrogates and values above U+10FFFF |
| `utf8_validate(src)`, `utf16_validate(src)`, `utf32_validate(src)` | Complete strict validation |
| `utf8_count(src)`, `utf16_count(src)`, `utf32_count(src)` | `Result[u32, TextError]`, number of scalars |
| `utf8_decode(src, offset)` and corresponding UTF-16/32 functions | `TextScalar { value, next }`, next code-unit offset |
| `utf8_decode_previous(src, end)` | Scalar ending exactly at `end`; `next` is its starting byte offset |
| `utf8_encode(dst, offset, value)` and corresponding UTF-16/32 functions | Number of code units written |
| `utf8_to_utf16`, `utf8_to_utf32`, `utf16_to_utf8`, `utf16_to_utf32`, `utf32_to_utf8`, `utf32_to_utf16` | `(dst, src)`, complete checked conversion |
| Each transcoder's `_size(src)` function | Required destination code units, validates without writing |
| `ascii_to_utf8(dst, src)`, `utf8_to_ascii(dst, src)` | Strict ASCII validation plus copy; rejects non-ASCII |
| `text_is_ascii(src)` | Every byte below 128 |

Decoding validates exactly one scalar, without requiring the rest of the source
to be valid. Offset equal to length returns `Empty`; greater returns `OutOfBounds`.
UTF-8 rejects overlong forms, continuation starts, truncated sequences, surrogate
encodings and out-of-range scalars. UTF-16 rejects lone or mismatched surrogates.
UTF-32 validates every scalar. No BOM is inserted, removed or treated as a byte-
order instruction: U+FEFF is ordinary text. UTF-16/32 operate on native numeric
code units; endian wire decoding remains the separate `bytes_read/write_*` API.

`TextError` contains `InvalidEncoding`, `InvalidScalar`, `OutOfBounds`,
`DestinationTooSmall`, `SizeOverflow`, `EmptySeparator`, and `Empty`. Encoders
check scalar validity before destination bounds. Transcoders check input validity
and size before destination capacity. Sizing and transcoding are O(n); encoding
and single-scalar decoding are bounded constant work.

## Comparison, searching and ranges

| API | Semantics |
| --- | --- |
| `text_equal(a, b)`, `text_compare(a, b)` | UTF-8 byte equality / lexicographic -1, 0, 1 |
| `text_equal_ascii_fold(a, b)` | ASCII A–Z folding only; other UTF-8 bytes unchanged |
| `text_equal_fold(a, b)` | Streaming Unicode default full case-fold equality |
| `text_has_prefix`, `text_has_suffix`, `text_contains` | Valid UTF-8 substring matching |
| `text_index`, `text_last_index` | First/last byte offset as `Option[u32]` |
| `text_index_byte(src, value)` | Raw byte offset; it can point inside a multibyte scalar |
| `text_index_rune(src, value)` | **Scalar index**, not byte offset; invalid scalar traps |
| `text_contains_rune(src, value)` | Scalar membership |
| `text_slice_range(src, start, end)` | Checks UTF-8 validity, bounds and scalar boundaries |
| `text_trim_prefix`, `text_trim_suffix` | Remove one matching prefix/suffix, return `TextRange` |
| `text_trim_space(src)` | Trim Unicode White_Space |
| `text_trim(src, cutset)` | Trim any scalar appearing in the cutset |

An empty substring matches at zero for first search and at length for last
search, and is a prefix/suffix of every valid string. A trim removing everything
returns `[len, len)`. Cutsets are scalar sets, not byte sets. This prevents trimming
part of a multibyte encoding. Unicode whitespace follows the pinned UCD property;
zero-width space and BOM are not whitespace under this operation.

Search currently uses a straightforward bounded scan: worst-case O(n*m), with
constant extra space. Equality and byte comparison are O(n). Scalar search and
whitespace trimming are O(n); cutset trimming is O(n*m). Read operations include
input validation in these bounds. Iteration helpers currently validate the full
input per public call, so repeated split/fields calls can cost O(k*n). Internal
helpers such as `text_find_from`, `text_is_boundary`, `text_decoded` and
`text_fold_next` require their caller to establish the relevant validity/state
preconditions; use the public operations above at input boundaries.

## Byte order, UTF-16 as bytes, Latin-1, and numbers

| API | Contract |
| --- | --- |
| `text_bom(src)` | Leading mark: 0 none, 1 UTF-8, 2 UTF-16 LE, 3 UTF-16 BE, 4 UTF-32 LE, 5 UTF-32 BE (UTF-32 LE is checked before UTF-16 LE, whose mark it extends) |
| `text_bom_width(kind)`, `text_strip_bom(src)` | The mark's byte length; the `TextRange` after any mark |
| `utf16_bytes_decode(src, offset, big_endian)` | One scalar from UTF-16 stored as bytes; `next` is a byte offset; odd tails and lone surrogates reject |
| `utf16_bytes_to_utf8(dst, src, big_endian)`, `_size(src, big_endian)` | UTF-16 bytes in either byte order to UTF-8 |
| `utf8_to_utf16_bytes(dst, src, big_endian)`, `_size(src)` | UTF-8 to UTF-16 bytes in the requested byte order; no mark is written |
| `latin1_to_utf8(dst, src)`, `_size(src)` | ISO-8859-1 bytes to UTF-8 (every byte is the scalar of its value) |
| `utf8_to_latin1(dst, src)`, `_size(src)` | UTF-8 to ISO-8859-1; a scalar above U+00FF is `InvalidScalar` |
| `text_parse_i64(src, radix)` | Optional leading `-` or `+`, then `text_parse_u64`'s digits; the magnitude must fit the sign |
| `append_i64(builder, dst, value)` | Decimal with a leading `-` when negative |
| `append_u64_radix(builder, dst, value, radix, upper)` | Radix 2..36, letters for digits above 9 in the requested case; an invalid radix records `InvalidScalar` |

## Splitting and construction

| API | Contract |
| --- | --- |
| `text_split(dst, src, separator)` | Write ranges into `[*]TextRange`; return field count |
| `text_split_next(cursor, src, separator)` | Iterate ranges using zeroed `[1]TextSplitCursor` |
| `text_fields_next(cursor, src)` | Iterate nonempty Unicode-whitespace-separated ranges |
| `text_join(dst, src, parts, separator)` | Join selected `[]TextRange` ranges of one source |
| `text_copy(dst, src)` | Validated copy |
| `text_repeat(dst, src, count)` | Repetition with checked total size |
| `text_replace(dst, src, old, replacement)` | Replace all non-overlapping matches |

Split preserves empty fields, including empty input and trailing separators.
An empty separator or replacement search pattern returns `EmptySeparator`.
Replacement text itself may be empty. Join accepts arbitrary valid boundary
ranges of a single source, including empty/repeated ranges; build from unrelated
source views with `append_text` instead. Repeat with count zero or empty source
writes zero bytes. Clear/exhausted split state must not be reused with a different
source or separator without resetting it. `Empty` means iteration has ended;
fields iteration may advance to the end when reporting `Empty`.

Split, repeat, copy and join are linear in input/output size. Replacement inherits
O(n*m) substring scanning. Split/join ranges preserve UTF-8 scalar boundaries.
Overflow is detected before narrowing to u32; join sizing saturates above that
limit so adversarial numbers of ranges cannot wrap the accumulator.

## Unicode case conversion

`text_to_lower(dst, src)`, `text_to_upper(dst, src)`, and
`text_case_fold(dst, src)` apply Unicode **17.0.0** default full mappings, including
one-to-many expansions. Default lowercase handles the contextual Final_Sigma
rule, including Case_Ignorable characters. Locale-specific Turkish, Azeri and
Lithuanian tailoring is not selected. Default folding is non-Turkic; for example,
`Straße` and `STRASSE` compare equal, and `İ` folds to `i` plus combining dot.

`text_case_size(src, mode)` measures output bytes without writing; mode 0 is
lowercase, 1 uppercase, 2 folding. `text_to_lower_ascii` and
`text_to_upper_ascii` map only ASCII letters and preserve other UTF-8 bytes.

Case folding does not normalize text: canonically equivalent spellings are not
implicitly equal. Grapheme segmentation, normalization, collation, locale
selection and display-width computation are separate Unicode facilities and
are not claimed by the core strings API. Byte/scalar counts are not user-perceived
character counts.

`unicode17.json` contains the versioned UCD extract. `generate_unicode.py`
regenerates `unicode.oak` deterministically; CI checks it. Sources are UnicodeData,
unconditional SpecialCasing, C/F CaseFolding and the Cased/Case_Ignorable properties
from [Unicode 17.0 UCD](https://github.com/unicode-org/unicodetools/tree/main/unicodetools/data/ucd/17.0.0).
The Unicode license is included. Lookup is binary search over static numeric
tables (about 96 KiB before linker optimization); conversion and streaming folding
use constant working space and no heap allocation.

## Fluent text builder and numeric conversion

```oak
import(std)
main: (): i32 {
  storage: [32]u8
  dst: [*]u8 = span(&storage)
  builder: TextBuilder = text_builder().
    append_text(dst, text_literal("request=")).
    append_u64(dst, u64(42)).
    append_rune(dst, u32(10))
  assert(text_result_value(builder.finish_text()) == u32(11))
  42
}
```

`TextBuilder { length, status }` is an ordinary value record paired with the same
storage throughout a chain. Start with `text_builder()`. Each append either writes
its entire fragment or writes nothing; the first error is sticky and later calls
preserve both state and bytes. `finish_text()` returns the completed prefix length
or the first `TextError`. It does not return an escaping borrow. Do not forge the
builder length/status or modify its live prefix through an unrelated alias.

`append_text`, `append_rune`, `append_u64` and `finish_text` also have ordinary
free-function spellings. Fluent syntax lowers to those calls with each receiver
present once; it adds no dispatch, allocation or builder object on the heap.
Whether individual calls disappear is the target optimizer's decision.
`append_u64` uses at most 20 local bytes and handles zero and the maximum u64.

`text_parse_u64(src, radix)` accepts ASCII digits (case-insensitive A–Z) in bases
2–36. It consumes the entire input and accepts no sign, whitespace, separators
or radix prefix. It returns `Result[u64, TextParseError]` with `InvalidRadix`,
`InvalidDigit`, `NumberOverflow`, or `EmptyNumber`. Multiplication is checked
before it occurs. Signed/floating formatting and general format-string/I/O
frameworks are separate APIs, not implicit work done by this builder.

## Verification and compiler boundary

Tests round-trip every Unicode scalar through UTF-8 and UTF-16, compare all six
transcoding directions to Go encoding fixtures, check malformed input and unchanged
failed writes, compare substring operations with Go, and verify expansion/context
casing fixtures. Generated lookup tables are exercised over the complete scalar
range with expected checksums from the versioned data extract. Other tests cover
split/join, byte boundaries, zero capacity, embedded NUL, maximum integer values,
borrowed slices, literal rejection and sticky builder errors. All examples are
compiled and executed. Emitted builder C is checked for allocator calls.

The checked code-unit API interoperates with the scoped runtime UTF-8 string
conversions below. General encoding-polymorphic wrappers and writer interfaces
remain separate work.

## Runtime UTF-8 strings

The compiler provides two zero-copy, zero-allocation conversions:

| Operation | Result | Work |
| --- | --- | --- |
| `str_from_utf8(bytes)` | `string` / `Str[Utf8]` | Strict O(n) UTF-8 validation; traps on invalid input |
| `str_bytes(text)` | Read-only `[]u8` | O(1), same backing storage |

Bind the source and result explicitly. `str_from_utf8` accepts a named read-only
byte view, including a view parameter; it does not accept owned arrays, writable
spans, or temporary view expressions. `str_bytes` accepts a named string borrow
or a literal. Neither adds a terminator, copies bytes, or allocates backing
storage. Empty strings and embedded NUL are supported.

```oak
data: [2]u8
data[0] = u8(104)
data[1] = u8(105)
bytes: []u8 = view(&data)
text: string = str_from_utf8(bytes)
same_bytes: []u8 = str_bytes(text)
```

For recoverable invalid input, branch on `is_valid_utf8(bytes)` before calling
`str_from_utf8`. The constructor still checks validity; no unchecked cast or
proof of validity is inferred from the branch. Its validation is runtime work,
while wrapping and unwrapping only copy the descriptor.

All aliases retain the backing owner and region. Function-call checks include
transitive writes to global backing arrays; unknown callees conservatively may
write all global owners. The owner cannot be written or
mutably borrowed until the read-only borrows leave scope. Direct view/span
parameters participate in provenance tracking too. A copied span is a reborrow
that suspends its parent until the alias leaves scope.

String bindings require initialization and cannot be reassigned. A function may
return a literal string directly, but cannot return a borrowed string without a
region contract. String-containing records, arrays, and ADT payloads are
conservatively rejected at the same storage boundaries as other borrows,
including aggregates containing literal strings. General aggregate lifetimes and
closure capture lifetimes remain unsupported; function literals in an active
borrow scope are rejected. UTF-16/32 string wrapping is not provided by these
builtins; their checked code-unit codecs remain available.

See [runtime_utf8.oak](../examples/strings/runtime_utf8.oak) for caller-owned
runtime input, string views, and a fluent text builder used together.

