# Codecs: Phantom-Typed Producers and Consumers

**Status: normative design with JSON strings and derived record codecs.**
`stdlib/json.oak` implements strict string encoding/decoding, bounded SIMD
runs, and a phantom-policy encoder cursor (§10). The compiler derives
concrete JSON encoders and decoders and lowers immediate producer/consumer
composition (§12–13). General codec interfaces, borrowed decode results,
and fusion remain design work. Prerequisites are listed in §9.

## 1. What is borrowed from weePickle, and what is not

weePickle's decomposition is right for Oak: a **producer** deconstructs a
value into operations, a **consumer** builds a result from them, and
connecting a producer directly to a consumer does not require an
intermediate document tree. That is the no-hidden-allocation doctrine
applied to serialization.

weePickle's *mechanism* is not right for Oak. Its `From[T]` / `To[R]` are
interface objects — visitor instances passed at runtime — and "the
abstraction disappears" rests on the JIT inlining through them. Oak's
abstraction never exists at runtime because it lives in the **type**: the
format, the encoding, the policy, and the validation state are phantom
type parameters, and every codec is a monomorphized generic function. There
is no visitor object to inline away.

## 2. The three phantom axes

```oak
Text[E]                   // E: Utf8 | Utf16 | Utf32 — representation
Encoder[Format, Policy]   // Format: Json | MsgPack …; Policy: Strict | Replace
Decoder[Format, Policy]
Bytes[State]              // State: Unchecked | ValidUtf8 — validation state
```

Phantom parameters select behavior during specialization and occupy no
storage unless the implementation genuinely needs runtime state:

- `Text[Utf8]` is a pointer plus a byte length; `Text[Utf16]` a pointer
  plus a `u16`-unit length. The encoding needs **no discriminator** — no
  stored tag, no pointer bits, no PAC tricks — because the compiler knows it.
- **Representation** (`Utf8` vs `Utf16`), **policy** (strict decoding vs
  replacement of malformed input), and **state** (unchecked vs validated;
  an encoder expecting a field vs expecting a value) are three distinct
  compile-time distinctions, and they compose independently.

This is the `Str[Utf8]` doctrine (`70-strings.md`) and the phantom-index
doctrine (`Idx[Thread]`, `40-records.md`) generalized: the phantom carries
*which* — which encoding, which format, which state — the way `Idx[P]`
carries *which pool*.

## 3. The surface

```oak
// value <-> bytes: T and the format are both static
encode[T, F]: (value: T, out: [*]u8): Result[u32, EncodeError]
decode[T, F]: (input: []u8, storage: [*]u8): Result[T, DecodeError]

// text: the phantom is the protocol
transcode[Utf8, Utf16]: (src: Text[Utf8], dst: [*]u16): Result[u32, TranscodeError]

// schema-less format-to-format: an event stream into a type-parameter sink
stream[F, S]: (input: []u8, sink: [*]S): Result[(), DecodeError]
```

`encode[User, Json]` monomorphizes to one straight-line function driven by
`User`'s declared fields and typed tags (§5). Encoding returns the written
length; decoding constructs the requested value into caller-provided
storage. Fluent adapter spellings (`from(x).to[Json](out)`) are surface
sugar over these functions and must lower to the same direct calls.

Schema-less format-to-format transcoding can use direct structural visitor
operations. It need not materialize an event ADT. An explicit event buffer
is an optional adapter with caller-owned storage; bulk text, byte, and
array operations must remain available to specialized implementations.

## 4. Zero cost, defined

"Zero cost" means **no additional overhead compared with equivalent
handwritten code, verified in the generated C.** Monomorphization alone
does not guarantee every wrapper disappears, and specialization can grow
code size; both are measured, not assumed.

| Feature | Runtime cost |
| --- | --- |
| Phantom format, encoding, policy, or state | no stored tag |
| Statically selected codec | direct specialized calls |
| Fluent adapters | no allocation; wrappers must vanish in emitted C |
| Caller-supplied output | the buffer and cursor state, nothing else |
| Parsing, validation, transcoding | the necessary computation |

Verification is the SIMD/intrinsics precedent (`93-simd.md`): golden and
differential tests over the emitted C, asserting the absence of wrapper
calls and the presence of the direct form.

## 5. Derivation from typed tags

`encode[T, F]` and `decode[T, F]` for a declared record are **derived**:
generated Oak code, checkable like any other, read from the record's
declared fields and typed tags (`40-records.md` §12). The generation is a
structured compiler transformation: the derivation builds typed syntax
(`compiler/synth.go`, the same nodes the parser produces) with a fresh
resolution context per generated function and a distinct position per node,
so no Oak source text is templated and reparsed, and every generated shape
is a node the checker, lowering, backend, and interpreter already know:

```oak
json: tag = { name: string, omit: Bool }

User: type = struct {
  id(json: "user_id"): u64
  score(json: { name: "score", omit: true }): u32
}
```

Derivation is a compile-time projection — the OCaml `deriving` doctrine,
never runtime reflection (the Elm rule). Codec derivation is the tags'
first consumer, and the reason tag namespaces are closed and typed: a
misspelled tag is a compile error before it can silently change wire
output.

Combinators follow weePickle: a decoded value may be mapped, an encoded
value projected, and both combined — with **fallible mapping** so decoding
an integer into a validated `UserId` returns an error. A bidirectional
codec does not imply a lossless round trip; that is a separate, stated
property.

## 6. Validated state is only as strong as its construction

`Bytes[ValidUtf8]` proves something only because:

1. the marker cannot be forged — the sole constructors are `validate`
   (performs the real check once and returns the validated type) and an
   explicit `unsafe` assumption that is recorded (`50-borrowing.md`,
   `LANGUAGE_MODEL.md` string validity); and
2. the borrow checker forbids mutation of the underlying bytes while the
   validated view lives — views are read-only, and a writable span over the
   same storage cannot coexist with it.

A freely constructible marker would prove nothing. The same rule governs
encoder typestate: `Encoder[Json, ExpectingValue]` is produced only by the
field-writing operation, so a value written without a preceding key is a
type error, not a malformed document.

Phantom types encode these distinctions; they cannot independently
establish memory safety (ownership does that) or hardware privilege
(capabilities do that), and runtime input still needs its runtime checks.

## 7. Two contracts that stay explicit

- **Borrowing.** Decoded views are tied to the input or to supplied
  storage. Escaped JSON strings must be unescaped *into* that storage; a
  decoded `Text[Utf8]` never points at memory the caller did not provide.
- **Buffering.** Streaming decode requires the discriminator first. A
  format that places it late does not get a bounded hidden buffer; it gets
  the non-streaming decode with caller-provided `[N]u8` scratch and an
  explicit overflow error. The buffering requirement is a *type* (which
  decode was called), not a runtime parameter.

## 8. What NOT to do

- Do not wrap the UTF transcoders in a per-scalar visitor. They are
  already direct span-to-span loops; a visitor would slow
  the fast path to fit an abstraction. Text stays phantom-encoded
  functions (§3).
- Do not introduce runtime codec dispatch by default. When the format is
  chosen at runtime, match the format ADT **once** at the boundary and
  dispatch into the monomorphized functions — never carry a runtime format
  tag through the codec.
- Do not begin with text. Begin with a JSON codec derived over records,
  where the composition model earns its keep.

## 9. Prerequisites and order

1. **Constrained-generics monomorphization** with method-set constraints
   (`20-types.md` §11.2 records the gap): `encode[T, F]` must require
   `F: Format` statically, and constrained templates must specialize the
   way unconstrained ones now do.
2. **Tag-driven derivation** as generated Oak code (§5).
3. **Borrowed decoded views**: relaxing `OAK-B0109` so a decoded view can
   be returned tied to its input region — the sound headroom `Oak.Escape`
   already proves. Until then, v1 decode copies into caller storage, which
   is honest and allocation-free.
4. Then the first codec: JSON over declared records, verified zero-cost
   per §4.

## 10. Concrete JSON string codec

The first implementation exports:

- `json_string_encode_size(src)`, `json_string_encode(dst, src)`, and
  `json_string_encode_at(dst, offset, src)`;
- `json_string_decode_size(src)` and `json_string_decode(dst, src)`;
- `json_encoder().append_json_string(dst, src).finish_json()`.

Results are `Result[u32, JsonError]`; lengths count bytes. Decoding accepts
exactly one quoted JSON string, without surrounding whitespace. It supports
all JSON escapes and paired UTF-16 surrogate escapes, rejects lone
surrogates, unescaped controls, invalid UTF-8, and trailing content. Encoding
preserves UTF-8 and escapes controls as `\\u00xx`. Neither path adds a NUL
terminator. Input and output must obey ordinary non-aliasing borrow rules.

Both directions preflight validity and output size before writing, so errors
leave the entire destination unchanged. Explicit preflight followed by an
encode/decode repeats validation: a size result is not a validity capability.

`JsonEncoder[JsonStrict]` has only two u32 fields: written bytes and sticky
error status. The policy is phantom. This bootstrap cursor emits one string
value; empty finish and a second successful append are syntax errors. It is
not a record/object builder or protected validation proof. Public cursor
fields do not establish validity for arbitrary forged cursor values.

## 11. SIMD, locality, and fusion

The concrete string scanner classifies 16 contiguous bytes per full block
using portable SIMD operations; the AArch64 backend supplies NEON lowering.
Unescaped runs copy with vector loads/stores and a scalar tail. Every vector
load fits within the actual view; no hidden input padding or cache-line-size
assumption exists. UTF-8 validation is a separate existing runtime pass.
There is no claim of fused UTF-8 validation or simdjson-equivalent parsing.

The steady-state working set is input/output spans plus scalar cursors and
vectors. No document tree, per-character event allocation, or token array is
required. Two-pass atomic output trades additional reads for unchanged output
on failure. Future incremental sinks must name their partial-write contract.

Future structural scanning should retain block classification, reductions,
prefix scans, and index compaction in compiler IR until fusion decisions are
made. Futhark's vertical/horizontal and scan-scatter fusion are useful models:
remove temporary arrays and combine compatible passes, subject to effects,
error ordering, bounds, and ownership. Monomorphization alone does not provide
these transformations. Scratch indexes remain explicit where materializing
them is beneficial; the IR must not mandate an event object per byte/token.

Futhark's uniqueness/consumption model also makes an operation's cost part
of its contract: an update must not silently copy an entire array. Oak uses
its own view/span ownership model, and must preserve source/result alias
relationships and consumption effects across codec composition. A generic
fluent wrapper cannot erase those facts or silently insert a copy to resolve
an ownership error.

CPU SIMD and multicore/GPU parallel execution are separate choices. The kernel
and hypervisor codec path must not implicitly launch workers or GPU work.
Physical cache tuning, kernel SIMD-context eligibility, native M-series
throughput, and code-size claims require target-specific verification.

Tests exercise strict escape semantics against Go's JSON decoder, malformed
inputs, exact/tiny buffers, and boundaries around 16/32/64 bytes. Generated C
checks cover allocation absence and the presence of NEON load/store paths;
these are not an assembly-level proof that all fluent wrappers disappear.

References: [weePickle](https://github.com/rallyhealth/weePickle),
[Futhark scan-scatter fusion](https://futhark-lang.org/blog/2026-03-24-scan-scatter-fusion.html),
[Futhark uniqueness and updates](https://futhark-lang.org/blog/2022-06-13-uniqueness-types.html).


## 12. Derived JSON encoding (implemented subset)

With `import(std)`:

```oak
json: tag = { name: string }
Point: type = struct { x: i32, y: i32 }
Sample: type = struct {
  id(json: "sample_id"): u64
  active: Bool
  position: Point
}

// value: Sample; output: [*]u8
encoded_size[Sample, Json](value)
encode[Sample, Json](value, output)
from[Sample](value).to[Json](output)
```

All three operations return `Result[u32, JsonError]`; lengths are bytes.
`Json` is a compile-time format marker. The fluent form emits identical C
to the direct form and evaluates the source expression once. `from` is an
immediate producer expression, not a storable codec object or borrowed
aggregate. `from`, `encode`, and `encoded_size` are reserved under
`import(std)`; no implicit codec search or runtime format dispatch occurs.

Supported values are all fixed-width signed/unsigned integers, `Bool`,
top-level `string`, and closed concrete records recursively containing
supported integer, boolean, or record fields. Fields emit in declaration
order. Integers use exact decimal text, including i64 minimum and u64
maximum; they never pass through floating point. JSON string encoding
uses the bounded SIMD implementation in §10.

A declared `json` tag schema can rename a field with a string literal,
either the bare first `name` property or `{ name: "wire_name" }`. Duplicate
wire names and unimplemented projection properties (including `omit`)
are errors. Ordinary type checking still validates the tag schema and all
generated field accesses. Unknown tags are not silently accepted.

The compiler generates ordinary Oak size, write, and encode functions;
they pass the same type, borrow, resource, and discipline checks as source
functions. Full size preflight precedes output mutation. Insufficient
space leaves output unchanged. Generated helpers retain capacity checks
because the bootstrap namespace does not yet provide private functions.
The input record follows Oak's existing value-passing ABI; this feature
does not introduce a borrowed-record ABI or claim that native compilers
eliminate every aggregate copy or repeated measurement.

This first projection requires explicit concrete names at expansion time.
Type aliases, generic record applications, codec calls depending on an
unspecialized type variable, top-level arrays, floats, ADT variants, and borrowed
record fields are not yet derived. `FromTo[T]`, generic visitor dictionaries, custom format implementations,
and derivation-time omission policies are not implemented by this subset.
Derived decoding is specified in §13. Failures are compile
errors, not serialization fallbacks or runtime reflection.

## 13. Derived JSON decoding (implemented subset)

```oak
// input: []u8
direct: Result[Sample, JsonDecodeError] = decode[Sample, Json](input)
fluent: Result[Sample, JsonDecodeError] = from[Json](input).to[Sample]()
```

The two spellings lower to identical C. Decoding returns a concrete value inside
`Result`; no boxed value, generic document tree, token array, or allocator
is required. For this fixed-size subset the destination is the returned
value, so there is no separate output-storage argument. Input is borrowed
read-only; no reference to its bytes escapes in the result.

Supported targets are fixed-width integers, Bool, and closed concrete
records recursively containing those types, including fixed-size array fields
(§14). Record fields may appear in
any order. All declared fields are required; duplicate and unknown fields
are errors. The `json` name tag from §12 governs both directions. Matching
compares decoded Unicode scalars: an escaped spelling of a field name is
the same field, including surrogate-pair spellings. No normalization or
case folding is implied. Plain ASCII keys use direct byte comparison;
escaped and non-ASCII keys use Unicode-scalar comparison. Tokenization uses
bounded SIMD string runs and fixed local schema-key arrays; no
unescaped key buffer is constructed. Field dispatch is currently linear
in the number of declared fields, not a hash lookup or a fused scan.

The root decoder validates UTF-8, consumes one value, and permits only
JSON whitespace before and after it. It rejects trailing values/content,
malformed number grammar, unescaped string controls, invalid escapes,
and unpaired surrogates. Integer targets accept integer lexical forms;
fractions and exponents are `TypeMismatch`, even if mathematically integral.
Unsigned targets reject a minus sign, including `-0`; signed targets accept
`-0` as zero. Decimal accumulation and target-width checks report overflow
before conversion; no number passes through floating point.

`JsonDecodeError` distinguishes `InvalidEncoding`, `InvalidSyntax`,
`TypeMismatch`, `NumericOverflow`, `MissingField`, `DuplicateField`, and
`UnknownField`, plus `LengthMismatch` for fixed arrays. InvalidEncoding takes precedence over all other errors. Other errors are fail-fast:
unknown/duplicate fields can be reported before their values are parsed.
Errors do not contain a partly constructed output record. The decoder does
not mutate caller storage. Returning `Result[T, JsonDecodeError]` still uses
Oak's existing value ABI; no claim is made that all aggregate copies vanish.

Each helper returns `JsonDecoded[T]` (a concrete value and next byte offset).
Nesting follows the finite schema: no runtime-depth stack allocation or
unbounded recursive JSON-tree traversal is introduced. Read helpers use
ordinary bounds checks, and out-of-range explicit helper offsets trap.
The root wrapper is the whole-document validation boundary; offset helpers
are not independently validated-input capabilities.

Borrowed strings, top-level arrays, general ADTs, floats, dynamic schemas, and aliases
are not derived yet. `decode[string, Json]` fails with guidance to use the
existing `json_string_decode` into a caller-provided span. Relaxing that
restriction requires explicit storage/lifetime contracts, not boxing.

Tests cover integer limits in every width, nested and reordered records,
escaped Unicode keys, malformed inputs, missing/duplicate/unknown fields,
trailing content, and C address/undefined-behavior sanitizers. Fluent/direct
C equality and allocator absence are checked alongside encoder regressions.

## 14. Fixed-size array fields (implemented subset)

```oak
Sample: type = struct { readings: [4]i32, flags: [2]Bool }
// input: []u8; output: [*]u8
value: Result[Sample, JsonDecodeError] = decode[Sample, Json](input)
// encode[Sample, Json](sample, output) and both fluent spellings also work.
```

Closed records may contain nonempty `[N]T` fields where T is a supported
integer, Bool, or concrete record. Records inside arrays may themselves
contain array fields. Arrays remain inline in the owning record and concrete
Result payload. No box, heap allocation, token tree, or separate array buffer
is introduced. Generated bounded loops have code size independent of N.
The ordinary record layout and borrow checks still apply.

JSON uses ordinary arrays, including for `[N]u8` (numbers, not base64).
Decoding requires exactly N elements; shorter or longer arrays report
`LengthMismatch`. Trailing commas, missing separators, and truncation are
syntax errors. Element errors propagate unchanged. Error reporting remains
fail-fast: an excess element can trigger a length error before its contents
are validated. No partial output is returned. Encoding measures the entire
record before writing, retaining destination-too-small atomicity.

Array lengths must be positive integer literals representable by u32 and
fit the backend's supported record layout. Zero-length arrays, slices,
spans, direct multidimensional array fields, and top-level array codec
arguments are not part of this subset. Use a named record around each
array level. Borrowed string elements still require explicit storage and
lifetime work. Record passing/returning may copy the inline arrays under
the existing value ABI; large arrays therefore have real stack and copy
costs. These loops do not introduce numeric SIMD parsing or guarantee
vectorization; bounded SIMD string scanning remains available to keys.

Sanitizer tests cover nested record arrays, scalar boundaries, length and
syntax errors, round trips, and unchanged short destinations. Fluent/direct
C equality (excluding source-location comments) and allocator absence are
checked for array-bearing records.

## 15. Nullable record fields (implemented subset)

A field `id: Option[u64]` encodes `.Some(n)` as a JSON integer and `.None`
as `null`. The same rule applies to Bool and supported concrete records,
including records with fixed array fields or other nullable fields. These
are required nullable fields: an absent key is still `MissingField`, and
null is distinct from an absent key. No omission/defaulting policy is
inferred. Duplicate and unknown field rules remain unchanged.

The concrete Option tag and payload live inline in their owning record;
no boxing, heap storage, or pointer tagging is introduced. The backend
places the tag and single-payload union with checked layout arithmetic
and C size/alignment/offset assertions. Aggregate copies remain possible.
Nested Option applications, Option of a bare array or borrowed string,
and arrays of Option are outside this initial derivation subset. A named
record can wrap an array. Nullable values do not weaken input validation
or encoding's complete preflight before modifying the output buffer.

## 16. Two API levels and the simdjson performance target

Oak offers a typed convenience layer and explicit lower-level operations.
The intended producer/consumer split follows
[weePickle](https://github.com/rallyhealth/weePickle), with static concrete
composition in Oak. High-level `decode[T, Json]`, `encode[T, Json]`, and
immediate `from[...](...).to[...]` calls derive typed operations; they must
not require an intermediate document tree or erased visitor allocation.

Low-level users control input views, output spans, offsets, and reusable
storage. Current building blocks include `json_token`, `json_read_integer`,
`json_string_decode`, and `JsonEncoder[JsonStrict]`. These helpers are not
interchangeable with complete-document validation: token and offset helpers
do not establish that a whole input is valid JSON. A general streaming
reader/writer and public typed visitor protocol are still design work.
Future streaming APIs must state chunk boundaries, incomplete-input
behavior, output exhaustion, lifetime rules, and validation coverage.
Both API levels should share scanning/conversion kernels; high-level
convenience must not force scalar processing or hidden allocations.

Matching simdjson on Apple M-series is a target, not a measured result.
Key scanning uses bounded SIMD runs; integer conversion uses scalar and
word-parallel operations, and field lookup remains linear. Successful typed
parsing establishes UTF-8 validity; failure paths retain a full validation
pass to preserve error precedence. Removing abstraction overhead alone
does not establish parity across JSON workloads. Investigate fused structural/UTF-8
scanning, faster checked numeric conversion, schema-specialized field
matching, and reusable bounded work buffers based on profiles. Any padded
input fast path requires an explicit verified readable-capacity contract;
the ordinary view API must retain bounded reads at its tail.

Follow [simdjson's performance guidance](https://github.com/simdjson/simdjson/blob/master/doc/performance.md)
when comparing: reuse parser/work buffers, distinguish setup from steady
state, and report number-heavy workloads separately. Measure on the same
M-series machine, compiler settings, and core configuration. Record exact
versions, bytes/s, time/document, allocations, and scratch/output capacity;
use consumed checksums and both warm-cache and streaming-sized workloads.
Compare full validated typed materialization with equivalent work; selective
extraction is a separate benchmark with its validation coverage stated.
No general parity claim accompanies this implementation. The native [typed JSON comparison](../../benchmarks/json/README.md)
now implements a first integer/Bool/fixed-array workload against pinned
simdjson On-Demand, with preflight validation and consumed checksums.
Its CI includes native ARM64 execution on hosted virtual Apple M1 machines;
these are not controlled dedicated-hardware results.
Allocation instrumentation and additional schemas remain future work.

## 17. Measured decoder fast paths

The common integer path validates and accumulates decimal digits in one
scan. Target-width checking remains in the concrete derived reader. For
`M = UINT64_MAX = 10q + 5`, multiplying magnitude `m` by ten and adding digit
`d` is safe exactly when `m < q` or (`m == q` and `d <= 5`). The implementation
uses `q = 1844674407370955161`. The first 19 digits need no overflow
check because `10^19 - 1 < UINT64_MAX`; subsequent digits multiply only
after the cutoff check. Overflow is sticky while the rest of the digit sequence is scanned.
Leading zeros, decimals, exponents, non-number tokens, and malformed suffixes
fall back to the original reader, preserving syntax/type/overflow precedence.
The original implementation remains available as `json_read_integer_slow`
for differential checks, not as a separate relaxed parsing policy.

Fixed-array lookahead now checks only for a closing bracket after whitespace;
it no longer parses an element token before the element reader parses it.
Punctuation has a small token wrapper; other tokens retain the full parser.
ASCII keys avoid per-scalar Unicode decoding, while escapes and non-ASCII
keys retain the existing semantic comparison.

The standalone UTF-8 validator has a bounded 16-byte SIMD ASCII fast path. An entirely
ASCII input is valid UTF-8; any high bit delegates to the original complete
validator. Incomplete tails use scalar reads. This does not fuse UTF-8 with
JSON syntax checking, relax JSON control-character rules, or assume readable
padding. The portable SIMD fallback remains available when NEON is disabled.

Differential sanitizer tests compare values, signs, offsets, and exact error
categories against the original integer reader. Tests cover every one-byte
input, u64 bounds, signed forms, malformed suffixes, long overflow sequences,
and deterministic random integers. Key tests compare escaped and Unicode
spellings against the original semantic matcher. UTF-8 tests sweep every byte
value at every position of a 65-byte buffer and valid/invalid sequences across
vector boundaries. These checks accompany the arithmetic argument above;
no new machine-checked proof of the complete parser is claimed.

The benchmark workflow now compares a pinned pre-optimization Oak revision
with the candidate on the same Linux and ARM64 macOS runner, using five
samples of 1,024,000 documents per backend. Paired reports check compatible
metadata and report simdjson timing drift as a noise indicator. Raw samples
remain in workflow artifacts. See [recorded measurements](../../benchmarks/json/RESULTS.md).
Field dispatch remains linear, numeric accumulation now includes word-parallel batches, and
aggregate copy elimination is not guaranteed. These results support specific
improvements on this schema, not universal parser or language superiority.

## 18. Schema matching and compact integer scans

Derived records compare bounded literal key spellings directly when the wire
name contains at most 32 printable ASCII bytes without quotes or backslashes.
The comparison includes both quotes and verifies the readable length before
indexing. Other spellings fall back to the full tokenizer and Unicode matcher,
including escaped equivalents of known fields. Duplicate, unknown, missing,
and malformed-key behavior remains unchanged. This is linear schema dispatch,
not a structural index or a general SIMD JSON parser.

Empty-object and post-comma array lookahead inspect only the relevant closing
byte after whitespace. Colons and separators use direct bounded checks where
every other token must produce InvalidSyntax. Positions requiring distinctions
between malformed syntax and a valid value of the wrong type retain token
classification. Successful typed decoding establishes UTF-8 validity as described
below; failures retain a complete validation pass.

The implementation-only JsonIntegerScan contains magnitude:u64, next:u32, and
status:u32. Status 0/1 denotes positive/negative success; larger values encode
json_decode_error_code + 1. Its 16-byte C layout permits register returns on
AArch64, avoiding the indirect aggregate return of Result[JsonInteger,
JsonDecodeError] in the hot scanner. Derived readers perform target-width
checks on this concrete value. The public json_read_integer API still returns
Result[JsonInteger, JsonDecodeError]; no pointer encoding, boxing, allocator,
or change to public error categories is involved. This layout is an internal
optimization, not a stable public wire format or a promise for every backend.

The native benchmark can retain generated C and assembly with --inspect.
Sanitizer coverage includes every truncated prefix of a representative record,
escaped key aliases and duplicates, malformed separators, and numeric error
precedence. Updated measurements and their scope are in the benchmark results.

## 19. Word-parallel scanning and successful-parse validation

Record fallback key matching lives in a separate derived helper, keeping its
fixed key storage out of the common reader's live state. Plain literal keys
and Boolean spellings use bounded little-endian word comparisons plus scalar
tails. Array lookahead classifies an initial closing bracket as LengthMismatch
and a closing bracket after a comma as InvalidSyntax, without a second scan.
Whitespace scanning tests the byte in the loop condition.

The integer scanner processes eight ASCII decimal digits at a time when eight
bytes remain within the first-19-digit bound. A word mask validates every byte
before combining adjacent digits into pairs, four-digit groups, and an
eight-digit number. The aggregate update is magnitude * 100000000 + group.
At most 19 accumulated digits fit u64, so this update cannot overflow. The
existing cutoff handles subsequent digits, and the original slow reader
preserves leading-zero, suffix, type, and overflow error precedence. This is
word-parallel arithmetic (SWAR), not eight heap values or a padded overread.

The C backend recognizes complete 4/8-byte little-endian packs written as
ORs of unsigned widened bytes shifted by 0, 8, ... bits. Recognition requires
the same u8 view identifier, the same side-effect-free offset identifier,
consecutive offset additions, and the matching unsigned result width. It
emits a helper with one overflow-safe range check and ordinary unsigned byte
loads from a common pointer. C optimization can combine those into one word
load; unaligned access, strict aliasing and byte order remain portable. Other
expressions retain their existing lowering. Out-of-range access still traps.
This compiler optimization applies to ordinary Oak expressions, not JSON names.

For the current derivation subset (integers, Bool, records, fixed arrays and
required nullable fields), a successful complete parse establishes valid UTF-8:
all value tokens, delimiters and whitespace are ASCII; direct key matches are
ASCII; other successful key matches validate UTF-8 or JSON Unicode escapes.
Nested readers satisfy the same property, and the root consumes the full
input. The success path therefore needs no additional UTF-8 pass. On any
failure, including trailing content, the root validates the entire input
before returning the error, preserving InvalidEncoding precedence even for
invalid bytes beyond the first syntax error. Extending the derivation subset
requires preserving this property or reinstating an explicit validity check.
The public standalone token and offset readers do not gain a whole-document
validity guarantee.

Sanitizer regressions sweep every byte value through digit lanes and through
every position of a representative record, check unaligned 32/64-bit loads
against a scalar oracle, and verify traps at short and extreme offsets.
Escaped-key, nullable, numeric-boundary and truncation tests remain in place.
These are executable checks and an algorithmic argument, not a machine-checked
proof of the complete compiler transformation or parser.
