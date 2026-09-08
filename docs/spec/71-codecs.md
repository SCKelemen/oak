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
declared fields and typed tags (`40-records.md` §12):

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
case folding is implied. Matching uses scalar comparison with bounded
SIMD runs in string tokenization, and fixed local schema-key arrays; no
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
`UnknownField`, plus `LengthMismatch` for fixed arrays. UTF-8 validation runs first. Subsequent errors are fail-fast:
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
