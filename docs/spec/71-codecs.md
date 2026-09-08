# Codecs: Phantom-Typed Producers and Consumers

**Status: normative design.** No codec surface is implemented yet; this
document fixes the model so that serialization, transcoding, and record
codecs are built against one design. Prerequisites and their status are
listed in §9.

## 1. What is borrowed from weePickle, and what is not

weePickle's decomposition is right for Oak: a **producer** deconstructs a
value into operations, a **consumer** builds a result from them, and
connecting a producer directly to a consumer never materializes an
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

The only place an event stream is unavoidable is format-to-format
transcoding **without a schema** (`Json -> MsgPack` for unknown data).
There the events are a stack-value ADT —
`Event = ObjectStart | ObjectEnd | Key: Text[Utf8] | Int: i64 | ...` —
delivered to a sink whose type is a **type parameter**, so even that
dispatch is monomorphized, never indirect.

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
  already direct span-to-span loops with SIMD paths; a visitor would slow
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
