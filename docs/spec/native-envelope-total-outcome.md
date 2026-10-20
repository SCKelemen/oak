# Total outcome of the strict native ELF envelope writer

This is a separate refinement of the actual complete source-extracted
`Oak.BitwiseELFProducer.native_bitwise_elf_image`. It composes the existing
successful-domain envelope proof and proves every remaining refusal branch.
The writer, extraction, strict checker, and existing successful-domain proofs
are unchanged.

## Independent result

`Oak.NativeBitwiseEnvelope.envelopeResult dst text arch name` is defined in
`NativeBitwiseEnvelopeTotalSpec.lean`, independently of the extracted writer,
its word reads, loop flags, mutation sequence, and returned result. It selects
ARM64 only for tag 1 and RV64 only for tag 2. Its explicit natural/byte predicates
require:

- A name length in 1–256, with every byte in 1–127.
- Text length exactly 20 for ARM64 or 52 for RV64.
- A byte-list startup prefix exactly equal to the corresponding independent
  12-byte or 16-byte startup.
- Destination capacity for the natural aligned envelope size.

On admission, the body is the remaining text suffix. Its length follows from
these predicates; body contents remain arbitrary. The result is the exact u32
length of the independent field-concatenation `E`, paired with an array made
from `E ++ dst.toList.drop E.length`. On any failure the result is `(0, dst)`.
No read-default behavior is used to admit missing bytes.

## Universal theorem

`Oak.BitwiseELFProducer.image_total` states, for every `UInt32` architecture and
all destination, name, and text arrays whose sizes are below 2^32, that fuel at
least 4929 yields:

```text
native_bitwise_elf_image dst text arch name fuel
  = some (envelopeResult dst text arch name)
```

There is no valid-input, startup, returned-run, or successful-output premise.
`image_refusal_exact` concludes `some (0, dst)` whenever there is no independent
eligible architecture/input witness. `image_total_ne_none` excludes fuel
exhaustion throughout the stated domain.

## Actual source obligations

The name scan theorem covers an arbitrary initial flag and a remaining list.
It proves termination and the exact final flag, `initial && allValid`, with a
bounded index. Invalid bytes short-circuit: the final index is not assumed to
be the end of the name. The scan's bounded-fuel argument is used only after the
actual outer guard admits a name of length at most 256. Invalid architectures,
empty names, and oversized representable names take the outer refusal instead.

`native_read_value` proves all four actual UInt32 read addresses are
nonwrapping under a complete in-bounds footprint. `read_value_bytes` identifies
the corresponding genuine four-byte list slice. `packed_read_octets` proves
byte recovery using ordinary UInt/BitVec extensionality, shift and OR lemmas,
and arithmetic. `startupCheck_iff` establishes both directions between the
actual fixed word tests and the independent startup byte prefix, after the
exact text-length guard. It does not assume a valid prefix on the refusal side.

`sourceInitial_eq` proves the actual text-length and capacity checks equivalent
to their natural predicates, including exact nonwrapping layout and alignment
arithmetic. Refusal continuation lemmas stop before the first destination
write. The successful branch reuses the unchanged `image_exact` theorem,
including its actual stores, zero/text/name loops, bounds, and uniform fuel.

## Validation boundary

The mandatory total-outcome gate rebuilds the entire 46-module local source
closure at trust zero with official Lean 4.33.1, checks source identities before
and after, and exactly audits 56 theorem/control roots. Only `propext`,
`Quot.sound`, and `Classical.choice` may occur. Controls cover unsupported tags,
empty/257-byte names, maximal DEL names, first/last bad bytes, initial-false
short-circuiting, zero scan fuel, full-writer invalid name bytes, wrong text
extents, bad startup at valid extents, and short capacity. These controls
supplement the universal proof and do not replace it.

The theorem does not verify extraction, source-operation or body semantics,
general linking, the compiler, ISA execution, or OS execution. Profile-name
proposals need not be source identifiers. Source/body binding remains the
unchanged source/image checker's responsibility. The preserved caller suffix
is not admitted ELF trailing data; the returned count identifies the artifact.
