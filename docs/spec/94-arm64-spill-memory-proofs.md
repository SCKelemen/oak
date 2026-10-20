# ARM64 spill byte-memory proofs

`Oak.AArch64SpillMemory` gives the selector's SP-relative spill stores and
loads a byte-addressed, little-endian memory model. Thirteen Lean theorems
establish byte round trips, disjoint-slot preservation, decoded store/load
composition, and physical layout obligations, without admitted proofs or
added axioms.

## Supported instructions and values

An independent fixed-mask decoder accepts the unsigned-offset SP-based forms
used by `storeSpill` and `loadSpill`: STRB/STRH/STR W/X, LDRB/LDRH/LDR W/X,
and LDRSB/LDRSH to W registers. It consumes the actual scaled immediate and
register fields. Other base registers, addressing modes, and signed loads
to X registers are outside this slice.

A store changes exactly its one, two, four, or eight bytes. A load assembles
those bytes in little-endian order and applies the type's register convention:
unsigned byte/halfword values zero-extend; signed byte/halfword values first
sign-extend to 32 bits, then zero-extend to 64 bits because the destination
is W. Both 32-bit source types use a W load, and 64-bit types retain all bits.
Bool uses a byte slot and assumes the source value is already a canonical
Boolean; this model does not validate arbitrary bytes as Booleans.

`checked_roundtrip` proves that accepted production words execute a store
and reload to the exact normalized source value, for every register file,
NZCV state, and initial byte memory. The theorem gives the entire final
state: PC advances eight bytes, SP and NZCV are preserved, registers other
than the reload destination are unchanged, and memory equals the single
store. Source/destination aliasing is supported. ZR reads as zero; the pair
certificate refuses a discarded reload into ZR.

`store_outside` proves preservation of bytes outside the written interval.
`load_disjoint` proves that a non-overlapping load observes the original
memory. Normalization is idempotent, so canonical register values survive
a spill/reload unchanged.

## Frame layout

`layoutValid` checks frame size at most 4,080 bytes, 16-byte frame alignment,
slot widths of 1/2/4/8 bytes, natural slot alignment, frame bounds and
pairwise non-overlap. Its soundness theorems establish slot bounds and
noninterference, and derive an access's address-space bound from the
allocated frame's bound.

Execution refuses misaligned SP and accesses that wrap the 64-bit address
space. `address_no_wrap` connects the natural-number byte address with
64-bit base-plus-offset arithmetic under the range condition.

## Production evidence

`machine/aarch64_spill_memory_lean_test.go` uses the actual frame-layout,
store/load selector, and `asm.EncodeFunction` output:

- 324 accepted store/reload pairs spanning all nine supported source types,
  six offsets through the frame limit, and six source/destination choices.
- 973 rejected encoding/contract mutations for wrong base, wrong offset,
  swapped load/store, and discarded reload destination.
- Nine universal round-trip theorems instantiated with emitted words.
- Two execution refusals for misaligned SP and address-space wrapping.
- All 256 four-slot width combinations, empty and limit-boundary layout
  certificates, six invalid-layout certificates, and Go's oversized-frame refusal.

The ARM64 proof workflow requires this oracle alongside the existing branch,
comparison and register-edge-copy proof gates.

## Remaining boundary

This is a supplied-instruction, no-fault projection over total byte memory.
It does not prove memory mapping, permissions, stack allocation, prologue or
epilogue correctness, caller-frame separation, spill-slot liveness/reuse,
rematerialization, or full architectural fetch/fault behavior. The instruction
semantics are a local projection, not a new full Arm-model refinement.

The preceding register-only edge-copy certificate has not yet been extended
to schedules containing these memory operations. That composition and
whole-CFG simulation remain separate obligations. Production correspondence
is finite evidence, not a universal proof of the Go compiler.
