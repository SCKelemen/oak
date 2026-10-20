# Oak strict one-function ELF envelope

`asm/selfhost/bitwise_elf.oak` is an additive, bounded writer for the existing
`Oak.NativeBitwiseImage.StrictProfile`. It does not change `elf.oak`, its
sectionless profile, the strict checker, the public compiler API, or execution
capabilities. It is implementation plus finite format-parity tests, pending
universal extracted implementation proofs.

## Contract

`native_bitwise_elf_image(dst, linked_text, arch, name)` returns the complete
image length, or zero on refusal. `dst` is a mutable byte span; both inputs are
immutable, disjoint borrows. `arch` is 1 for ARM64 or 2 for RV64. `name` is the
unprefixed proposal, with 1–256 bytes each in 1–127. This is the image profile's
representable name domain, **not** source identifier validation. Names such as
`main`, `A_B`, and control-byte names may pass the envelope writer but cannot
pass the unchanged canonical source checker.

Before any destination write, the writer checks the architecture, complete name,
exact linked-text length, every startup byte, and complete destination capacity.
Refusal preserves the entire destination; success preserves the suffix beyond
the returned length. The body is an opaque proposal and receives no source or
operation authority from this API. Its exact contents must still be checked by
the complete source/image admission path.

Base and entry are fixed at 65536. Text starts at file offset 4096. ARM64 has a
12-byte linked startup and an 8-byte body, padded to a 32-byte RX load. RV64 has
a 16-byte linked startup and a 36-byte body, padded to a 64-byte RX load, with
LP64D flags 4. The RV body extent is the existing nine-instruction framed profile;
a shorter leaf is refused. No generic linker, alternate relocations, additional
functions, data/BSS, or compressed RV instructions are introduced.

There are six sections, including the empty 16-aligned `.rodata`, and three
symbols: null, `_start`, and `oak_<name>`. With `n = len(name)`:

- `sym = 4096 + load`, `str = sym + 72`
- `shstr = str + n + 13`
- `sections = align8(shstr + 41)`
- `size = sections + 384`, at most 4896 for ARM64 or 4928 for RV64

The writer initializes precisely `[0,size)`, then writes nonzero fields and
copies the text/name proposals. Every ELF64 value fits in 32 bits; zeroed upper
halves, null records, header gap, text padding and section alignment padding are
part of the exact output. This fixed placement avoids introducing the general
Oak object resolver/linker into this writer's proof obligation.

## Evidence and bootstrap boundary

`TestE2ESelfHostedBitwiseELF` captures actual binary stdout from compiled Oak,
checks the reported length and **every caller-buffer byte**, compares against an
independent struct-serialization oracle, and compares each canonical output with
a fresh Go compiler object plus `asm.WriteExecutable` complete artifact. It does
not trim stdout or reconstruct an ELF after capture. Cases cover AND/OR/XOR,
`bitwise` and `Mix9`, name/alignment boundaries including 1 and 256, exact and
short capacities, every changed startup byte, late-invalid names, invalid
architectures/text extents, suffix framing and full-buffer refusal. Profile-name
and altered-body controls demonstrate that writer success is not source
admission. The separate complete-bundle harness must pass these captured bytes
and the original source unchanged to `ImageInstallation.CheckImageBundle`.

The generator still runs through Go `Compilation.EmitC` and system `cc`.
Neither complete artifact parity nor admission proves either compiler. No full
self-hosted compiler, universal producer correctness, OS-process completion or
hardware execution claim follows.

`TestE2ESelfHostedBitwiseELFExtract` mechanically extracts all three functions
from this same source into fuel-indexed Lean definitions without `sorry`.
This is a feasibility/syntax probe, not a committed extraction-drift theorem or
a proof of exact output. The projection uses `Array.getD`, `setIfInBounds`, and
`size.toUInt32`; future refinement must prove represented lengths below 2^32,
every read/write in bounds, nonwrapping arithmetic, fixed-endian helper laws,
sufficient fuel for all loops, exact success/refusal and suffix framing, then
strict-profile admission. The current loops reuse their supplied fuel; the
longest successful loop is the at-most-4928-byte initialization. A suggested
4929 bound still requires proof, rather than a returning-run assumption.

Focused command:

```sh
go test ./compiler -run '^TestE2ESelfHostedBitwiseELF(Extract)?$' -count=1
```

These tests are separate from checker authority and do not alter existing
semantic/proof profiles.

The [raw complete-image integration](94-selfhost-image-admission.md) captures
these actual outputs for direct unchanged-checker admission and adds separate
mandatory exact producer/admission gates without replacing the existing gates.
