# Oak strict one-function ELF envelope

`asm/selfhost/bitwise_elf.oak` is an additive, bounded writer for the existing
`Oak.NativeBitwiseImage.StrictProfile`. It does not change `elf.oak`, its
sectionless profile, the strict checker, the public compiler API, or execution
capabilities. Its successful valid-input path now has a universal, source-extracted
exact-envelope proof, alongside the preserved finite format-parity tests.
Universal refusal refinement remains a separate obligation.

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
Neither complete artifact parity nor admission proves either compiler. The
universal theorem below is bounded native-envelope producer correctness, not
full self-hosted compiler correctness. No OS-process completion or hardware
execution claim follows.

## Universal extracted success theorem

`NativeBitwiseEnvelopeExtracted.lean` contains the complete mechanically generated
three-function closure, including the four actual loops and all 71 word calls.
`TestLeanNativeBitwiseEnvelopeExtract` regenerates the entire file from the
current type-checked Oak source and requires byte-for-byte equality; no helper
substitution, filtering, or hand editing is used.

The independent `Oak.NativeBitwiseEnvelope.E` specification concatenates natural
little-endian ELF header/program fields, startup/body bytes, padding, symbols,
string tables, and six section records. It is not defined by memory writes.
`Oak.BitwiseELFProducer.image_exact` proves the actual generated function returns
`some (UInt32.ofNat E.length, writeBytes dst 0 E)` for every machine, initial
buffer, name, text, fixed-extent body proposal, and fuel satisfying:

- `archTag` is 1 for ARM64 or 2 for RV64
- The name has 1–256 bytes, each strictly between 0 and 128
- Text is exactly the architecture's linked startup followed by the supplied body
- Body length is 8 for ARM64 or 36 for RV64; body bytes are otherwise unrestricted
- Destination size is below 2^32 and fits the complete `E`
- Fuel is at least 4929

There is no premise that execution already returned or that a proposed output
was accepted. Name/text representability follows from the bounded lengths.
The actual validation, initialization and copy loops have exact termination
lemmas. Helper calls require the complete four-byte footprint, copy/scan indices
are genuine in-bounds accesses, and u32 sums/increments are nonwrapping. Startup
read footprints and fixed legal shift counts are exported explicitly. The
zero-then-overwrite proof passes through an ordered patch normal form that is
proved equal to the independent field specification. It does not apply the
unrelated generic linker model to the source writer.

`image_frame` derives unchanged storage size and the entire output array
`E ++ dst.toList.drop E.length`, for arbitrary nonuniform destination contents.
`image_output_admitted` proves the exact returned u32 length and connects the
actual reported prefix to the existing, unchanged `StrictProfile` and `accepts`.
Only that prefix is the artifact: an oversized caller buffer's preserved suffix
must not be submitted as trailing ELF bytes. The independent specification is
bounded by 4896 bytes on ARM64 and 4928 on RV64. Each loop receives the same fuel;
4929 covers the largest initialization plus its terminating guard.

These results establish envelope production and copying only. They do not
validate canonical source identifiers, bind an opaque body to an operation, or
prove the Go seed, extractor translation, C compiler, generic linker, source
compiler, ISA execution, or Linux startup/exit behavior. The existing source
checker remains responsible for canonical source grammar and body binding. The
successful-domain theorem `image_exact` does not itself assert universal
refusal. The separate [total-outcome refinement](native-envelope-total-outcome.md)
now proves exact success or unchanged zero-return refusal for every representable
destination/name/text array and arbitrary UInt32 architecture at fuel at least
4929. The compiled-Oak refusal tests remain supplementary finite evidence.

`TestLeanNativeBitwiseEnvelopeProof` first checks exact regeneration, then runs
`tools/native_envelope_proof/check.py`. It rebuilds every local transitive import
from current source in an isolated output directory with pinned Lean 4.33.1,
`-j1 -t0 -M3000`, and no candidate `.olean` search path. The exact exported-root axiom
inventory admits only `propext`, `Quot.sound`, and `Classical.choice`; missing,
extra, duplicated, custom, `sorryAx`, or native evaluator roots fail. Both tests
are mandatory in the existing `selfhost-image-producers` inventory. Existing
compiled-Oak full-buffer and complete-tuple admission tests are retained.

Focused command:

```sh
go test ./compiler -run '^(TestE2ESelfHostedBitwiseELF(Extract)?|TestLeanNativeBitwiseEnvelope(Extract|Proof))$' -count=1
python3 -m unittest discover -s tools/native_envelope_proof -p 'test_*.py'
```

These tests are separate from checker authority and do not alter existing
semantic/proof profiles.

The [raw complete-image integration](94-selfhost-image-admission.md) captures
these actual outputs for direct unchanged-checker admission and adds separate
mandatory exact producer/admission gates without replacing the existing gates.
