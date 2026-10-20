# Native envelope proof gate

Run from the repository root with the official pinned Lean 4.33.1 toolchain:

```sh
OAK_REQUIRE_SELFHOST_IMAGE_PRODUCERS=1 go test ./compiler \
  -run '^TestLeanNativeBitwiseEnvelope(Extract|Proof)$' -count=1
python3 -m unittest discover -s tools/native_envelope_proof -p 'test_*.py'
```

The Go extraction test regenerates the complete type-checked three-function
closure and compares every byte with `NativeBitwiseEnvelopeExtracted.lean`.
An intentional regeneration uses `OAK_LEAN_EXTRACT_UPDATE=1`; review every changed
definition before updating the committed artifact.

The proof test first repeats drift checking, then invokes `check.py`. Every local
transitive import is rebuilt from current source in a temporary output directory
with official Lean `-j1 -t0 -M3000`; only release core/Std modules are reused. The
script refuses nonlocal dependencies outside those release namespaces. Candidate
`.olean` outputs are never searched. Each imported source is hashed before and
after checking to reject concurrent changes. The committed audit manifest must
match an independent exact theorem inventory. Missing, extra, duplicate, custom,
`sorryAx`, and native-evaluator axiom reports are rejected.

The memory limit is a fixed 3000 MB per sequential Lean process, with a
900-second timeout per invocation and a 20-minute outer proof-test timeout.
An initial 1500 MB gate run failed with Lean's explicit excessive-memory error
in the 71-write main composition. With unchanged proof sources, a single-module
resource probe at 3000 MB passed in 119.758 seconds with a maximum resident set
of 1,874,072 KiB. That probe reused built dependencies for measurement and was
not a fresh-closure claim. Linux `getrusage(RUSAGE_CHILDREN).ru_maxrss` supplied
the RSS measurement. No timeout, trust setting, proof obligation, or theorem
premise was weakened to address the resource limit.

The successful-domain theorem has no successful-return hypothesis. It covers all
valid 1–256-byte profile names, both architectures, arbitrary fixed-size body
proposals, arbitrary fitting representable destination arrays, and fuel at least
4929. It proves exact output bytes, length, suffix preservation and admission of
the reported prefix by the unchanged strict native-image profile. Universal
refusal, extractor correctness, general linking, source/body authority, compiler
correctness and ISA/OS execution remain outside this theorem. See
[the envelope specification](../../docs/spec/94-selfhost-bitwise-elf.md).

The required `selfhost-image-producers` inventory retains all existing finite
compiled-Oak and tuple-producer tests and adds extraction and proof roots. The
separate `selfhost-image-admission` inventory remains unchanged.
