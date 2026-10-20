# Complete production native-image evidence

This test-only gate binds the complete current `asm.WriteExecutable` output to
`Oak.NativeBitwiseImage.accepts`, including nonloaded metadata. It changes no
production verification API, receipt, or authority. It proves neither original
source parsing nor startup/ISA/OS execution.

## Current writer correspondence

The generator compiles each unchanged original declaration with
`compiler.New().WithSource(...).WithTarget(...).EmitNativeObject(asm.ELF).Get()`.
It proposes the complete named native body to the unchanged `asm.WriteExecutable`
with Linux, `Base: 0` (the fixed default `0x10000`), no data, alignment four,
and RV64 `RV64FloatABI: "double"`. It never appends `main`.
The Go object reader is an untrusted proposal producer. The final complete image,
requested source-name bytes, and expected modeled body are passed to Lean;
**no Go-extracted final address, symbol index, extent, or body is an admission
premise**. Lean independently decodes and binds those records.

There are eighteen actual writer images:

- AND, OR, XOR on ARM64 and RV64 for `mix/a/b` and `Mix9/left0/Right9`
- AND on both targets for one-byte, 256-byte, and 257-byte source names
- Sixteen accepted name/body profiles; the two 257-byte names are refused

Three-byte-name images are exactly 4648 ARM bytes and 4680 RV bytes. The maximum
accepted name yields 4896 and 4928 bytes. The defensive 5120-byte cap is not a
claim that a 5120-byte image is accepted under this canonical profile.
The complete source and image hashes, lengths, and requested names are reviewed
pins in `evidence.json`; regeneration in `--verify-pins` mode fails on drift.
Any pin update requires explicit writer/profile review, never automatic test
normalization.

## Kernel evidence and mutations

The retained fixture inventory has sixteen admission roots, sixteen derived
loader roots, and 706 refusal roots. Together with seven model roots, the fixed
gate audits exactly 745 theorem closures. The fresh-emission gate has sixteen
admissions, sixteen loader roots, 162 refusal roots, and 201 audited closures.
Every fixture theorem statement and theorem name is independently pinned.
Changing or weakening a statement, removing/duplicating a root, changing retained
input bytes, or missing/extra/malformed axiom reports fails before a successful
gate result. Only `propext`, `Quot.sound`, and `Classical.choice` are allowed.

The fixed AND/mix mutation matrix independently changes:

- Every ELF identification byte and every remaining ELF header field
- Every program-header, section-header, and symbol-record field
- Every startup, modeled function, name-table, section-name-table, short padding byte
- Header-padding start, adjacent byte, middle, and last byte
- Soft-float/RVC flags; shifted, shortened, extended, overflowing function extents
- Symbol aliases, wrong binding/type/section, section overlap, wrong links,
  extra-symbol/data/relocation declarations, writable segments and zero-fill tails
- Boundary truncations, appended zero/nonzero bytes, missing nonloaded metadata,
  oversized inputs, target/name/op/body replay and invalid requested names

The manifest also inventories every byte in disjoint regions for independent
bit-flip sweeps. The retained kernel cases are the stated finite mutation matrix,
not a claim that every possible malformed ELF has been enumerated. The universal
recognizer theorem covers arbitrary admitted inputs.

## Lossless representation and bounded checking

Images are represented as their exact first 120 bytes, 3976 zero bytes, and exact
suffix starting at 4096. The renderer first checks that the original gap is
exactly zero and expands its restricted generated expression back to the original
complete byte string. A changed gap byte is refused, never normalized away.
Unit controls cover gap start/interior/end and complete literal roundtrips.
The checker independently reconstructs retained inputs and checks all image,
source, and name pins, including the complete name-replay images.

Admission is still the full `accepts ... = true` statement. Its proof supplies
all strict-profile atoms through kernel decisions, with checked list identities
for the long zero gap and reads after it. Per-image header and length facts are
proved from actual bytes before rewriting; generated constants are never assumed. Loader roots instantiate `accepted_named_load`; they do
not independently assume loader success. Refusals derive a necessary checked
field (or exact admitted body slice) and contradict a small kernel-checked fact.
This avoids a single very expensive elementwise decision on thousands of zeros.
No `native_decide`, runtime observation, diagnostic hash, or extra axiom provides
a proof premise. Private helper closures are included transitively in root audits.

The checker builds only `Oak.NativeBitwiseImage`'s dependency closure. Fixtures
are outside the Oak library discovery directory. Shards contain at most four
positive roots or eight refusal roots, with fresh single-thread Lean processes,
a 3000 MiB Lean memory limit, and 240-second per-process timeout. The default is
one worker; `--jobs 2` is the hard maximum and should be used only with adequate
aggregate memory. `--report FILE` records elapsed time, peak child RSS, counts,
and bounds. Fixed and fresh results must be reported separately.

## Commands

Use the pinned Go 1.27.1 and Lean 4.33.1 on `PATH`, writable Go caches, and available
module dependencies. From the repository root:

```sh
GOTOOLCHAIN=local GOPROXY=off GOSUMDB=off go run -p=2 ./tools/native_image_fixtures -out diagnostics/native-image-fixtures -verify-pins
python3 tools/native_image_fixtures/render_lean_fixtures.py diagnostics/native-image-fixtures --output /tmp/FreshNativeImages.lean --fresh
python3 tools/native_image_fixtures/check.py --fixture-source /tmp/FreshNativeImages.lean --fresh --report /tmp/native-image-fresh-report.json
python3 tools/native_image_fixtures/check.py --report /tmp/native-image-fixed-report.json
python3 -m unittest discover -s tools/native_image_fixtures -p 'test_*.py'
OAK_REQUIRE_NATIVE_IMAGE_LEAN=1 go test -p=2 ./compiler -run '^TestNativeBitwiseImageLean$' -count=1 -timeout=30m
```

The Go regression executes fresh production generation, verifies pins, renders
fresh whole-image facts, and runs the fresh kernel gate. Missing Lean is a failure
when `OAK_REQUIRE_NATIVE_IMAGE_LEAN=1`. The mandatory formal workflow uses that
mode; a locally skipped test is not evidence of success.
