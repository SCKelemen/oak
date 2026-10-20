# Complete production native-object fixtures

Run from the repository root with the pinned Go toolchain and locally available
module dependencies:

```sh
GOTOOLCHAIN=local GOPROXY=off GOSUMDB=off go run -p=2 ./tools/native_object_fixtures -out diagnostics/native-object-fixtures
python3 tools/native_object_fixtures/enumerate_mutations.py diagnostics/native-object-fixtures --materialize
```

The Go helper calls the unchanged production
`compiler.New().WithSource(...).WithTarget(...).EmitNativeObject(asm.ELF).Get()`
entrypoint. It emits AND, OR, XOR for Linux AArch64 and Linux RV64, with the
canonical source-name/parameter-name families `bitwise/x/y` and
`Mix9/left0/Right9`. The different source-name lengths cross section-header
alignment buckets. Original source is preserved byte-for-byte; no main function,
assembly unit, reconstructed source, or selected-body-only artifact is used.

Outputs:

- Twelve complete `.o` files and their original `.oak` source files.
- `FixtureData.lean`: decimal literals of the complete source/name/object bytes.
  These are data definitions only, without admission claims or theorems.
- `manifest.json`: exact lengths/digests, diagnostic ELF inspection, a disjoint
  full-byte region inventory for exhaustive single-bit flips, and explicit
  mutations of every header/section/symbol field plus every body/name/padding
  byte, truncations, and appended bytes. Apply each mutation independently.
- `targeted-mutations.json`: adversarial cases including overflow/overlap,
  symbol aliases/binding/type/extent, shifted complete ELF images with an extra
  duplicate symbol or body-touching relocation, flags, wrapper replacement, and
  replaying actual OR code against AND source. `--materialize` also writes each
  complete mutated object under `targeted-mutants/`.

For exhaustive bit coverage, flip each bit 0–7 independently at every byte of
`bit_flip_regions`. For exhaustive truncation, retain lengths 0 through
`object_length - 1`. Also check cross-target, cross-name, and cross-operation
replay while retaining the original requested declaration/target/operation.

The helper checks expected shape defensively before output (seven sections,
three non-null symbols, expected named GLOBAL/FUNC symbol, empty data and
relocations, ARM eight-byte or RV 36-byte body). This Go-side inspection,
Python mutation generation, and digests are diagnostics. They neither prove ELF
semantics nor create production verification authority; independent Lean
acceptance and rejection checks must consume the complete original objects.

Prepare the kernel-decide fixture source (without compiling):

```sh
python3 tools/native_object_fixtures/render_lean_fixtures.py diagnostics/native-object-fixtures
```

The resulting `spec/lean/NativeBitwiseObjectFixtures.lean` contains all twelve
positive whole-object cases, every explicit base-manifest mutation for both
`bitwise` AND objects, the targeted adversarial cases for those objects, and
wrong-target/name/opcode/NUL-name/leaf replay refusals. `lean-fixture-counts.json`
records the generated case count; generation is not proof checking. These declarations must be kernel checked with the pinned Lean toolchain after
`Oak.NativeBitwiseObject`; the gate below uses bounded shards with at most two active processes.

Run the complete fixed-fixture and theorem-axiom gate with the pinned Lean on PATH:

```sh
python3 tools/native_object_fixtures/check.py
OAK_REQUIRE_NATIVE_OBJECT_LEAN=1 python3 .github/scripts/required_backend_tests.py native-object
```

The checker builds only the native-object model dependency closure, then checks
the retained fixtures in batches of at most sixteen declarations per fresh Lean
process, with at most two single-thread processes active. This bounds elaboration
memory while preserving every case.
The fixture source is outside the Oak library discovery directory to avoid
unbounded parallel aggregate compilation. An independent pinned inventory fixes all 15 model and 547 fixture theorem names.
Deletion/renaming/duplication fails before any build. Every public theorem
requires one exact axiom report, allowing only `propext`, `Quot.sound`, and
`Classical.choice`. The existing formal workflow runs the full gate.
The separate fresh-emission Go regression checks actual objects from the current
compiler, not just these retained literals. Neither gate authorizes production
receipts, compiler verdicts, or external loader/ISA claims.
