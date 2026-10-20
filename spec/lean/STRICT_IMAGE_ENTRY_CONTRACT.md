# Strict original bundle to the existing RV64 ELF-entry consumer

## Validation boundaries

The pure `Oak.StrictImageEntryContract` projection is checked under the pinned
official Lean 4.33.1. It starts from the existing original-source/Wasm/
ARM64/RV64 strict bundle checker and preserves that source, parsed declaration,
and complete RV64 file. It adds no checker, alternate ELF profile, image-binding
record, or public checked capability.

The real-consumer modules in `../lean-sail429` require the actual pinned Lean
4.29/Sail build and are registered for the required CI gate:

- `OakSailStrictImageEntry`: the one-way admission adapter
- `OakSailStrictImageEntryExecution`: direct application of the existing actual
  entry execution theorem, retaining its exact full-state equality and premises
- `OakSailStrictImageEntryChecks`: existing explicit initialized-state witness
  plus two pure touching-stack layout facts

No external execution conclusion follows from the 4.33 diagnostic.
That diagnostic mechanically extracts only current pure admission expressions
under a conspicuous `ExtractedOnly` namespace. It does not import the external
model, substitute or axiomatize an execution theorem, or validate an execution
corollary against a stand-in. Actual consumption and its external axiom closure
must pass the real 4.29 gate.

Parent commit is the published combined head
`fbe9acd2194bd16efdc8386f38ac3fa2fca4988e`, tree
`0e5f93c50431647d56328e0961b72d0cb5e038e0`. Initial reviewed local commit
`84a5799889ac175b5bc3a408550701007a8b0f7d` has the identical tree and ordered
parents; only the unpublished branch ancestry was corrected.

No existing semantic source, frozen checker/auditor, compiled-in image source
manifest, upstream model/provenance hash, `prepare.py`, or public API changes.
The existing-file changes are only the 4.29 Lake configuration, Sail workflow,
and required-test runner/its unit tests. All old targets, suites and audits remain.

## Exact admission connection

`entry_preconditions` derives the five input facts needed by the actual entry
consumer, directly in already shared definitions:

1. `BitwiseSource.parse source = some d`, the original declaration identity
   required by `OakSailComposition.acceptsProjection` and its `acceptsFrame` alias.
2. The existing `RiscVFramedBitwise.accepts` check for the complete source-derived
   36-byte LP64D frame.
3. `MinimalELF.admittedBytes` for that body at this same image's `segment.entry+16`.
4. The exact eight-byte AUIPC/JALR prefix admitted at this same ELF entry.
5. The existing `ImageLayout` expression: low-RAM whole segment, aligned 96-byte
   initial stack frame, and whole-segment/frame separation.

`strict_source_entry_admitted_of_layout` is the smallest actual consumer
interface: original strict-check success plus the existing
`OakSailImageLoad.ImageLayout image sp` premise yields literally
`OakSailEntrySource.acceptsEntry source d image sp = true`. No production
extraction/refactor, second layout predicate, body replacement, independent
function address, successful load, or execution outcome is assumed.

The implication is one-way. Strict admission owns all 16 startup bytes and
symbol/metadata records; the older entry consumer needs the first eight startup
bytes and body and deliberately accepts changes to the excluded post-return
ADDI/ECALL suffix. The tests retain this positive/negative contrast.

`source_entry_binding` reuses the existing `ImageBinding`: exact parse/render/
grammar identity, actual symbol ownership/uniqueness, body bytes/address/file
extent, flat loading and bounds. It adds decoded segment
`(65536,4096,65536,64,64,5,4096)`, body address `entry+16`, and successful flat
loading of all 16 checked startup bytes. The actual body and startup belong to
the same complete file.

The numerical stack assumptions remain explicit: `96 ≤ sp ≤ 0x02000000`,
`sp % 16 = 0`, and `65600 ≤ sp-96 ∨ sp ≤ 65536`. Equality is intentional;
frames ending at 65536 or starting at 65600 are disjoint touching boundaries.
Additional pure theorems expose nonwrapping bounds and bytewise separation of
the entire startup/body from the full reserved frame.

## Direct external execution, without a new execution model

`strict_typed_entry_clocked_prefix` passes the new admission proof directly to
`OakSailEntrySource.accepted_typed_entry_clocked_prefix`. From the left/right
arguments onward, its signature and full result are unchanged. It keeps
`MemoryConfig`, `StepProfile`, `ClockProfile`, `t.toNat + 5 < deadline.toNat`,
and x2/x9/x18/x10/x11 mappings, together with the same state, saved registers,
clock values, step and previous PMA regions.

The result is literally the old source grammar, typed `evalX`, and full state
identity after `boundedPlatform 11`, ending at `e_entry+8`. The initialized
witness uses the existing `initialState` and `initial_profiles` and applies this
new corollary. The audit compares both entire signatures/results to the originals and requires
each fixture execution to be exactly the closed application to its own checked
bundle and layout, with no extra premise or replacement theorem. These source
guards supplement, but do not replace, the actual kernel execution check.

The runtime remains initialized Machine/Bare with explicit ABI/platform state.
The specified loader installs RX code and RW, non-executable stack PMA regions;
ELF flags do not themselves configure hardware. No reset, firmware or OS
reachability follows. The existing separate exit-readiness theorem stops before
ECALL execution. There is no Linux-process/syscall/termination claim here.

## Required real 4.29 gate

The existing RV64 CI lane now additionally runs:

```
cd spec/lean-sail429
lake build OakSailStrictImageEntry OakSailStrictImageEntryExecution OakSailStrictImageEntryChecks
python3 -m unittest discover -p test_strict_entry_audit.py
python3 strict-entry-audit.py
```

Then, from the repository root with `OAK_REQUIRE_RV64_LEAN=1`:

```
python3 -m unittest discover -s .github/scripts -p test_required_backend_tests.py
python3 .github/scripts/required_backend_tests.py strict-entry
```

The runner requires exactly `TestRV64StrictEntryToolchainSelection`, the root
`TestRV64StrictEntryBitwiseCompilerMatchesLean`, and the latter's `interfaces`,
`pins`, and `audit` children. Missing/zero selected tests,
failed process/package, nested skip, missing child, or unexpected child fails.
The test itself also fails on unavailable tools/export when required.

The fixture compiles three fresh canonical AND/OR/XOR sources through current
Wasm and native production emission, verifies both RV64 proposal routes agree,
and retains the original source plus whole Wasm/ARM64/RV64 bytes. It rechecks
`BitwiseSourceImageParity.check` in the actual 4.29 project before deriving
admission and invoking the real initialized execution corollary. It consumes
neither a 4.33 receipt nor copied cross-version proof objects. Atomized native
profile proofs retain every original byte, including the long zero padding.
Controls cover changed source/type/Wasm/body/startup/entry, stack placement and
the broader-consumer/strict-checker suffix contrast.

`strict-entry-audit.py` pins 4.29 and trust level zero. Each Go/Python subprocess
validates the selected project's tracked `lean-toolchain`, uses that project's
cwd even for temporary proof files, and sets a process-local `ELAN_TOOLCHAIN`
to override conflicting inherited values. Actual version checks remain mandatory;
no global environment is changed. The pure diagnostic selects its own 4.33.1
pin in the same way. It inventories all 13 new
model roots and, when a compiler certificate is supplied, exactly 48 fresh
fixture roots. Pure admission roots admit only the standard three Lean axioms;
the admission adapters retain their exact standard-three closure. Both model
execution roots and all three fixture executions must equal the real original
entry theorem's exact 77-name external closure. Standard-only and external
execution policies are separate. Missing/duplicate/unlisted reports and extra
source proof helpers fail closed; the fixture cannot supply its own allowlist.

The full 42-module shared pure import closure is covered by workflow push paths.
Compared with the old entry closure, five existing modules plus the new pure
bridge must re-elaborate under 4.29: `BitwiseSourceImageParity`,
`NativeBitwiseImage`, `NativeBitwiseObject`, `AArch64BitwiseFunction`,
`AArch64ReturnEncoding`, and `StrictImageEntryContract`. Their successful 4.33
build does not establish 4.29 compatibility. The actual project compiles tracked
`../lean` sources into its own cache. No upstream export, provenance or source
preparation change is required.

## Local evidence and reproduction

With official Lean 4.33.1 on `PATH`:

```
cd spec/lean
lake build Oak.StrictImageEntryContract
python3 check-strict-image-entry-contract.py --evidence-dir /absolute/local/evidence
```

This diagnostic builds the projection, mechanically extracts current pure
consumer declarations, and reuses the actual adapter proof text. It rechecks
selected complete committed native compiler fixtures for all three operations,
with exact original sources and a canonical checked Wasm companion. That
companion is not described as freshly compiler-generated. Both touching stack
boundaries and numerical/source/artifact refusals are checked. Source/snippet
SHA-256 values, generated source, build/kernel logs and 47 standard-only root
closures are retained. Extracted expressions exist only as local test data.

Fresh compiler tuples/certificate can additionally be retained with
`OAK_RV64_STRICT_ENTRY_INPUTS_OUTPUT` and `OAK_RV64_STRICT_ENTRY_PINS_OUTPUT`.
Their generation is not evidence of successful Sail admission/execution. An
environment without the pinned full Sail export and 4.29 toolchain cannot check
the actual consumer build, fixed 77-name audit or required fresh execution
fixture. Reports must distinguish those missing checks from the pure diagnostic.
A missing-model preflight is recorded as unavailable, never as a semantic
refusal or a passing test.

Optional future sharing of only `ImageLayout`/`startupBytes` with old-name aliases
could remove repeated statement syntax, but is unnecessary for this direct
consumer connection and is not part of these changes.
