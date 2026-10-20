# Original-source / complete-image parity (local proof layer)

This layer is deliberately separate from the production ET_REL checked bundle.
It adds no runtime receipt, transport, embedded-source inventory, compiler API,
production authority, ELF startup execution, or external ISA/hardware claim.

## Contract

`Oak.BitwiseSourceImageParity.check` parses the unchanged original canonical
source, derives its declaration/name/operator, and checks a complete Wasm module
and both complete ARM64/RV64 executables through `NativeBitwiseImage`. It returns
only that parsed declaration. Unsupported syntax and mismatched artifacts refuse.

The accepted binding includes the actual decoded named symbol, strict complete
profile, unique name, complete body and extent, exact flat load, and in-file /
nonwrapping / aligned address facts. No caller supplies a trusted native address,
body, load-success assertion, or execution-success assertion.

`accepted_all_input_success` chooses the two decoded named functions and then
quantifies over every u32 input pair and compatible caller state. It establishes:

- Exact original-source meaning and the existing typed-expression evaluation
- Complete-module Wasm invocation success
- Full-u32 ARM64 and RV64 results
- ARM zero-extension, other-register preservation, X30 return, SP and NZCV
- RV LP64D result representation, register preservation, SP/s1/s2 restoration,
  return PC, exact saved-word memory, and the existing outside-16-byte footprint

The RV premise is the existing aligned, mapped ordinary coherent 96-byte frame,
instantiated at the decoded RV function address. The ARM model is the existing
no-fault scalar/ordinary-RET projection. Code and data remain separate local
projections; physical fetch, translation, Linux loader/syscall behavior, actual
hardware, and external model/exporter faithfulness are not proved. Whole startup
and nonloaded ELF metadata are bound as bytes but are not executed.

## Fixed local auditor

`Oak.BitwiseSourceImageParityAudit` defines `#oak_source_image_parity_audit`.
Current-request definitions and theorem roots live in `Oak.SourceImageParityRequest`:

- `source`, `wasm`, `arm`, `rv`, and source-derived `declaration`
- `admitted`, `binding`, `all_inputs`

The auditor reconstructs expected root types from the fixed model, forces kernel
checks, rechecks every reachable current-file definition/theorem body, requires only the existing standard-three axioms,
and echoes all input bytes. Input caps are source 2048, Wasm 1024, native images
5120 each. The diagnostic schema is `oak.source-image-parity.audit.v1`; the profile
is `bitwise-source-complete-images-local-invocation-v1`.

Current-file dependency cycles, unsafe/polymorphic helpers, and unsupported local
declaration kinds are refused. This is a fixed numeric-request format, not a
sandbox for arbitrary Lean commands.

The consumer must require zero process exit, exactly one record, the expected
schema/profile/root inventory, and byte-for-byte input echoes. Imported proof
objects/metadata, fixed source closure, toolchain and executor custody remain
external prerequisites. This diagnostic does not itself confer production trust.

## Focused reproduction

Use pinned Lean 4.33.1 and the repository's pinned Go toolchain. First build only
the prerequisites `Oak.BitwiseSourceLowering` and `Oak.NativeBitwiseImage` in
`spec/lean` (or reuse a verified identical-source build). Put the toolchain's
`lean`, `lake`, and `go` on PATH.
The runner validates `spec/lean/lean-toolchain` and explicitly selects its exact
`leanprover/lean4:v4.33.1` pin in every Lean child environment. This also works
through elan with no default toolchain when the child runs in the isolated
evidence directory; an inherited `ELAN_TOOLCHAIN` cannot redirect selection.

Generate current production native inputs with the existing producer:

    go run -p=2 ./tools/native_image_fixtures -out /tmp/native-images -verify-pins

Then run:

    python3 tools/source_image_parity/check.py /tmp/native-images --output /tmp/source-image-check

The runner compiles the two new modules one process at a time with `-j1 -M3000`
and 240-second command limits. `--reuse-build` is only for controlled, already
compiled identical-source modules. `--reuse-fixtures` is a development-only
reuse path requiring unchanged generated source, native model, compiled proof
hashes and a previously successful exact native-root audit; it is not a
production cache trust mechanism. The runner renders fresh native fixture proofs from the actual production
outputs, requires literal byte equality with all eight selected executable/source
files, independently checks the retained byte/source pins, and compiles current
complete Wasm from those exact sources.
It does not run the broad native mutation matrix.

Four complete triples cover AND/OR/XOR and a consistent rename. Separate controls
exercise source/name/operator/module/body-only mismatches, unsupported source,
thirteen auditor refusals (wrong/conditional/weakened roots, declaration/root-kind
substitution, imported roots, unauthorized axioms/native evaluation, disabled
kernel checks, invalid helper bodies after a transient skip, and nonzero trust), and a process failure after a valid audit
record. The latter checks the exact successful byte-echo record before requiring
the final nonzero exit, and is reported separately. Each negative must have
exactly one intended error; unrelated proof failures cannot satisfy it.
Source/artifact refusal roots and all public model roots are audited. Expected
model theorem statements and complete model/auditor source hashes (including
binding/contract predicate definitions) are pinned in `expected-roots.json`.

Evidence contains generated proof files, exact input hashes, complete auditor
records, per-process wall/RSS/exit metrics and a final `report.json`. There is no
success report until every required focused check and audit finishes.

## Mandatory hosted gate

`.github/workflows/source-image-parity.yml` adds a separate required-test job on
all specification pull requests and pushes to the specification/consolidation
branches, with no path filters or optional skip. It installs pinned Go 1.27.1,
elan 4.2.2 and Lean 4.33.1, rebuilds prerequisites, generates actual production
native output on the checkout, and runs the focused gate without reuse flags.
The 30-minute job and 240-second subprocess limits bound work; all failures
propagate to the final exit. This source change does not configure repository
branch-protection settings or claim a hosted run has occurred.

`expected-cases.json` pins the exact tuple, source-refusal statement, auditor
refusal/error and late-failure inventories. Sixteen lightweight harness controls
reject missing/skipped/extra results, changed identities, altered valid-looking
hashes, malformed lengths, and disagreement with actual generated bytes. They
also reject missing or changed toolchain pins before launch and check explicit
selection, inherited-selection overrides, and isolated-cwd launcher behavior.
`verify_report.py` independently requires the complete final report, exact
counts/inventories, model/auditor hashes and retained source/image identities.
The CI job invokes both the controls and final report validator unconditionally.

## Checked representative resource point

The final October 19 local focused run proved both complete native image admissions,
source/Wasm composition and the final audit in one process, with 35-byte source,
41-byte Wasm, 4648-byte ARM and 4680-byte RV inputs. Lean 4.33.1 with `-j1 -M3000
--trust=0` completed in 42.78 seconds at 2,235,120 KiB maximum RSS, including
recursive current-dependency rechecking. The earlier root-only audit took 25.65
seconds at 2,093,404 KiB; its evidence is retained separately. This is a
representative small-name measurement, not a validated maximum-name/maximum-input
production resource envelope. An earlier 768 MiB cap stopped immediately after
imports; that bounded resource failure is retained separately from proof results.

The four complete tuples, fourteen source/artifact refusal roots, fourteen model
roots, thirteen auditor negatives and one late-failure control passed. The upstream
full fixed-image mutation gate and independent review are separate prerequisites;
this local result does not imply that either gate has finished.
