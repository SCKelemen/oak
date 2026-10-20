# Separate checked complete-image bundles

`InstallImages` and `CheckedImageBundle` form a separate opt-in capability for
original canonical source, a complete Wasm module, and complete one-function
Linux ARM64/RV64 ET_EXEC images. The existing `Install`, `CheckedBundle`, object schema, legacy compiler verdicts
and resource limits remain separate and unchanged. The object closure now has
42 files, including the shared control-flow planning dependency. No object capability or diagnostic receipt licenses image admission.

```go
installation, err := bitwisecheck.InstallImages(ctx, archivePath)
if err != nil { return err }
defer installation.Close()
bundle, err := installation.CheckImageBundle(ctx, source, wasm, armImage, rvImage)
if err != nil { return err }
armToPublish := bundle.ARM64ImageBytes() // fresh owned copy
receipt := bundle.Receipt()            // diagnostic ImageReceipt
```

## What the capability establishes

The fixed checker independently reads all four exact owned byte snapshots in
one request. Successful admission establishes original canonical source grammar,
source-derived names and operation, complete image symbol/section/extent/load
binding, and universal successful full-u32 named-function local invocation in
the existing models. The audited `all_inputs` root also includes:

- ARM: zero-extended result in X0, preservation of every other register, return
  PC equal to caller X30, and SP/NZCV preservation.
- RV: sign-extended result in a0, preservation of registers other than x0/a0 relative to the initialized LP64D entry state,
  restored SP/s1/s2, clearLow-RA return, exact `frameMemory`, and unchanged memory
  outside the sixteen saved bytes of the required 96-byte frame.

These guarantees retain the explicit initialized ABI/frame, aligned valid stack,
coherent readable/writable noninterfering frame, immutable/separate instructions,
no-fault scalar and bounded Wasm model premises. They do not prove execution from
ELF entry, startup, Linux loading/process exit, physical hardware/ISA faithfulness,
external Wasm engine/Core refinement, or whole-language/compiler correctness.

Both image receipts report ELF entry 65536 separately from named-function
addresses 65548 (ARM) and 65552 (RV); file offsets are 4108/4112 and body extents
8/36. These are checked profile consequences, never caller-supplied premises.

## Installation, custody and identity

The public host remains Linux amd64. Supply the same exact pinned official
Lean 4.33.1 archive described in [README.md](README.md), with the trusted host
`/usr/bin/zstd`. Shared private setup verifies and extracts a fresh private copy,
then freshly builds the separate 43-file image closure directly from embedded
sources. The object build remains a distinct 42-file closure. Both kinds share implementation,
not mutable installations or trusted build caches. Simultaneous object and image
installations duplicate the roughly 2.9 GiB distribution and proof builds.
The two fixed public constructors alone supply private source/identity/control
functions to common pinned setup. The common machinery validates the closed kind,
distinct seal and complete profile without referencing either profile's proof
sources or driver. Object-only consumers can therefore dead-strip the image
closure; ordinary CLI/browser builds retain neither optional installer. No image
installation/checking is added to object requests. The source proposal regular
expression is initialized lazily.

Image proof package: `c9452b2c3772ccf9367be36735063855b0cef5d1`.
Image closure SHA-256: `9060359c9cdba07e6fa81bd1058b8453614861e01ad2b0eb33b3eb0916405208`.
Object closure SHA-256: `ab2af11d0ae904b63fa3fba54cd2ade4d16f85c52649c851ddae6ac99c09f659`.
Both identities intentionally roll over with the reviewed shared
`Oak.ControlFlowPlan` dependency and compatible ARM64 plan aliases; the image
roots and separate object/image admission contracts are unchanged.
The image digest has distinct length-framed domain separation and includes the
exact strengthened model and independent new-image auditor. No frozen proof
source is rewritten by the runtime.

Installation requires a real positive admission and a successful silent kernel
refusal proof; timeout, OOM or failed processes are not passing negative controls.
No caller-provided source/import path, runner, proof text, theorem type, prebuilt
proof object or cache enters the public API. `--trust=0` does not authenticate
imported objects by itself; fresh-source custody remains essential. Same-UID
attackers, unsafe code in the caller, and compromised host/toolchain/system
libraries remain outside this boundary.

## Request and receipt boundary

Input bounds are source 2048 bytes, Wasm 1024 bytes and each complete image 5120
bytes. The strict profile supports names of 1–256 ASCII bytes and actual maximum
production image sizes 4896/4928 bytes. Every original byte is preserved. The
fixed numeric renderer compresses only the actual 3976-byte zero header gap after
checking that every byte is zero. It never reconstructs or normalizes metadata,
names, body bytes, padding, source or artifacts.

Generated driver, stdout and stderr each have separate 65536-byte caps. Requests
have a 240-second deadline including both installation and global Lean queue
waits. Setup has the unchanged 30-minute deadline. Every Lean command uses
`-j1 -M4096 --trust=0`; the Lean allocator budget is not an OS RSS sandbox. These
bounds are fail-closed limits, not a promise of completeness for every byte tuple.

Fixed roots are `Oak.SourceImageParityRequest.admitted`, `.binding` and
`.all_inputs`. The new auditor independently constructs their exact types and
rechecks reachable current-file bodies, requiring safe monomorphic closed
current-request declarations and only `propext`, `Quot.sound` and
`Classical.choice`. The runtime validates the distinct audit schema/profile,
strict field-specific integer byte arrays, complete exact echoes, reconstructed
original declaration, exact root inventory and axiom policy. Duplicate/missing/
unknown JSON fields, logs, additional records and any unsuccessful process exit
refuse authority.

Cancellation and `Close` kill and reap the process group before private files are
removed. A state lock linearizes successful sealing with `Close`. Sealed payloads
are immutable strings; getters and receipt slices are copies. Completed bundles
remain historical admissions after `Close`. Zero values are invalid, and JSON
unmarshalling always refuses authority restoration. Receipt schema
`oak.checked-image-bundle.v1`, hashes and serialized diagnostics are not tickets
or caches; actual bytes must be checked again.

## Validation

Fast checks: `go test ./bitwisecheck ./spec/lean`.
For mandatory real admission set `OAK_REQUIRE_BITWISE_IMAGECHECK=1` and
`OAK_BITWISECHECK_LEAN_ARCHIVE` to the exact archive, then run the dedicated
`checked-image-runtime`, `checked-image-sources` and `checked-image-bundle` required
suites. The runtime suite uses Go `-race` for its exact live inventory and real
equipped lifecycle checks; Linux amd64 CGO/compiler support is required rather
than silently skipped. Lean flags and resource limits are unchanged. The
image-only workflow preserves existing object jobs. Required named
inventories reject missing cases, skips and process failure.
