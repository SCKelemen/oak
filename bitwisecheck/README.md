# Checked canonical bitwise bundles

This optional package admits one narrow tuple: the exact original canonical
ASCII two-u32 AND/OR/XOR declaration, a complete Wasm module, and complete Linux
AArch64/RV64 ELF64 relocatable objects. Admission is fresh Lean kernel checking
and fixed theorem-type/axiom-closure auditing, not a compiler verdict or digest
comparison. Existing native/Wasm verification flags are unchanged.

## API

```go
installation, err := bitwisecheck.Install(ctx, "/offline/lean-4.33.1-linux.tar.zst")
if err != nil { return err }
defer installation.Close()
bundle, err := installation.CheckBundle(ctx, source, wasm, arm64ELF, rv64ELF)
if err != nil { return err }
// Each getter returns an owned copy of the exact admitted bytes.
wasmToPublish := bundle.WasmBytes()
receipt := bundle.Receipt()
```

`Install` supports only Linux amd64 hosts and needs the existing trusted host
`/usr/bin/zstd`. It never downloads software or modifies a system installation. Supply an offline copy
of the official Lean release asset:

- Release: https://github.com/leanprover/lean4/releases/tag/v4.33.1
- File: `lean-4.33.1-linux.tar.zst`, exactly 570405234 bytes
- SHA-256: `890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235`
- Lean commit: `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`

The archive is copied into a fresh private owned directory while hashing. Only
that checked snapshot is extracted. Safe regular/directory entries and the
release's same-directory library symlinks are accepted; special files, traversal,
symlink ancestors, hard links, duplicates and ownership/setuid restoration are
refused. There is no caller-provided expected hash, runtime, runner, manifest,
proof root, import path, plugin or options API.

The authoritative 41-file Lean proof/auditor closure is embedded directly from
`spec/lean` and freshly compiled using the extracted runtime, absolute executable
paths and a controlled environment. Caller `.olean` files, `.lake`, `LEAN_PATH`,
`LEAN_SYSROOT`, `PATH` hooks and loader environment variables are not imported.
Installation runs a freshly audited positive control and requires a successful
kernel proof of a negative control. Timeout/OOM/error is not a passing control.
No installation authority is persisted or reconstructed from JSON.

Setup uses roughly 544 MiB of compressed input and 2.9 GiB extracted, plus proof
build outputs. The first measured fresh build took about three minutes on the
development host. Reuse an installation instead of rebuilding for each request.
`Close` cancels and reaps active work before deleting its private files. Completed
bundles remain historical admissions after `Close`.

## Admission and bounds

The only variable request text is decimal numeric byte lists. Fixed roots are:

1. `Oak.CheckedBundleRequest.admitted`
2. `Oak.CheckedBundleRequest.binding`
3. `Oak.CheckedBundleRequest.all_inputs`

The auditor independently constructs and kernel-checks their exact expected
types and bodies, requires current-request theorem declarations and only
`propext`, `Quot.sound`, `Classical.choice` in transitive axiom closures. It echoes
all four exact byte arrays and the checked declaration. Go rejects duplicate or
missing/unknown JSON keys, null/non-integer bytes, extra output, wrong metadata,
wrong/missing/duplicate roots, forbidden/duplicate axioms and mismatched echoes.
A success record grants nothing until the subprocess has exited successfully.

Fixed request caps: source 2048 bytes, Wasm 1024, each ELF 2048, generated driver
65536, stdout 65536 and stderr separately 65536 bytes; 240 seconds including queue
time. Every Lean process uses `-j1 -M4096 --trust=0`. Lean processes are serialized
per Go process, and each installation serializes Check/Close. The 4096 MiB value
is Lean's allocator budget, **not** an OS-enforced total RSS/virtual-memory limit.
The canonical positive request measured about 8 seconds and 2.34 GiB RSS in the
initial direct checker run; `-M2048` refused that request. Setup has a 30-minute
wall deadline, 4 GiB extracted-file-byte cap and 20000-entry cap. Bounds are
refusals, not automatic unbounded retries or completeness promises.

Context cancellation, closed/uninitialized installations, missing tools,
unsupported/malformed bytes, resource exhaustion and any later subprocess
failure return no checked bundle. There is no fallback to an old verdict.
Callers must not concurrently write input slices while the synchronous snapshot
is being copied; later mutation is harmless. Sealed payloads are immutable strings internally, including against safe reflection
that could otherwise expose unexported byte-slice storage. All byte/receipt getters
copy.

## Receipts and exact claim

Zero/nil `CheckedBundle` values are invalid; private authority is created only
by successful admission. A JSON receipt is a historical diagnostic report, not a
capability. `CheckedBundle.UnmarshalJSON` always refuses. Reverification requires
reading the actual source/artifacts and calling `CheckBundle` again. Diagnostic
hashes do not replace exact-byte comparisons. `proof_package` names the semantic
baseline commit; `proof_source_sha256` separately identifies the exact embedded
closure, including the current auditor.

The composed theorem observes universal full-u32 results within the existing
models. The receipt preserves these boundaries:

- Canonical ASCII closed grammar and existing typed-expression interpretation;
  no whole-language/package/parser/compiler correctness claim
- Wasm's bounded module loader/interpreter; no external engine/Core refinement
- ARM low W0/W1 inputs, arbitrary high halves, aligned base and base+8 below
  2^64, and the no-fault scalar projection
- RV LP64D entry, aligned base and base+36 below 2^64, SP >= 96 and 16-byte
  alignment, ordinary coherent readable/writable noninterfering 96-byte frame
- Flat section loading and immutable/separate instructions; no system linker,
  physical fetch/mapping/coherence, faults or physical return-destination proof
- No added composed SP/callee-save guarantee

The authentic Oak binary and embedded reviewed closure, official pinned Lean
kernel/runtime, fixed auditor/serializer/launcher, trusted host `/usr/bin/zstd`,
system libraries/OS and same-user filesystem custody are the trusted base.
Private snapshots do not protect against malicious same-UID processes, unsafe
in-process code or a compromised OS. `--trust=0` does not authenticate imported
`.olean` metadata; authenticated source-built import custody is essential.

## Tests

Fast tests: `go test ./bitwisecheck ./spec/lean`. To require the real independent
runtime tests without a skip, set `OAK_REQUIRE_BITWISECHECK=1` and
`OAK_BITWISECHECK_LEAN_ARCHIVE` to the exact offline archive, then run
`go test -timeout 40m ./bitwisecheck`. The equipped suite uses one installation
for real admission, mutation/copy custody, malformed tuples, cancellation,
concurrency, receipt replay, valid-record-then-process-failure and active Close.

The separate complete executable-image capability is documented in [IMAGES.md](IMAGES.md).
