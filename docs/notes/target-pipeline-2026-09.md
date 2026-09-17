# Target descriptions and emission pipelines

Status: first implementation, driven by the Core Wasm/browser backend. This is
an incremental porting boundary, not a universal backend or a new proof claim.

## Go lessons

Go separates generic SSA optimization from architecture lowering and final
object emission. Its shared compiler infrastructure is used across GOARCH
variants; the lowering rules remain architecture-specific
([compiler overview](https://go.dev/src/cmd/compile/README)).
Its assembler accepts a partly abstract instruction representation, but that
does not make arbitrary assembly portable between ISAs
([assembler guide](https://go.dev/doc/asm)). The `LinkArch` adapter combines an
architecture description with target callbacks for preprocessing, instruction
editing and assembly ([object interface](https://go.dev/src/cmd/internal/obj/link.go)).
References reviewed 2026-09-17; these are architectural lessons, not pinned
dependencies or imported formal authority.

For Oak, reuse this separation and cross-build discipline, not Go's runtime,
GC/stack ABI, assembly syntax or global target initialization. Keep target
configuration in compilation values so browser requests and concurrent builds
cannot change one another's selected architecture. Untrusted code generation
and independently checked semantics must remain separate adapters.

## Implemented boundary

`target.Target.Describe()` resolves the existing closed `os/arch` set to a
value-only `Description`: backend route, execution environment, container,
implemented native ISA, baseline pointer width, C int width and byte order.
Unknown combinations fail; missing native support is explicit, never an
AArch64 default. Wasm has no C ABI (`CIntBits=0`) and names the import-free Core
environment, not the browser hosting the compiler.

`Description.Validate()` checks every field against the registered profile.
`EmitC`, `EmitNative`, `EmitWasmWithReport` and C-toolchain resolution use this
boundary. Even an explicit external compiler cannot license an unregistered
target. Existing C/native lowering, CPU resolution and verdict policies remain
otherwise unchanged. This baseline is **not** a complete ABI/data-layout or
CPU-feature manifest and does not replace legacy frontend width options.

The shared internal typed emission helper owns this small graph:

```text
target description ─────┐
                       ├── materialized candidate ── admission ── returned output
owned checked input ────┘
```

It uses the existing `opt.ArtifactGraph` and typed root/derived builders. A
backend supplies two independently revisioned callbacks: materialization and
admission. Both consume the exact target description; the checker does not
infer its target from untrusted materializer metadata. No candidate/report
escapes on failure or cancellation. Producer
identities include exact input and target keys. There is no persistent or
cross-request artifact cache. Frontend `Stage.Then` remains ordinary code;
generic graph context cancellation does not make the frontend interruptible.

Wasm is the first production consumer of this helper. Its checked raw CFGs are
deep-snapshotted and fingerprinted; declaration order of identical CFGs is
normalized. The existing OptIR analysis DAG now snapshots its root too, so a
caller cannot mutate an already-keyed input through retained slices.

`wasm.EncodeCandidate` is explicitly untrusted and carries no byte-admission
report. `wasm.Emit` retains its safe combined API. The compiler's graph uses
encoding followed by independent `Module.ValidateBytes`, including export
manifest checks. `Compilation.EmitWasm()` retains its return type;
`EmitWasmWithReport()` also returns diagnostic target/key/dependency provenance.

Hashes and graph nodes identify computations; they do not prove them correct.
The input digest identifies the checked CFGs, not a full source-frontend
refinement certificate. Wasm admission is currently byte/type validation only:
`TranslationVerified=false`, `-verified` refuses, and optimized OptIR candidates
still require a future target-specific equivalence/admission path.

## Browser consumer

The browser displays the same pipeline report instead of reconstructing stages
from UI assumptions. “Compile only” checks/compiles and enables download without
instantiating the guest module or requiring `main`. “Compile & run” retains the
separate execution worker and timeout. Both use the same compiler API.

WebCrypto hashes the actual submitted UTF-8 source and decoded output bytes
before a byte-admission status/download is displayed. Matching two report
strings is insufficient. Source edits or Stop invalidate in-flight hash work;
old completion cannot restore an artifact. These are integrity and operational
checks, not a signature, trusted compiler certificate or sandbox proof.

The browser now reuses only the loaded compiler worker for bounded sessions,
not checked inputs or DAG artifacts. Each call constructs a fresh compilation.
The versioned worker protocol, request/worker identity checks and cancellation
controller are browser-host concerns, not new semantic artifact nodes. Structured
diagnostics reuse the compiler's diagnostic sink and UTF-16 ranges; source hashes
bind even failed requests before diagnostic navigation. Cold/warm request timing
is displayed separately from semantic admission. See the
[playground contract](../../playground/README.md) for budgets and lifecycle tests.

## Next increments

1. Extend browser measurements to memory and deployment payloads; add real
   browser CI and incremental editing. Bounded sessions, structured diagnostics
   and initial cold/warm request timings are implemented.
2. Broaden Wasm semantics and implement validated structured lowering; connect
   generic optimized candidates only with appropriate target evidence.
3. Evolve target descriptions into explicit layout/feature/ABI contracts as
   memory, browser imports and WASI actually need them. Keep compiler host,
   target ISA and execution environment independent.
4. Move native ISA dispatch, register constraints, ABI and artifact adapters
   behind exhaustive target-owned boundaries. Current native verifier/cost
   defaults are not removed by this increment.
5. Extend independent decoded-byte/translation/certificate checking, with
   target-local proof coverage and performance regression gates.

Tests cover description parity/refusal, recipe identity, admission failure,
stale reports, CFG snapshot ownership, old/new Wasm API byte equality, actual
engine execution and browser compile-only/hash/cancellation behavior. They do
not constitute universal implementation refinement or a throughput improvement.
