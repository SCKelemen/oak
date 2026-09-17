# Wasm, WASI and the browser: design and roadmap

Status: staged implementation, not a claim of a fully verified target.
See [target maturity](../targets.md) and the [scalar profile](../spec/91-wasm.md).

## Objectives and boundaries

Make Wasm a first-class portable Oak output, and make a local-first language
playground possible without a compilation server or self-hosted Oak compiler.
Continue native performance work; the browser project is a bounded vertical
slice, not a reason to restart the optimizer architecture.

Separate three things:

1. **Compiler host:** Go's js/wasm port runs the compiler inside a browser.
2. **Compilation target:** Oak lowers checked OptIR to a Core Wasm module.
3. **Embedding:** browser or WASI capabilities supply explicitly modeled host
   services. Neither is required for import-free scalar modules.

The first registered target is `core/wasm32`. `core` names an embedding profile,
not an operating system. Browser execution initially uses that same output;
there is no pretend WASI implementation behind it. Future `wasi/wasm32` needs
an explicit interface version and command/reactor/component ABI decision.

## Formal foundation

Core Wasm specifies validation, execution and binary representation. The
living specification currently identifies itself as 3.0 (2026-09-11); that
document date is not the initial 3.0 release date. Pin an immutable revision
and feature subset when connecting Oak's formal model, rather than depending
on the moving specification URL.

WASI 0.3 is the current release family. Its interface definitions do not by
themselves prove host filesystem, network or scheduling behavior. The
Component Model repository still describes a formal specification and
reference interpreter as future work. WasmCert provides mechanized groundwork,
but its current binary parser is described as unverified and its SIMD execution
uses reference-implementation functions. Audit each reused component's actual
theorem boundary and license.

Primary references, checked 2026-09-17:

- [Core Wasm scope](https://webassembly.github.io/spec/core/intro/introduction.html)
- [Binary modules](https://webassembly.github.io/spec/core/binary/modules.html)
- [Numerics](https://webassembly.github.io/spec/core/exec/numerics.html)
- [WasmCert](https://github.com/WasmCert/WasmCert-Coq)
- [Component Model status](https://github.com/WebAssembly/component-model)
- [WASI releases](https://wasi.dev/releases)
- [Go browser hosting](https://go.dev/wiki/WebAssembly)

## Compiler architecture

```text
source → existing checks → owned checked raw OptIR CFG ─┐
                                                      ├→ materialization
                         checked target description ──┘        │
                                                              ▼
                                            independent byte/type admission
                                                              │
                                                         Wasm bytes
```

Reuse the existing checked OptIR projection; do not add an AST-to-Wasm compiler.
The first emitter uses an i32 program counter and structured dispatch loop for
general CFGs. Each SSA value has a Wasm local. Edge arguments are read before
any destination is assigned, preserving parallel phi copies and cycles.
This is intentionally simple, not an optimized structurizer. Preserve natural
structured regions or introduce a validated structurizer later.

The target, input, materialization and admission nodes now use the shared typed
artifact DAG, with diagnostic recipe/dependency reporting. Frontend checks stay
linear; native selection retains its stronger verifier policy. See the
[Go-inspired target pipeline boundary](target-pipeline-2026-09.md).

Do not consume optimized candidates merely because their CFG validates.
Future optimization admission must bind preservation/equivalence evidence to
the exact input and output artifact identities. The current raw-CFG route
does not bypass a failed optimization proof by relabeling its result.

For the initial single-module profile there are no relocations or imports.
Later multi-module linking, data layout, allocation and Canonical ABI adapters
are additional implementation and proof work, not automatically solved by Wasm.

## Verification ladder and acceptance criteria

1. **Executable profile:** actual bytes validate in an independent runtime;
   differential/edge-case tests cover the admitted operations. Current level.
2. **Decoded-byte boundary:** bounded independent decoder and validator, formal
   correspondence to the pinned rules, malformed-input/fuzz coverage. The Go
   decoder/validator and test infrastructure are implemented. `Oak.WasmLEB`
   proves the mathematical prefix decoder against its grammar, with range,
   length and suffix laws; production Go outcomes have finite kernel pins.
   Universal Go decoder/validator correspondence remains open. Matching
   an encoder and decoder is insufficient if they share the same mistake.
3. **Translation refinement:** source-to-OptIR and OptIR-to-decoded-Wasm behavior,
   including traps, calls, loops, divergence and state. No value-only proof
   may silently drop observable effects or introduce success on a trapping path.
4. **Certificate authority:** an independently checked certificate binds exact
   source, semantic profile, target, import contracts and executable bytes.
   Untrusted search cannot promote a verdict or substitute an unrelated root.
5. **Host/component closure:** supported import contracts, memory and resource
   ownership, effect traces, component adaptation and implementation refinement.

Keep the UI labels separate: source checked; engine validated; translation
verified; certificate checked. No checkmark for steps not performed. The first
emitter reports `translationVerified: false`; `-verified` refuses it.

The browser engine/JIT, host imports and the compilation/execution of the proof
checker remain explicit assumptions unless separately connected. A small Go
checker compiled to Wasm is not automatically a verified checker binary.
Hashes identify artifacts; they do not establish semantic correctness.

## Semantics that need deliberate lowering

- Oak signed minimum divided by -1 wraps; Wasm signed division traps. Preserve
  Oak's specified exceptional arithmetic, not the convenient instruction.
- Wasm masks shift counts. Oak's checked count semantics must not be silently
  replaced by modulo-width shifting. Pin logical versus arithmetic right shift.
- Preserve narrow integer normalization, checked conversions and Bool domains.
- Float NaNs, signed zero, conversion traps and rounding require their own
  relation. No implicit FMA/reassociation license; proof-licensed relaxation
  must name a contract and account for the selected Wasm feature semantics.
- Linear-memory containment is not Oak object/lifetime/provenance safety.
  Pointer authority, overflow in effective addresses and subobject bounds
  survive lowering. Memory growth and allocation failure are observable.
- Explicitly state recursion/stack/resource limits and termination assumptions.

Scalar v1 now lowers 32/64-bit division and remainder with zero-divisor traps
and Oak's signed overflow behavior: division by `-1` becomes wrapping negation
instead of executing a trapping Wasm `div_s`. The independent validator admits
the eight new typed opcodes, with a new profile/validator/encoding identity.
Shifts, casts, narrow integers, floats, memory and pointers still refuse rather
than receiving a provisional incompatible interpretation.

## Local-first browser architecture

The checked-in prototype is `playground/web`, built by `playground/build.sh`.
A Go-built compiler worker accepts one source file through `playground.Compile`.
It rejects imports/globals before resolution and never runs user code. A
separate disposable worker runs the final module with an empty import object.
The page receives diagnostics, typed exports, hashes and bytes; user text is
rendered with `textContent`, never HTML or JavaScript evaluation.

The loaded Go runtime is reusable, but `playground.Compile` constructs a fresh
compiler for each source. The worker protocol binds each reply to a monotonic
request ID and the current worker instance. One request may be active at a time;
late replies from cancelled workers/requests cannot complete a newer request.
After 32 completed requests or 60 seconds idle, the worker is recycled. Source
edits cancel active compilation by termination, retain only an idle runtime,
and clear old diagnostics/artifacts. Stop discards both workers. Ordinary
source errors retain the compiler session; protocol/runtime failures discard it.

Structured diagnostics project the existing compiler model into a bounded
browser DTO (64 diagnostics, 8 KiB messages, code/severity/source and optional
zero-based UTF-16 range). The page checks the source hash on refusals as well
as successful emission, validates ranges and offers text-only source navigation.
Unlocated backend/profile failures do not acquire invented source positions.
This is request-level reuse, not incremental compilation or persistent caching.

“Compile only” runs no guest code and needs no `main`; it returns the same
admitted module and pipeline report for inspection/download. Before publishing
an artifact, the page hashes the actual source/module bytes and compares them
to the response. Stale asynchronous digest results are discarded after edits
or Stop. This detects mismatched artifacts, not malicious-compilation semantics.

Current budgets: 32 KiB source, 1 MiB executable module, 90 seconds compiler
startup, 10 seconds compilation, 2 seconds execution. Stop terminates workers;
stale responses are ignored. These are UI cancellation limits, not a formally
proved per-worker memory quota. Core v1 has no guest linear memory, but compiler
and engine allocation/stack exhaustion still need operational protection.

No CDN dependencies, source upload, persistent browser storage, domain changes
or deployment are part of this increment. Compiler artifacts are loaded from
the same origin. A production deployment needs CSP/security headers, isolation
from authenticated applications, pinned reproducible assets, browser testing,
abuse/resource review, accessibility work and transfer/startup measurements.

Later: syntax-aware editing, incremental diagnostic requests, virtual multi-file
projects, examples, explicit host console capabilities, proof inspection and
certificate replay. Gate stronger features on their actual evidence.

## Roadmap

| Milestone | Deliverable / acceptance gate | State |
| --- | --- | --- |
| W0 | Scalar raw-CFG emitter, direct `.wasm` CLI/API, fail-closed profile, independent runtime tests | Implemented subset: scalar v1 adds 32/64-bit division/remainder with Oak trap/overflow behavior |
| B0 | Local compiler/editor/runner prototype; cancellation; explicit unverified status | Initial implementation |
| W1 | Pinned Core rules, independent bounded decoder/type validator, malformed-byte/engine/fuzz tests; LEB model theorems and finite Go/Lean pins | Partial; universal production decoder/validator refinement open |
| W2 | Integer/control-flow source-to-decoded-bytes refinement; authoritative certificate admission | Planned |
| B1 | CI browser tests, incremental diagnostics, accessible editing, measured payload/startup/latency | Partial: bounded reusable sessions, source-linked diagnostics, request timing instrumentation and deterministic lifecycle CI; expanded Chrome harness awaits rerun; incremental compilation, memory measurements and browser CI open |
| W3 | Memory/spans/aggregates, pointer and allocator contracts; wider source coverage | Planned |
| W4 | Validated structured lowering, local reuse, direct stack expression emission; measured speed/size gates | Planned |
| H0 | Minimal browser import contracts, explicit capabilities and observable traces | Planned |
| H1 | Selected versioned WASI interfaces and runtime conformance tests | Planned |
| C0 | WIT mapping and component generation, explicit borrowed/owned resources and Canonical ABI | Planned |
| C1 | Component/WASI implementation refinement; state any remaining host premises | Research / planned |

Native speed and Wasm speed are separate measurements. A browser's JIT chooses
physical allocation, scheduling and ISA instructions. Measure guest runtime,
module size, compiler download/startup, compilation latency and memory separately.
The current dispatch-loop implementation makes no native-parity claim.

Initial execution evidence (2026-09-17): actual bytes pass V8 engine tests;
headless Chrome compiles the example locally and returns 4950, terminates an
infinite loop after the execution deadline, and clears stale artifacts after
invalid source. Dedicated CI requires engine tests and browser-compiler builds.
The first Go compiler payload is approximately 39 MiB uncompressed; no cold
download/startup baseline or Wasm runtime performance advantage is claimed.

The session increment reports startup, compiler work and request round trip
separately for cold and warm requests. The Chrome harness records one cold and
three warm calls, requires one compiler-worker instance, and checks recovery
after a source error. It imposes no noisy timing threshold and excludes guest
runtime/hash/engine-validation time from compilation metrics. Such measurements
do not establish browser memory bounds, network-transfer performance or faster
generated Wasm. Production payload and memory work remain open.

Session-increment validation (2026-09-17): nine deterministic JavaScript tests
cover lifecycle, production worker protocol and host-timer receiver safety;
the Go diagnostic/isolation tests and browser compiler build pass. The first
expanded Chrome run stalled at startup. The timer-receiver fix is unit-tested,
but the post-fix Chrome rerun was blocked by local sandbox policy. No successful
post-fix browser run or measured cold/warm speedup is claimed here.

Independent-engine test infrastructure now shares `internal/wasmtest` across
scalar execution and decoded-byte conformance. `OAK_WASM_TEST_ENGINE=node|deno`
selects a known executable explicitly; this avoids version-probe flakiness but
does not skip execution or replace its result. Automatic discovery retains
three-second Node/Deno probes and reports bounded startup errors. Required or
explicitly selected missing engines fail closed; no semantic failure falls back
to another engine. CI selects Node deliberately. Engine execution is still
conformance evidence, not source-to-Wasm refinement or browser-host validation.

With Deno explicitly selected (2026-09-17), the actual scalar/loop/Bool execution
and integer-operation conformance tests pass. The independent byte-validator
comparison covers 4,683 cases, with all 91 Oak-accepted cases also accepted by
the engine. Seven engine-selection unit tests cover explicit selection,
automatic fallback, cancellation/whitelisting, diagnostic retention, required
versus optional policy, bounded output and invalid command refusal. This closes
the opaque engine-discovery failure, not the separate Chrome rerun gap above.

Scalar-v1 execution evidence (2026-09-17): `TestWasmDivisionRemainderExecution`
compares 4,360 arithmetic/trap cases against BigInt reference arithmetic, then
checks calls, guarded branches, unused results, constant-zero traps, zero-trip
loops and a remainder-based GCD loop. Independent byte validation now compares
5,875 cases, including the eight new division/remainder opcodes; all 160
Oak-accepted cases also validate in the engine. Malformed effect declarations,
operation shapes, operand widths and old profile manifests still refuse.
These are conformance tests, not a new formal refinement or performance claim.
