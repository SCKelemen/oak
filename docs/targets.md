# Target support, verification and optimization maturity

Snapshot: 2026-09-17. This is a capability map, not a benchmark ranking or a
claim that every program on a target is verified. Supported spellings are
defined by `target.Supported`; detailed proof coverage is in
[STATUS](spec/STATUS.md), [native semantics](spec/94-assembler.md), and
[Wasm scalar v1](spec/91-wasm.md).

Distinguish **implementation**, **execution tests**, **formal models/properties**,
**implementation refinement**, and **performance measurements**. A per-body
native `proven` verdict is not a theorem about an entire executable, OS, loader
or runtime. Passing QEMU tests is not a hardware performance measurement.

| Target | Code generation / execution evidence | Formal verification boundary | Optimization maturity |
| --- | --- | --- | --- |
| `darwin/arm64` | Oak native + C; hardware E2E and benchmark workloads | Per-body seam/semantic validation for supported bodies; many models and partial implementation refinements. Full source→loaded Mach-O closure remains open | Most exercised Oak-native lane: SSA/memory cleanup, candidate search, register allocation, scheduling, scalar/vector transforms. Workload-dependent gaps remain |
| `linux/arm64` | Oak native + C; cross-build and QEMU coverage | Same AArch64 body machinery; Linux ABI/ELF and loaded-image closure are separate obligations | Shares generic/AArch64 mechanisms; macOS timings do not establish Linux performance |
| `freestanding/arm64` | Oak native + C; image/object and OS-pilot coverage | Conditional architectural/memory-model results and selected native body proofs; not a verified OS, boot chain or MMU implementation | Same backend where the profile admits it; OS-specific hot paths have selective evidence |
| `linux/riscv64` | Oak native + C; cross-build/QEMU coverage | RV64 body checker/verifier and selected refinements; aggregate/vector coverage and artifact closure are incomplete | Generic SSA plus RV64 transforms/allocation; less hardware workload/performance evidence than AArch64 |
| `freestanding/riscv64` | Oak native + C; bare execution tests | RV64 subset/ABI-specific proof coverage; not a whole bare-metal system proof | Scalar native path and selected transforms; CPU features/soft-float ABI constrain coverage |
| `darwin/amd64`, `linux/amd64`, `freestanding/amd64` | C backend/external compiler; platform-dependent execution/cross-build tests | Shared frontend proof work applies where stated. No Oak amd64 native semantic-verification lane or complete C→machine proof | External C compiler performs machine optimization; no Oak-native amd64 optimization claim |
| `freestanding/arm` | C/external compiler; Cortex-M emulator fixtures (STM32-class direction) | Shared frontend/data-model work, not verified ARM32 instruction lowering or arbitrary STM32 hardware | External C compiler; MCU runtime/code-size/power benchmarking still needed |
| `freestanding/riscv32` | C/external compiler; RV32 emulator fixtures | Shared frontend/data-model work, not an Oak RV32 native verifier | External C compiler; no mature RV32 hardware performance suite |
| `core/wasm32` | Experimental direct scalar OptIR→Wasm, including 32/64-bit division/remainder with Oak trap/overflow behavior; exact structured/CFG binding; independent bounded Go byte/type validator and engine execution tests | LEB prefix model theorems and finite production/Lean pins; full decoder/validator and translation refinement open. Verified-only mode refuses | Direct returning blocks, bounded acyclic CFGs, compact loops, pre-test loops with acyclic bodies, and recursively nested structured loops/conditionals; byte/instruction gates and preliminary local V8 timings. Raw irreducible CFGs dispatch; no representative browser/native parity claim |

## Embeddings and adjacent outputs

| Surface | Current state | What remains |
| --- | --- | --- |
| Browser playground | Local prototype: bounded reusable Go compiler sessions, source-linked diagnostics and cold/warm timings; disposable `core/wasm32` execution workers; local Chrome smoke and lifecycle unit tests | Browser automation/CI expansion, incremental editing, memory/payload measurements, capability contracts, proof checker, deployment/security review |
| WASI | Planned; not a registered supported target | Versioned interface/ABI choice, bindings, capabilities, runtime tests, host-contract/refinement work |
| Component Model / WIT | Planned | Type/resource ownership mapping, adapters, canonical ABI, component artifact and host verification |
| Metal kernels | Separate constrained kernel output, not an `os/arch` target | Kernel-specific evidence must not be presented as whole-program or GPU-driver verification |

Native equality certificates currently have **audit-only** coverage; formal
certificate models do not imply that certificates authorize every native verdict.
The source/checker, encoding, relocation, linking, loaded image and environment
boundaries must each be accounted for. The existing `Oak.Target` model covers
C/native targets; adding the experimental Wasm target does not extend its proofs.

For actual performance, use [native measurements](../benchmarks/native/README.md)
and [kernel results](../benchmarks/kernels/RESULTS.md), including their revisions,
flags, semantics and host-noise qualifications. Static instruction counts and
optimizer feature counts are not evidence of wall-clock superiority.

Update this matrix when a target/embedding is added or a proof boundary closes.
Record a concrete theorem/test/measurement, not a percentage-complete score.
The [Wasm/WASI/browser roadmap](notes/wasm-wasi-browser-2026-09.md) records the
new target's explicit acceptance gates.

## Adding a target: reuse and porting gates

The first [shared target-description/emission boundary](notes/target-pipeline-2026-09.md)
is implemented: C/native/Wasm entry points resolve checked descriptions, and
Wasm materialization/byte admission uses the typed DAG. Native ISA/cost dispatch
below these entry points still needs the further refactoring described here.

Adding an OS/ABI on an existing ISA, adding an external-C target, and adding an
Oak-native verified backend are different projects. A target spelling is not
evidence of native lowering, proof coverage or competitive performance.

| Layer | Reuse today | Work for a new target |
| --- | --- | --- |
| Source checking and semantic projection | Parser, type/effect/resource checks, specialization, checked OptIR CFG/SSA | Admit the target data model and supported source subset; keep target-dependent layouts/facts explicit |
| Middle-end optimization | SCCP, GVN/DCE, loops/LICM, checked region-memory analyses and cleanup; artifact identities/preservation machinery | Consume admitted results; prove/validate the target lowering, preserve trap/effect/float contracts; regenerate layout-dependent facts |
| Candidate orchestration | Typed DAG, search budgets, proof gating, metrics/cost interfaces | Register target candidate families, provenance and verdict policy; no inherited AArch64 cost assumptions |
| Native machine algorithms | CFG, liveness, allocation and scheduling over explicit defs/uses | Instruction shapes, register overlaps/classes/constraints, ABI, spill/copy rules, scheduling barriers and actual CPU costs |
| Verification engine | Symbolic bit-vector/equality and certificate-replay machinery for its supported semantic domains | ISA/VM transition semantics, architectural state, memory/endian/atomic/trap behavior, source/ABI bindings and model correspondence |
| Executable artifact | Some object/layout infrastructure and test harness patterns | Encoder and independent decoder, relocations/linking/loading or VM validation; exact-byte proof binding and environment assumptions |

This is **not yet a plug-in backend interface**. `machine/target.go` provides
real lane callbacks, but currently selects only AArch64 and RV64. Native lowering
and `asm/verify.go` still contain lane-specific branches, including RV64 versus
AArch64-default behavior. `opt.CostsFor` likewise defaults unknown lanes to
AArch64 costs. A new native ISA must not enter those defaults. Wasm instead
reuses checked structured OptIR bound to its canonical CFG through
`compiler/wasm.go`; it does not
yet consume the optimized native candidate pipeline or the native ISA verifier.

Recommended implementation sequence:

1. Freeze a small target profile: ISA/version/features, OS or embedding, ABI,
   integer/pointer widths, endianness, alignment, floats/atomics, artifact and
   runtime/host assumptions. Extend the target registry/model/tests together.
2. Establish an executable baseline: external C where an appropriate toolchain
   exists, or a minimal direct backend. Run the same semantic/edge-case programs
   on hardware or an independent emulator/VM. Label this tested, not verified.
3. Lower the admitted checked OptIR subset. For native targets, supply machine
   register/instruction/ABI adapters; for a stack VM, use its own structured IR
   and validator instead of pretending it has physical registers. Refuse gaps.
4. Add independent target semantics and translation validation. Reuse solver
   and replay algorithms, not another ISA's assumptions. Preserve source traps,
   effects, pointer authority and any explicit numerical-relaxation license.
5. Connect proofs to final decoded bytes and the ABI/loader/host boundary.
   Admit verified-only builds only for the closed profile and exact evidence.
6. Enable generic and target-specific candidates incrementally, with semantic
   tests and runtime/size measurements. Hardware costs do not transfer with
   generic legality proofs. Track regression gates and proof coverage separately.

The next abstraction improvements should be driven by the third backend:
explicit target data layouts and feature profiles; exhaustive, fail-closed
semantic dispatch; register-unit/operand constraints rather than an assumption
of interchangeable registers; and target-owned ABI, encoding and cost adapters.
Keep untrusted lowering/cost decisions separate from trusted semantic/checking
code. Do not build a universal backend framework before testing these seams.

`amd64` already has the external-C route; Oak-native x86-64 verification is new
work (32-bit x86 would be a separate profile). Its overlapping registers and
instruction/flag semantics need explicit adapters ([Intel manuals](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html)).
Neither Motorola 68k nor SPARC is currently registered. A 68k port must select a
CPU/ABI and model distinct data/address registers, width/alignment and byte order
([Motorola family manual](https://www.nxp.com/docs/en/reference-manual/M68000PRM.pdf)).
SPARC adds register-window/calling-convention concerns
([Oracle register windows](https://docs.oracle.com/cd/E19120-01/open.solaris/819-3196/6n5ed4hmj/index.html)).
These are useful tests of portability, not small opcode-table additions or
promises of immediate formally verified support.
