# Target support, verification and optimization maturity

Snapshot: 2026-09-17. This is a capability map, not a benchmark ranking or a
claim that every program on a target is verified. Supported spellings are
defined by `target.Supported`; detailed proof coverage is in
[STATUS](spec/STATUS.md), [native semantics](spec/94-assembler.md), and
[Wasm scalar v0](spec/91-wasm.md).

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
| `core/wasm32` | Experimental direct scalar OptIR→Wasm; independent engine execution tests | Source checks and engine validation only. No Wasm translation-refinement proof; verified-only mode refuses | Raw CFG dispatch baseline; no Wasm optimization or performance-parity claim |

## Embeddings and adjacent outputs

| Surface | Current state | What remains |
| --- | --- | --- |
| Browser playground | Local prototype hosts the Go compiler and executes `core/wasm32` output in separate workers | Browser automation/CI expansion, incremental editing, capability contracts, proof checker, deployment/security review |
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
