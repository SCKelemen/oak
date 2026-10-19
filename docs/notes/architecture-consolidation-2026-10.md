# Architecture consolidation: native target boundary (October 2026)

## Baseline and non-goals

This audit is based on the `specification` branch as of October 19, 2026.
The repository already contains shared parser/typechecking, SemIR, OptIR,
machine algorithms, target descriptions, native bodies, certificate checking
and ISA-specific proofs. Do not introduce a second universal target IR or
weaken existing verifier obligations merely to reduce file lengths.

Largest high-risk handoff files at this snapshot include `asm/verify.go`,
`asm/loops.go`, `nativegen/nativegen.go`, and
`typechecker/typechecker.go`. Size motivates auditing responsibilities;
it is **not** evidence of semantic duplication by itself.

## First concrete boundary

`machine.targetFor` rejects unknown architecture lanes, while historically
`opt.CostsFor` silently used ARM64 weights. This discrepancy made an
unreviewed backend extension look partially implemented, even though a
cost model cannot establish target correctness.

After this patch:

- `opt.CostsFor(arch)` returns `(TargetCosts, error)`; explicit
  `arm64` and `rv64` are the only admitted lanes.
- The compiler's `nativeSearch` resolves the model before registering
  candidate transforms.
- `lowerNativeBodies` carries failure as a native compilation diagnostic
  rather than proceeding with ARM64 costs for an unrelated ISA.
- `opt.Search.Run` retains its old nil-cost default for generic/in-memory
  search users. This first patch closes the **production native** entry
  and does not claim all cost dispatch or target profiles are fully sealed.

This changes no verifier, ISA decoder, ABI, certificate, or proven semantics.
A cost-model choice is an optimization heuristic, **not** proof authority.

## LRAT acceptance dependency guard

The `internal/lrat` Go acceptance kernel is a deliberate trust boundary.
Its production sources currently require only `fmt`, `strconv` and
`strings`. A source-level unit test now parses every non-test Go file in
that package and refuses any import outside this reviewed set, including
imports of the compiler, prover, Oak-generated packages, reflection or unsafe
machinery. New imports require updating the reviewed allowlist, explicitly
acknowledging an expansion of the trusted base.

The guard was exercised in an isolated Go 1.23 harness: the approved import
set passed, an injected otherwise-valid `errors` import failed, and removing
it restored a pass. This establishes the guard's local mechanics, **not**
production build success or a proof of LRAT acceptance soundness. A complete
package test and Go/Oak/Lean correspondence remain release gates.

## Cleanup dependency plan

| Stage | Ownership / design boundary | Gate before merge |
| --- | --- | --- |
| A1 | Native target selection and cost registration | Reject unknown/empty architecture; preserve ARM64/RV64 costs; native compiler diagnostic |
| A2 | ISA semantics vs. generic `asm` verification | Map every current `asm/verify.go` lane-dispatch default; extract exact target adapter interfaces only where semantics match |
| A3 | Trusted LRAT checker vs. prover and producer | Document complete inputs, allocation ownership, replay state and error semantics; prohibit compiler/prover imports into kernel |
| A4 | Type identity, inference, and authority | Prove scoped substitution rollback and alias handling; reject same-name binder conflation |
| A5 | Native generation and code shape | Separate machine algorithm, ISA encoder, ABI, and artifact/link concerns without widening admitted profiles |
| A6 | Compiler bootstrap replacement | Stabilize Go/Oak interfaces; compare both implementations and self-build artifacts before replacing the Go seed |
| A7 | Cross-target proof composition | Bind checked source, OptIR, exact decoded bytes, object layout, loader and machine execution with explicit environmental assumptions |

For each stage, preserve a paired positive/negative regression corpus, exact
proof or test evidence, and observed performance before/after. No PR counts
toward roadmap completion until merged to `specification`; a green isolated
model proof is not a universal production refinement.

## A2: call-ABI responsibility extracted

The first `asm/verify.go` split is deliberately behavior-preserving. The
`Verdict`, `VerdictKind`, dependency-union logic and outcome labels now live
in `asm/verify_verdict.go`. The two executor call-boundary methods,
`forgetCallerSaved` and `summarizeCall`, now live unchanged in
`asm/verify_calls.go`. This isolates the largest direct call/ABI decision
from the main verifier without changing the certificate authority boundary.
Tests pin AArch64 and RV64 register invalidation and the distinction between
proved, witnessed, mismatch and trusted outcomes.

**Important boundary:** A file move is not a universal Go implementation
refinement, a target-independent ISA adapter, or a new Lean/Sail theorem.
Next refactors must separate call ABI policy from symbolic execution **using
the current behavior as the reference**, and must explicitly fail closed for
unsupported ISA profiles rather than inheriting AArch64 defaults. The entire
`asm` package and its proof/integration gates must pass before semantic
rewrites are merged.

## A2: explicit verifier ISA dispatch (October 19, 2026)

The native verifier now registers AArch64 and RV64 call-ABI policies explicitly
in `asm/verify_native_policy.go`. The existing caller-saved register lists,
entry-readable recognition (including RV64 ra/x1), RV64 FPR treatment, and AArch64 vector/flag clobber
behavior are unchanged, but no other target can inherit ARM64 policy.

- `Check`/`CheckWithFacts` reject an unknown or empty native architecture
  before applying the AArch64 seam rules.
- `Verify` returns a **trusted/refused**, never **proven**, verdict for an
  unregistered architecture; this guard runs before diagnostic environment
  switches and before inspecting a signature.
- `summarizeCall` refuses an unregistered ISA and preserved-register inference
  no longer treats `arch != RV64` as proof of AArch64 semantics.
- Unknown-ISA call-state invalidation conservatively discards register facts.

This does **not** make the remaining instruction executor into a plugin
architecture. The separate RV64 vector/flags behavior is unchanged; any new
policy is subject to review against the psABI, executable ISA semantics and
proof/correspondence gates. The next stages are target-owned instruction
semantics, verified result-register layout and full machine-byte closure.

## A2: entry-register provenance after native calls (October 19, 2026)

The verifier previously treated some *entry-readable* registers as perpetually
recreatable. A call deleted the current symbolic value, but a later lazy read
of RV64 `ra/x1` or AArch64 `x30` produced the original `entry.xN` again.
This could introduce an unsupported value into an otherwise proved path.

`symbolicState.invalidEntryGPR` now records the entry values invalidated by
ABI call clobbers. All call-result shapes (unit, scalar, floating-point,
vector, multiword aggregate and memory result) use `clobberGPR` to invalidate
both the register value and its entry provenance. A *new, actual register
write* remains readable. Forks clone the invalidation independently and joins
combine invalidation by union; an untouched path cannot reinstate an entry
value lost on another path.

Tests pin RV64 ra and AArch64 link-register invalidation, post-call writes,
preserved registers, fork isolation, and conservative joins. These are
executable correspondence tests, not a new Lean proof of the full path
executor. Full `asm` regressions and source-to-machine proof composition
remain release gates.

## A2: parametric Lean provenance theorem and Go correspondence gate

`spec/lean/Oak/AssemblerEntryProvenance.lean` defines a pure,
architecture-indexed register-provenance state for ARM64 and RV64, with
separate materialized values and invalidated entry authority. Theorems
establish no resurrection after a call, safe explicit rewrites, immutable
fork isolation, conservative join behavior (either branch clobbered), and
continued availability when both branches explicitly write.

The architecture-indexed type excludes cross-ISA joins by construction,
whereas the Go executor rejects mismatched `state.arch` dynamically.
`asm/verify_entry_provenance_refinement_test.go` independently sweeps
the current per-ISA entry-register masks and observed call clobbers and
ensures the theorem/example obligations are present. A dedicated
`assembler-entry-provenance` formal CI job builds the Lean module and
executes those Go checks independently of the full compiler suite.

**Trust boundary:** The Lean proof covers the formal model, not an
automatically extracted implementation; the bounded Go corpus tests
the correspondence but does not universally prove it. Source-to-ISA
refinement, complete call-result paths and whole `asm` tests remain
required for full verified status.
