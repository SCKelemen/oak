# RV64 relaxation proofs

`Oak.RiscVRelaxation` extends the [compressed control-transfer encoding
proofs](94-rv64-compressed-control-proofs.md) to shrinking instruction layouts.
The production loop in `asm/rv64_encode.go` calls `rv64RelaxPass`, which takes
one snapshot of instruction and label offsets and shortens the admitted
control transfers. It repeats until a pass makes no changes.

## Layout model

A layout is a list of booleans: `true` means a two-byte instruction and `false`
means four bytes. `offset` sums widths before an instruction-boundary index.
Labels retain those indices as widths change, including the boundary after the
last instruction. `delta` subtracts source from target using unbounded integers.
`Shrinks newer older` permits only pointwise width reductions, preserving list
length and instruction order.

This models the expanded function after the non-control compression prepass.
It assumes valid label indices and two- or four-byte units. There are no padding
or alignment regions: the production RV64 expander rejects `align` directives.

## Proved guarantees

- Every offset and displacement is even.
- Forward displacements remain nonnegative and cannot increase when any subset
  of instructions shrinks. Reversing the endpoints gives the backward case.
- An admitted signed range `[-limit, limit)` remains admitted after shrinking.
  The proof preserves the asymmetric positive endpoint used by branch and jump
  encodings; it does not substitute an absolute-value bound.
- An accepted compressed branch or jump can be re-encoded at the new offsets,
  and its decoded displacement still reaches the same label index. These
  theorems compose with the previous encoding module's exact-target proofs.
- A pass only shrinks. Every changing pass strictly reduces `wideCount`, the
  number of remaining four-byte instructions.
- `relax` is a well-founded, terminating driver for any deterministic snapshot
  eligibility function. Its final layout is a fixed point and shrinks the
  initial layout. It takes at most the initial `wideCount` changing passes,
  bounded by the number of instructions, plus one unchanged pass to detect exit.
- Every range admitted before relaxation remains admitted in the final layout.

`relaxFuel` is a structurally recursive evaluation view used for concrete
production checks. Its equivalence to `relax` is proved when the fuel exceeds
the initial `wideCount`; its cutoff is not used as evidence of convergence.
Proofs use Lean's standard logical axioms, without native-evaluation or SAT
axioms.

## Production correspondence

The Go loop's existing body is extracted into `rv64RelaxPass` without changing
its admission policy or snapshot timing. The same helper is called by the
function writer and by `asm/rv64_relaxation_lean_test.go`.

The tests exhaust 3,279 small layouts: every short / wide eligible / wide
blocked arrangement through six instructions, with forward, backward, and
self targets. Blocked cases include pinned relocation units, nonzero JAL
destination registers, non-prime branch registers, non-control instructions,
and missing labels. Fixture candidate descriptors are supplied independently
of the production eligibility code.

Two larger functions exercise the compressed branch and jump range boundaries.
Each requires three changing passes: the last forward jump enables the second
transfer, which then enables the first and a backward transfer. Tests check
each pass, final label offsets, the emitted mixed-width stream, and independently
decoded compressed targets. The Lean-equipped workflow requires 934 concrete
claims for pass results, boundary offsets, final layouts, and changing-pass counts.

```sh
cd spec/lean
lake build Oak.RiscVRelaxation
cd ../..
OAK_REQUIRE_RV64_LEAN=1 go test ./asm -run '^TestRV64Relaxation' -count=1
```

## Remaining boundary

The mathematical layout and driver are proved; correspondence to arbitrary Go
executions is still a refinement obligation beyond these bounded tests. Machine
integer representation, pseudo-instruction expansion, instruction execution,
and linker relocations remain separate obligations.

A fixed point means that no candidate fits under the current snapshot policy.
It does not establish globally minimal code size. For example, a branch at
displacement +256 stays wide if nothing else shrinks, even though speculatively
shortening that branch itself would move its forward target to +254. A regression
test records this conservative behavior.
