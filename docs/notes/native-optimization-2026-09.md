# Where the native lane stands, and the optimization program (2026-09-15)

This note captures the verification work that landed on the native lane
over 2026-09-13 to 2026-09-15, the burn-down that remains, and the program
that comes next: making the code the Oak assembler emits the fastest code
for the program, using what the compiler knows and no other compiler
does — the types, the proofs the checker carries, the borrows, and an
assembler whose every function is checked and verified against its
source — and proving each optimization down to the assembler. It is the
companion of `docs/spec/94-assembler.md` §9, `docs/notes/verification-chain-2026-09.md`,
`BENCHMARKS.md`, and `benchmarks/native/README.md`.

## 1. What landed

The verified profile. `oak build -verified` refuses a program with any
body the verifier does not prove equal to its Oak source and any body the
C backend still owns, and prints the burn-down grouped by reason
(`compiler/compilation.go` `verifiedProfile`). It is the gate the OS pilot
builds under.

The verifier's reach, in the order the increments landed (each has its
paragraph in `94-assembler.md` §9 and its end-to-end test):

- Record results of two chunks (x0/x1, a0/a1), padding through the
  defined mask; aggregate arguments by value; sum-type tags decided under
  the hypothesis that they name a variant.
- Table reads: a package-level constant array is a span named by its Oak
  identifier, on both lanes; `adrl`/`la` serve tables and constant globals.
- Frame memory as bytes: a never-stored slot is a fresh unknown, so a body
  that reads uninitialized frame memory is a mismatch, not a proof.
- Loops: exit tests that read memory, guards to a trap, internal
  short-circuit branches, frame spills and calls inside the body, spans
  written inside the body carried as loop memories, Bool loop variables,
  the conflict-directed coupling search bounded by node, term, and
  decision budgets; an assert is a no-op under the verifier's executor
  (upstream then made it a trap arm of the comparison).
- Bounded quantifiers `forall (x: T) { … }` / `exists (…) { … }`
  (`10-syntax.md` §3e): a Bool expression over finite domains in the
  interpreter, the C backend, the theorem decider (a fresh leaf per
  binder, eliminated from the diagram by cofactors), the Lean projection
  (`List.all`/`List.any` over the explicit domain), and the prover written
  in Oak end to end (parser, serializer, lowering, blaster, projection),
  with the Go ladder agreeing on every row and the projection byte for
  byte (`spec/oak/quantifiers.oak`).

Where the stdlib-bearing program stands (`examples/stdlib_builder.oak`,
`oak build -native -verified`, 2026-09-14 evening): arm64 201 proven, 25
witnessed, 252 trusted; rv64 179 proven, 24 witnessed, 186 trusted; no
mismatches, no checker refusals. The day began at 115 and 42 proven.

## 2. The verification burn-down that remains

In leverage order, from the `-verified` burn-down of the same program:

1. **Results beyond sixteen bytes through memory** (the x8 area). The
   summary must read the result leaves back from the caller's area and
   couple them; the lowering's side is done (`resultIndirect`).
2. **Loops that call functions with memory effects** (the path budget
   reaches 23 of 8 on `utf8_decode`-shaped bodies). A callee's span writes
   inside a loop body need the loop memory carried through the summary.
3. **Node-budget witnessed bodies** (eight on arm64): the decision over
   `/` by a non-power-of-two divisor and the wide multiplications. The
   uninterpreted quotient upstream added (`udiv`/`sdiv` as operations)
   covers the first; the rest want the grouped variable order tried per
   body, not per theorem.
4. **Vector and float parameters** are out of the verified profile by
   definition today (`asm/verify_simd.go` verifies the SIMD kernels' bodies
   against their Oak source; the profile counts them trusted). Admit them
   once the float operations' uninterpreted reading is the profile's
   stated semantics.
5. **RV64 catch-up**: span arguments that are not whole spans
   (`text_require`, `utf8_decode`), the by-reference record rules.
6. **The Lean subset for quantifier bodies**: a body with statements or a
   call to a program function is refused by both extractors; the fix is
   the do-block form inside the fold's lambda.
7. **The self-hosted prover's counterexamples** still name a binder's leaf
   (`x@q1`) where the Go decider's omit it; cosmetic, statuses agree.

## 3. The optimization program

The program itself is `docs/notes/optimization-2026-09.md` (the doctrine,
the survey of both backends, the table of facts Oak proves that a C
compiler cannot, the measured gaps, and the increments in measured
order), and the rules are `docs/spec/90-backend.md` §16. This note adds
what a day on the verifier contributes to it.

**Two levels of proof.** An optimization below the source — selection,
allocation, scheduling, guard elision, load combining, loop shape — is
proven by the verifier alone: the transformed body must still be proven
equal to its Oak body, function by function, and a body the verifier
cannot follow is re-lowered without the transform (the strength-reduction
increment's fallback is the model). Extending the verifier's reach is part
of such an optimization's cost, never a reason to trust it. An
optimization at the source — inlining, unrolling a reduction over
independent accumulators, fusion — rewrites the checked tree, so its
meaning-preservation is a law stated in Lean over the extraction
(`95-extraction.md`), the way the source inliner's expansion is exactly a
call's binding, and the verifier then compares the lowering with the
rewritten source. A reduction is unrolled only where the source declares
the reassociation (`operator … laws { associative }`, `55-parallelism.md`
§4); the integer `+`, `|`, `&`, `^`, `min`, and `max` have it by the
language, floats never do.

**Loop shape, read from the lowered bodies** (`OAK_NATIVE_DUMP=1` over
`benchmarks/kernels/oak`). The `sum` loop today:

```
loop_4:
  cmp w3, w20
  b.hs done_5
  ldr x9, [x19, w3, uxtw #3]
  add x2, x2, x9
  add w3, w3, #1
  b loop_4
```

Six instructions and two branches per element, top-tested. clang emits
a bottom-tested loop (one branch per iteration) over two 128-bit
accumulators, four elements per iteration, and a scalar tail. Two
increments the program's list does not name separately, both below the
source and both gated by the verifier's loop coupling as it stands:

- *Bottom-tested loops.* The test at the bottom, the entry jumping to
  it: one conditional branch per iteration instead of a compare, a
  conditional exit, and an unconditional back edge. Every loop kernel.
- *A guard the loop test already decided.* `bench_search`'s outer loop
  read `probes[p]` under `while p < len(probes)` with both the exit test
  and the guard comparing the same registers: the index was proven and
  the checker admits it, but a second access in the body (`keys[mid]`,
  proven by the decreasing-bound law the checker cannot read) made the
  compiler fall back to every guard. Landed 2026-09-15: the fallback is
  per source line (`94-assembler.md` §9 "Check elision"), so the admitted
  accesses stay elided. Next: teaching the checker the equalities the
  extent facts carry (a bound copied to another register, a decreasing
  bound below a length) removes the remaining guards where the proof
  exists.

**Condition selection (landed 2026-09-15).** The survey's "a Bool
negation materialized before its branch" and the match chains'
`movz; cmp` pairs: negations invert the branch, Bool homes are tested in
place, small constants are compare immediates, in-range bitwise constants
are not re-masked (`94-assembler.md` §9 "Condition selection";
`bench_dispatch` 68 → 60 instructions), and the repeated `cmp` of a
conditional chain is reused now that the checker carries flag validity
across a label through its guard-fact fixpoint (`bench_search` 53).

**The verified profile is the gate.** An increment that turns a proven
body witnessed or trusted does not land; the count under
`oak build -verified` on `examples/stdlib_builder.oak` is reported with
every increment beside the kernel rows.

## 4. Next steps

1. The program's increments in their order (`optimization-2026-09.md`):
   vector locals in registers across calls and the liveness allocator;
   the word-assembly and constant-offset-guard idioms; reductions
   unrolled under a declared law; non-aliasing to the C backend.
2. Beside them, the loop-shape increments above: the guard a loop test
   decided, then bottom-tested loops — measured structurally on
   `search`, `page_probe`, `sum` (instructions and branches per
   iteration), then timed on a quiet host.
3. The verification burn-down of §2 continues in parallel: results
   beyond sixteen bytes, loops calling functions with memory effects,
   the node-budget bodies, RV64's span arguments.
