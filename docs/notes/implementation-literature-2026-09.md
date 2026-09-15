# Implementation-literature optimization techniques for Oak

Status: source survey, September 2026.

This note complements:

- `docs/notes/optimizer-search-2026-09.md`, which defines Oak's candidate and
  validation architecture;
- `docs/notes/llvm-optimization-catalog-2026-09.md`, which surveys the
  conventional middle-end and machine-optimizer analyses and passes;
- `docs/notes/proof-guided-optimization-2026-09.md`, which records the
  optimizations Oak licenses from checked facts;
- `docs/notes/mojo-futhark-optimization-2026-09.md`, the companion source
  survey for two other systems;
- `docs/notes/native-optimization-2026-09.md`, which records where the native
  lane stands and what is measured.

The catalogs above take LLVM and two research compilers as their references,
which is the right frame for *what* to optimize. This note takes a different
literature — the implementation-oriented writing on interpreters, JITs, and
code generators — which is better on *how* to build the machinery cheaply, and
which contains two ideas the catalogs do not hold at all. The sources are:

- Max Bernstein's programming-language resources list,
  <https://bernsteinbear.com/pl-resources/>, a curated index of compiler,
  runtime, and JIT implementation material;
- V8's Maglev design note, <https://v8.dev/blog/maglev>, on a mid-tier
  optimizing compiler built for compile speed.

Both describe systems Oak is not. Maglev is a just-in-time compiler with
runtime feedback and deoptimization; most of Bernstein's list is about dynamic
languages. Section 4 says plainly what does not transfer, so that a later
reading of the same sources does not propose it again. What remains is
engineering: how to get the analyses, the allocator, and the rewrite machinery
for the least code, and how to keep them friendly to the seam checker and the
verifier, which is Oak's real constraint and no one else's.

## 1. One prepass, computed once, consumed by everything

Maglev walks the bytecode once before it builds anything. That walk finds the
loop headers, the variables assigned inside each loop, and liveness, and the
graph builder then runs in a single pass because the loop phis can be created
up front from what the prepass found.

Oak computes all three of those today, in three places, for three consumers:

- last-use release per statement list, in `nativegen/liveness.go`, so a vector
  local's register returns to the pool;
- loops by back edge, in `asm/loops.go`, for the verifier's loop coupling;
- writes per register over the whole body (`countWrites`) and the
  definition-site rules (`definedBefore`) in `asm/rv64_check.go`, to decide
  which facts survive a join.

One prepass over the emitted items, producing loop membership, the registers
and slots each loop assigns, and live ranges, would serve all three, plus the
allocator and loop-invariant motion. `llvm-optimization-catalog-2026-09.md`
§1.3 already states the principle that analyses are reusable products; this is
the cheapest concrete instance of it, and it is the per-ISA item-level layer
that `94-assembler.md`'s layering decision asks for (the paragraph
"Where the optimizer's layers should live"). The measurement is
not a speedup: it is the deletion of the duplicate scans, with every existing
test and verdict unchanged.

## 2. Single-pass SSA construction

Braun, Buchwald, Hack, Leißa, Mallon, and Zwinkau, "Simple and Efficient
Construction of Static Single Assignment Form" (CC 2013), linked from the
resources list, builds SSA directly from an abstract syntax tree or bytecode
without first computing dominance frontiers: it resolves each variable use by
searching predecessors, inserting phis lazily and removing the trivial ones as
it goes. Maglev uses the same shape and says why — a plain SSA form over a
control-flow graph, not a sea of nodes, for compilation speed and simplicity.

For the MachineIR the optimizer notes plan, this matters twice. It removes the
dominator-tree dependency from construction, which is the part that usually
arrives first and constrains everything after it. And the resulting graph
keeps a direct correspondence with the emitted item list, which Oak needs for
a reason no JIT has: every rewritten body is re-proved against its Oak source
by the verifier, so an IR whose shape maps back to the items it came from
costs less to validate than a flexible one.

## 3. A single forward-pass register allocator

Maglev allocates in one forward pass: prefer the register a value already
occupies, take a free register when one exists, and when none does, spill the
value whose next use is furthest away.

That is the allocator Oak should build first, and for Oak the argument is
stronger than compile time. The seam checker reads register facts — a span's
base and length registers, an index's guard, a frame address, the slot facts
of `94-assembler.md`, "Masked and narrow indices into tables and arrays" — and an allocator that moves values unpredictably
destroys them. This is not hypothetical: a scratch register holding a
not-yet-computed value was once spilled around a call, which the checker read
as an uninitialized register, and the fix was to spill only defined registers.
A predictable allocator with a stated spill rule can be taught to the checker;
a clever one cannot. The measurement is the arm64 lane's `mov` traffic: today
expressions evaluate into an `x9`–`x15` operand stack, so a large share of the
instruction stream is shuffling between a scratch register and a home.

Maglev's other storage decision is worth reading beside
`mojo-futhark-optimization-2026-09.md`'s proposal that one interference-and-
coloring machinery serve registers, stack slots, scratch arrays, and spill
slots alike. Maglev goes the other way and deliberately coarsens, splitting
its frame into two regions rather than tracking slots individually, because
its consumer is a garbage collector that needs only to know which words are
tagged. Oak's consumer is the seam checker, which reads slots by address, so
the fine-grained side is the one to keep; the lesson is that the granularity
should follow the consumer.

## 4. Destination-driven code generation

Dybvig, Hieb, and Butler's destination-driven code generation, also on the
resources list, passes the destination and the control context down into the
generator instead of evaluating into a fixed place and copying afterwards.

This attacks the same `mov` traffic as §3 and needs no IR: it is a change to
how `nativegen` threads a target register through expression lowering. It is
worth listing separately because it can land before an allocator exists and
because the two compose — the allocator then has fewer copies to coalesce.

## 5. Block versioning by fact context

Chevalier-Boisvert and Feeley's basic block versioning compiles a block once
per distinct incoming type context, rather than compiling it once against the
meet of all contexts.

Oak has no dynamic types, so the technique's purpose does not apply, but its
mechanism addresses the exact limit that four of this month's proof-guided
increments each worked around. Guard facts die where paths meet:

- the AArch64 checker's guard-fact fixpoint keeps only what every predecessor
  carries (`asm/check.go`, `meetGuards`);
- the RV64 checker needed the same fixpoint built for it (`94-assembler.md`, "Check elision on the RV64 lane");
- a condition materialized into a boolean and tested after a label proves
  nothing, which is why the second stage of a short-circuit conjunction stays
  unread (same file, "Proof-guided elision: the guards the checker carries");
- the per-line guard fallback exists precisely because one refused access in a
  body costs the whole body its elision (§9 "Check elision").

Versioning is the alternative to teaching the checker one more join rule at a
time: emit the block once per incoming fact set, so the facts that hold on a
path stay available along it. The cost is code size, which is why the versions
must be bounded and chosen by the cost model, and the gate is unchanged — each
version is a candidate the seam checker admits and the verifier proves, or it
is not selected. This is the one item in this note that is Oak-specific rather
than borrowed.

**Measured, 2026-09-15, and the claim above was wrong.** It was written
here that this is the largest remaining lever on elision reach. It is not.
The mechanism was built (`94-assembler.md` §9.ai) and changed nothing on
the stdlib-bearing program: of the 89 bodies the checker refuses, the
findings are dominated by structural refusals no context affects, and
every elision-relevant refusal reports the same missing fact under each
arriving state. The limit is missing fact rules — the largest class by far
is an index the typechecker proved by `scaled_under_bound` that the
checker has no rule for — and the join is not where the reach is lost.
The mechanism is kept, gated to the findings a lost guard could explain,
because the shapes it does fix are real and because each new fact rule is
worth more when a fact that holds on one path survives the next label.

It is not the multi-versioning that `mojo-futhark-optimization-2026-09.md` §8
already records from Futhark's incremental flattening, and the two should not
be conflated. That versioning chooses between whole implementations of one
semantic operation, and may defer the choice to startup or run time. This one
is inside a single body: the same statements emitted more than once so that a
fact holding on one path is not lost to the meet at a join. They compose —
each version of a body is still one candidate in the search — but the
mechanisms, the cost models, and the proof obligations differ.

## 6. Verified rewrite rules at scale

The resources list points at the egg library for equality saturation and at
Cranelift's use of e-graphs. Published work on that compiler checks its
instruction-selection rules against an SMT semantics rather than trusting
them; how much of the production rule set that covers is not something this
note establishes.

`optimizer-search-2026-09.md` §7 already proposes equality saturation for pure
scalar regions, so the new information is the precedent for the verification
discipline at scale: a rule set large enough to be useful is maintained with a
machine-checked semantics per rule, which is what Oak already does by hand —
every transform cites a law in `spec/lean`. Cranelift is the evidence that the
discipline survives a few hundred rules, and its failures are the evidence for
where it strains.

## 7. What the sources validate about the present design

Three of Oak's existing choices are independently arrived at by Maglev, which
is worth recording because each looked like a compromise when it was made:

- **Facts are consumed while lowering, not in a later pass.** Maglev
  specializes nodes as it builds them and carries a side table of known
  information forward. Oak's lowering reads `IndexProven` at the access
  (`guardedIndexAt`) rather than rewriting guards away afterwards. The
  generalization worth taking is a wider side table: known constants and value
  ranges beside in-range indices, for which `llvm-optimization-catalog-2026-09.md`
  §4.2 and §4.3 are the reference.
- **A cheap bailout beats a complete analysis.** Maglev's bailout is
  deoptimization; Oak's is the fallback ladder, per line and then per body.
  `llvm-optimization-catalog-2026-09.md` §1.7 states this as doctrine
  already.
- **A plain graph over a control-flow graph beats a sea of nodes** when the
  output must be re-validated, for the reason in §2.

## 8. What does not transfer

Recorded so the same proposals are not made again from the same sources:

- **Deoptimization and its frame-state metadata.** Oak emits one program; it
  has no unoptimized tier to fall back into at run time. Its analogue is the
  candidate fallback, which happens at compile time.
- **Tiering.** The C backend, the native lanes, and the verified profile are
  not tiers of one program's execution; they are separate build products.
- **Runtime type feedback, inline caching, object shapes and hidden
  classes.** Oak's dispatch is static and its layouts are declared.
- **Pointer tagging and NaN boxing.** Oak's values are unboxed and typed.
- **Trace-based optimization and allocation sinking through traces.** The
  structure Oak optimizes is the source's structured control flow, which is
  already better than a recorded trace.
- **Copy-and-patch compilation.** It buys baseline code generation speed for
  an interpreter tier Oak does not have.

## 9. Order and ownership

The items divide cleanly between the two sessions now working on this:

| Item | Owner | Why |
| --- | --- | --- |
| §1 prepass, §2 SSA construction, §3 allocator | the MachineIR session | they own `nativegen`'s machine layer and the artifact DAG |
| §4 destination-driven generation | the MachineIR session | same files as §3, and it composes with the allocator |
| §5 block versioning by fact context | the proof-guided session | it is an extension of the checkers' fact machinery |
| §6 verified rules at scale | the MachineIR session, when the transform registry grows | it is a property of the registry |

One measurement should precede §6 and any further growth of the transform
library: the compile-time cost of the candidate search itself. The optimizer
reports show bodies lowering eighteen candidates and verifying up to three of
them, and verification already dominates a native build. Maglev's whole
justification is that compile time is a first-class cost, and Oak has not yet
measured its own.
