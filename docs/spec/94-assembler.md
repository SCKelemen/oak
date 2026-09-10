# The Oak Assembler: Typed Abstract Assembly Units

This chapter fixes the design of Oak's assembler. The baseline is Go's
assembler — one abstract assembly language over per-architecture
instruction sets, function-shaped, integrated with the normal build — with
the parts Go leaves untyped made typed, and with lower-level control
available where systems code needs it. The instruction-function layer
(`92-ffi.md` §3, `93-simd.md`) is already normative and implemented; this
chapter governs the next layer: **whole functions written as instruction
sequences**. **v1 is implemented** (§7 lists exactly what landed and what
is pending); the design sections remain normative for the rest.

## 1. Position

- Assembly lives in **`asm` translation units** (`name.arm64.oakasm`),
  never inline in Oak function bodies — the same rule as C
  (`92-ffi.md` §1). An Oak file declares the typed interface; the asm unit
  provides the body for a named architecture. The build system selects the
  unit matching the target, or the Oak fallback body if one is declared.
- An asm function is **function-shaped**: it has exactly the declared Oak
  signature, receives arguments per the Oak calling contract, and must
  return through it. There is no open-coded fall-through between asm
  functions.
- The assembler is an **abstract assembler** in Go's sense: mnemonics and
  operand order are the architecture's own (what the ARM ARM documents),
  but frame layout, symbol references, and calling-contract plumbing go
  through typed pseudo-operands rather than raw offsets.

## 2. Surface: the same declaration form

An asm function is declared and defined with Oak's ordinary declaration
form — the interface is a function type, the definition is an instruction
block. The Oak side declares the interface (definition-less, legal exactly
when an asm unit or an Oak fallback provides the body):

```oak
add_asm: (left, right: u32) -> u32
```

The architecture unit (`add.arm64.oakasm`) repeats the **identical**
signature and supplies the instruction sequence as its definition:

```oakasm
add_asm: (left, right: u32) -> u32 = {
  push left
  push right
  add
}
```

Rules:

- **Signature identity**: the asm unit's signature must match the Oak
  declaration token-for-token after normalization; a mismatch is a
  compile-time error naming both sites. The signature is the contract — the
  caller never knows or cares that the body is assembly.
- **Named operands**: parameters and asm-local names are first-class
  operands. The assembler performs register binding for named values; the
  operand-stack shorthand above (`push`/`add` popping two, pushing one) is
  sugar over the same bound values, for bodies where explicit register
  choice adds nothing. The final stack value (or the named result) is the
  return value, checked against the declared return type.
- **Explicit registers when it matters**: a body may pin names to
  registers with the register types of §3 (`bind x0 = left`), and from that
  point the width and clobber discipline of §3 applies. Mixed bodies are
  legal; the assembler refuses ambiguous bindings rather than guessing.
- **One function, one unit**: each asm function body lives in exactly one
  unit per architecture. The build selects `name.arm64.oakasm` for an
  AArch64 target, another architecture's unit for its target, or the Oak
  fallback body; a target with neither is a build error, not a silent stub.

## 3. Register types

Registers are values of **register types**: nominal, zero-cost types known
to the assembler's checker. They exist so that an asm unit is checked, not
trusted, at its seams. v1 register classes for AArch64:

| Type | Class | Members |
| --- | --- | --- |
| `arm64.X` | 64-bit general register | `x0`–`x30` |
| `arm64.W` | 32-bit view of a general register | `w0`–`w30` |
| `arm64.V` | 128-bit vector register | `v0`–`v31` |
| `arm64.SP` | stack pointer (singleton) | `sp` |
| `arm64.Flags` | condition flags (singleton) | `nzcv` |

Rules the checker enforces inside an asm unit (whether names were bound explicitly or by the assembler):

- **Binding**: each parameter of the Oak signature is bound to its
  contract register with its class type (`a: i64` arrives in an `arm64.X`;
  a `simd.U8x16` arrives in an `arm64.V`). The result must be produced in
  the contract result register. Bindings are written, not inferred, so the
  unit is readable without knowing the contract by heart — and checked, so
  it cannot be wrong.
- **Width discipline**: an instruction taking `arm64.W` operands cannot be
  handed an `arm64.X` binding, and vice versa; `wN`/`xN` aliasing of the
  same physical register is tracked (writing `w5` clobbers the `x5`
  binding's upper half — the checker knows).
- **Clobber declarations**: every register the body writes beyond its
  bindings is declared. Writing an undeclared register is an error;
  declaring callee-saved registers adds the save/restore obligation to the
  frame contract.
- **Flags are a register**: instructions that set or read `nzcv` say so in
  their instruction-table entries, and a conditional consuming flags must
  be dominated by a producer with no intervening clobber — checked, the
  way value dataflow is.
- **No hidden memory**: memory operands go through declared frame slots or
  through pointer parameters that arrived typed. Stray absolute addresses
  are not expressible.

The register types also appear (read-only) in Oak's diagnostics and
tooling, but they are **not** first-class in ordinary Oak code: an Oak
function cannot declare an `arm64.X` local. They exist at the asm boundary
only, which is what keeps them zero-cost.

## 4. Lower-level than Go

Where Go's assembler stops, Oak's continues, in declared and checked form:

- **Explicit register binding** (`bind x0 = a`) instead of frame-symbol
  indirection for arguments.
- **Flags dataflow** as in §3 — Go treats flags as invisible; Oak checks
  them.
- **Barriers and ordering**: `dmb`/`dsb`/`isb` and load-acquire /
  store-release instruction forms are first-class table entries whose
  memory-order effects tie into the machine-memory model
  (`spec/lean` machine-memory foundation).
- **System registers**: reads of counter/ID registers (`mrs`) are table
  entries with declared effects; writes are behind a per-unit `system`
  capability declaration.
- **Prefetch and cache maintenance** as effect-annotated instructions.

Everything remains within the abstract-assembler frame: no raw encodings,
no undeclared side effects, no self-modifying code.

## 5. Trust and verification

An asm unit is a **declared trust boundary** narrower than `c.extern`: the
signature is enforced by the checker at the seams (bindings, clobbers,
frame), the instruction semantics come from the per-architecture table, and
what remains trusted is the author's algorithm, exactly as with any
verified-boundary component. The roadmap for shrinking that trust:
instruction-table entries carry semantic definitions compatible with
`Oak.Intrinsics`/`Oak.Simd`, so straight-line asm bodies can eventually be
checked against a stated postcondition. Until the checker exists, the
`arm64.*` instruction functions are the supported way to reach specific
instructions — they need no trust beyond the compiler itself.

## 6. Relation to the instruction-function layer

The instruction functions of `92-ffi.md` §3 and `93-simd.md` are the
assembler's semantic anchor: each asm instruction-table entry that has an
instruction-function counterpart must cite the same semantics. A kernel
should be written with instruction functions first; an asm unit is the
escalation for register-allocation-critical or flags-critical inner loops,
not the default.

## 7. v1 implementation scope

Landed (`asm/` package; `Compilation.WithAsmUnit`; executed natively on an
AArch64 host — `compiler/e2e_asm_test.go`; laws in `Oak.Assembler`):

- **Units and stitching.** `.oakasm` units hold `name: (params) -> Ret = {
  ... }` blocks whose header is parsed by the Oak parser; each pairs with a
  definition-less Oak declaration of identical signature (structural
  comparison; mismatch, missing declaration, missing unit, and duplicate
  definitions are `asm`-phase errors). Body-less declarations are legal
  syntax only for this purpose.
- **Directives.** `bind <reg> = <param>` (written, never inferred; must be
  the AAPCS64 contract register at the parameter's width class — `w0` for
  `u32`, `x0` for `u64`, `v0` for `simd.*`), `clobber <regs>`, `frame N`
  (multiple of 16), `system` (capability for `mrs`/`msr`/`eret`), and
  `align N` (a power of two; the first sets the entry alignment).
- **Instruction table (AArch64).** `mov add sub adds subs and orr eor lsl
  lsr cmp ldr str ldp stp b b.<cond> bl ret eret mrs msr dmb dsb isb nop`,
  each with its legal operand forms, flag effects, memory effect, branch
  kind, and privilege requirement. Nothing outside the table is
  expressible.
- **The seam checker.** Width discipline with `wN`/`xN` aliasing; no read
  of a register that is not bound, written, `sp`, or a zero register (no
  uninitialized reads); no write outside bound registers, the result
  register, and declared clobbers; callee-saved `x19–x29` refused as
  clobbers (save/restore obligations pending); flags consumers dominated by
  a producer with labels and calls invalidating; memory only through the
  declared `sp` frame, with the static sp displacement tracked through
  pre/post-index and `add/sub sp` and every access bounds-checked against
  `[-frame, 0)`; displacement agreement at every label, 0 at every `ret`
  and at every branch to another function; `bl` requires `clobber x30` and
  invalidates caller-saved state; `align` regions whose instruction bytes
  exceed their stride are refused, and an aligned region is an **entry
  point** (fresh state, displacement 0 — the vector-table shape); no
  unreachable instructions, no fall-through past the end, no `ret` from a
  `never` function, `eret` only from `never`/unit results.
- **Emission.** The Oak declaration emits an ordinary C prototype; the
  block emits a top-level `__asm__` under the prototype's C symbol
  (`OAK_ASM_SYMBOL` applies the target's user-label prefix, so Mach-O and
  ELF both link), numeric local labels (`1:`/`1b`/`1f`, assembler-local on
  both object formats), `.balign` for entry and region alignment. A
  non-AArch64 target fails closed with `#error`.
- **Executed:** `add_asm`, a trap-frame save/restore of `x0–x17` as pairs
  under `frame 160`, a flags/label loop, and a 2 KiB-aligned sixteen-entry
  `eret` vector table (assembled, its extents checked statically).

- **Units beside the sources.** A package build (`oak build`, `oak run`,
  `Compilation.WithPackageDir`) picks up every `*.oakasm` in the root
  package's directory; each unit function pairs with the package's
  definition-less declaration of the same name, or with a defined function
  as its fallback body. Verification verdicts (§8) are informational
  diagnostics the CLI prints as `asm: …` lines; a mismatch is an error.
  `examples/asm` is the reference: four kernels, all proven, run both ways.
- **Typed pointer memory.** A span (`[*]T`) or view (`[]T`) parameter of
  fixed-width elements crosses as its `{base, u32 len}` pair and binds
  both registers explicitly — `bind x0, w1 = frame` (the base pointer,
  then the 32-bit length; the upper half of `x1` is padding the contract
  never defines, so only `w1` is ever consulted). Memory through the base
  (`ldr x9, [x0, #8]`) is admitted only under a **dominating bounds
  guard**: `cmp w1, #N` immediately followed by `b.lo <fail>` proves
  `len >= N` on the fall-through path, and the checker then proves each
  access `[off, off+size)` lies within `N * elem` bytes
  (`Oak.Assembler.span_access`). Guards die at calls and on any write to
  the base or length register, and at a label they survive only when every
  predecessor carries them (below); a span base is never moved
  (no pre/post-index); stores through a view are refused; a comparison
  of `x1` is not a guard. **Walking a span by index** uses the scaled
  register-offset form `ldr w11, [x0, w9, uxtw #2]` — element `w9`, the
  shift the element size's log2 and the register the element's width —
  admitted only under a **dominating index guard**: `cmp w9, w1` then
  `b.hs <exit>` proves `w9 < len` on the fall-through path (or `cmp w9,
  #K` then `b.hs` with `len >= K` already established), so the access lies
  inside the span (`Oak.Assembler.index_access`). Index facts die like
  length guards: at calls, and on any write to the index or the register
  it was compared against. **At a label a fact survives exactly when every
  predecessor carries it** — fall-through and every branch targeting the
  label, forward or backward — computed as a fixpoint over checker passes
  (assume everything, record the meet of what arrives, repeat until
  stable; proven minimum lengths meet at the smaller value,
  `Oak.Assembler.meet_sound`). So the loop idiom is one length guard
  before the loop, then guard the index, load, advance, branch back: the
  outer `len >= N` holds at the header because both the fall-through and
  the back edge carry it, and a back edge that wrote the length register
  drops it. This is the bounds-check doctrine made explicit
  in assembly: the runtime check is written by the author, its dominance
  is verified by the checker, and the offsets under it are proven.
- **Callee-saved obligations.** `x19`–`x30` carry the caller's values on
  entry (readable without a write), may be written only after being
  **saved** into the declared frame (a `str`/`stp` from the still-untouched
  register records its absolute slot), and every `ret` requires each
  written callee-saved register **restored** from that same slot (`ldr`/
  `ldp`, matched by absolute address relative to entry sp, not by textual
  offset) with no write after the restore. `bl` in a returning function
  requires the link register saved first (`stp x29, x30, [sp, #-16]!`) —
  the call clobbers it, so the same restore obligation covers it before
  `ret`; never-returning functions keep the clobber-only rule.
- **Oak fallback bodies.** A declaration may carry both an Oak body and an
  asm unit of identical signature: the asm block emits under
  `__aarch64__` (and not `OAK_PORTABLE_INTRINSICS`), the compiled Oak body
  under the complementary condition, so programs with asm units build on
  non-AArch64 hosts and the Oak body is the portable semantics the asm
  must agree with — the differential-witness convention of `93-simd.md`
  extended to hand-written assembly. Without a fallback, a non-AArch64
  target still fails closed with `#error`.
- **`address_of(f)`** yields the `u64` code address of an asm-backed
  function and nothing else — the `VBAR_EL2` install path
  (`arm64.write_vbar_el2(address_of(vectors))`). Ordinary Oak functions
  have no exposed address.

- **The operand-stack shorthand** (§2) is implemented as desugaring
  (`asm/stack.go`): `push <param>` writes the parameter's contract binding
  for the author, `push #imm` pushes an immediate, an operand-less
  data-processing mnemonic (`add sub and orr eor lsl lsr`) pops two values
  and pushes its result in a compiler-chosen scratch register (`x9`–`x15`,
  declared as clobbers for the author), and the single value left at the
  end moves into the result register before `ret`. The desugared body is
  then checked exactly like a handwritten one. Refused: underflow, a
  leftover value, mixing explicit operands or explicit `bind` lines into a
  shorthand body, vector parameters. Executed: the spec's own
  `add_asm` example and a chained `push a / push #2 / add / push #3 / lsl`.

Pending: the semantic
verification of straight-line bodies against `Oak.Intrinsics`.

## 8. Semantic verification of asm bodies (six increments implemented)

**Implemented** (`asm/verify.go`, `Oak.AssemblerSemantics`): for a function
with both an asm unit and an Oak fallback body, the asm gate runs the
verifier and labels its verdict — **proven** when both sides normalize to
the same linear form modulo the result width (sums of parameters and
constants; `lsl` by a constant as multiplication; the `wN` write/read masks
are transparent modulo 32), **mismatch** when any witness input disagrees
(a hard error naming the input and both values — a wrong body never
compiles), **proven at the bit level** when, beyond the linear form, both sides
bit-blast (`asm/blast.go`, a small ROBDD with interleaved variable order)
to the same canonical decision diagram for every result bit — the complete
decision for the term language (`and`/`orr`/`eor`, shifts by constants and
by registers as a mux barrel, `add`/`sub` as a ripple-carry chain), with a
differing bit reported as a **mismatch** carrying a concrete counterexample
(`Oak.AssemblerSemantics.eq_of_bits` is the justification; the ripple-carry
chain is now **Lean-refined**: `rippleCarry`/`rippleSum` are the blaster's
recurrences verbatim, `rippleCarry_eq_carry` identifies the chain's carry
with `BitVec.carry`, `rippleSum_eq_add` gives bit i of `a + b`, and
`rippleSum_eq_sub` gives bit i of `a - b` through the complement chain with
carry-in 1), **witness-checked** only when the bit-level decision exceeds
its node budget (evidence, labeled so), and **trusted** when the body or the
Oak expression is outside the executable subset (labels, calls, memory,
system instructions, non-constant shift counts on the Oak side — Oak traps
where the machine wraps the count).

**Conditional bodies (second increment).** `csel` and `cset` join the
instruction table (`csel wD, wN, wM, cond` / `cset wD, cond`; a condition
code is an operand; both consume flags under the same dominance rule as
`b.cond`). The executor tracks the flags as *the operands that produced
them*: `cmp l, r` and `subs` leave NZCV as the flags of `l - r` at the
operands' width; `adds` leaves flags no comparison describes (a select
after it is trusted, never falsely proven). A select lowers to `cond ? a :
b` over a comparison term; on the Oak side a two-armed Bool conditional
`x < y ? a | b` whose scrutinee compares parameters lowers to the same
shape, with the condition code chosen from the operator *and the parameter
type's signedness* (`<` on `u32` is `lo`, on `i32` it is `lt`). Deciding
the comparison is the flag computation itself: the blaster runs the
complement chain, takes C as its carry-out, Z from the difference, N its
sign, V the subtraction's signed overflow, and applies ARM's condition table
(`asm/blast.go`'s `condition`); the witness evaluator computes the
comparison directly. `Oak.AssemblerSemantics` ties the two readings:
`flagsOf`, `Cond.holds`, and `condHolds` are the table; `c_eq_carry` proves
C is the chain's carry-out; `eq_holds_iff`, `hs_holds_iff`, `lo_holds_iff`,
`hi_holds_iff` prove the unsigned codes are the comparisons Oak lowers to;
the four signed codes are checked exhaustively at width 4 against
`BitVec.slt`; `csel_lo_max` is the unsigned maximum on the semantics. `mi`,
`pl`, `vs`, `vc` (single-flag reads) and conditions composed with `&&`/`||`
remain outside the subset (trusted). Executed: `max32` via `cmp`/`csel lo`
proven and run both ways; `csel hi` for `a < b` refuted at the gate with a
concrete counterexample; `lo` for a signed comparison refuted at
`a = -1, b = 0`.

**Acyclic branches (third increment).** The executor unfolds a body into
its paths: `b.cond L` forks the symbolic state — the taken path continues
at `L` under the branch's condition (read off the flags exactly as `csel`
does), the fall-through under its negation — and the two results meet as a
select (`Oak.AssemblerSemantics.branch_as_select`; `branch_map` is the law
that lets paths rejoin at a shared tail through an unconditional `b`).
Every branch target must lie ahead of the branch: a backward target is a
loop, outside the subset, and the body is trusted, as is a body exceeding
the path budget. On the Oak side, nested conditionals lower to nested
selects, comparisons joined by `&&`/`||` lower to the strict and/or of their
0/1 terms (over pure comparisons of parameters, short-circuiting is
unobservable), Bool literals are `1`/`0`, and a Bool-typed body is its C
representation — so a range test `lo <= v && v < hi` is the specification
of a two-branch chain. The signed condition codes are now theorems at the
contract widths: `lt_holds_eq_slt_w32`/`_w64` (and `ge`/`gt`/`le`) prove
the N ≠ V reading against `BitVec.slt` for every 32- and 64-bit operand pair
by `bv_decide` (a SAT certificate the kernel checks). Executed: a clamp
with two branches and three paths proven and run both ways; `b.hs` for a
`<` branch refuted; an inclusive bound for an exclusive one refuted; a loop
trusted. **Register-offset span addressing** (`[x0, w9, uxtw #2]`, §7)
reaches the verifier as an element load whose index is the index register's
term: along an unrolled counted loop that term is a constant, so the load
is `v[k]` exactly as a constant offset would be; a data-dependent index
names no single element and is trusted. Executed: a four-element sum loop
walking a view by index proven against its Oak `while` (and against the
flat `v[0] + … + v[3]`), run both ways; three iterations refuted with
`v[3]` named; the data-dependent `while i < len(v)` walk checked but
trusted.

**Span memory (fourth increment).** A span or view parameter enters the
executor as its `{base, len}` pair: the base register holds an opaque
address term (no Oak spelling — a result depending on it can never match),
the length register the 32-bit parameter `len(v)`. A load `ldr rD, [xB,
#off]` whose base term is a span base reads the element parameter `v[k]`
with `k = off / elem`, admitted only when the offset is a whole element and
the register width is the element width; the seam checker has already
placed the load under a dominating `cmp wL, #N; b.lo` guard, so the
verifier asks only *which* element is read (`Oak.AssemblerSemantics.Span`,
`loadElem_at`, `guarded_index_in_bounds`). The Oak side lowers `len(v)` and
constant-index `v[k]` to the same parameters, with the element type's width
and signedness (`[]i32` elements compare signed). Stores through a span,
frame memory, moving bases, and loads whose width differs from the element
(`ldr w` over `[]u8`) stay outside the subset (trusted). Executed: a
guarded `pair_sum` over `[]u32` proven and run both ways; reading element 0
twice refuted with the elements named in the counterexample; a guard
constant of 3 for Oak's 2 refuted at `len(v) = 2`; a 64-bit first-or-default
and a signed head max proven.

**Counted loops (fifth increment).** The term constructors fold constants,
so a comparison of a counter that is a constant on every iteration decides
itself. The asm executor follows a backward branch whose condition folds
(and an unconditional `b`) instead of refusing it, bounded by a global
instruction-step budget; a backward branch whose condition is not constant
is a loop with a data-dependent trip count — trusted (so is an unconditional
`b` closing a loop in which the path forked on the inputs: the exit is the
fork). A counted loop whose body forks on the inputs still unrolls — its
closing branch is decided on every path — into up to 2^K paths, bounded by
the path budget (beyond it, trusted). On the Oak side the fallback
body may now be a statement block: typed locals with initializers,
assignments (at the local's declared width), and `while` loops whose
condition folds to a constant before every iteration (unrolled under a
budget; a data-dependent condition is trusted), ending in the result
expression. `Oak.AssemblerSemantics.counted_loop_unrolls` is the law: a
counter from 0 to N under fuel N + 1 runs exactly N times, so the loop is
the N-fold iterate of its body — the term both sides compute. Executed:
`3*a` by a three-iteration accumulate proven (linear form); four iterations
refuted; an eight-step popcount of the low byte proven at the bit level
against its Oak `while`, and run both ways; seven steps refuted with a
concrete input; data-dependent trip counts on either side trusted; a
three-iteration loop that branches on the input inside proven against its
conditional accumulate (eight paths) and refuted against the unconditional
one; nine such iterations exceed the path budget and are trusted. **Data-dependent loops (sixth increment).** A loop whose trip count depends
on the inputs is summarized rather than unrolled: on meeting a `while`
whose condition does not fold (Oak) or a recognized loop — header label,
`cmp` + `b.cond` exit, straight-line body, unconditional back edge — whose
exit does not fold (asm), the executor records a **loop event**: the
loop-carried variables' values at the header, fresh symbols standing for
them on an arbitrary iteration, the continue condition over those symbols,
and their values after one iteration; it then continues past the loop on
the fresh symbols (the exit sees the header values of the exiting
iteration; asm scratch registers are unbound after the loop). Element reads
at a symbolic index become **select** terms — evaluated through a fixed
element-content function, and bit-blasted as uninterpreted values shared by
selects with identical index bits (sound for equality: equal under
independent element values means equal under every memory). Verification
then has two layers. **Witnesses**: both sides are re-executed on small
concrete inputs, under which the loops become counted and unroll; a
disagreement is a mismatch with a concrete input (a stride-2 walk, summing
indices instead of elements, returning the counter — all refuted). **The
coupling proof** (`Oak.AssemblerSemantics.whileFuel_coupled`): each Oak
loop variable is paired with a register of the same width whose header
value is bit-level equal — a small search, since two zeroed counters start
alike — and the pairing is accepted when the continue conditions are
proven equal and one iteration provably preserves every pair; the results
after the loops are then compared as usual over the fresh symbols. The sum
over a view of any length, and an n-fold 64-bit accumulate, are **proven**;
the commuted body is the same loop; a count-down asm loop against a
count-up Oak loop cannot be coupled and is **witness-checked** (evidence,
never a false mismatch); a loop on one side only is trusted. Executed:
`sum` over views of length 5, 2, and 0, both ways. **Forks inside the
body**: a recognized loop body may branch forward within itself; one
iteration is then executed along every path (a body-path budget bounds
them) and the paths merge register by register into selects on their path
conditions at the back edge. On the Oak side a statement-level conditional
`c ? { x = e } | { }` runs each arm on a snapshot of the locals and merges
the locals either arm assigns as selects — so the branchy asm, the
`cset`-based asm, the value-position Oak spelling, and the statement-level
Oak spelling of "count the elements above a threshold" are all one loop,
and a running maximum by conditional move is proven; the wrong branch sense
is refuted on a concrete input. **Affine couplings with invariants**: a
pairing may relate a register to an Oak variable by `r = x + b` or
`r = b - x` with `b` read off the header values and required to be
loop-invariant (equality is `b = 0`); the Oak symbols are substituted by
the inverse expressions. The Oak guard weakened to its closure (`i < n`
gives `i ≤ n`) is a candidate invariant — admitted when it holds at the
header and one iteration preserves it under the guard — and every check
(condition agreement, body preservation, and the exit comparison under the
negated guard) is a bit-level implication from the invariant, so R in
`whileFuel_coupled` is the affine relations conjoined with the invariant.
The exit comparison in loop mode never reports a symbolic disagreement as a
mismatch (the state may be unreachable); only the concrete layer refutes.
A count-down asm loop (`w1 = n - i`, under `i ≤ n`) and an inclusive
1-based counter (`w9 = i + 1`) are now proven against the count-up Oak
loop. **Nested loops**: the events form a tree in creation order with
parent links on both sides — an inner loop met while executing the outer
body is summarized in place, with fresh symbols namespaced per event
(`loop2.j`), and the body continues at its exit; the asm shape admits
recognized inner loops inside a body, and Oak loop bodies admit local
declarations (a body-local counter is the body's own, not an outer
loop-carried variable). The coupling pairs every event's variables in one
search (an inner header mentions the outer symbols, so candidates are read
under the substitution so far) and checks each event under its premise:
its invariant and guard, its ancestors' invariants and guards, and its
children's exit premises — an outer body's successors mention the inner
loops' exit symbols. The nested `n × m` counter and row sums over a view
are proven; an inner stride of two is refuted on a concrete input; loops
that nest differently on the two sides are trusted. **Flags from additions
and compare-and-branch.** `adds` leaves NZCV as the flags of `left + right`
(`Oak.AssemblerSemantics.addFlagsOf`; `add_carry_iff`: the carry is the
unsigned overflow, `a + b < a`), so the idiomatic saturating add
`adds; csel cs` is proven against `a + b < a ? max | a + b`; every code is
read through one NZCV table for both flag kinds, which brings `mi`/`pl`/
`vs`/`vc` into the verified subset (`mi` after `cmp` is the difference's
sign bit, `vs` after `adds` the signed overflow). `cbz`/`cbnz` and
`tbz`/`tbnz` join the instruction table as conditional branches without
flags (the checker reads the register and bounds the bit index); the
executor, the loop-body executor, and loop recognition treat them like
`b.cond`, so a count-down loop exiting through `cbz` is proven by the
affine coupling and a `tbz` bit test verifies. Byte-offset pointer walks
(`[xB, xO]`) remain deliberately outside the subset: the scaled-index form
is the idiom and costs nothing on AArch64, and a byte offset would need
value tracking the seam checker fails closed on.

§5 named the roadmap: shrink the trust in an asm unit from "the author's
algorithm" to "a stated postcondition". With Oak fallback bodies landed
(§7), the design has a natural anchor — **the Oak body is the
specification** — and three layers:

1. **Differential witness (landed).** A function with both an asm unit
   and an Oak fallback executes both realizations under the test harness
   (`-DOAK_PORTABLE_INTRINSICS` selects the fallback), the SIMD convention
   of `93-simd.md`. This is evidence, not proof: it covers the inputs the
   tests reach.

2. **Instruction semantics (next).** Each data-processing entry of the
   instruction table (`mov add sub adds subs and orr eor lsl lsr`, later
   `cmp` and the conditional branches) carries a semantic definition as a
   function on machine state — general registers as `w`/`x` bitvectors with
   the `wN`/`xN` aliasing law of `Oak.Assembler`, the flags as the ARM
   `NZCV` computation — written once in Lean (`Oak.Assembler.Semantics`,
   compatible with `Oak.Intrinsics`/`Oak.Simd` so `arm64.*` instruction
   functions and asm table entries cite the same semantics) and
   transliterated into a Go symbolic executor.

3. **Postcondition discharge.** For a body the executor can unfold
   (straight-line, conditional selects, forward branches, span loads,
   counted loops, and coupled data-dependent loops all landed), the symbolic executor produces
   the result register's value as a bitvector term over the bound
   parameters. The Oak fallback body, when it is a pure expression over the
   same parameters (the `add_asm: ... = left + right` shape), lowers to a
   bitvector term too. The obligation is term equality, decided by
   normalization over the total fixed-width semantics of `20-types.md`
   §11.1 (wrapping arithmetic), with bounded exhaustive evaluation at
   8-bit width as the executable cross-check of the normalizer itself.
   Bodies the executor cannot reduce (memory, calls, system registers,
   loops) keep §5's trust boundary and say so in diagnostics — the same
   fail-closed shape as every other checker here.

What this buys: the pilot's hot leaf functions (bitfield extraction,
counter reads wrapped in arithmetic, saturating adds) become *proven equal*
to their Oak specification, not tested equal; register-allocation-critical
inner loops remain trusted until the acyclic extension lands. What it does
not claim: liveness, timing, or anything about the frame beyond the §7
seam checks, which remain the frame's only guarantee.

Dependencies: the semantics table is independent work; the normalizer can
reuse the total-arithmetic helpers' definitions; the executor needs the
checker's binding and clobber facts, already computed. Acceptance: the
spec's `add_asm` and a shift/mask extractor verify; a deliberately wrong
body (`sub` for `add`) is rejected with the differing term printed; a body
with memory or a call reports "not verified: trusted per §5".
