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
| `arm64.Z` | scalable vector register (streaming SVE; `zN` extends `vN`) | `z0`–`z31`, with an element size `z0.b/h/s/d/q`, a bare `z0`, or an element `z2.s[1]` |
| `arm64.P` | scalable predicate register | `p0`–`p15`, with an element size (`p0.s`) or a qualifier (`p0/m` merging, `p0/z` zeroing) |
| `arm64.PN` | predicate-as-counter register (SME2) | `pn8`–`pn15` (`pn8/z`, `pn8[0]`) |
| `arm64.ZA` | the ZA array and its tiles (SME) | `za`, tiles `za0.s`–`za3.s`, `za0.d`–`za7.d`, …; slices `za0h.s[w12, 0]`, `za1v.b[w13, 0:3]`, vectors `za.s[w8, 0, vgx4]`, `za[w12, 0]` |
| `arm64.ZT` | the lookup-table register (SME2) | `zt0` |

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
- **Streaming mode and ZA are state**: `smstart`/`smstop` switch PSTATE.SM
  and PSTATE.ZA along the block; each SVE/SME instruction needs the mode
  Arm's pseudocode checks for it (streaming SVE needs SM, the ZA
  instructions need ZA, most Advanced SIMD is illegal under SM); a change
  of SM zeroes `z0`–`z31` and `p0`–`p15`, so a value bound or written before
  it is gone after it; `bl` inside either mode and `ret` before leaving
  both are refused (Oak callers have no streaming interface). Predicates
  need `clobber pN`; `zN` is `vN`'s clobber. The predicated SVE/SME loads
  and stores read their base and index registers and are otherwise trusted
  (§5): their extent is the predicate's and the vector length's.

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
value tracking the seam checker fails closed on. **Instruction breadth.**
`ldrb`/`ldrh`/`strb`/`strh` access one- and two-byte elements (the span
element size must match; the indexed form takes `uxtw #0`/`uxtw #1` and
bytes emit as `[x0, w9, uxtw]`), and a narrower load zero-extends the
element into its `w` register — so packet-buffer kernels over `[]u8` verify
(a byte checksum by coupling, a big-endian 16-bit field). `mul` is a term
operation (a constant factor keeps the linear form: `a * 10` is proven
linearly; two symbolic operands blast as a shift-and-add product within the
budget or stay evidence), `neg` and `mvn` are subtraction from zero and
exclusive-or with all ones, `asr` is the arithmetic shift, and `tst` sets
the flags of the AND (a third flags kind; C and V clear), so `tst; cset ne`
is a bit test. Note Oak's shift and bitwise operators take unsigned
operands only (`20-types.md`: bitwise on signed values is refused), so
`asr` never implements an Oak body; should a signed shift ever be spelled,
the verifier refutes the arithmetic reading at a negative input rather than
assuming it. **Frame memory.** The executor carries sp's displacement
(exactly the checker's number, through `sub`/`add sp` and pre/post-index)
and a map from entry-relative slot addresses to the stored terms
(`Oak.AssemblerSemantics.storeSlot`, `loadSlot_storeSlot`): `str`/`stp`
record, `ldr`/`ldp` read back a slot stored with the same width, and a load
of a slot never stored on the path, a width mismatch, or a narrow reload is
outside the subset (trusted — never a fresh value that could match by
accident). Callee-saved registers read before any write are the caller's
opaque values, so a save/use/restore body round-trips them and is proven;
spills and reloads are proven; reloading the wrong slot is refuted. Frame
memory inside a loop body stays outside the subset. **Bit fields,
conditional compare, conditional increment/negate, multiply-add.**
`ubfx`/`ubfiz`/`sbfx`/`bfi` (the checker bounds the field inside the
register) lower to shift/mask/or terms — `ubfx` is the extractor spelled
directly, `bfi` keeps the destination's other bits, `sbfx` shifts the field
to the top and arithmetic-shifts it down. `ccmp` reads and sets flags: the
new flags are the comparison's when the prior condition holds and the
immediate NZCV otherwise (`Oak.AssemblerSemantics.ccmpFlags`), so the
range-check chain `cmp v, lo; ccmp v, hi, #2, hs; cset lo` is proven
against `lo <= v && v < hi` and the wrong immediate (`#0`, which leaves
`lo` true on the failing path) is refuted. `cinc`/`cneg` are selects
(`cinc_eq_csel`), `madd`/`msub` multiply-add terms (a constant factor stays
linear). The Oak side gained the prefix `^` (bitwise not).

**General-purpose ISA coverage.** The table now spans the A64
general-purpose instruction set; `asm/isa_test.go` is the coverage
witness (every mnemonic parses, matches a form, passes the checker, and
renders). Operands: shifted registers (`x2, lsl #3`, also `lsr`/`asr`/`ror`)
on the arithmetic and logical group, extended registers (`w2, uxtw #2`,
`sxtw`) on `add`/`sub`/`cmp`/`cmn`, and shifted immediates (`#imm, lsl #16`)
on the wide moves. By group, with the verifier's status:

| Group | Instructions | Verifier |
| --- | --- | --- |
| arithmetic, carry | `add sub adds subs adc sbc adcs sbcs neg negs ngc ngcs cmp cmn madd msub mneg` | modeled (`adcs`/`sbcs` flags unknown) |
| logical | `and ands orr eor bic bics orn eon tst mvn` | modeled |
| shifts, rotates, fields | `lsl lsr asr ror extr ubfx ubfiz sbfx sbfiz bfi bfxil bfc`, and `lslv lsrv asrv rorv bfm sbfm ubfm` under their own names | modeled (the raw names checked only) |
| bit manipulation, extends | `rev rev16 rev32 rbit clz cls sxtb sxth sxtw uxtb uxth` | modeled (`clz` as a priority encoder) |
| wide moves | `movz movn movk` | modeled |
| conditional | `csel cset csetm csinc csinv csneg cinc cinv cneg ccmp ccmn` | modeled |
| multiply, divide | `mul smull umull smaddl umaddl smsubl umsubl smnegl umnegl smulh umulh udiv sdiv` | modeled; two symbolic operands, high products, and division exceed the bit-level budget (evidence); Oak's `/` and `%` trap and stay unlowered |
| memory | `ldr str ldp stp ldnp stnp ldrb ldrh strb strh ldrsb ldrsh ldrsw ldpsw ldur stur ldurb ldurh sturb sturh ldursb ldursh ldursw`, the unprivileged `ldtr sttr ldtrb ldtrh sttrb sttrh ldtrsb ldtrsh ldtrsw`, `adr adrp`, `prfm prfum rprfm` | loads through spans and the frame modeled (sign-extending loads sign-extend the element); the unprivileged forms, `adr`/`adrp`, and the prefetches checked only |
| ordered, exclusive, atomic | `ldar ldxr ldaxr ldapr stlr stxr stlxr ldlar stllr` (+`b`/`h`), the pairs `ldxp ldaxp stxp stlxp`, the LSE set `ldadd ldclr ldeor ldset ldsmax ldsmin ldumax ldumin swp cas` × {`-`,`a`,`l`,`al`} × {`-`,`b`,`h`}, `casp` × {`-`,`a`,`l`,`al`}, the store-only `stadd stclr steor stset stsmax stsmin stumax stumin` × {`-`,`l`} × {`-`,`b`,`h`}, `clrex` | checked: a guarded writable span, one element or pair sized by the value registers, roles per operation (`stxr`/`stxp` write their status register, `cas`/`casp` read every register, the store-only forms write none); trusted by the verifier |
| branches | `b b.cond cbz cbnz tbz tbnz bl blr br ret ret-xN` | `br`/`blr` checked as an indirect transfer/call; trusted |
| hints, traps, exceptions | `nop wfe wfi sev sevl yield csdb esb ssbb pssbb hint brk svc hvc smc` | hints have no value semantics; `brk` ends control; `svc`/`hvc`/`smc` need `system` and clobber the caller-saved state; trusted |
| system, barriers, maintenance | `mrs msr eret eretaa eretab dmb dsb isb dc ic tlbi at cfp cpp dvp` | checked under `system`; trusted |
| CRC, flags | `crc32{b,h,w,x} crc32c{b,h,w,x} cfinv` | checked; trusted |
| scalar floating point | `fmov fadd fsub fmul fdiv fnmul fmax fmin fmaxnm fminnm fneg fabs fsqrt frint{a,i,m,n,p,x,z} fmadd fmsub fnmadd fnmsub fcmp fcmpe fccmp fccmpe fcsel fcvt fcvt{z,a,m,n,p}{s,u} scvtf ucvtf frecpe frecps frecpx frsqrte frsqrts facge facgt fcvtxn` on the `h`/`s`/`d` views; `f32`/`f64` parameters bind to `s`/`d` registers, results return in `v0` | checked (forms, view widths, `fcmp` flags feed `b.cond`/`csel`/`fcsel`); trusted |
| NEON integer | arithmetic, logical, bitwise selects (`bsl bit bif`), saturating, halving and rounding-halving forms (`shsub uhsub srhadd urhadd sqabs sqneg suqadd usqadd`), absolute differences with accumulate (`saba uaba sabal uabal sabdl uabdl`), pairwise, compares (register and against zero), min/max and reductions (`addv smaxv … uaddlv`), shifts, rounding shifts, and shift-inserts (`srshr urshr srsra ursra sqshlu sqrshl uqrshl`), saturating doubling multiplies (`sqdmulh sqrdmulh sqrdmlah sqrdmlsh sqdmull sqdmlal sqdmlsl`), widening and narrowing (`ushll xtn sqxtn sqxtun uaddl umull uaddw addhn raddhn subhn rsubhn shrn sqshrun sqrshrun …` and their `2` halves), integer reciprocal estimates (`urecpe ursqrte`), `dup ins umov smov mov ext tbl tbx zip uzp trn rev16/32/64 cnt movi mvni` | checked: arranged operands agree unless the instruction widens, narrows, or reduces; lanes bounded at parse | trusted |
| NEON float | `fadd fsub fmul fdiv fmla fmls fmulx fabd fmax fmin faddp fmaxp fminp fmaxnmp fminnmp` (and their scalar pairwise forms) `fneg fabs fsqrt frint* fcmeq fcmgt fcmge fcmlt fcmle facge facgt frecpe frecps frsqrte frsqrts fcvtn fcvtl fcvtn2 fcvtl2 fcvtxn fcvtxn2` and the vector conversions | checked | trusted |
| vector memory | `ldr str ldp stp ldur stur` of `h`/`s`/`d`/`q`; `ld1 st1 ld2 st2 ld3 st3 ld4 st4 ld1r ld2r ld3r ld4r` with register lists | checked: sizes from the register view (a `q` load moves 16 bytes; `ld2 {v0.2d, v1.2d}` 32), through guarded spans or the frame | trusted (the verifier never keys vector state with the general registers) |

| Apple M-series extensions (ARMv8.4–8.6, arm64e) | pointer authentication (`pac*`/`aut*` register, zero-modifier, and `sp`/`lr` forms, `xpac*`, `pacga`, `retaa`/`retab`, `eretaa`/`eretab`, `braa`/`brab`/`blraa`/`blrab` and z forms, `ldraa`/`ldrab`), `bti`, `sb`, `dgh`, `wfet`/`wfit`, FlagM/FlagM2 (`setf8 setf16 rmif axflag xaflag`), RCpc2 (`ldapur*`/`stlur*`), FP16 scalar arithmetic on the `h` view, DotProd (`sdot udot`), I8MM (`smmla ummla usmmla usdot sudot`), BF16 (`bfdot bfmmla bfmlalb bfmlalt bfcvt bfcvtn bfcvtn2`), FHM (`fmlal fmlsl` and `2` forms), FCMA (`fcadd fcmla`, rotations validated), JSCVT (`fjcvtzs`), FRINTTS (`frint32z/x frint64z/x`), crypto (`aes* sha1* sha256* sha512* eor3 rax1 xar bcax pmull pmull2` with the `1q` arrangement), scalar NEON integer forms on `b`/`h`/`s`/`d` | checked (`paciasp`-style link-register signing is transparent to the callee-saved discipline; authenticated returns and indirect transfers follow the `ret`/`br`/`blr` rules); trusted |

| SVE and SME (streaming SVE, SME, SME2, SME_F64F64, SME_I16I64 — the M4's set; `asm/isa_sme.go`) | every mnemonic of the generated encoding table on those features — the streaming-legal SVE data processing, predicates and compares, `whilelt`/`ptrue`/`cntp`, the SVE loads and stores (`ld1w {z0.s}, p0/z, [x0, x1, lsl #2]`, `[x0, #1, mul vl]`, multi-vector groups under `pn8/z`), `smstart`/`smstop`, `zero`, the outer products (`fmopa fmops bfmopa smopa umopa sumopa usmopa addha addva`), tile slices and array vectors (`mova`, `ld1w {za0h.s[w12, 0]}`, `fmla za.s[w8, 0, vgx4]`, `ldr za[w12, 0]`), `luti2`/`luti4` over `zt0` | checked: the legal operand forms are exactly the readings of Arm's templates (the encoder's structural match decides — no hand-written form list); mode, zeroing, and authority per §3 | trusted |

The bitvector verifier does not model floating-point or vector values: any
body touching a vector, scalable, or ZA register is trusted per §5 and says
so. What the table does not cover, by design: non-streaming SVE (the M4
has SVE only inside streaming mode), the SME features beyond the M4's
(SME2p1 and later, the FP8 and B16B16 products), strided multi-vector
lists and `psel`, and the system-register namespace beyond `mrs`/`msr`
(any register name is accepted under `system`).

**Grounding the model in the hardware and in Arm's specification.** The
verifier's semantics are a reading of the Arm manual, transliterated into
Lean (`Oak.AssemblerSemantics`) and Go. The **silicon differential**
(`asm/silicon_test.go`) executes every modeled register-level instruction
body natively on the host's AArch64 core — pinned-register inline asm over a
deterministic operand set of boundary values and a generator — and requires
bit-for-bit agreement with the executor's term semantics: 181 bodies (every
data-processing form, every condition code after `cmp`/`adds`/`subs`/`tst`,
`ccmp`/`ccmn` chains, carry chains, multiplies, division, bit fields, bit
manipulation, extends, wide moves, shifted and extended operands) × 60
inputs agree. **Arm's ASL primitives, transliterated and proved
(`Oak.ArmASL`).** The shared pseudocode functions the semantics rest on are
transliterated into Lean from the Sail model of Armv8.5-A that Arm and the
REMS group generated from Arm's own ASL (`sail-arm`, BSD-3-Clause-Clear),
with the Sail text quoted beside each definition, and our definitions are
proved equal to them: `AddWithCarry` — the `cmp`/`subs` form is `l - r`
and the `adds` form `l + r` (`AddWithCarry_sub_result`/`_add_result`); its
N, Z, and C flags are our `flagsOf`/`addFlagsOf` at every width
(`subFlags_n/z/c`, `addFlags_n/z/c` — C is the "no borrow" reading, `r ≤
l`), and V — Arm's `SInt` overflow against our sign-bit formula — is
checked exhaustively by the kernel at width 5 and by the silicon
differential at 32 and 64 bits; `ConditionHolds` on the A64 condition-code
encodings is our `Cond.holds` for every code and every flag pattern
(`holds_eq_ConditionHolds`); the conditional-select family is Arm's
`integer_conditional_select` with its `else_inv`/`else_inc` switches
(`csel_asl`, `csinc_asl`, `csinv_asl`, `csneg_asl`); `ccmp`'s flags are
Arm's `integer_conditional_compare` (`ccmp_asl_n`); `tst`'s flags are the
logical-result flags (`tst_asl`); `HighestSetBit`/`CountLeadingZeroBits`
are stated with `clz_zero`, and `udiv` by zero is zero as Arm specifies.
The chain is now: Arm's ASL ≡ `Oak.ArmASL` ≡ `Oak.AssemblerSemantics`
(proved) ≡ the Go executor (transliteration, checked against the silicon).
**The table audited against Arm's decoder (`asm/sail_coverage_test.go`).**
The same Sail model carries Arm's A64 decode tree as one clause per
encoding class — a 32-bit pattern of fixed bits and fields, and the decode
function it dispatches to. The audit walks every clause, draws encodings
from its pattern (the free bits clear, set, and pseudo-randomly filled from
a fixed seed), and asks the host LLVM disassembler, configured for the
Apple M4, which mnemonic each defined encoding spells; the disassembler is
the encoding-to-text oracle only, the classes come from Arm's tree. Every
mnemonic Arm's decoder reaches must be in the table or on the audit's
exclusion list, each entry with its reason — so an instruction class the
table silently lacks fails the test by name. On landing the audit reached
720 mnemonics from 917 classes and found 185 missing; all but seven are now
in the table (non-temporal and exclusive pairs, pair compare-and-swap, the
store-only atomics, unprivileged and limited-ordering accesses,
authenticated loads and exception returns, `adr`/`adrp`, the bit-field
aliases `bfc`/`bfxil`/`sbfiz` — modeled by the verifier and checked on
the silicon — the negated widening multiplies, the speculation barriers,
the prefetch forms, and the NEON/FP families the first pass left out:
bitwise selects, narrowing high halves, second-half widening forms,
saturating doubling multiplies, rounding shifts, absolute compares,
reciprocal estimates and steps, FP conditional compares, the inexact
narrowing conversion, replicating structure loads). Excluded by design:
the debug-state instructions (`dcps1–3`, `drps`, `hlt`) and the raw `sys`/
`sysl`, whose aliases (`dc`, `ic`, `tlbi`, `at`) are the table's spelling.
The audit skips when the model or the disassembler is absent.

**Operand forms audited against Arm's A64 ISA XML
(`asm/isa_xml_test.go`).** Arm's machine-readable release (one XML file per
instruction: encodings, assembler templates such as `ADD <Wd>, <Wn>,
<Wm>{, <shift> #<amount>}`, feature requirements, and the operand
explanations with the size tables behind `<V>`) is read from
`external/isa-a64` beside the checkout — Arm's notice forbids
redistribution, so nothing from it is committed and the test skips without
it. Every template of a mnemonic the table carries, on features the
M-series has (Armv8.7-A plus the extensions LLVM enables for apple-m4; the
optional features it lacks are listed with reasons), is expanded — optional
groups present and absent, alternatives, the correlated scalar sizes
`<V>`/`<Va>`/`<Vb>` taken from the encoding's own tables so `<Va><d>,
<Vb><n>` yields exactly the pairings the encoding expresses — and
translated to our operand-form vocabulary; the table must admit every
derived form, and every table form must be spelled by some template. On
landing the audit found 214 forms Arm spells that the table refused and
94 table forms no template spells. The refusals are closed: the
extended-register `add x, x, w` family, scalar and by-element FP/NEON forms
(compares against `#0.0`, fixed-point conversions with a fraction-bit count,
`fmla`/`fmul`/`fmulx` and the long multiplies by element, saturating scalar
shifts and narrowing shifts, `sqshl`/`uqshl` register forms), byte-view
loads and stores, vector pairs for `ldnp`/`stnp`, `mov` of a scalar from an
element, `msr` of a PSTATE field from an immediate, prefetch operations by
number, `rev64`, `sxtb`/`sxth` widening into an X register, `sxtl`/`uxtl`,
`bfm`/`sbfm`/`ubfm` and `lslv`/`lsrv`/`asrv`/`rorv` under their own names,
`dmb`/`dsb`/`isb` by number, `bic`/`orr` vector immediates, `dup` and the
integer reductions into `b`, PAC with an `sp` modifier, `fmov` between `h`
and `x`. The suspect table forms were real errors, now removed: integer
compares against a float immediate and float compares against an integer
one, zero-compare forms for `cmhi`/`cmhs`/`cmtst` that Arm does not define,
a vector `fnmul`, a scalar `mvni`, 64-bit `uxtb`/`uxth`, `sxtb x, x`, scalar
`sshl`/`ushl`/`srshl`/`urshl` beyond `d`, reductions into `q`. The audit
also exposed an initialization-order bug: the M-series file's FP16
extensions ran before the FP file replaced those entries, so every `h`
form it added was silently lost — the table files are now ordered
(`isa.go`, `isa_fp.go`, `isa_m_series.go`) and the audit guards it. Left
out by design and reported, not required: literal loads (`ldr x0, label` —
an asm unit has no data section), forms through `sp` beyond `add/sub sp,
sp, #imm` (the frame discipline), post-index by register, and structure
lane lists (`ld1 { v0.b }[3]`). The same release also audits mnemonic
coverage, feature-gated for the M-series, on top of the Sail-decoder audit
above (the XML is Armv9.7 current where the Sail model stops at v8.5).

**Sail-to-Lean: the hand transliteration proved against mechanically
generated Lean (`spec/sail/`).** `spec/sail/arm_primitives.sail` carries
Arm's Sail text for the primitives the semantics rest on — `AddWithCarry`,
`ConditionHolds`, `integer_conditional_select`,
`integer_conditional_compare_register`, `HighestSetBit`,
`CountLeadingZeroBits`, with `IsZero`/`UInt`/`SInt` from Arm's prelude —
copied from the Armv8.5-A model with the adaptations listed in the file's
header (register reads and writes become parameters and results; Arm's
prelude names are restated over the Sail standard library; none changes a
computed value). Sail's Lean backend (Sail 0.20.2, `regen.sh`) generates
`spec/sail/lean/Out.lean` from it, against the Sail Lean support library
(rems-project/lean-sail, `setup.sh`); the generated files are committed and
`asm/sail_lean_test.go` requires them to equal a fresh generation. Then
`spec/sail/lean/Bridge.lean` proves `Oak.ArmASL` equal to the generated
code: `AddWithCarry_bridge` (result and all four flags, every width ≥ 1),
`ConditionHolds_bridge` (every code and flag pattern), `conditionalSelect_bridge`,
`conditionalCompare_bridge`, and `HighestSetBit_bridge`/
`CountLeadingZeroBits_bridge` (the generated early-return `foreach` loop,
through the support library's integer-range loop, is our list search at
every width). With the theorems of `Oak.ArmASL`, the chain is closed
mechanically: Arm's ASL → Sail (Arm's tooling) → Lean (Sail's backend) ≡
`Oak.ArmASL` ≡ `Oak.AssemblerSemantics` (proved) ≡ the Go executor
(checked on the silicon). The bridge is a separate Lake package so the
main specification builds without the Sail toolchain.

## 9. Native encoding, and the architectures to come

**The encoder (`asm/encode.go`, table `asm/encodings_gen.go`).** Oak emits
C and lets the system toolchain assemble the `__asm__` text — that remains
the default path. Alongside it the assembler now encodes its own machine
words, so that a unit's bytes depend on nothing outside this repository and
Arm's specification. The encoding table is *generated* from Arm's A64 ISA
XML by `asm/internal/isagen` (run against the release under `external/`;
only the derived facts are written, never Arm's prose): for every encoding
on features the M-series has — 3046 of them, the base and SIMD&FP sets
and, since the SME lane, the streaming-legal SVE and SME sets — the fixed
bits (from the encoding diagram, the per-encoding bit settings, and the
decode-time `if size != '10' then UNDEFINED` and `if size IN {'0x'} then
UNDEFINED` constraints), the named bit fields, and
every assembler template reading with its operands mapped to the fields
Arm's operand explanations state: register operands to their register
field (with `sp` and the zero register admitted where the template spells
them), immediates with the range, scale ("a multiple of 8", "encoded as
<pimm>/8"), offset ("encoded as imm6 plus 1"), and special forms (bitmask
immediates, wide moves, the vector shift and fixed-point immediates whose
`immh:immb` carry the element size, the byte-mask and modified immediates,
the 8-bit floating-point constants), spelled words with their value tables
(shifts, extends, conditions, barrier and prefetch options, arrangements,
element sizes — including the correlated `<V>`/`<Va>`/`<Vb>` sizes and the
per-size element-index formulas), labels with their scale and range, field
slices (`op2[2:1]`), the defaults of omitted optional operands (`ret` →
Rn = 30, `clrex` → CRm = 15, `isb` → SY), and for every alias the
equivalence template Arm gives (`BFI … ≡ BFM <Wd>, <Wn>, #(-<lsb> MOD 32),
#(<width>-1)`) with its preference condition (`Rd == '11111' || Rn ==
'11111'`).

The encoder matches a checked instruction against the readings of its
mnemonic and writes the fields. Aliases encode directly when their own
fields determine the word and the preference condition holds; when an
operand is computed (`bfi`'s lsb and width) or the condition names a field
the alias's operands did not write (`cinc`'s `Rn == Rm`), the equivalence
template is evaluated — its expressions (`MOD`, `+`, `-`, register
re-spellings such as `<Xn>` for a bound `<Wn>`, `WZR`/`XZR` literals,
inverted conditions) — and the instruction it stands for is encoded
instead. `mov #imm` chooses among `movz`, `movn`, and a bitmask `orr` as
the three aliases prescribe; scaled loads fall back to their unscaled
spelling when the offset is not a multiple of the access size; the
extended-register forms are taken without an extend only when `sp` makes
them unambiguous, as Arm's text states. Labels within a function resolve
to PC-relative displacements (range- and alignment-checked); a symbol
outside it yields a relocation record (branch26, condbr19, tbz14, adr21,
adrp21) with a zero displacement. `EncodeFunction` produces the bytes of a
checked function with its relocations; nothing links or writes object
files yet.

**Trust.** The encoder is checked against the host LLVM assembler three
ways (`asm/encode_test.go`, `asm/sme_test.go`, skipped without `llvm-mc`): 672 hand-written
instructions across the general-purpose, system, FP, and NEON surface
agree word for word; a seeded fuzz instantiates every template reading of
the generated table with random operands and requires agreement wherever
both assemblers accept the text (on landing 5307 instantiations from 1319
encodings, 4219 agreeing, the rest rejected by LLVM as architecturally
invalid random operands, none we encode differently); and whole functions
of `examples/asm` encoded with labels resolved equal LLVM's object code.
The specification side is Arm's: the table is Arm's XML, so a disagreement
with LLVM is a bug in one of the two readings of the same document, and the
tests found several on the way (the wide-move and byte-mask immediates,
the element-index field orders, the omitted-operand defaults). Not yet
encoded: post-index by register, structure lane lists, `wsp`, literal
loads.

**System registers (`asm/sysregs_gen.go`, from Arm's SysReg XML by
`asm/internal/sysreggen`).** Every AArch64 register MRS or MSR can name —
1232 of them, register arrays expanded (`dbgbvr0_el1` … `dbgbvr15_el1`,
`icc_ap0r1_el1`, `pmevcntr30_el0`) from the index expressions of their
encodings — with its op0:op1:CRn:CRm:op2 and its access directions. The
checker holds `mrs`/`msr` to that table: an unknown name is an error
(implementation-defined registers keep the `S<op0>_<op1>_<Cn>_<Cm>_<op2>`
spelling), reading a write-only register or writing a read-only one is an
error. Checked against the host assembler on every access it knows: 1772
agree, none differ; the 417 it does not know are newer than the host
LLVM. `TestGeneratedTablesCurrent` regenerates both tables from the
releases under `external/` and requires the committed files to match.

**Object emission (`asm/object.go`).** The encoded functions of a
compilation's asm units are written as a relocatable object — Mach-O
(`MH_OBJECT`, `CPU_TYPE_ARM64`, one `__TEXT,__text` section,
`LC_SYMTAB`, `LC_BUILD_VERSION`, `MH_SUBSECTIONS_VIA_SYMBOLS`) or ELF64
(`ET_REL`, `EM_AARCH64`, `.text`/`.rela.text`/`.symtab`/`.strtab`) — under
the C symbols the emitted C declares, functions laid out at their entry
alignment, calls to other Oak functions as relocations
(`ARM64_RELOC_BRANCH26`; `R_AARCH64_CALL26`/`JUMP26`/`CONDBR19`/`TSTBR14`/
`ADR_PREL_LO21`/`ADR_PREL_PG_HI21`). Every offset and count is computed
from the encoded bytes and checked against the field that carries it; a
layout the format cannot express (a conditional branch to an external
symbol on Mach-O, an odd alignment) is an error, never a truncated file.
The compilation's `EmitNative` emits, in one pass, the C with asm units
as prototypes (`EmitCExtern`: no `__asm__` text; without an Oak fallback
body the C fails closed off AArch64) and the companion object; `oak run`
and `oak build` link the object beside the C. **On AArch64 hosts this is
the default (`-asm native`)**: the C toolchain compiles the C and links,
and never sees the assembly. `-asm c` keeps the inline `__asm__` path (the
portable lowering under `-DOAK_PORTABLE_INTRINSICS` still uses it, since
the C then defines the functions itself). Checked: `llvm-objdump`
disassembles our Mach-O and ELF objects to exactly the encoder's words
with the recorded relocations, `llvm-nm` lists the symbols, and
`examples/asm` builds, links, and runs to its expected exit through the
native path (`TestE2EExampleAsmPackageNative`).

**What self-hosting still needs.** (1) A native backend for Oak bodies —
a real compiler back end from the checked tree to machine code through
this encoder and object writer, with the C backend kept as the portable
realization and the differential oracle: its first increment has landed
(below). (2) The proof and solver stack in Oak itself, the long arc
(`95-extraction.md` is its current foothold).

**Native backend for Oak bodies (first increment landed; `nativegen`).**
The backend lowers a type-checked Oak function to an `asm.Function` — the
same object an `.oakasm` unit yields — so everything this chapter built
applies to the compiler's own output: the seam checker holds the generated
code to its bindings, clobbers, frame, flags, and callee-saved disciplines
(a finding is a backend bug and rejects the compilation), the §8 verifier
proves it equal to the Oak body where its subset reaches (a mismatch
rejects), the encoder and object writer realize it, and the Oak body stays
as the portable realization under `OAK_PORTABLE_INTRINSICS` — the
differential oracle. `Compilation.WithNativeBodies()` (CLI `-native`)
switches it on; a function outside the subset is left to the C backend
with the reason reported.

The subset: parameters, locals, and results of the fixed-width integers
and `Bool` (or a unit result); literals; wrapping `+ - * & | ^`; `/` and
`%` with the C helpers' edge cases (zero traps through `brk #1`; `MIN /
-1` and `MIN % -1` wrap as `sdiv`/`msub` give); shifts (a count at or
beyond the width traps; constant counts fold the check away);
comparisons as `cmp`/`cset` at the operands' signedness; short-circuit
`&&`/`||`; `!`, `-`, `^`; the widening constructors and the
`trunc`/`bits` conversions; the Bool conditional in value and statement
position; typed locals and assignment; `while`/`break`; `assert` (a
trap); and calls to program functions with scalar signatures, including
tail self-calls (as calls — the loop lowering is a follow-up). Values
live in 8-byte frame slots, one per parameter and local, stored and
loaded at their type's width; expressions evaluate into x9–x15 as a
small operand stack, spilled to their own slots around calls — the checker
would refuse a caller-saved register read after `bl`, so the discipline is
enforced, not assumed. A narrow value stays normalized in its register
(zero- or sign-extended), which is also how a narrow parameter enters:
AAPCS64 leaves the register bits above it unspecified.

That contract is now what the verifier models: a parameter of type `u8`
is an 8-bit unknown with a fresh unknown above it in the register
(`a#hi`), a `Bool` a 1-bit one, results compare at their type's width,
locals carry their declared width, and the `trunc`/`bits` conversions
lower — so `byte_sum: (a, b: u8) -> u8 = a + b` is proven for the
normalizing code and would be refuted for code that added the raw
registers, the ABI bug the old 32-bit model could not see. Executed
(`TestE2ENativeBodies`): a twelve-function program — wrapping and narrow
arithmetic, signed division, conditionals, a loop with `break`, calls with
live temporaries across them, tail recursion, conversions, and `main`
itself — lowered entirely by the backend, six functions proven at the bit
level and the rest trusted with the reason (`bl`, no integer result, the
conversion the verifier had not modeled before this increment), exit 42
natively, through the C backend alone, and as the portable realization.
**Second increment — spans, views, and the tail loop.** Span (`[*]T`) and
view (`[]T`) parameters of fixed-width elements bind as their `{base, u32
len}` pair and stay in those registers (the checker keys a span's facts on
its bound base, so a span kernel is a leaf: a call would clobber the pair
and a reload would drop the fact — such functions stay with the C
backend). `len(v)` reads the length register; `v[i]` and `v[i] = e` go
through the checker's own idiom — the index in a 32-bit scratch register,
`cmp wI, wL` then `b.hs <trap>` immediately before the access, then
`ldr`/`ldrb`/`ldrsh`/`str`/… `[xBase, wI, uxtw #log2(elem)]` — so every
element access is bounds-checked (out of range traps, as the C backend's
`oak_index` does), stores need a writable span, and the checker's
index-fact rule admits the access rather than trusting it. A self-call in
result position lowers to a loop: the arguments into the parameter slots,
then a jump to the header after the prologue — constant stack depth, as
the discipline requires. The verifier now drops a path that ends in `brk`
from the fork that reached it (the Oak body traps on the same inputs:
a failed bounds check, division by zero, an overflowing shift), so the
guarded element load `at: (v: []u32, i: u32) -> u32 = v[i]` is proven and
`byte_sum`/`clamp8` are proven at their 8-bit contracts. Variables now live in the callee-saved registers x19–x28 in declaration
order (saved in pairs in the prologue, restored before `ret` — the
checker's callee-saved discipline applies to the compiler's code), with
frame slots only past ten variables; a comparison of simple operands emits
directly as `cmp` then `b.cond`; and a result conditional with one
tail-call arm is laid out with the tail arm falling through to the back
edge. That is the loop shape the verifier recognizes, and its loop
recognizer now admits a guard's branch to the trap block inside a body —
so the compiled `sum` and `byte_total` loops are **proven** equal to their
Oak `while` bodies by inductive coupling (`acc↔x19, i↔x20` under the
invariant `i ≤ len(v)`), exactly as the hand-written checksum was.
Executed (`TestE2ENativeSpans`): a view sum, a byte total with
zero-extending loads, a fill through a span with halfword stores, an
element read, and a tail-recursive count as a loop — exit 42 natively and
through the C backend, and an index at the length traps in both
realizations. The verifier also reads a tail-recursive Oak body `c ? v | f(args)`
as the loop it denotes (the parameters as locals, `while !c { params =
args }`, then `v` — with fresh temporaries so the arguments read the old
parameters, as the compiler's own layout does), so the compiled
`count_down` is proven by coupling and the 64-bit `fact` agrees on every
witness (its product's continue-condition proof exceeds the budget).
**Third increment — floating point.** `f32`/`f64` parameters, locals,
results, and span elements: arguments and results in `s0`–`s7`/`d0`–`d7`
by their own AAPCS64 count, expression temporaries in `v16`–`v23`,
variables in the callee-saved `v8`–`v15` with their `d` views saved in
pairs and restored before `ret`; literals as their IEEE bit pattern through
an integer register and `fmov`; `+ - * /` and unary minus as
`fadd`/`fsub`/`fmul`/`fdiv`/`fneg` (nothing is contracted, as the C
backend's `FP_CONTRACT OFF` states); comparisons as `fcmp` with the codes
that read the flags as C does (`mi`, `ls`, `gt`, `ge`, `eq`, `ne`, so an
unordered pair is unequal and neither below nor above); widening `f64(x)`
and `f32_round_f64` through `fcvt`; `fN_round_iM` through `scvtf`/`ucvtf`;
`bits` through `fmov`; `iN_saturating_fM` through `fcvtzs`/`fcvtzu` (which
saturate at the register and send NaN to 0, the helper's semantics) with a
`cmp`/`csel` clamp to a narrower target's range; `iN_trunc_fM` with the C
backend's range check first (NaN or a value outside the target's open
interval traps) and the correctly rounded intrinsics that are one
instruction each (`sqrt abs floor ceil trunc round round_even min max
min_num max_num`, `fma` as `fmadd`). The checker now holds `d8`–`d15` to
the callee-saved obligation it held `x19`–`x30` to — readable on entry,
written only after a save, restored before every `ret`, with
`smstart`/`smstop` (which zero them) counting as writes — which found that
the shipped SME kernel had been clobbering the caller's `d8`–`d15`; it
saves them now. Executed (`TestE2ENativeFloats`): thirteen float
functions natively against the C backend and the portable realization,
including a float span reduction and a store loop, and an out-of-range
`trunc` trapping in both. Float bodies are trusted by the verifier (§5).
**Fourth increment — owned arrays in the frame.** A local `buf: [N]T`
occupies `N·sizeof(T)` bytes of the frame (whole 8-byte slots), zero-filled
by `stp`/`str` of a zero register as the C backend leaves no storage
uninitialized, or stored element by element from a literal `[e0, …]`.
`buf[i]` with a literal index inside the array addresses its slot through
`sp` directly; any other index goes through the array's frame address —
`add xB, sp, #off`, the constant guard `cmp wI, #N; b.hs trap`, then
`ldr/str … [xB, wI, uxtw #s]` — so an index at or past `N` traps exactly as
the C backend's guard does. `view(&buf)` and `span(&buf)` are admitted as
call arguments (the callee receives the `{frame address, N}` pair in two
consecutive argument registers; a `[]T` parameter takes either, a `[*]T`
one only `span`), and `len(buf)` is the constant `N`. The checker gained the
matching fact: `add xN, sp, #imm` (a new form of `add`) records that `xN`
holds an entry-relative frame address; memory through it is checked
against the declared frame like `[sp, #imm]` — a plain offset must lie
inside the frame, an indexed access needs a dominating constant index guard
(`cmp wI, #K` then `b.hs <exit>`) with all `K` elements inside the frame,
scaled by whole elements, and pre/post-indexing is refused. The fact dies
with a write to the register or a call, flows through the label fixpoint
with the span and index guards (the meet keeps it only where every
predecessor agrees on the address), and is exercised by
`TestCheckerFrameArrays` (an accepted body and eight refusals). A call's
result is now readable in `v0` as well as `x0` (the checker sees no callee
signature; the same latitude it always gave `x0`). Executed
(`TestE2ENativeArrays`): a byte histogram bucketed into four owned counters
by a computed index, a literal-initialized array passed to a leaf through
`view`, zero-filled storage filled through `span` and read back, signed
bytes with sign extension, float elements, and an index at the length
trapping in both realizations — the program's `main` is now itself lowered
natively. Bodies with owned arrays are trusted by the verifier (§5): it
models frame memory only through `sp`, not through a frame address in a
register.
**Fifth increment — spans in functions that call.** A span or view
parameter arrives in its argument pair, which a `bl` clobbers; the
lowering of a function that calls now parks each pair in two callee-saved
registers in the prologue (`mov x19, x0; mov w20, w1`, from the pool the
variables use, saved and restored with them) and walks the span from
there, and a span parameter passed on to a callee moves its parked pair
into consecutive argument registers. The checker follows the copies: `mov
xD, xB` over a span base makes `xD` a base of the same span, `mov wD, wL`
over a length register adds `wD` to that span's length registers (one set
shared by a base and its copies), guards accept any register in the set,
a write drops the register from it, and a call forgets every fact on
`x0`–`x17` (a span parked there does not survive the callee — which also
closes the latitude that had let a bound argument base be dereferenced
after a `bl`). `TestCheckerSpanAliases`: walking the parked pair after a
call is accepted; the original base after the call, an overwritten length
copy, and a guard against an unrelated register are refused; a length
guard through the copy holds. Executed (`TestE2ENativeSpanCalls`): a view
forwarded twice with `len` read after the calls, a store loop calling a
helper for every element, and two parked views with a leaf called before
and inside the loop — natively against the C backend and the portable
realization. Bodies that call remain trusted by the verifier (§5).
**Sixth increment — record locals.** A declared record type of scalar
fields (`Point: type = struct { x: i32, y: i32 }`) is placed by
`semir.RecordLayoutWithSpec` over the C backend's field representations
(`u8`…`u64`, `i8`…`i64`, `f32`, `f64`; `Bool` the 4-byte C enum; a declared
per-field alignment raising the natural one; packed layouts and non-scalar
fields left to the C backend) — the same numbers `codegen/records.go`
asserts against the C compiler, so a natively compiled body and a
C-compiled one agree on every offset. A local `p: Point = Point { x: e, y:
e }` occupies the layout's size in whole 8-byte frame slots with every
field value evaluated before the name is bound; `p: Point = q` and `p = q`
copy the record slot-wise (padding travels, as C's struct assignment copies
it); `p.f` loads the field at its own width and offset with the field
type's extension (`ldrb`/`ldrh`/`ldrsb`/`ldrsh`/`ldr`, a Bool field's
32-bit `ldr`), `p.f = e` stores it likewise — through `[sp, #imm]`, which
the checker bounds to the declared frame and requires naturally aligned. A
record local without an initializer is left to the C backend (which leaves
it uninitialized; no semantics are invented natively), and records as
parameters, results, or call arguments are not yet lowered (AAPCS64
composite passing is a later increment). Executed (`TestE2ENativeRecords`):
absolute-value updates through a `Point`, a five-field record of mixed
widths updated in a loop with a Bool field written from a comparison and
read as a condition, a copy diverging from its source, whole-record
assignment, and a float field — natively against the C backend and the
portable realization. Record bodies are trusted by the verifier (§5): its
Oak side has no record locals.
**Seventh increment — records across the call boundary.** AAPCS64's
composite rules, as the C compiler applies them on the host: a record of
up to 16 bytes travels as `ceil(size/8)` consecutive `x` registers, each
an 8-byte chunk of its memory image (so `Point {x: i32, y: i32}` is one
register, `Pair {lo, hi: u64}` two), and a larger record by reference to
a copy the caller owns; a result of up to 16 bytes comes back in `x0`
(and `x1`), a larger one is written into the area whose address the
caller passes in `x8`. The lowering stores a parameter's chunks into its
frame slots in the prologue (or copies the referenced record in, whole
words then a 4/2/1-byte tail, since the body may write its own copy),
loads a record argument's chunks from its local (or copies it into a
fresh temp and passes `add xN, sp, #off`), places a record result by
loading its chunks into `x0`/`x1` or copying into the `x8` area — `x8`
parked in a callee-saved register when the body calls — and receives a
call's record into a temp (chunks stored from `x0`/`x1`, or `add x8, sp,
#temp` before the `bl`). Record literals and record-returning calls are
admitted wherever a record value is needed (initializers, assignments,
arguments, results, conditional result arms). Homogeneous floating-point
aggregates (all fields one float type, at most four), which AAPCS64
passes in `v` registers, are left to the C backend. The checker learned
the same rules from a composites table the compiler builds from the
program's record declarations (`asm.Function.Composites`, never from the
unit text; hand-written units get it too): a record parameter binds `bind
x0 = p` or `bind x0, x1 = p` by its size, a larger one binds the address
as a read-only memory region of exactly the record's size (`[xN, #off]`
inside it, naturally aligned, no indexing or moving, dying with a write to
the register or a call, copied by `mov`), a two-chunk result must leave
`x1` written at `ret`, a larger result makes `x8` a writable region of the
size on entry, and a call's result may now occupy `x1` as well as `x0`
(`TestCheckerComposites`: five accepted shapes, nine refusals). Executed
(`TestE2ENativeRecordABI`): 8-, 16-, 4-, and 24-byte records in and out,
a by-reference chain of calls with scalars interleaved, a callee mutating
its copy without touching the caller's, and a record result chosen by a
condition — natively, through the C backend, and as the portable
realization; and (`TestE2ENativeRecordMixed`) natively lowered leaves
called from a C-compiled `main`, so the two compilers' composite passing
agrees on the host ABI. `OAK_NATIVE_DUMP=1` prints every lowered
function's assembly as the checker sees it. Record bodies remain trusted
by the verifier (§5).
**Eighth increment — nested records and array fields.** A record field
may itself be a declared record or an owned array of scalars, placed by
the same natural layout the C backend asserts (a nested record at its own
size and alignment, `[N]T` as `N·sizeof(T)` at the element's alignment; a
record containing itself is refused). An access chain resolves to a frame
place — a record (a local, a nested field, or a call's record result
landed in a temp), an array (a local or an array field), or a scalar field
— and each shape has one lowering: scalar fields load and store at their
offset and width, nested records copy by their exact size in the widest
naturally aligned units then a narrowing tail (never a neighbor's bytes;
`r.b = shift(r.b, d)` replaces a nested field in place), and array fields
go through the owned-array idiom (`add xB, sp, #off`, the constant guard,
`[xB, wI, uxtw #s]`; `len(h.counts)` is the constant, `view(&h.counts)` a
call argument). Record literals take record-valued and array-valued
fields (a record place, a typed literal, a call's result; an array literal
or an array place). A nested record at an offset that is not 8-aligned is
copied into an aligned temp before its chunks are loaded for a call or a
result. Arrays of records and records holding spans remain with the C
backend. Executed (`TestE2ENativeNestedRecords`): the corpus's
`Rect {a: Point, b: Point, tag}` sum, nested field stores and a nested
record passed on and copied out, a histogram record with a `[4]u32` field
walked by a loop index, and a field of a call's result — natively against
the C backend and the portable realization.
**Ninth increment — `subslice` and local spans.** `subslice(v, start, n)`
lowers to the C helper's exact check and derivation: `cmp wS, wL; b.hi
trap` (start > len traps), `sub wT, wL, wS`, `cmp wN, wT; b.hi trap`
(n > len − start traps), `add xD, xB, wS, uxtw #s`, `mov wD', wN` — the
derived pair {base + start·elem, n}, bounds typed `u32`. A local span or
view (`field: []u8 = subslice(v, start, n)`, `w: []u8 = v`) holds its pair
in two callee-saved registers, scoped like any local, so it survives calls
and is walked, stored through, forwarded, and re-sliced exactly like a
parameter; a `subslice` in argument position takes scratch registers. The
checker gained the derived-span idiom as three facts: `cmp wS, wL; b.hi
<trap>` proves wS ≤ wL for a span's length register, `sub wT, wL, wS` under
it makes wT = wL − wS, `cmp wN, wT; b.hi <trap>` proves wN ≤ wL − wS, and
`add xD, xB, wS, uxtw #s` over the span at xB (with s the element size's
log2) then creates the span fact at xD whose length registers are every
such wN — so every index below it stays below the original length. The
facts die with a write to any register involved, at labels, and at calls;
the original span, its writability, and every other rule are untouched
(`TestCheckerSubslice`: three accepted shapes, six refusals — a missing
start or count check, the wrong scale, a rewritten start, a store through
a derived view, a guard against an unrelated register). Lean lemmas for
the rules added since the frame-array idiom (frame arrays, record regions,
the derived span) are pending — Lean is not installed on the development
host — and are listed as proof debt in `docs/spec/STATUS.md`. Executed
(`TestE2ENativeSubslice`): a tokenizer-like walk splitting a byte view at
zero bytes into local views summed by a leaf, a span re-sliced twice and
written through, an empty subslice at the end, a local view copied from a
parameter, and a subslice past the end trapping in both realizations.
Array literals now store element by element (a long literal no longer
exhausts the scratch registers).
**Tenth increment — tagged unions and `match`.** A monomorphic ADT
(`Shape: type = | Circle: i32 | Square: i32 | Empty`) is the synthetic
record `semir.TaggedUnionLayout` places: the `u32` tag at offset 0 (its
value the declaration index, or the declaration's `TagValues`) and one
field per payload-carrying variant, named after the variant, at the
payload union's offset — the numbers `codegen/records.go` asserts against
the C compiler — so an ADT is a record local, crosses calls under the
composite rules (`Shape` is 8 bytes, one chunk), and joins the composites
table. `.Circle(5)` / `Shape.Circle(5)` (the type from the written name,
the checker's resolution, or the expected type) stores the tag with a
32-bit `str` and the payload at its field (a scalar, a record place, a
call's result). A general `match` loads the tag once and compares it per
arm (`cmp wT, #tag; b.ne next`); a payload binding becomes a local of the
payload type (a scalar loaded at its width, a record copied into a fresh
local, as the C backend binds a copy), `_` or a bare binding ends the
chain, and a chain no arm closes falls to the trap block (the checker
proved exhaustiveness, so it never runs). Matches lower in statement
position (arm blocks, calls, asserts), value position (arms moved into one
register), result position (scalar and record results, each arm placed
directly), and as record values (arms copied into one temp); a scalar
scrutinee takes literal patterns. Generic ADTs, string or span payloads,
array payload bindings, and nested payload patterns stay with the C
backend. Executed (`TestE2ENativeADTs`): the corpus `Shape`/`area2`
program, a record payload bound and read in an arm, an ADT built by a
nested conditional and returned then matched by the caller with the call
as the scrutinee, a statement-position match updating a local, a literal
match over `u32`, and reassignment of an ADT local — natively against the
C backend and the portable realization. ADT bodies are trusted by the
verifier (§5).
Next increments: the verifier's frame addresses, record locals, and
derived spans (so array, record, ADT, and subslice bodies are proven, not
trusted), `break` as a second loop exit in the recognizer, arrays of
records, and the slicing syntax `v[lo:hi]` once the C backend lowers
`len` over it.



**SME/SME2 (landed).** The Apple M4 implements the Scalable Matrix
Extension (SME, SME2, SME_F64F64, SME_I16I64 — the features LLVM enables
for apple-m4) and reaches SVE only through SME's streaming mode. The
generator now reads Arm's `sveindex.xml` and `mortlachindex.xml` beside the
base and SIMD&FP indexes, gated by the shared M-series profile
(`asm/internal/armfeat`: a boolean evaluator over Arm's arch_variant
feature expressions — `FEAT_SVE || FEAT_SME` holds through SME,
`FEAT_SVE2p1 || FEAT_SME2p1` does not; non-streaming SVE is skipped where
its pseudocode says `CheckNonStreamingSVEEnabled`). Every encoding carries
the mode its pseudocode checks (`sm`, `za`, `smza`, or `nosm` for the
Advanced SIMD illegal in streaming mode) and whether its Execute writes
NZCV. New template symbols: z registers with element sizes and elements,
predicates with `/M`, `/Z`, and `/<ZM>` qualifiers, predicate-as-counter
registers (`PNg` plus 8), ZA tiles and slices (`<ZAt><HV>.S[<Ws>, <offs>]`,
`ZA.<T>[<Wv>, <offs>{, VGx4}]`, `ZA[<Wv>, <offs>]`, slice ranges
`<offs1>:<offs2>`), multi-vector groups (`{ <Zn1>.<T>-<Zn4>.<T> }`, the head
"times 2/4"), zero's tile mask, `MUL VL` offsets, `MUL #<imm>` multipliers
with the offset the Decode leaves implicit (`UInt(imm4) + 1`), and the SVE
immediate encodings (shift amounts in `tszh:tszl:imm3` as `esize + shift`
or `2·esize − shift`, dup's index above the size marker in `imm2:tsz`,
`16 minus imm4`, the FP constants). The parser knows the scalable register
file (§3), and the checker's forms for these mnemonics are exactly Arm's
template readings — the encoder's structural match decides — with the mode,
zeroing, and authority disciplines of §3 on top (`asm/isa_sme.go`).
Checked against llvm-mc: 254 hand-written SVE/SME spellings agree (the ten
LLVM rejects for apple-m4's features we reject too), the seeded fuzz over
every template reading now covers 2471 encodings with none differing, and
the whole-function differential and objects are unchanged. Executed:
`examples/sme` multiplies matrices by outer products on the M4's matrix
unit — `smstart`, `whilelt`, `zero {za0.s}`, `ld1w`/`fmopa za0.s` per step
of k, `st1w {za0h.s[w12, 0]}` per row, `smstop` — through the native
object, through the C toolchain's assembler (`.arch_extension sme`), and as
its Oak fallback (`TestE2EExampleSMEPackage`). Not modeled, reported by the
audit: strided multi-vector lists, `psel`, `movt` to `zt0[…]`, and the SME
features beyond the M4's.

**RISC-V and RVV (planned lane).** The second architecture, RV64GC first
(user-level integer and FP — the profile a hypervisor or firmware needs),
then the V extension. The plan mirrors this chapter with a better
specification situation: the instruction list comes from riscv-opcodes
(redistributable, so the table is generated and committed, not only
audited); the semantics come from riscv/sail-riscv, the ratified golden
model, which already targets Lean — the bridge of §8 applies to the whole
model rather than to a transliterated fragment; the differential oracle is
the Sail C emulator (no RISC-V silicon on the host). What is new: no flags
(the checker's dataflow rule becomes a comparison-branch rule), the RISC-V
calling convention as a second binding profile, compressed encodings, and
for RVV the vector-length and type registers (`vsetvli`) as checker state.
The term language and the BDD blaster carry over unchanged.

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
