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
  **Library units.** A standard library package may carry units too
  (`stdlib/hash.arm64.oakasm`, embedded as `stdlib.AsmUnits`): the module
  loader attaches them when the package is imported, rewriting each unit
  function's header to the package's internal name
  (`83-modules.md` §7), so the pairing rule is the root package's; the
  emitted block adds `.arch_extension crc`/`sha2` when a unit uses the
  CRC-32 or SHA-256 mnemonics, for host assemblers whose default
  architecture lacks them. The `hash` units keep their Oak bodies as
  fallbacks, so the interpreter, the Lean extraction, and non-AArch64
  builds see the portable definition and the differential tests compare it
  with the hardware path.
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

**Vector accesses (2026-09-13).** A `q` load or store over a byte span at
element index `wI` touches sixteen elements; the checker admits it under
the *slack* guard the native backend emits: `cmp wL, #16; b.lo trap`
establishes `len ≥ 16`, `sub wT, wL, #16` records `wT = len − 16` for
the span whose length register is `wL` (`slackFacts`), and `cmp wI, wT;
b.hi trap` leaves the fall-through path knowing `wI + 16 ≤ len`
(`idxFacts` with `slack`), which admits an access of `16 / elem` elements
at `wI` with `uxtw #log2(elem)` (`Oak.Assembler.index_access_lanes`,
`slack_guard`). The constant may sit in a register a `movz` just filled
(`constFacts`), as the generator spells converted literals; a slack fact
follows a copy (`mov wJ, wI`) and an added constant (`add wJ, wI, #k`
leaves `wJ + (K - k) <= len`), so the loads at `off + 16`, `off + 32`,
`off + 48` of a sixty-four-byte step are admitted by the loop condition's
own compares — the native backend emits no guard where its loop condition
`len(v) >= u32(N) && i <= len(v) - u32(N)` already proves the access
(`nativegen` loop facts, dead once `i` is assigned). The facts die as
index facts do: a write to `wI`, `wT`, or `wL` forgets them. A span's
proven minimum length is a fact about the span, not about a register: it
survives the overwrite of a copy of the length and lapses only when no
register holds the length.

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

## 8. Semantic verification of asm bodies (seven increments implemented)

**Implemented** (`asm/verify.go`, `Oak.AssemblerSemantics`): for a function
with both an asm unit and an Oak fallback body, the asm gate runs the
verifier and labels its verdict — **proven** when both sides normalize to
the same linear form modulo the result width (sums of parameters and
constants; `lsl` by a constant as multiplication; the `wN` write/read masks
are transparent modulo 32), **mismatch** when any witness input disagrees
(a hard error naming the input and both values — a wrong body never
compiles), **proven at the bit level** when, beyond the linear form, both sides
bit-blast (`asm/blast.go`, a small ROBDD with complement edges — negation a bit flip, a function and its negation one node, every high edge positive so equal functions are one edge (`Oak.BddComplement`) — under an interleaved variable order, run beside a per-parameter blocked order and a control-first order, the first within the node budget deciding)
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
| NEON integer | arithmetic, logical, bitwise selects (`bsl bit bif`), saturating, halving and rounding-halving forms (`shsub uhsub srhadd urhadd sqabs sqneg suqadd usqadd`), absolute differences with accumulate (`saba uaba sabal uabal sabdl uabdl`), pairwise, compares (register and against zero), min/max and reductions (`addv smaxv … uaddlv`), shifts, rounding shifts, and shift-inserts (`srshr urshr srsra ursra sqshlu sqrshl uqrshl`), saturating doubling multiplies (`sqdmulh sqrdmulh sqrdmlah sqrdmlsh sqdmull sqdmlal sqdmlsl`), widening and narrowing (`ushll xtn sqxtn sqxtun uaddl umull uaddw addhn raddhn subhn rsubhn shrn sqshrun sqrshrun …` and their `2` halves), integer reciprocal estimates (`urecpe ursqrte`), `dup ins umov smov mov ext tbl tbx zip uzp trn rev16/32/64 cnt movi mvni` | checked: arranged operands agree unless the instruction widens, narrows, or reduces; lanes bounded at parse; trusted |
| NEON float | `fadd fsub fmul fdiv fmla fmls fmulx fabd fmax fmin faddp fmaxp fminp fmaxnmp fminnmp` (and their scalar pairwise forms) `fneg fabs fsqrt frint* fcmeq fcmgt fcmge fcmlt fcmle facge facgt frecpe frecps frsqrte frsqrts fcvtn fcvtl fcvtn2 fcvtl2 fcvtxn fcvtxn2` and the vector conversions | checked; trusted |
| vector memory | `ldr str ldp stp ldur stur` of `h`/`s`/`d`/`q`; `ld1 st1 ld2 st2 ld3 st3 ld4 st4 ld1r ld2r ld3r ld4r` with register lists | checked: sizes from the register view (a `q` load moves 16 bytes; `ld2 {v0.2d, v1.2d}` 32), through guarded spans or the frame; trusted (the verifier never keys vector state with the general registers) |

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

**Vectors (seventh increment, 2026-09-13; `asm/verify_vector.go`,
`asm/verify_simd.go`).** The verifier follows the vector file. A NEON
register is a 128-bit value held as lanes of one width, each lane a term
of the scalar language, repacked through its two 64-bit halves when read
at another width; the instructions the native backend emits
(`nativegen/simd.go`) are lane functions over those terms — `and`/`orr`/
`eor`/`bic` bitwise, `add`/`sub`/`umin`/`umax`/`uqsub`/`uqadd`/`cmeq`/
`cmhi`/`cmhs` per lane at the arrangement's width (`cmeq #0` included),
`ushr`/`sshr`/`shl #n`, `dup` from a general register or a lane, `movi`,
`tbl` with one table register as a sixteen-way select per lane (an index
at or beyond sixteen selects zero), `ext #n` as the bytes of the
concatenation from position n, `umaxv`/`uminv`/`addv` into a scalar view
(the rest of the register zeroed), `cnt`, `umov`/`smov` of a lane into a
general register, and `fmov` between the files. A `q` store or load of the
frame is two 8-byte slots (the low half at the lower address), a `d` or
`s` view its low bits; `stp`/`ldp` of `d` views save and restore the
callee-saved low halves, which enter as opaque symbols. A `ldr q` through
a span base under the slack guard (§7) reads sixteen element terms from
the index. A `simd.<Name>` parameter is its lanes `p[k]`, bound whole to
its `v` register; a vector result is read from `v0` one 64-bit half at a
time and each half decided as a scalar equality (the verdict names both
halves). On the Oak side a `simd.<Name>` type is an owned array of lanes
and each `simd.<op>_<shape>` call is the lane function `Oak.Simd` gives
it — `splat`, `load` (the span elements from the index, or an owned
array's elements at a literal offset), `add`/`sub`/`and`/`or`/`xor`/`min`/
`max`/`eq`/`subs`, `shr` and `prev` by a literal, `tbl`, `movemask`,
`any`/`all`, `ctz`/`popcount` — built with the same constructors the
machine side applies to the instructions, so the equality the decider
settles is between the instruction sequence and the operation sequence.
Two variable orders join the bit-level decision for this: each leaf's
bits in a block of its own (a lane-wise computation resolves a lane's
contribution as its bits are read; the mask sum of `shuffle` is 5,045
nodes there where the interleaved order exceeds the budget) and control
bits first (a table lookup at a symbolic index is a selection); the orders
run together and the first to decide stops the others, as the theorem
decider does. The asm unit now carries the program's functions, so a call
the native lowering expanded into its caller (§9.y) is inlined on the Oak
side as well. Verdicts on the SIMD corpus (`compiler/e2e_native_simd_test.go`):
`lanes_mask`, `logic`, `shuffle`, `words`, `bits`, `doubled_mask` proven,
`double_it_neon_abi` proven on both halves; on the UTF-8 kernel
(`benchmarks/native/utf8_valid.oak`): `special_cases` and `check_block`
proven on both halves of their vector results, `check_blocks` proven
(the same term on both sides), and the loop kernel `valid_with`
**proven** since the increments below: its three data-dependent loops
coupled inductively, every obligation the same term on both sides once
the machine's branch is settled by a case split. The lane functions are stated in Lean as
`Oak.NeonSemantics` (`spec/lean/Oak/NeonSemantics.lean`) and each is
proved to be the `Oak.Simd` operation the lowering uses it for:
`uqsub_eq_subSat`, `cmeq_eq_eqMask`, `add_eq_addWrap`, `ushr_eq_shr`,
`tbl_eq_tbl`, `ext_eq_prev` (`ext #(16-n)` is `prev n`),
`umaxv_ne_zero_iff` (`any`), `umaxv_cmeq_zero_iff` (`all`), and
`movemaskBytes_eq_movemask` (the `sshr #7`/`and`/`addv`/`orr` sequence is
`movemask 8`). The silicon differential (`asm/silicon_test.go`) runs the
vector instructions too — 160 bodies over `v0 = {a, a}`, `v1 = {b, a}`
built by `dup` and `ext`, each half of the result read back with `umov` —
and it found the first modeling bug before it shipped: a lane narrowed
from a wider register must be masked explicitly (`narrowLane`), where the
scalar `truncate` takes a parameter to be bounded by its declared width.
Arm's own text is in place for the grounding: `spec/sail/arm_primitives.sail`
carries the execute bodies of every vector instruction the backend emits
(`aarch64_vector.sail`, with the register operands as parameters and the
adaptations listed in the file), Sail generates their Lean, and
`spec/sail/lean/Bridge.lean` proves the lane-level identities against the
generated code — `Elem[]` reads the lane of the verifier's decomposition,
`Ones` is the all-ones lane, `UnsignedSatQ` of a lane difference is
`uqsub`, the `cmeq` test is `cmeq`, and the bitwise forms are the
operators — and the register-level theorems over the generated per-lane
loops: the loop `for e in [0:elements-1]` is a fold over the lane indices
(`forIn_laneRange_fold`), a lane written by `Elem[]` reads its write and
leaves the others (`aget_aset_same`, `aget_aset_other`), so `dup`, `add`,
`sub`, `cmeq` (register and zero forms), `umin`, `umax`, `uqsub`, `tbl`,
and `umaxv` compute the verifier's lane functions over the lanes of their
operands (`dup_lanes`, `add_lanes`, `cmeq_lanes`, `tbl_lanes`,
`umaxv_lane`, …); `ext #(8p)` reads lane for lane as `Oak.Neon.ext p`
(`ext_lanes`), `ushr #n` is the lane shift (`ushr_lanes`, through the
support library's iterated halving), `sshr #7` on a byte is the sign fill
of `movemask` (`sshr7_lane`, decided over the 256 bytes), and Arm's
recursive `Reduce` — stated by hand as `reduceAdd`, since Sail's Lean
backend cannot discharge its termination — sums eight bytes as `addv`'s
fold (`reduceAdd_eight_bytes`), and `cnt` is the population count of each
lane — Arm's `BitCount` loop as `Oak.Intrinsics.popcount` (`cnt_lanes`).
Every vector instruction the backend emits is bridged to Arm's text.

**Loops over the vector file (the loop increment, 2026-09-14).** The
loop kernel `valid_with` is three data-dependent loops in one body — a
sixty-four-byte step, a sixteen-byte step, and a byte copy into a
sixteen-byte frame array — and the sixth increment's loop machinery
refused it four ways in turn, each now admitted. The **recognized loop
shape** allows setup instructions between the header label and the first
exit test (the `sub wT, wL, #K` the conjunction `len(v) >= K && i <= len(v)
- K` lowers to) and several exit tests to one exit label: the continue
condition is that none is taken (`TestVerifyConjunctiveExitLoop`; the
wrong stride is still refuted on a concrete input). **Loop-carried state**
is now the vector file and the frame as well as the scalar registers: a
vector register written in the body gets fresh 64-bit symbols per half
(`loopK.vN.lo`, `.hi`), a frame slot written in the body a fresh symbol
per eight-byte slot (`loopK.s<addr>`), both with header values and
one-iteration values like the scalars (a narrow slot written in a loop
body stays outside the subset). The **body executor** runs frame spills
and reloads, frame-array element accesses through an address register,
vector `ldr q` loads and every vector instruction. A **frame store at a
data-dependent index** (`strb w9, [x11, w10, uxtw]`, the tail copy) names
no single slot: the store forgets every slot from the array's base up and
marks the region unknown, so a later load there — the `ldr q` of the tail
— reads an opaque symbol `frame#addr` (a load at a data-dependent index
stays outside the subset). On the Oak side the loop-carried locals may be
**aggregates** (the `simd.U8x16` locals, the `[16]u8` tail): they are
carried leaf by leaf with a fresh symbol per lane, and an index assignment
`tail[i] = ...` marks its root as assigned. The witness inputs gained the
span lengths 63, 64, 65, 80, 81: under the small ones alone every input of
a body that reads sixty-four bytes of tables before its loops traps at the
table loads and no witness decides anything. **Lane coupling.** The
coupling proof pairs the lanes of an aggregate local as a group: the
lanes `acc[0]`..`acc[n-1]` of one width w dividing 64 form slots of 64/w
consecutive lanes (`acc[0..7]`, `acc[8..15]`), and a slot is paired with a
64-bit machine symbol — a vector register half or a frame slot — through
`r = pack(x) + b`, lane k at bits k·w (`packLanes`), so that the
substitution carries the register half as the pack of the lanes' symbols
and one iteration must preserve the pack. The obligations are decided as
before, with two additions: **valuations first** — a valuation of the
symbols satisfying the premise under which the two sides differ refutes an
obligation before any diagram is built (span elements read the fixed
memory, as the witness layer does), and the same refutation prunes the
search as soon as a chosen pairing's register value mentions only coupled
symbols; slots are ordered by how many of the event's own variables their
one-iteration value mentions, so accumulators that fold the others in are
paired last and a wrong pairing is refuted at once — and the **variable
orders of `equalityBlasters`** (interleaved, per parameter, each leaf's
bits in a block, control bits first) race for every implication as they do
for a straight-line equality. A slot none of whose candidates survives its
own obligation fails the coupling before any search, and the search
itself is bounded (4,096 pairings). `TestVerifyVectorLoopCoupling`: a
vector accumulator `acc = or(acc, load(v, i))` over a data-dependent loop
is **proven** with `acc[0..7]↔v16.lo`, `acc[8..15]↔v16.hi`, `i↔r9`; `and`
for `orr` is refuted on a concrete input. **The reductions against zero.**
`any` lowers to `umaxv`, a sixteen-deep chain of `ite(l hi r, l, r)`,
whose diagram over sixteen free byte lanes exceeds the node budget even in
a straight-line body; the term constructor now applies
`Oak.NeonSemantics.umaxv_ne_zero_iff` and its dual: a max or min chain
compared with zero (`cmp #0` then `cset eq/ne`) distributes into per-lane
zero tests — `max(l, r) ≠ 0 ⇔ l ≠ 0 ∨ r ≠ 0`, `min(l, r) ≠ 0 ⇔ l ≠ 0 ∧ r
≠ 0` — looking through the masks that keep every significant bit (a
zero-extension, the lane's extraction). `any` over free lanes is proven
(`TestVerifyVectorAnyFreeLanes`; `uminv` for `umaxv` refuted). Result on
the kernel: `valid_with` agrees with its Oak body on 76 concrete inputs
and is **evidence**, now for a stated reason — the tail array `tail[0..7]`
has no machine image, since the byte copy into it stores at a
data-dependent index and the frame region is opaque after it (a frame
array as a loop-carried memory is the next step), and the `error`
accumulator's one-iteration obligation is the `check_blocks` composition,
beyond the node budget.

**The frame array as a loop-carried memory (2026-09-14).** The tail copy
stores at a data-dependent index (`strb wV, [xB, wI, uxtw]`), and the
checker admits it only under a dominating guard `cmp wI, #K; b.hs <trap>`
(§9). The executor now keeps that bound: the path falling through the
guard records `wI < K` (`symbolicState.bounds`, cleared when the register
is written), and a store at the register's index then names the K
possible slots, each taking `ite(index = e, value, old)` in place — a
byte inside a wider slot as a bit-field replace, so the slot keeps its
width and the frame keeps its shape. The loop summary finds the slots
such a store reaches by running the body once on the fresh register
state before the slots' symbols exist (a body with inner loops or calls
is not probed), and carries each changed slot at its width; the coupling
pairs the array's lanes singly with byte slots, or packed when the
machine holds the array as words (`TestVerifyFrameArrayLoop`: a
sixteen-byte tail copy proven under both layouts, the store at a fixed
index refuted). **The search, conflict-directed.** With sixteen tail
slots between an accumulator and the register it was wrongly paired
with, chronological backtracking re-enumerated the tail on every
failure; the search now returns the depths a refutation depended on —
the slots owning the symbols the obligation mentions, and the slots
holding the symbols a level could not choose — and a level not among
them passes the failure up untried. An obligation the bit level cannot
decide within its budget ends the search: no other pairing shrinks it.
The valuations try, for every comparison of a symbol with a constant in
an obligation, the symbol at that constant and its neighbors (an index
selecting a lane), then the small, boundary, and random values. On the
kernel every loop variable of the three loops is now coupled — `off`,
`error`, `prev_input`, `prev_incomplete` to their registers, `i` and the
sixteen `tail` bytes to theirs — in seventeen seconds, and the one
obligation left is `error`'s: one iteration of the sixty-four-byte loop
is the `check_blocks` composition, whose decision exceeds the node budget
as it does straight-line. That was the state before the increment that
follows.

**The kernel proven (2026-09-14).** Measuring rather than guessing at the
budget settled what the diagrams can and cannot do. Every "bit-level"
proof of the kernel's straight-line helpers — `special_cases`,
`check_block`, the four-block `check_blocks` — was in fact **structural**:
the two sides lower to the same term (`equalTerms`, "the same term on
both sides"), and no diagram was ever built for them; the diagram of one
`check_block` lane over symbolic tables is already near the budget and the
composition's is beyond it at 16M nodes as at 2M. So the route to the
loop kernel is to make the two sides *spell* one term wherever they mean
one, and to decide the rest by algebra rather than by diagram. Four
spellings were unified. A **w view reads back the 32-bit term its write
zero-extended**, not a mask over the extension, so the machine's element
index `off + 16 + k` is the Oak side's and the two reads of an element
share one abstraction — with independent abstractions the equality had
to go through the quadratic consistency constraint, which is what put
`check_blocks` through span loads over the budget. A **lane read out of a
recognizable pack** — a vector spilled and reloaded, a frame word
assembled from byte slots, a loop-carried register the substitution made
the pack of its Oak lanes — is the lane term itself (`unpackLane`,
`extractedLane`, applied at extraction and at substitution), not a mask
over a shift over the pack. **Bitwise vector operations** run at the
finer of their operands' lane widths, and byte by byte over two words
that are packs of nothing recognizable (two loop symbols), since bitwise
operations distribute over lanes: the machine then spells `error |
check_blocks` lane by lane as the Oak side does, where a word-level or
over two packs spelled a different term. And a coupling whose header
values are one term is an **equality** (b = 0) rather than `b = P − P`.
Two decisions were added beside the diagrams. A **case split** on the
condition of the largest branch (`splitDecide`, nested at most twice):
each case is decided under its condition as a premise, and under a
premise the terms are **pruned** first (`pruneUnder`: a branch whose
condition the premise implies or refutes, decided on a small diagram of
the premise and the condition, becomes the arm the premise selects — the
steps of a table lookup, `index = k`, excepted) and the diagrams, when
still needed, prune the same branches as they blast (`blaster.assume`).
The kernel's `any(step & 0x80) ? … | …` is one machine branch over the
merged path values against sixteen Oak lane branches on the same
condition; settled by the split, the arms are the same term on both
sides. Second, a result that is a **reduction over lanes** — `!any(error
| prev_incomplete)`, the Oak `or` of `lane ≠ 0` tests against the
machine's `umaxv`, `cmp #0`, `cset`, `eor #1` — is decided by its lane
tests (`equalReductions`): the same negation and the same lanes, each the
same term on both sides, whatever order or width the reduction was
spelled in. With these, `valid_with` is **proven**: three data-dependent
loops coupled inductively (`off`, `error`, `prev_input`,
`prev_incomplete`, `i`, the sixteen `tail` bytes to their registers and
slots), every continue condition, one-iteration obligation, and the
result after the loops decided — in eight seconds, no diagram of a
`check_block` lane among them. The RV64 `fact` loop's 64-bit product,
witnessed before, is proven the same way (the same term once the w view
reads back what it wrote). `TestE2ENativeSimdKernelVerdicts` asserts the
kernel's proof; the trace (`OAK_VERIFY_TRACE`) prints each case split,
the pruned sizes, and whether the sides became one term.

**The floating-point forms (2026-09-14).** `spec/sail/arm_primitives.sail`
gains Arm's execute bodies for `fadd`/`faddp`, `fsub`, `fmul`, `fmla`/
`fmls`, `fmin`/`fmax` (the 1985 forms), `fminnm`/`fmaxnm` (2008),
`fsqrt`, and `fneg`/`fabs`, with the register operands and `FPCR` as
parameters, and Arm's `FPNeg`/`FPAbs` as written. The IEEE operations
themselves — `FPAdd`, `FPSub`, `FPMul`, `FPMulAdd`, `FPMin`, `FPMax`,
`FPMinNum`, `FPMaxNum`, `FPSqrt`, defined in Arm's text over reals — are
declared without bodies and mapped by Sail's `lean` extern binding to
uninterpreted constants of the same names in the support library
(`spec/sail/lean-sail-4.33.patch` carries them): exactly the standing the
verifier gives them (`asm/floats_ops.go`, `Oak.Uninterpreted`). The
bridge then proves, against the generated code, that each instruction
applies its operation lane for lane — `fadd_lanes`, `fsub_lanes`,
`fmul_lanes`, `fmla_lanes` (`FPMulAdd` of the accumulator's lane and the
multiplicands', the verifier's `fma`), `fmls_lanes` (the first
multiplicand negated), `fmin_lanes`/`fmax_lanes`, `fminnm_lanes`/
`fmaxnm_lanes`, `fsqrt_lanes`, `fneg_lanes`/`fabs_lanes`, and
`faddp_lanes` (lane `j` is `FPAdd` of lanes `2j` and `2j+1` of the
concatenation `operand2 @ operand1`, the adjacent-pair shape the
verifier's `faddp` builds and the `reduce_add` tree is made of) — and
that `FPNeg` flips the sign bit and `FPAbs` clears it at both widths
(`FPNeg_32`, `FPNeg_64`, `FPAbs_32`, `FPAbs_64`, decided). So the chain
for a float unit is: the verifier proves the unit equal to its Oak body
up to the operation terms; the bridge proves Arm's instruction text
applies the same operations to the same lanes; and the identification of
`Sail.FPAdd` with the verifier's `fadd` — IEEE addition under Arm's NaN
rules — is what the silicon differential checks on the host core and
`Oak.FloatOps` models at the bit level. The loop increment's remainder
above was closed by the kernel's proof.

**Floating point as uninterpreted operations (eighth increment,
2026-09-14; `asm/floats_ops.go`, `asm/verify_float.go`).** Until this
increment a unit touching the floating-point file was *trusted*: IEEE
addition is not a bit operation the decider can blast. It need not be.
The unit and its body must apply the *same* operations to the *same*
operands in the *same* order to agree bit for bit on every input, and that
is a property the bit level can decide with the operations left
uninterpreted. Each of `fadd`/`fsub`/`fmul`/`fdiv`, `fsqrt`, `fma`, the
number-preferring `fminnm`/`fmaxnm`, the conversions (`fcvt` between the
widths, `scvtf`/`ucvtf` from an integer of its width, `fcvtzs`/`fcvtzu`
to one), and the NaN a `min`/`max` yields on a NaN operand (`fnan`, some
NaN whose payload the platform chooses — one function of the operands on
both sides, since no law may rely on it) is a term of its own kind at its
width, built by the same constructor on both sides: on the Oak side from
`a + b`, `fma(a, b, c)`, `sqrt(x)`, `min_num`, `f64(x)`, `u32(x)`, and the
simd float operations (`add_f32x4` … `fma_f64x2`, `sqrt`/`neg`/`abs`,
`insert`/`extract` at a literal lane, `reduce_add` as the pairwise tree
`(l0 + l1) + (l2 + l3)` whose grouping is the semantics); on the machine
side from the scalar instructions over `s`/`d` views (`fmadd`/`fmsub`/
`fnmadd`/`fnmsub` as one `fma` over sign-adjusted operands, `fmov` with a
float immediate as the literal's bits, `fcmp` leaving the IEEE comparison
as the flags and every condition code reading them as the predicate the
compilers use it for — `mi` is `<`, `ls` is `<=`, `gt`, `ge`, `eq`, `ne`,
`hi`/`lt`/`le`/`hs` the unordered-inclusive forms — `fcsel` as the
select) and the lane instructions over `2s`/`4s`/`2d` (`fmla`/`fmls` as
`fma` into the accumulator lane, `faddp` as the adjacent-pair sums of both
sources, `dup`/`mov` of a lane, `mov vD.s[i], …` as one lane replaced).
The sign operations, `min`/`max` (754-2019 minimum/maximum, `fmin`/`fmax`),
the comparisons, and the classifiers stay bit operations as before. The
witness evaluator computes each operation as IEEE arithmetic (Go's
float32/float64, an exactly rounded 32-bit fma with subnormals at their
own grid, and NaN operands under Arm's `FPProcessNaNs`: a signaling NaN
wins over a quiet one, earlier operands over later, the addend of a fused
multiply-add first, the result quieted — written out rather than left to
Go's `+`, whose operand order the compiler may swap), so a disagreement
on a witness is a definite mismatch under the real semantics; the silicon
differential (`asm/silicon_test.go`) now runs the float instructions too
— the scalar and lane arithmetic, the fused forms, `fmin`/`fmax`/
`fminnm`/`fmaxnm`, `faddp`, the conversions, `fcmp`/`fcsel` under every
condition code — over the same NaN-, denormal-, and boundary-laden
inputs as the integer ones, and the model agrees with the core bit for
bit (it found two modeling errors before they shipped: the NaN operand
order and the subnormal rounding of the 32-bit fma); the bit-level
decision abstracts each application as a fresh block shared by every
application of the same operation to the same operand bits, under
Ackermann's functional consistency (`asm/blast.go`, the select
machinery). A proof therefore says *equal up to the IEEE operations
themselves* — `Oak.Uninterpreted.ackermann_sound`: terms equal under
every consistent table of application values are equal under any
interpretation, IEEE's included — whose bit-level model is
`Oak.FloatOps` and whose agreement with the hardware the differentials
check. No algebraic law is assumed (`no_commutativity_assumed`): `a - x`
against `fsub d0, d1, d0` is a mismatch, `a * x + y` against `fmadd` is a
mismatch (the backends never contract), the left-fold reduction against
`reduce_add` is a mismatch, `min` against `fminnm` is a mismatch (a NaN
operand suppressed rather than propagated); `fma` against `fmadd`, the
two-instruction `fmul`/`fadd` against `a * x + y`, `f32(n)` against
`ucvtf`, `sqrt(abs(-x))`, `a < b ? a | b` through `fcmp`/`fcsel`, the
pairwise dot product `reduce_add(mul(a, b))` against `fmul`/`faddp`/
`faddp`, and `fma_f32x4` against `fmla` are proven
(`asm/verify_float_test.go`). A call to a program function with `f32`/
`f64` parameters or result is summarized like an integer one (the
twenty-ninth increment's call summary): the arguments are read from the
low lanes of `v0`–`v7` (`fa0`–`fa7` on RV64) in declaration order, the
callee's parameters are floats of the callee's lowering, its body lowers
at its return width, and the result lands in the low lane of `v0`
(`fa0`) with the upper bits of the half fresh — AAPCS64 leaves them
unspecified; `Oak.Uninterpreted.float_result_low_lane`: the `s` view
reads the result whatever they are. Every summarized call, a unit
callee's included, forgets the caller-saved vector and float registers
(`v0`–`v7`, `v16`–`v31`; `ft0`–`ft11`, `fa0`–`fa7`), which the summary
had left standing. On the Oak side a call returning a float is a float
of the callee's return width in both lowerings — `-diff(a, b)` flips the
sign bit, `sum(a, b) < 0.0` compares at the callee's width — and a
prefix operand carries its contract (`f64_round_i64(-n)` converts a
signed 64-bit source); `-diff(a, b)` against `bl diff`/`fneg` is proven
naming the callee, `-diff(b, a)` and the un-negated call are mismatches,
on both lanes (`asm/float_call_test.go`; `spec/oak/floats.oak`
`neg_of_call`, `call_is_its_body`, `from_signed_of_neg`). Floats in loop
bodies: an f32 span's element loads through the `s` view (`ldr sN, [xB,
wI, uxtw #2]`, the element into the low lane, the rest of the register
zero as every scalar write leaves it) and an f32/f64 element through
`flw`/`fld` at a span element address on RV64 (`fsw`/`fsd` store one,
outside a loop body; inside, a store keeps the loop trusted like every
storing loop); the RV64 lane's floating-point registers the body writes
are loop-carried variables (`f8`, one symbol at the pattern's width, as
the `v8.lo`/`v8.hi` halves are), and the coupling pairs a 32-bit float
local with a 64-bit `v` half or `f` register zero-extended
(`Oak.RiscV.zext_coupling_preserved`: a body reading the register at 32
bits and writing back zero-extended preserves `r = zext x`). With it the
native `total` — the accumulator in `d8`/`fs0`, the counter in
`w2`/`s4` — is proven on both lanes; `acc - v[i]` against `fadd` is a
mismatch and the swapped `v[i] + acc` evidence only (another
application of `fadd`, which the witnesses cannot tell apart:
`asm/float_loop_test.go`). What stays trusted: the rounding intrinsics
(`floor`, `ceil`, `trunc`, `round`), a float converted to `u8` or `u16`
(the narrow saturation), and a loop body that stores (`fill_f64`).

**Vector stores as memories (2026-09-14; `asm/effects.go`,
`asm/verify_simd.go`).** The twenty-eighth increment's write log takes
vector stores: a `str qN` (or `dN`) through a span base — indexed,
through an element address, or at an offset — appends one write per lane
at consecutive indices, and so does `vse8.v`/`vse16.v`/`vse32.v`/
`vse64.v` through a span element address on RV64 under the fixed
configuration; on the Oak side `simd.store_<shape>(v, i, x)` in
statement position appends the lanes of `x` at `i .. i+lanes-1` under the
path condition (or writes an owned array local's elements at a literal
offset), and a vector load on either side consults the log first, so a
load after a vector store reads the stored lanes (`Oak.Simd.store_lane`:
element `off + k` of a store is lane `k`). Two logs that are the same
sequence of unconditional writes at the same indices decide as one
equality per write (`alignedWrites`) — a sixteen-lane store is sixteen
small decisions rather than one sixteen-way conditional at the fresh
index, which exceeded the budget — and otherwise the memories compare at
the fresh index as before. With it the `simd.store` units of the native
corpora are proven on both lanes (`combine_store`, `unary`), the AArch64
bridge's "`simd.store`" remainder has its verifier half, and the tally of
the native simd corpora is: every function proven (`asm/effects_vector_test.go`:
a byte increment stored back proven, the wrong increment refuted, a store
forwarded to a reload, a float negation stored through an element
address proven and `fabs` for `fneg` refuted, on both lanes).

**The RV64 lane's floating-point and vector files (ninth increment,
2026-09-14; `asm/rv64_verify_float.go`, `asm/rv64_verify_vector.go`).**
The same terms through the RV64 mnemonics, so an RV64 unit and a NEON
unit of one Oak body decide against the same lane terms. The F/D
registers are a file of their own in the executor (`fregs`), each holding
a pattern at the width of the instruction that wrote it; f32/f64
parameters bind in `fa0`–`fa7` and an f32/f64 result is read from `fa0`
(LP64D), and a summarized callee's float arguments and result travel the
same way (`asm/float_call_test.go`). `fadd`/`fsub`/`fmul`/`fdiv`/`fsqrt .s/.d` under the dynamic
rounding mode (a static mode leaves the unit trusted), `fmadd`/`fmsub`/
`fnmsub`/`fnmadd` as one `fma` over sign-adjusted operands, `fmin`/`fmax`
as `fminnm`/`fmaxnm` — RISC-V's are IEEE minimumNumber/maximumNumber, so
they match Oak's `min_num`/`max_num` and mismatch its `min`/`max`, which
the NEON `fmin`/`fmax` match — the sign injections `fsgnj`/`fsgnjn`/
`fsgnjx` as the bit operations (`fneg`, `fabs`, `copysign`), `feq`/`flt`/
`fle` into the integer file as the IEEE predicates, `fmv.x.w` (sign-
extended) and the other bit moves, `fcvt` between the widths and from
the integer file at its width and signedness, and to the integer file
under `rtz` (the contract converts toward zero; without `rtz` the unit
stays trusted); `flw`/`fld`/`fsw`/`fsd` through the frame or, at a span
element address, the element at the access width. The vector
file is modeled under a *fixed configuration*: `vsetivli zero, K, eS, m1`
with `K·S ≤ 128`, under which `vl = K` on every VLEN ≥ 128
(`Oak.RiscV.fixed_config_vl`, `fixed_lanes_fit`) and the instructions are
the lane functions of the NEON model over `K` lanes of `S` bits —
`vle`/`vse` at the SEW through a span element address (the guarded-index
and slack idioms of §9) or a register-held frame address (`addi rD, sp,
imm`, two 8-byte slots, whole-register spills), `vadd`/`vsub`/`vand`/
`vor`/`vxor`/`vminu`/`vmaxu`/`vssubu .vv`, `vsrl.vx`, `vmv.v.x`, `vmv.x.s`
(sign-extended), the comparisons `vmseq.vv`/`vmsne.vx`/`vmslt.vx`/
`vmsltu.vx` into a mask register holding one bit per lane in its low
bits, `vmerge.vvm` by those bits, `vcpop.m` as the population count of
the low `K` bits, `vredsum.vs` as the sum and `vfredosum.vs` as the
ordered float sum from `vs1[0]`, `vrgather.vv` as the byte-table lookup
for an index below sixteen, `vslidedown.vi`/`vslideup.vi`, and the float
forms `vfadd`/`vfsub`/`vfmul .vv`, `vfmacc.vv` as `fma` into the
accumulator, `vfcvt.f.xu.v`, `vfmv.v.f`/`vfmv.f.s`. What the ISA leaves
unspecified is a fresh unknown of the verification: the lanes past `vl`
after a write under `K·S < 128`, a mask register's bits past `vl`, a
reduction's tail lanes, the elements a gather or a slide reads past `vl`
(they lie in the tail of a wider VLEN's register). So the native
lowering's `movemask`, which reads the mask through element 0 at `e32`
and then clears the bits above the lane count, is proven, and the same
read without the clearing is a mismatch naming the tail; the masked
gather of `tbl` is proven and the unmasked one a mismatch. A register
AVL (`vsetvli`), a configuration whose `vl` depends on VLEN, a masked
form (`v0.t`), and the widening forms keep the unit trusted. Verdicts
(`asm/rv64_verify_float_test.go`, `asm/rv64_verify_vector_test.go`):
`fma` against `fmadd.d` proven and `a*x + y` a mismatch; `min_num`
against `fmin.s` proven and `min` a mismatch; `sqrt(abs(-x))` through
the sign injections; `copysign` against `fsgnj.d`; `a < b` against
`flt.d`; `f32(n)` against `fcvt.s.wu` proven and `fcvt.s.w` a mismatch;
`u64(x)` against `fcvt.lu.d rtz`; a frame round trip; the zero mask
through the slack idiom, `any` through `vcpop.m`, the masked gather, the
slides for `prev`, a whole-register spill, and the ordered f32 dot product
`(((0 + a₀b₀) + a₁b₁) + a₂b₂) + a₃b₃` against `vfmul`/`vfredosum` proven,
with the pairwise grouping a mismatch. **The float vectors of the native
RV64 lane (2026-09-14).** The forms the eleventh native increment emits
join the model: `vfdiv.vv`, `vfsqrt.v`, `vfsgnjn.vv`/`vfsgnjx.vv` (the
sign injections as bit operations: `neg`/`abs`), `vmfne.vv` (the IEEE
`!=` into a mask), `vid.v` (lane `i` holds `i`), `vmseq.vx`,
`vfmerge.vfm` (`v0[i] ? fs1 : vs2[i]`), and `vfmin.vv`/`vfmax.vv`. Three
refinements make the lane's sequences decide. *The number-preferring
minimum and maximum* (`min_num`/`max_num`, Arm's `fminnm`/`fmaxnm`,
RISC-V's `fmin`/`fmax`, RVV's `vfmin`/`vfmax`) are one hybrid term on
every side (`floatMinMaxNum`): on numbers the same bit-level order chain
as `minimum`/`maximum` (they agree there, `-0.0` below `+0.0`), on a NaN
operand the `fminnm`/`fmaxnm` operation term — so the RVV lowering of
`min`, which is `vfmin` with the NaN operands merged back over the result
through `vmfne`/`vmerge`, is proven equal to Oak's `min` on numbers
exactly and on NaNs up to the next point. *A float result is decided up
to its NaN payload* (`floatCanonicalNaN`, applied to both sides of an
`f32`/`f64` result and to every lane of a float vector result): the
payload is the platform's (docs/spec/20-types.md §11.3.5, no law may
rely on it), so a unit that yields one operand's NaN where the body's
`min` yields the sum's NaN agrees; the NaN a `min`/`max` yields carries
its exponent and quiet bits forced (`floatSomeNaN`) so the decider knows
it is a NaN whatever the payload, and the witness value is unchanged.
*An operation over operands whose every bit is known folds to its IEEE
value when the term is built* (`floatTerm`, by a known-bits analysis over
the term DAG — constants; and, or, xor; shifts by a constant; the width
masks; a conditional under a known selector bit; `Oak.KnownBits` proves
each transfer sound — so the mask bits the tail unknowns cannot reach
fold), as the constructor folds constant applications — without it a
folded constant on the Oak side met an abstracted application on the
machine side. The fold is syntactic rather than the diagram's, so the
theorem lowering written in Oak makes the same fold on the same terms and
the solver written in Oak blasts the same applications (kind 6 of the
problem table, `docs/spec/125-verification.md` §7); the blaster itself
folds nothing. The callee-saved float registers
`fs0`–`fs11` carry the caller's pattern on entry (`entry.fN`), so a
prologue's `fsd`/`fld` pair round-trips. With these, every function of
the native RV64 float and integer simd corpora that returns a value is
**proven** (`compiler/e2e_native_rv64_float_simd_test.go`,
`compiler/e2e_native_rv64_simd_test.go` assert it: `arith`, `dot`,
`pairwise`, `minmax`, `doubles`, `words_view`, and the integer
`lanes_mask`, `logic`, `shuffle`, `words`, …; the two units that store
through a span stay trusted), as every NEON float unit is
(`compiler/e2e_native_float_simd_test.go`). The lowering's shapes are
decided in `asm/rv64_verify_vector_test.go`: the min sequence proven and
bare `vfmin` a mismatch; div/sqrt/abs/neg with a slid extract; the
vid/vmseq/vfmerge insert; the pairwise reduce through slides proven and
`vfredosum`'s fold a mismatch.

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
with a write to the register or a call — except in a callee-saved register
`x19`–`x28`, which the callee preserves, so a span bound over a frame
array (`span(&buf)`, parked in a callee-saved pair) stays addressable after
a `bl`; its element guard is the constant `cmp wI, #N` of this idiom, not a
compare against the length register — flows through the label fixpoint
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
**Eleventh increment — arrays of records.** `pool: [N]Rec` as a local
(zero-filled, or from a literal of record values) and as a record field,
with C's stride (`sizeof(Rec)`, the layout the C backend asserts). A
literal index is a static place; a computed `pool[i]` is a record place
addressed through a register, produced by the element idiom the checker
now admits: the array's frame address, the constant guard `cmp wI, #N;
b.hs trap`, then `add xE, xB, wI, uxtw #s` for a power-of-two stride up to
16 bytes (the extended-register form's limit) or `movz wK, #stride; umaddl
xE, wI, wK, xB` otherwise. The checker records `xE` as a writable region of
exactly one element — `add xE, xB, wI, uxtw #s` or `umaddl` over a frame
address with the index guarded below a constant `K` and `base + K·stride`
inside the declared frame (`movz`/`mov wK, #c` records the stride as a
constant fact, dying with a write, at labels, and at calls) — and narrows
it through `add xD, xE, #imm` to a field's tail; memory through a region
now also takes the indexed form `[xR, wJ, uxtw #t]` under a constant guard
whose `K'·2^t` fits the region (an array field inside the element). Every
place-taking path — field loads and stores, exact-size copies, chunk loads
for calls (a register-addressed element is copied into an aligned frame
temp first, so its last chunk never reads past the element), results,
match scrutinees, payload bindings — takes the base register into
account. Computed indexing into an array of records that itself lies
inside a computed element stays with the C backend
(`TestCheckerElementRegions`: three accepted shapes, six refusals).
Executed (`TestE2ENativeRecordArrays`): a link pool of 8-byte nodes walked
by index, a 12-byte record array updated in place through `umaddl` with an
element copied out and passed on, and a record array field inside a record
read and written by computed index — natively against the C backend and
the portable realization.
**Twelfth increment — spans and views of records.** `pool: []Node` and
`[*]Node` as parameters and locals, `view(&arr)`/`span(&arr)` over arrays
of records, and `subslice` over them (for power-of-two strides up to 16
bytes, the derived-span idiom's scale). An element `pool[i]` is a
register-addressed record place produced by the span element idiom: the
index guarded against the length register (`cmp wI, wL; b.hs trap`), then
`add xE, xB, wI, uxtw #s` or `movz wK, #stride; umaddl xE, wI, wK, xB` by
the record's stride; field reads, field stores, whole-element replacement,
and copies out follow, and a view's elements refuse stores. The checker
sizes a span of records from the composites table (the compiler adds
every span parameter's element record) and derives the element region
from a span base: `add`/`umaddl` over a span fact whose element size
equals the stride, with the index guarded below the span's length
register or below a constant the span's proven minimum length covers,
makes `xE` a one-element region writable iff the span is a `[*]T`
(`TestCheckerRecordSpans`: three accepted shapes, five refusals — a store
through a view, no guard, the wrong stride, a guard against an unrelated
register, a field past the element). The verifier never models a record
element as a scalar: spans of records leave a body trusted. Executed
(`TestE2ENativeRecordSpans`): a link pool passed as a view and walked by
index, a span of 12-byte records renumbered in place with an element
replaced whole and one copied out, and a subslice of a record view walked
by a leaf — natively against the C backend and the portable realization.
**Thirteenth increment — the verifier reaches aggregates.** On the
assembly side, frame slots tile: a store records its term at its width and
splits any older slot it partly covers into the untouched aligned pieces,
and a load reads back one slot, a sub-range of it (the low bytes of a
64-bit slot for a 32-bit reload, little-endian), or the exact concatenation
of adjacent pieces, zero- or sign-extending as its mnemonic says — so byte
and halfword element accesses over word-zeroed storage and word copies over
field stores resolve where they used to fail on a width mismatch (the
narrow-reload case in `TestVerifyFrameMemory` is now proven for the low
half and refuted for the high half). `add xN, sp, #imm` yields a frame
address term (`sp#A`), constant element and field offsets fold onto it, and
a load or store whose base resolves to a frame address reads or writes that
slot; a data-dependent index leaves the body trusted. A span base plus a
constant byte offset (a `subslice` with a constant start) is the element at
the shifted index. On the Oak side, locals may be aggregates — records and
tagged unions as field trees of leaf terms (the ADT's `u32` tag and one
payload per carrying variant), owned arrays as element lists — built from
typed literals, variants, array literals, copies, value-less arrays
(zero-filled, as both backends fill them), field and constant-index element
stores, and read through access chains; conditional arms merge aggregates
leaf-wise; a `match` over a tagged union whose tag is decided on the path
runs exactly its arm and binds the payload; a value-position `match` over a
scalar that does not fold becomes a chain of selects on equality ending in
its wildcard arm; unary minus wraps at the width. Aggregates across a
data-dependent loop, data-dependent indices, and matches over undecided
tags stay outside the subset (trusted), as do record and union parameters
and results, which the executor does not yet bind (their chunk terms and
leaf terms are the next increment's work). The declarations reach the
verifier through the function (`asm.Function.Records`/`ADTs`, set by the
compiler for native bodies and hand-written units alike). Proven now among
the executed suites: `manhattan` (a record local with conditional field
updates and unary minus), `copy_point` and `swap_in` (copies and
whole-record assignment), `name_len` (a literal match over a parameter),
beside the loop kernels proven before.
**Fourteenth increment — records and unions at the verifier's boundary.**
The composites table now carries the placed layout (`asm.Composite.Fields`:
scalar, nested, and array members with offsets; `Variants` with tag
values), filled by the native backend from the same layouts the C backend
asserts and passed to every function (nested types included). The executor
binds a record or union parameter's scalar leaves as parameters named by
access path (`p.x`, `r.a.y`, `h.buf[2]`, `s.tag`, `s.Circle`): a
chunk-passed argument's registers hold the chunks assembled from those
leaves at their byte offsets (a union payload selected by its tag — the
other variants' bytes are zero, which is also what constructed values now
hold, since `.Variant(…)` zero-fills its temp before storing tag and
payload), and a by-reference argument's loads assemble the leaves inside
the accessed bytes (padding zero; a load cutting through a leaf is outside
the subset). A one-chunk record or union result comes back in `x0` and is
compared over its fields (padding masked) against the Oak result aggregate
packed the same way; the Oak side binds those parameters as aggregates of
the same leaf terms, lowers aggregate results through blocks, Bool
conditionals (merged leaf-wise), and matches, and decides matches in value
and statement position as chains of selects on the tag or literal equality
(each arm on a copy of the locals, the wildcard — or, exhaustively, the
last arm — standing for the rest). A Bool parameter is the C enum, an int
holding 0 or 1 with every bit of the low word defined (the earlier model
of unspecified upper bits produced an impossible counterexample for
`pick`). Bool fields at the boundary, two-chunk and `x8`-area results, and
aggregates across data-dependent loops stay trusted. Proven now: `shift`,
`wide_sum` (a 24-byte record by reference), `pick` (a one-chunk result
chosen by a Bool), `small_total`, `sum_cell` (a 12-byte record in two
chunks), `classify` (a union built by nested conditionals and returned),
`tally` (a statement-position match over a union parameter); `area2` and
`score` agree on every witness (their products exceed the BDD budget).
Witness runs assign leaves like scalars.
**Fifteenth increment — generic instantiations.** A survey of the
examples under `-native` showed the dominant reason bodies stayed with the
C backend was generic instantiations (`Option[u32]`, `Result[u32, …]` — some
two hundred functions), so the compiler now specializes every instantiation
the type checker recorded (`ADTInstantiations`) into a monomorphic
declaration under its mangled name (`Option_u32`, `Result_u32_Bool`), the
template's variants with the type parameters substituted by the one
substitution authority (`typechecker.SubstituteTypeAST`), record templates
included (`Ring[u8, 4]`), and hands them to the native backend and the
verifier beside the declared types. A type application in a signature or a
local's type resolves to that name (`asm.TypeApplicationName`, the
typechecker's mangling: the base name and the argument atoms joined by
underscores), `.Some(v)` resolves through the checker's variant resolution,
and everything else — construction, matches, parameters, results, spans of
them — follows the tagged-union and record paths unchanged; the composites
table is keyed both by mangled name and by each signature type's own
spelling, which is what the checker and verifier look up. The verifier's
boundary model now takes Bool fields as 1-bit leaves whose zero-extension
is the field's whole word (the C enum holds 0 or 1), so `Result[u32, Bool]`
crosses. Element indices of type `u64` are admitted: the high word is
checked (`lsr x9, xI, #32; cbnz x9, trap` — an index of 2^32 or more is
past every span and array) and the low word walks the checker's 32-bit
index idiom. Hand-written `.oakasm` units see declared types only (they are
checked before type checking records instantiations). Executed
(`TestE2ENativeGenerics`): `Option[u32]` returned from a search over a byte
view and unwrapped, `Result[u32, Bool]` from a checked add and matched, a
wide index, and a wide index past 2^32 trapping in both realizations;
`unwrap_or`, `checked_add`, `value_of`, and `at_wide` proven.
**Sixteenth increment — constant globals, and the prover through the
backend.** The prover written in Oak (`prove/solver`, 125-verification.md
§7) is the first whole program held to this chapter's discipline: built
with `-native` (`OAK_SOLVER_NATIVE=1` for the binary `oak prove -solver
self` runs), every function the backend reaches is checked, verified
against its Oak body, and encoded by the Oak assembler, and the C build of
the same source is the oracle — the two binaries print identical rows over
the whole law corpus. The survey that started it: of the prover's 913
functions 595 stayed with the C backend, 409 of them because a constant
global (`T_PIPE: u32 = 17`) was not in the subset, and the build failed on
four functions the seam checker refused — real backend bugs the checker
found, exactly as §9 promised: a call spilled every live scratch register,
including ones allocated for an enclosing expression's result and not yet
written (`f(b) || (b >= 97 && …)`: a read of an uninitialized register),
and a function whose one arm placed its result in `x0` — the base of a span
parameter — before its other arm walked the span (the checker's span facts
flow in text order, so the write ended the span). Now: a typed scalar
top-level binding under the C backend's constant rule (90-backend.md §8a:
a constant initializer, never assigned, index-assigned, borrowed, or
addressed, outside any placed section, not a `c.const`) is folded by the
compiler through the interpreter in declaration order — the semantics the
C backend's own file-scope fold uses, so both realizations agree on every
value — and handed to the backend and the verifier alike
(`asm.Function.Constants`): the backend materializes the identifier as an
immediate at its declared type, the verifier reads it as that constant
(sign-extended to the context when the type is signed), so `scale: (x: u32)
-> u32 = x * STEP + LIMIT` is proven in linear normal form and `narrow: (b:
u8) -> u8 = b + SMALL` at its 8-bit contract; a written global stays a
mutable static and its readers stay with the C backend. A call spills
exactly the live scratch registers an instruction has written; a span
parameter is parked in callee-saved registers when the function returns a
value as well as when it calls; a unit function may end in a conditional or
match in statement position; and the zero fill of an owned array uses two
`str` where the offset leaves `stp`'s scaled 7-bit field (the encoder had
refused `off: 512 is outside -512..504` rather than truncate — the object
level catching what the checker's model does not). Both lanes take the
changes. After it, of the 954 functions of the prover and the library it
imports, 712 lower natively — 123 proven equal to their Oak bodies, 589
trusted with the reason (339 call, 195 have no integer result, 22 return a
record beyond one chunk) — and 242 stay with the C backend, for reasons the
next increments name: arguments beyond the eight registers (144 functions,
callers and callees), frames beyond 4080 bytes and expressions deeper than
the scratch registers (100 together), `c.Ptr` parameters and locals (44),
signed element indices (34), and record locals without an initializer
(34). Executed (`TestE2ENativeConstants`): the constants, a mutable
global's writer and readers left to C, and the three shapes the checker had
refused — natively against the C backend and the portable realization; and
the prover itself (`TestOakShellAgreesNative`), built natively, agrees
with the Go ladder on every law file exactly as its C build does. Measured,
as the performance note requires of anything that lands: the natively
built prover is slower than the C build — `lattice.oak` 9.2 s against
2.7 s, `mono.oak` 19.5 s against 9.0 s, `protocols.oak` 24.0 s against
3.3 s, the small files within a factor of two — which is the backend as it
stands (every value through a frame slot or a callee-saved home, every
element access guarded, no register allocation across expressions) beside
the C compiler at `-O1`. That gap is the work the types and the proofs are
for: the checker's dominating guards and the verifier's loop invariants
(`i ≤ len(v)`) already state when an access needs no guard, and a proof of
equality against the Oak body is what licenses removing one.
**Seventeenth increment — the accessor chains inlined, and reads under
one memory.** The natively built prover was profiled (`sample` on the
lattice file): half of its time was in one-line accessors — `state`,
`term_at`, `tword`, `tkind` — that the C compiler inlines and the native
backend called, each call paying a prologue, a whole-record copy of its
by-reference parameter, and a guard. The source-level inliner
(90-backend.md §9) had not reached them: its candidates and callers were
block-bodied functions, and the accessors are expression-bodied and call
one another. It now takes an expression body as the one-statement block it
denotes and runs in rounds, so the chains flatten; the remaining calls are
the positions the pass refuses on purpose (loop conditions, short-circuit
operands, value-position arms). Measured on the binaries themselves — not
through `oak prove`, whose wall time includes the law file's own checking
and, on a first run, the prover's build — the native prover on
`lattice.oak` went from 8.1 s to 3.4 s, `protocols.oak` from 0.82 s to
0.29 s, `effects.oak` 2.45 s to 2.06 s, `floats.oak` 7.3 s to 6.7 s, the
exhaustive files (`mono.oak` 15.3 s to 14.7 s, `extents.oak` 10.9 s to
10.4 s) within noise; the C build is unchanged throughout (it inlined them
already). Proven functions rose from 123 to 190 (the spliced bodies are
self-contained), fallbacks fell from 242 to 220. The inlined bodies also
found three holes in the verification stack, each now closed: **(1)** the
bit-level decision abstracted every span read at a distinct index as an
independent value — sound for a proof, but a differing bit under
independent values is no counterexample, and two inlined bodies were
rejected as mismatches whose reported values were equal; a read now
carries functional consistency (Ackermann's reduction, built only once a
bit differs: reads of one span at equal indices hold equal values, a read
at an index equal to a constant holds that element parameter), and the
Oak side splits a read over a conditional in its index (`v[x + (c ? a :
b)]` is `c ? v[x + a] : v[x + b]`, the machine's own branches), so both
bodies are proven; **(2)** the loop verifier's concrete witnesses compared
values on inputs where the body traps (a read past a length the input set
to zero) — the asm side's trap path and the Oak side's out-of-range read
now both mark the input as decided by neither; **(3)** a local view of an
owned array indexed directly (`whole: []u32 = view(&buf); whole[2]`,
which inlining a helper produced) addressed the frame through the parked
pair, whose base register carries a frame-address fact the checker
forgets at the first call — the element now goes through the array's own
idiom. The prover binary cache (`oaksolver.go`) is keyed on the compiler
executable as well as the sources, since a compiler change yields a
different binary from the same files (a stale one was measured once).
**Eighteenth increment — by-reference record parameters read in place.**
The next profile put the BDD engine's own functions at the top — `apply`,
`cache_get`, `mk` — every one taking the 60-byte `Layout` by reference and
copying it into its frame at entry (eight loads and eight stores) for the
one or two fields it reads, and every call passing it on copying it again
into a fresh temp. A by-reference parameter the body never assigns,
never writes a path under, never borrows or addresses, and that carries
no array field, is now read where it lies: its address parks in a
callee-saved register in the prologue (`mov x19, x0`; the checker's
read-only region follows the `mov`), its fields load through
`[x19, #off]`, and a callee taking the same type by reference receives
the address itself (a callee that writes its parameter copies it at entry
as before, so the memory nothing writes stays the caller's for the whole
call; the referenced storage is always a caller's temp or local, never an
array element, since a register-addressed element is copied into a temp
before its address is taken). Measured on the binaries: `lattice.oak`
3.06 s to 2.77 s, `extents.oak` 10.6 s to 9.2 s, `floats.oak` 6.4 s to
5.8 s, `mono.oak` 14.8 s to 13.5 s, `effects.oak` 2.5 s to 2.1 s; the
frames shrink, and twelve more functions fit the limits (fallbacks 220
to 208, 746 of 954 lowered). Executed (`TestE2ENativeRecordInPlace`): a
leaf over the parameter's fields (proven), a caller passing it on twice,
a writer working on its own copy while the caller's record is unchanged,
and a field read after a call that passed the record on — natively
against the C backend and the portable realization. The native prover
now runs at 1.6–1.9 times the C build (`lattice.oak` 2.8 s against
1.5 s, `mono.oak` 13.5 s against 8.3 s, `extents.oak` 9.2 s against
5.4 s); what remains is the operand-stack lowering itself — a variable
moved into a scratch register before every operation and back after,
constants materialized instead of used as immediates, every element
access guarded — which the next increments take in that order.
**Nineteenth increment — operands where they lie.** The operand-stack
lowering moved every variable into a scratch register before an
operation and the result back after (`mov w9, w19; mov w10, w20; add w9,
w9, w10; mov w19, w9` for `a = a + b`), and materialized every constant
with `movz` before using it. Three rules take that out, each within the
same checker and verifier obligations: a binary operation or comparison
reads a variable that lives in a callee-saved register directly (`add
w9, w19, w20`), the result landing in the left operand's scratch when it
has one and a fresh one when the left is a variable, so the scratch
pressure never exceeds the moving form's; a constant right operand —
a literal, a widening of one, or a folded constant global — is the
instruction's immediate where its field admits it (a 12-bit unsigned for
`add`/`sub`/`cmp`, a bitmask immediate, asked of the encoder's own
`LogicalImmediate`, for `and`/`orr`/`eor`; a constant left operand of a
commutative operation moves right); and a value assigned or declared into
a register variable is written there by the instruction that produced it
(`add w19, w19, #1`), the trailing move dropped, when that instruction is
the last one emitted and reads only its sources (`movk` and the
exclusives stay). Measured on the binaries: `lattice.oak` 2.86 s to
2.49 s, `mono.oak` 13.0 s to 12.0 s, `effects.oak` 1.98 s to 1.74 s,
`floats.oak` 5.5 s to 5.2 s, `extents.oak` 8.7 s to 8.4 s — the native
prover at 1.5–1.7 times the C build; the remaining gap is the guard on
every element access and the frame traffic of functions past ten
variables, the next increments.
**Twentieth increment — leaves live in the argument registers.** The
dumps of the hot leaves (`cache_get`, `mk`) showed their prologues and
epilogues outweighing their bodies: every scalar parameter moved into a
callee-saved register at entry, up to five register pairs saved and
restored around a five-line body, and locals past the tenth in frame
slots. A function that makes no call now keeps each scalar parameter in
the argument register it arrived in, places its locals in the argument
registers no parameter occupies (x2–x7; x0 and x1 stay the result's, written
at the end) before taking a callee-saved one, moves nothing in the
prologue, and lists those registers as clobbers — the checker's obligation
for a written argument register, the result register excepted when the
result is an integer. Spans and by-reference records keep their parking.
Alongside: a constant-count shift reads its operand in place, a bounds
guard whose index is a register variable compares that register and
indexes by it (one move less per element access), and the short-circuit
operators retarget the operand's producing instruction into the result
instead of moving it. `cache_get` went from sixteen prologue and epilogue
instructions to six. Measured on the binaries, interleaved runs:
`lattice.oak` 2.45 s to 2.3 s, `mono.oak` 13.0 s to 12.0 s, the rest
within the noise of a busy machine. Executed (`TestE2ENativeLeaves`):
parameters assigned in place, a loop counter in an argument register, an
arm staging the result while another reads a parameter, a float result
beside integer homes, and a leaf with more locals than free argument
registers — natively against the C backend and the portable realization,
the scalar leaves proven.
**Twenty-first increment — the limit of one home per variable.** With
the registers of ended scopes returning to their pools (the recycling
above), 194 functions prove, the rows are unchanged, and the prover's
time is unchanged within noise — because the function every profile puts
first, `apply`, gains nothing from it: its six parameters, its two
accumulators, and the three locals its loop body declares at the top all
live across the body's calls, so after the ten callee-saved registers the
rest go to frame slots, and the loop reads and writes the frame 296 times
per iteration's worth of code. That is the boundary of a lowering that
gives every variable one home for the whole function. What the C compiler
does here is liveness: a variable not live across a call may sit in a
caller-saved register (x9–x15 beside the temporaries, the free argument
registers) and only what is live across a `bl` needs a callee-saved
register or a slot around that call. The next increment is that
allocator — per-variable live ranges over the statement tree, homes
chosen by whether a range crosses a call, the seam checker unchanged
(every register it admits today) and the verifier unchanged (registers by
value) — measured on `apply` first.
**Twenty-second increment — caller-saved homes around calls, and the
store forwarded.** The first step of that allocator, without liveness:
once the ten callee-saved registers are taken, a variable of a function
that calls lives in a caller-saved home — x16, x17, then the argument
registers no parameter occupies (x2–x7) — saved to its spill slot before
each call's argument registers are written and restored after the `bl`,
so a variable costs one store and one load per call instead of one memory
access per read or write. Alongside, a read that directly follows the
store of a slot variable (`t: u32 = f(x); t != NONE`) takes the value
from the register that stored it, since nothing has written that
register since; the register is then a defined value for the call spill,
which a first version had missed and the checker caught as a read after
`bl`. `apply`'s loop went from 316 frame accesses to 234. Measured on the
binaries, interleaved: `mono.oak` 11.8 s to 11.4 s, `floats.oak` 5.0 s to
4.7 s, `extents.oak` 8.0 s to 7.5 s, `effects.oak` 1.66 s to 1.59 s;
196 functions proven. Executed (`TestE2ENativeCallerHomes`): a body with
more variables than callee-saved registers, all read after calls, one
call's argument holding a call. What remains in `apply` is the variables
that outnumber even the caller-saved homes, and the spills of homes dead
at the call — both the liveness step: live ranges over the statement
tree, a home spilled at a call only when its variable is read after it.
**Twenty-third increment — liveness for the homes.** A pre-pass
(`nativegen/homes.go`) numbers the body in the order the lowering emits it
and records, per variable, its declaration and its last read, and per
`while` loop the positions its body spans. A read counts at its own
position — a call's argument is copied to a scratch register before the
call — except an operand the lowering reads in place: a variable named
directly under a binary operation, a comparison, or an element index is
read by the instruction that runs after the operation's other operands,
calls included, so it counts at that expression's end; a call counts after
its arguments; an index assignment's value counts before its index, as
`elementStore` evaluates them. A variable declared outside a loop and read
anywhere inside it is live across every call in the loop. From that: a
call saves a caller-saved home only when its variable is read afterward,
and a declaration whose variable never crosses a call takes a caller-saved
home before a callee-saved register (the crossing ones keep the
callee-saved ones, which cost nothing at a call). Two versions of the
numbering were wrong on the way and the seam checker refused both as a
read after `bl` — a read numbered at the same position as the call it
followed, and an index assignment numbered target-first while the
lowering evaluates the value first — which is the checker doing what the
chapter promised for the compiler's own output. This pass complements
the last-use release within a statement list (`liveness.go`); the two
are conservative in the same direction. `apply`'s loop: 234 frame
accesses to 226; 196 functions proven, rows unchanged; the timed runs
fell within the noise of a machine shared with other sessions' test
suites, so the structural count is the measurement here. Executed (`TestE2ENativeCallLiveness`): an in-place operand after
a call, an argument read before its call, a loop-carried variable, an
index assignment whose value calls, and a variable dead before the calls
that follow — natively against the C backend and the portable
realization.
**Twenty-fourth increment — the scratch registers the expressions never
reach.** The generator reserved x9–x15 for expression temporaries whatever
the body needed, and the four caller-saved homes left `apply` with most
of its variables in slots. A body is now lowered twice when its first
pass had to give a scalar variable a caller-saved home or a slot: the
first pass measures the most integer temporaries any expression held at
once (an overflow into x16, x17 or a callee-saved register counts as all
of them), and the second withholds the scratch registers above that peak
from the temporary pool, from x15 down, and hands them to the variables
as caller-saved homes — saved around calls like the others, already among
the clobbers. A second pass the lowering refuses (a variable in a
register needs no temporary a slot did, so it should not) keeps the
first's code. `apply`'s loop went from 226 frame accesses to 132.
Measured with the machine still shared with other sessions' suites (a
load average near twenty, so the ratios of interleaved runs are the
measurement, not the seconds): against the previous build `mono.oak` ran
10 percent faster, `extents.oak` 7, `effects.oak` 9, `lattice.oak` and
`floats.oak` within noise; and against the C build in the same runs the
native prover stands at 1.25–1.4 times its time (`mono.oak` 12.6 s to
14.0 s against 9.7 s to 10.7 s, `extents.oak` 8.4 s against 6.3 s,
`effects.oak` 1.85 s against 1.5 s), down from 2–5 times when this track
began.
**Twenty-fifth increment — the braces that kept the helpers calls.**
With the BDD engine's own functions at the top of every profile, the
question was why `cache_get` — five lines, a leaf — was still a call
while the C compiler inlines it. The inliner refuses a helper whose tail
holds a block where the C form would need a block in an expression, and
the tail `(…) ? { mem[e + u32(2)] } | { NONE }` is such a tail by its
braces alone: each arm is a block holding one expression. The pass now
reads an arm of that shape as the expression it holds (`c ? a | b`), so
`cache_get`, `cache_put`, `push_frame`, `deliver`, `mask64`,
`witness_count`, and the one-line conditionals throughout the prover
inline. `apply`'s loop keeps two calls (`mk`, `terminal_case`, both past
the twelve-line rule) where it had six, and its frame accesses fall from
132 to 112. Measured over three interleaved rounds on a shared machine
(load average near thirteen, so the ratios are the measurement): against
the previous build `mono.oak` 13.6 s to 11.1–13.1 s, `extents.oak` 8.5 s
to 7.1–7.9 s, `floats.oak` 4.9 s to 4.5 s, `lattice.oak` 3.1 s to 2.9 s,
`effects.oak` within noise; against the C build in the same runs the
native prover stands at 1.1–1.35 times its time (`mono.oak` 11.1–13.1 s
against 8.3–10 s, `extents.oak` 7.1–7.9 s against 6.2–7.1 s, `floats.oak`
4.2–4.9 s against 3.7–4.6 s). The rows are identical throughout.
**Twenty-sixth increment — arguments beyond the registers.** Of the
prover's 206 remaining fallbacks, 139 were one reason in four spellings:
a ninth integer argument, on the caller's or the callee's side. AAPCS64
puts it in the caller's outgoing area at the bottom of the caller's
frame — the callee's sp at entry — and one shared rule now lays that area
out (`asm/abi.go`, `LayoutArguments`): registers while an argument fits,
then every integer-class argument after the first that does not on the
stack, at increasing offsets; under the standard convention each rounded
to an 8-byte slot, under Apple's arm64 convention a fundamental type at
its natural size and alignment (composites stay 8-aligned) — the
convention the target's C compiler follows, since a native caller reaches
C-compiled callees and C-compiled callers reach native ones across the
same area. The callee's prologue loads each stack parameter above its
frame (a scalar at its width, then normalized; a span's base and length
into the callee-saved pair it would have been parked in; a by-reference
record's address into its parked register or a copy; a small record's
chunks into its slots) and binds it as `bind [sp, #off] = p`; the caller
reserves the largest area its calls need below its saved registers
(`outgoingArea`, from the callees' signatures under the same rule),
stores each stack argument at its offset at the value's own width, and
fills the registers as before. The seam checker recomputes the layout
from the signature under the function's declared convention and admits a
load from the incoming area only where a parameter lies — a stack span's
base word makes the destination a span base and its length word joins the
span's length registers, a by-reference record's word a read-only region
— refusing a store there, a read past the area, or a word no parameter
covers; the verifier leaves a body with stack parameters trusted (the
incoming area is not in its model yet). Alongside, a call no longer holds
every argument in a scratch register until the moves: a constant is
materialized into its place at the move, a variable whose home is no
argument register is read there at the move, and a stack-bound argument
is stored as soon as it is computed — which took `main`'s calls with nine
arguments out of "an expression deeper than the scratch registers", and
which the checker corrected once on the way (a variable so deferred is
read after every call among the later arguments, so the liveness
numbering counts it past the call). Fallbacks fell from 206 to 90, 864
of 954 functions now lowered, 197 proven; the prover's rows are identical,
and its compiled witness — a native `witness_all` reaching the C-compiled
`witness_run` with ten arguments across the packed area — exercises the
mixed convention on every law file. Executed
(`TestE2ENativeStackArgs`): nine and twelve scalars of mixed widths, a
view whose pair lands on the stack and is walked in a loop, a small
record's chunk and a large record's reference on the stack, and a native
caller reaching a C-compiled callee with two stack arguments — natively
against the C backend and the portable realization.
**Twenty-seventh increment — value-less record locals.** A record local
declared without an initializer (`out: Bits`, then filled field by field
— the shape of every bit-vector helper in the BDD engine's blaster) was
left to the C backend so that no semantics would be invented natively.
None need be: 90-backend.md §6 has the C emitter initialize such storage
with `{0}` and the interpreter give it its zero value, so the native
lowering zero-fills the local's slots whole, as it does an owned array's.
Seventeen functions follow (fallbacks 90 to 75, 879 of 954 lowered);
`TestE2ENativeZeroRecord` reads a field of each width before any write
and after. **What the 75 that remain are.** Twenty-nine take or hold a
`c.Ptr` and three call foreign code: the prover's I/O shell — `read_file`
over `c_open`/`c_read`, the buffers `c.own`ed and `c.disown`ed inside
`unsafe`, the environment and spawn helpers of the witness — whose native
lowering would be a foreign-call and custody subset (extern symbols the
checker admits as call targets, `Buffer[T]` as a span with a custody
state, `c.cstr` and `c.span_of` as the address arithmetic they are) and
whose verification value is nil, since bodies that call foreign code are
trusted by construction. Fourteen exhaust the callee-saved registers with
spans (five or more span parameters and locals, each a parked pair, in
the exploration and LRAT functions): the checker's span facts live on
registers and die at a call, so a span cannot spill around calls the way
a variable does without a checker rule for reloading a fact from a known
slot. Sixteen are the deepest expressions (the `*_layout` functions'
record literals, `px_lex`): more temporaries live at once than x9–x15
and the overflow registers hold. The compute paths — the decider, the
lowering, the exploration, the projections — are native; what stays in C
is the shell around them.
**Twenty-eighth increment — memory effects through spans.** The largest
reason a lowered body stayed trusted was no longer a construct but a
shape: a function with no result — 246 of the prover's 879, the setters,
the emitters into the word arena, the arena pushes — was refused before
execution ("no integer result"), and a function that stored through a
span on the way to its result stopped at the store ("instruction str").
A store through a span parameter is now an effect the verdict compares,
as it compares a result and a package cell (asm/effects.go). Both sides
keep a write log per span parameter: the asm executor appends an entry
for every `str`/`strb`/`strh` whose base is a span's (`[xB, wI, uxtw #s]`,
an element offset, or the element address the atomics build) — the
32-bit index term and the stored register's value at the element width —
and a fork's two logs rejoin as a shared prefix plus each side's own
stores under the branch condition and its negation; the Oak lowering
appends `v[e] = x` under its path condition, the same statement-level
conditional and match arms the cells already lower under. A read on
either side consults its log newest-first before the entry memory — the
newest store at an equal index under a holding guard, else the entry
select or element parameter — so a read after a write sees the write
whether the machine forwards the value from the register or reloads it.
The final memories are compared at a fresh symbolic index per span
(`v[?]`, 32 bits, declared as a fresh unknown): the asm memory and the
Oak memory at that index are two terms at the element width, decided
exactly as a result is — witnesses, the linear form, the diagrams under
the reads' functional consistency — and equal at every index is equal
memories. The bounds stay the checker's: a store the verifier sees is
already under a dominating length guard, so its only question is which
element takes which value. Outside the subset, with the reason: a store
inside a data-dependent loop body (the loop summary has no memory), into
a by-reference record argument, of a register pair or a vector register,
and either side's memory written around a data-dependent loop. On the
prover: 58 unit functions are now proven in the span memory they write
(`set_lst`, `le_fail`, `cache_put`, `bind_scalar`, `ab_push`, the
`ap_*` emitters that write inline) and 11 more in their result and their
memory; proven functions 197 to 265 of 879, no disagreement, the rows
identical. The remaining unit functions are trusted for two reasons: 106
call a unit callee with a span in its signature (`ap_lits`, `write_lit`,
`sb_str`: the call summary threads a callee's cells since #384 but not
yet its span writes, and a span parameter keeps the call opaque) and 48
store inside a data-dependent loop. Pinned: `asm/effects_test.go` (a unit writer
proven, the wrong value and the wrong element refuted, a conditional
store proven and its unconditional lowering refuted, a result with a
forwarded write, a swap proven and its reordered lowering refuted at
`i == j`, a store the body does not make refuted) and
`compiler/e2e_native_span_effects_test.go` (the same shapes through the
backend, `fill`'s loop store trusted with the reason, the C backend the
oracle for the values).
**Twenty-ninth increment — a callee's effects through the call summary,
and shifts below the width.** Three things kept the arena emitters
(`ap_close` calling `ap_lits` calling `ab_push`) trusted after the
twenty-eighth. First, the call summary took only scalar arguments. It now
takes a span argument that is one of the caller's span parameters passed
whole — the `{base, len}` pair holding `&v` and `len(v)` — as an alias:
the callee's parameter is spelled in the caller's name wherever the
lowering names a span (its elements, its length, its write log,
`oakLowering.spanAlias`), so the callee's reads see the caller's stores so
far and its stores land in the caller's log; a by-reference record
argument (beyond 16 bytes) that is one of the caller's record parameters
binds the callee's parameter to the caller's leaves by name; the argument
registers follow the shared layout (a span two, a record one, a scalar
one). The Oak side inlines the same calls with the same alias
(`enterCall`), so both sides' logs agree in their spelling. Second, a
unit callee's loop whose count is a constant argument (`ap_lits(le, ew,
lo, hi, u32(1))`) unrolls inside the summary, since the summary lowers the
callee's body under the argument substitution. Third, `ab_push` shifts by
`(at % 4) * 8` — a data-dependent count, which the verifier refused
because Oak traps at the width where the machine wraps. A syntactic range
bound (asm/range.go: constants, masks, products and sums by constants,
shifts, the wider arm of a conditional) shows such a count never reaches
the width, where the two agree; a count whose bound reaches the width
stays outside the subset. The bound is memoized over the term DAG — its
first form recomputed shared subterms and turned a two-minute build into
ten. And a write log's read no longer builds an index equality for every
write it meets: two indices in linear normal form over the same unknowns
(`le.state_at + 9` against `le.state_at + 16`) are equal or unequal by
their constants alone, so the arena's `base + k` addressing folds before
the diagrams see it. On the prover: proven 265 to 281 of 879; 35 bodies
that were trusted are now evidence (agreeing on every witness, the
bit-level decision over the node budget — the byte extractors and the
longer emitters, whose write-after-write chains through symbolic word
indices outgrow the diagrams); no disagreement, the rows identical. Found
on the way: `oak build` compiled the program twice — once through the C
emitter up front, once through `emitFor` in the chosen asm mode — so
every native build ran the backend and the verifier twice; the first
compile now happens only for `-emit-c`, halving the native build. What
keeps the rest trusted: 18 callers pass more than eight argument words
(`px_node`), which the summary does not yet read from the outgoing area;
17 call the byte writer that reaches foreign code; 17 call `sb_str`,
whose loop count is data (an aggregate across a data-dependent loop);
and the deeper syntax walkers whose callees have data-dependent loops.
Pinned: `asm/effects_test.go` (`TestVerifyCalleeEffects`: a unit caller
proven in its span through the summary, a read after the summarized
store, a callee storing another value refuted; `TestVerifyBoundedShift`)
and `compiler/e2e_native_callee_effects_test.go` (the arena shape: a
record and a span passed through two levels of unit callees, the constant
count unrolled, the bounded shift proven, a data count trusted).
**Thirtieth increment — stack arguments in the call summary.** A call
whose arguments exceed the eight registers (`px_node` with eleven, the
syntax-node constructors `mk_*` behind it) left the summary at "arguments
beyond the registers". The summary now lays the callee's parameters out
by the shared rule and reads the ones beyond the registers from the
caller's outgoing area, which is the path's frame at the call's sp: a
scalar its natural size at its offset, zero-extended as the callee's
load is; a span's base and, eight bytes on, its four-byte length; a
by-reference record's address. The classification is one function now
(`classifyArguments`, asm/abi.go): the checker's contract binding, the
backend's placement, and the summary's reading share it, so the three
cannot disagree on a slot. On the prover: proven 281 to 299 of 879 (the
`mk_*` constructors, `cnf_header`/`cnf_lit`, `add_fn`, `trailing_zeros`),
no disagreement, the rows identical. **Where the build's time went.** With
the summaries reaching the arena emitters, the verifier's share of a
native prover build rose to about four CPU-minutes, and sampling put it
not in the diagrams but in the witness pass of `decideEqual`: each of
the 324 boundary inputs evaluated the two memory terms through a map
memo, and a memory built by a chain of summarized stores is a DAG of
tens of thousands of nodes. The pass now numbers the terms once and
evaluates them through slices (`termEvaluator`, which the theorem
decider already used) and thins the inputs so that it visits a bounded
number of nodes (`witnessVisitBudget`; the witnesses are the early
refutation, the decision that follows is the proof), which took the
slowest evidence verdicts from twenty seconds to two; the range bound of
a shift count is memoized per lowering rather than per shift (a count
that reads memory written by earlier summarized calls is a large DAG),
and `significantBits`, which a zero test's flag reading consults, walks
that DAG once per call rather than once per path through it — an
emitter with fourteen string literals (`reason_text`) took the verifier
past thirty minutes there before the memo, and takes a second after.
Alongside, the functional consistency constraint skips a pair of reads
whose indices are provably at different elements by their linear forms
(the `base + 9` against `base + 16` of the arena), keeping it linear
rather than quadratic in such a body's reads. The cost that remains is
the reach itself, measured on one machine with the two compilers
interleaved: the native prover build took about 30 CPU-seconds per
compile before the twenty-eighth increment and takes about 220 after the
thirtieth (the verifier's share about 150: evidence verdicts running the
three orders to the node budget about 90, `emit_header` alone about 40
exhausting the path budget across its conditional pushes, the proofs
about 20). `TestOakShellAgreesNative` builds both provers and runs the
corpus on each in about seven minutes on a loaded machine — under CI's
45-minute package timeout, over `go test`'s ten-minute default when the
whole root package runs on a busy host. Pinned:
`compiler/e2e_native_stack_summary_test.go` (a callee with three
arguments on the stack of mixed widths — `u16`, `u32`, `u64`, a `Bool` —
summarized into a unit caller proven in its span and into a caller
proven in its result and its span; the C backend the oracle).

**Thirty-first increment — integer division as an uninterpreted
operation (2026-09-15; `asm/floats_ops.go`, `asm/verify.go`,
`asm/rv64_verify.go`, `Oak.IntegerDivision`).** `/` and `%` by a divisor
that is not a constant power of two left a unit trusted on both lanes
("operator / (only by an unsigned constant power of two)"): the diagrams
have no division, and a 32-bit multiply of two unknowns exceeds every
budget. The increment treats the quotient as the same kind of term the
floats are — `udiv`/`sdiv` in the operation table, an application shared
under Ackermann's functional consistency by every side that divides the
same operands (`Oak.Uninterpreted.ackermann_sound`) — and spells every
remainder as `a - (a / b) * b`: the Oak `%`, the AArch64 lowering's
`sdiv`/`udiv` followed by `msub`, and RISC-V's `rem`/`remu`, which the
RV64 executor expands the same way (`rv64ALUTerm`). That spelling is
the machines' definition (`Oak.IntegerDivision.umod_eq_sub_udiv_mul` at
every width through the natural numbers, `srem_eq_sub_sdiv_mul_8` at the
bit level; RISC-V unprivileged spec §7.2, Arm's `msub` after a zero
quotient), so an RV64 `remw` and an AArch64 `msub` are one term. Both
lanes trap on a zero divisor before dividing and the Oak semantics trap
too, so the applications compared lie off `b = 0`; the theorem decider
states the zero divisor as a trap obligation, and the witness evaluation
returns the AArch64 result there. A structural decision follows the
diagrams' budget in the straight-line decider and precedes them in the
coupling's obligations (`termEquivalent`: equal in the low bits up to
the width adapters' masks and the RV64 extension idiom `(x shl 32) sar
32`): `(a / b) * 100 + a % b` is
the same term on both sides once the quotient is shared, and `divmod`,
`quot`, and `rem` are proven on both lanes (`asm/division_test.go`;
swapped operands and signed against unsigned division are mismatches).
The lowering written in Oak mirrors the rule (`FOP_UDIV`, `FOP_SDIV`, the
trap, `int_sdiv` for the fold), and `spec/oak/intrinsics.oak` states
`rem_is_sub_div`, `signed_rem_is_sub_div`, and `div_same_operands`.

**Thirty-second increment — parameters in the caller's outgoing area
(2026-09-15; `asm/verify.go` executeBodyChunk, `asm/unit.go`,
`Oak.StackArguments`).** The thirtieth increment read a callee's stack
arguments from the caller's side; the callee's own side still refused
them ("parameters beyond the register contract (the incoming stack area
is not modeled)"), so `nine`, `twelve`, `tail_sum`, and `records_last`
of the stack-argument corpus were trusted. The executor now holds such
a parameter in the frame slot at its offset above the entry sp (the
binding's `Stack`, the layout the checker and the backend share), at the
size the caller stored it — a narrow scalar its own bytes, a `Bool` the
four of the C int, a 64-bit scalar eight, a span its base at the offset
and its length eight on, a by-value record its chunks, a by-reference one
its address — and the body's `ldrb`/`ldrh`/`ldr` of the slot reads the
parameter as it reads any frame slot (`Oak.StackArguments`: the slot
round-trips at its width, the span pair's slots are disjoint). A unit may
now spell the binding as the compiler does, `bind [sp, #N] = p`, under
the packed convention. `nine` is proven; `twelve`, a 64-bit sum of
twelve unknowns, reads them all and stays evidence at the diagrams'
budget; dropping a stack parameter from the body is a mismatch
(`asm/stack_params_test.go`); `tail_sum`, whose span arrives on the
stack and is walked in a loop, is proven.

**Thirty-third increment — the RV64 lane's parameters beyond the
registers (2026-09-15; `nativegen/rv64.go`, `asm/rv64_check.go`,
`asm/rv64_verify.go`).** The rv64 lane left every function with more than
eight argument words to the C backend ("more than eight parameters", "the
parameters exhaust the eight argument registers"), and every call with
more than eight arguments. It now lays the integer-class parameters out
by the shared rule (`asm.LayoutArguments`, unpacked: XLEN-sized slots in
order, as the LP64 psABI passes them) and reads a scalar beyond a0–a7
from the caller's outgoing area in the prologue — `ld t0, frame+N(sp)`,
the slot holding the value widened as a register would (`Oak.RiscV.widen`,
so the callee's homes hold the canonical form) — and a native caller
stores its scalar arguments beyond the registers into the outgoing area
at its frame's bottom (the return address and the callee-saved area move
up by it), each into its slot as it is evaluated when no later argument
calls. The checker learns the incoming area (a load of a whole slot binds
the parameter, widened for a `u32`; a store into the area is refused) and
the binding `bind [sp, #N] = p`, which a unit may now spell on either
lane; the verifier holds the slot as a frame slot at its offset above the
entry sp. A span or a record beyond the registers stays with the C backend
in this increment — the psABI may split a two-word aggregate across the
last register and the stack, which the shared layout does not model — and
the lane says so. A call's constant arguments and the variables homed in
callee-saved registers are read at the move, as on AArch64, holding no
scratch register: `through_c`, which passes ten arguments to a C function,
lowers where its eight register arguments alone exceeded the operand
stack. On the stack-argument corpus `nine` lowers and is proven and
`twelve` is evidence as on AArch64; `tail_sum` and `records_last` stay
with the C backend with the reason
(`compiler/e2e_native_rv64_stack_args_test.go`, the corpus run on the
bare machine under QEMU against the C backend's realization;
`asm/stack_params_test.go`).

**Thirty-fourth increment — the RV64 lane's span locals and value-less
records (2026-09-15; `nativegen/rv64.go`; `spec/lean/Oak/SpanLocals.lean`).**
A `main` that named a view
of its own array (`whole: []u32 = view(&buf)`), or declared a record
without an initializer, stayed with the C backend on the rv64 lane ("a
local of type ([]u32)", "the record local p without an initializer"),
while the AArch64 lane lowered both. The lane now binds a span or view
local over an owned frame array as it binds a parked span parameter: the
array's frame address (`addi sB, sp, off`) and its constant length (`li
sL, N`) in two callee-saved registers, the length register serving as the
raw and the normalized length, so the local reads and stores through the
checker's guarded-index idiom, passes on as a `{base, len}` pair, and
another named span aliases by copying the registers; a subslice stays with
the C backend in this increment. A record local without an initializer is
zero-filled from the zero register, word by word (docs/spec/90-backend.md
§6). The Lean model states the pair's two facts — a guarded element access
(`i < n`) stays inside the array's slots and so below the frame, as an
instance of the checker's span access rule, and the word-by-word zero fill
is the record's zero value — and the verifier's Oak side now holds every value-less aggregate
local — an array, a record, a sum — at its zero value, as both backends
fill it, where it refused a record or a sum. `compiler/e2e_native_rv64_span_locals_test.go`
runs a program with both on the bare machine under QEMU and on the
AArch64 host against the C backend.
**Thirty-fifth increment — variable shift counts (2026-09-15;
`asm/verify.go` lowerVariableShift, `Oak.Shifts`).** A body shifting by a
count that is not a constant — `shifts`, `byte_shift` of the rv64 extra
corpus — was trusted ("the Oak body contains a non-constant shift count")
unless the count's range stayed below the width. Oak traps at the width
(docs/spec/10-syntax.md §3b) and so does the native code — both backends
guard the count (`cmp wN, #width; b.hs trap`, `bgeu n, width, trap`)
before the register shift — and the executor already drops a trapping
path from its fork, so the equivalence is over the counts below the width,
where the guarded machine shift is Oak's. The Oak side now lowers the
shift at the machine's register width — a w register on AArch64 for
operands up to 32 bits, `sllw`/`srlw` on RV64 for a 32-bit operand and
XLEN for a narrower one — and truncates back, so that on the counts the
trap removes the term is the machine's wrapped value rather than a claim
about Oak's (trapping) result; below the width the two coincide
(`Oak.Shifts`: the widened shift masked back is the narrow shift for
every count below the width, and a count below the width is its own
remainder at the register width). The claim rests on the machine's
guard: the executor records, on every path, the trap bound under which a
register-count shift ran (`cmp wN, #K; b.hs trap` bounds wN below K, and
so does `li rK, K; bgeu rN, rK, trap` on the rv64 lane), and the Oak side
admits the variable count only when every such shift was guarded at or
below Oak's width — a shift with no guard, or one guarded at the
register's width rather than the operand's, stays trusted as before, since
there Oak traps where the machine delivers. A signed operand keeps the
refusal, as the backends leave those bodies to C. `shifts` and `byte_shift` are proven
on both lanes (`asm/shift_test.go`; `compiler/e2e_native_rv64_test.go`);
the theorem decider's treatment — the trap as a recorded obligation — is
unchanged.
**Thirty-sixth increment — span arguments over the caller's owned arrays
(2026-09-15; `asm/span_args.go`, `Oak.SpanArguments`).** The call summary
took a span argument only as one of the caller's span parameters passed
whole, so every `main` that handed its own array to a helper —
`put(span(&buf), …)`, `fill(span(&buf), …)`, `sum(view(&buf))` — was
trusted ("the span argument v is not one of the caller's span parameters
passed whole"), on both lanes. The summary now recognizes the pair the
backends build for `span(&buf)` / `view(&buf)`: the array's frame address
(`add xN, sp, #off`; `addi rN, sp, off`) and its constant length, and
binds the callee's parameter as the Oak side's inline binds it — an
aggregate local holding the array's elements, each read from its frame
slot (a zero-filled array reads as zeros through the slot tiling), so the
body's element reads and writes, its `len`, and its data-dependent loops
(which carry the aggregate's leaves as fresh symbols, the same symbols on
both sides) are the aggregate's. After the body a writable span's final
leaves are stored back, leaf `i` into slot `i` (`Oak.SpanArguments`: the
slots are pairwise disjoint and lie inside the array, a leaf written back
is read back from its slot, and a second element's write-back leaves the
first's bytes). An array that follows a store at a data-dependent index
(the frame's unknown region), a length that is not a constant, or an
array beyond the summary's budget stays trusted with the reason. The
span-effects `main` is proven on both lanes, as are `filled` and `squares`
of the rv64 corpus, whose callees loop over the array
(`asm/span_args_test.go`; `compiler/e2e_native_span_effects_test.go`,
`compiler/e2e_native_rv64_test.go`). A constant table handed to a callee
(`sum_view(view(&TABLE))`) is the table passed whole: its address beside
its constant element count takes the span-parameter alias, and `len` over
the callee's parameter resolves through the alias to the table's count, so
`table_sum` is proven too (`compiler/e2e_native_tables_test.go`).

**Thirty-seventh increment — unit bodies without effects (2026-09-15;
`asm/effects.go` decideEffects, `Oak.UnitBodies`).** A unit function whose
body has no effect the model tracks — `check_all`, an assert over a call,
on both lanes — was trusted ("no integer result"): a unit body is decided
in the package cells and the span memories it writes, and with neither
side writing any there was nothing to compare. Nothing to compare is the
agreement: both sides leave the entry state as it is, so the body is
proven "(a unit body that writes no package state and no span memory on
either side)" (`Oak.UnitBodies`: the empty effect log is the identity, and
two empty logs agree exactly when the entry states do). A body that does
store through a span the signature lacks, or writes a cell the Oak body
does not, is decided as before (`asm/unit_bodies_test.go`).
**Thirty-eighth increment — frame loads at a data-dependent index
(2026-09-15; `asm/verify.go` boundedFrameLoad, `Oak.FrameIndex`).** A load
from an owned frame array at an index that is not a constant — `bytes[i]`
in `signed_bytes`, `ldrsb w0, [x10, w0, uxtw]` under the checker's guard
`cmp w0, #3; b.hs trap` — left the body trusted ("a frame load at a
data-dependent index"): the executor stored at such an index as a memory
(the bounded frame store) but read only at a constant one. The load now
reads the guard's K elements merged under the index, from the last element
down with the last as the default — the fold the Oak side already uses for
an array element under a symbolic index (elementUnderIndex) — so below the
bound both sides read element `i`, and on an index at or past the bound,
the path the guard's trap removes, both read the last element and no
mismatch is invented there (`Oak.FrameIndex`: `chain_select`,
`chain_beyond`). The value is extended as the load extends it (`ldrsb`
signed). An element in the frame's unknown region, a slot never stored, or
a bound past the subset's budget stays trusted with the reason.
`signed_bytes` is proven on the AArch64 lane (`asm/frame_index_test.go`;
`compiler/e2e_native_array_test.go`). The rv64 lane forms the element
address by a scaled add after the guard (`li k, N; bgeu i, k, trap; slli
i, i, s; add i, b, i`), so the guard's bound is recorded on the index's
term as well as its register and follows the index through the rewrite
(`asm/rv64_frame_index.go`): a load through add(frame address, index
scaled) reads the same merged elements, a store is the bounded frame
store, and `signed_bytes` is proven on that lane too
(`compiler/e2e_native_rv64_test.go`).

Next increments: stores in data-dependent loops as a summarized memory
(the span-writing loops behind `sb_str`, `px_acc_list`, and the 52 bodies
with a store in a loop body); guard elision from the checker's facts; the foreign-call subset only if the shell itself is to
be verified —
calls by inlining or by the callee's proven contract, and effects through
spans as the result — so that "trusted" shrinks toward the foreign
boundary; then two-chunk and `x8`-area record results in the verifier,
`break` as a second loop exit in the recognizer, `view` over record fields
and the other survey items, and the slicing syntax `v[lo:hi]` once the C
backend lowers `len` over it.



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

**RISC-V: the RV64 lane (first increment landed).** The second
architecture, RV64IM first (the base integer set with multiplication,
control transfer, loads and stores — what a hypervisor's or a database
engine's hot integer paths need), then the F/D and V extensions, and the
A extension's `lr`/`sc` and `amo*` (`asm/rv64_atomics.go`: through a span
element as the plain accesses, with their `.aq`/`.rl`/`.aqrl` suffixes,
the checker holding them to the same bounds and the verifier deciding
them under the sequential model of `65-machine-memory.md` §7a). A unit
names the lane in its path (`name.rv64.oakasm`) or with an `arch rv64`
directive before its bindings; every phase dispatches on it
(`Function.Arch`). The specification situation is better than Arm's: the
instruction list comes from riscv-opcodes (redistributable, so the table
`asm/rv64_encodings_gen.go` is *generated and committed* by
`asm/internal/riscvgen`, recording the upstream commit); the semantics
have riscv/sail-riscv as the ratified golden model, which already targets
Lean. What is new against the AArch64 lane, and how it landed:

- *The contract* is the LP64 psABI (`asm/rv64_check.go`): integer
  parameters in `a0`–`a7` in declaration order, a span or view as the
  `a_i`/`a_{i+1}` pair, the result in `a0`; `sp` is x2 and parses as the
  frame register so the frame machinery is shared. The psABI widens a
  narrow integer by its own sign to 32 bits and then sign-extends — so a
  `u32` arrives sign-extended and the verifier binds it so
  (`Oak.RiscV.widen`), unlike AAPCS64's unspecified upper half.
- *No flags*: the checker's flags dataflow rule becomes the
  comparison-branch rule — a conditional branch reads two registers, so it
  needs them readable and nothing else. In the verifier the branch is the
  same comparison term (`cmpTerm`) the AArch64 flags produced;
  `Oak.RiscV.Br.holds_eq_condHolds` proves each branch holds exactly when
  the condition code the verifier assigns to it (`beq`↔`eq`, `bne`↔`ne`,
  `blt`↔`lt`, `bge`↔`ge`, `bltu`↔`lo`, `bgeu`↔`hs`) holds on the flags of
  the same subtraction, so the shared term has one meaning across lanes.
- *The link register* `ra` and the callee-saved `s0`–`s11` carry the
  AArch64 lane's obligation: save to the frame (`sd reg, imm(sp)`) before
  a write, restore from the same entry-relative slot before `ret`; a call
  (`call sym`, `jal ra`, `jalr ra`) requires `ra` saved first and forgets
  the caller-saved `a1`–`a7`, `t0`–`t6` (`a0` carries the callee's
  result). `ra` and `s*` cannot be clobbers. The frame moves only by
  `addi sp, sp, ±imm` in multiples of 16 within the declaration, and every
  `imm(sp)` access is inside `[-frame, 0)` and aligned. Memory through any
  other base is outside this increment and refused (fail closed; the span
  element rule follows).
- *The W-forms* (`addw`, `subw`, `sllw`, `srlw`, `sraw`, `mulw`, `addiw`,
  …) compute at 32 bits and sign-extend (`Oak.RiscV.addw_eq`); `slt`/`sltu`
  are comparison terms; division and remainder carry RISC-V's total
  semantics (a zero divisor gives all ones and the dividend, the signed
  overflow the dividend and 0 — `Oak.RiscV.div_zero` and its kin,
  `rv64Divide` in Go); `auipc` and calls are outside the verified subset
  (checked, trusted). The pseudo-instructions `mv li not neg negw sext.w seqz snez sltz sgtz
  j jr ret nop beqz bnez bgez bltz blez bgtz call` are the assembler's
  spellings of base encodings (`li` up to 32 bits as `lui`+`addiw`,
  `call` as `auipc`+`jalr` under one `R_RISCV_CALL_PLT`).
- *The encoder* (`asm/rv64_encode.go`) places the fields by name from the
  generated table (the permuted `jimm20`, `bimm12hi/lo`, `imm12hi/lo`
  forms); the ELF writer emits `EM_RISCV` objects (e_flags 0: LP64
  soft-float, no RVC) that link with `riscv64-elf-gcc -march=rv64im
  -mabi=lp64`; the C emitter guards the unit with `defined(__riscv) &&
  (__riscv_xlen == 64)` in GNU syntax and fails closed elsewhere.
- *The oracles*: `TestRV64EncoderAgreesWithGNUAs` encodes every mnemonic
  of the lane and compares words with `riscv64-elf-as`;
  `TestRV64QEMUDifferential` links four units into a bare-metal image and
  runs them under `qemu-system-riscv64 -machine virt` on edge and random
  inputs, comparing the machine's results with the verifier's concrete
  execution of the same units — the silicon-differential shape of the
  AArch64 lane with the emulator as the machine (no RISC-V silicon on the
  host). Both skip without the tools.

**Lanes and targets (landed with `90-backend.md` §2a).** The build's
target selects the lane: a unit applies when its lane is the target
architecture's; one unit per lane may realize a signature (`pick.arm64.oakasm`
beside `pick.rv64.oakasm`), and a unit of another lane yields to the Oak
fallback body or, without one, fails the build at compile time. The
fallback body is emitted under the negation of *its unit's* lane condition
(`!(defined(__riscv) && (__riscv_xlen == 64))` for an rv64 unit), the
companion object follows the target (ELF `EM_RISCV` with the lp64d float
ABI for a hosted RISC-V target, lp64 for freestanding), and `oak build
-target linux/riscv64` links the assembled unit into a static musl binary
through `zig cc` from any host.

**Span element memory (landed).** A `[]T`/`[*]T` parameter arrives as the
`a_i`/`a_{i+1}` pair with the `u32` length widened like any other `u32`
argument — sign-extended from bit 31 (`Oak.RiscV.widen`), so the raw
register compares correctly only against another widened `u32`. The
checker admits a bound from the normalized copy, the exact pair
`slli rX, a_{i+1}, 32` then `srli rX, rX, 32` (one definition of rX, so the
fact survives labels), against any index; or from the raw register
against an unmodified widened `u32` parameter (below). From there the guard facts
mirror the AArch64 lane, computed on straight-line code and forgotten
where paths meet (a label) and after a call: the fall-through of
`bgeu idx, lenN, exit` proves `idx < len` (`Oak.RiscV.index_guard`, and
`index_guard_lt32`: the index fits 32 bits, so the psABI's sign-extended
upper half of a `u32` index cannot pass the guard); `bgeu idx, K, exit`
against a constant register (`li`) proves `idx < K`; the fall-through of
`bltu lenN, K, fail` proves `len >= K` (the minimum-length fact);
`slli t, idx, s` carries the guard scaled by `2^s`
(`scaled_index_exact`: no wrap), and `add r, base, t` with `2^s` the
element size makes `r` the address of one element — a region of `2^s`
bytes, writable iff the span is; `r` may be the base register itself (the
write forgets the span, the region takes its place). GCC's shape for the
prelude's `oak_index` at `-O1` is admitted as well: `bgeu idx, len` on the
*raw* pair, with both registers unmodified widened `u32` parameters (the
index a scalar, the length a span's), proves the low halves' order
(`index_guard_widened`: sign extension preserves the unsigned order of
two 32-bit values) and yields a *raw* index fact that addresses nothing
by itself; the fused zero-extend-and-scale `slli t, idx, 32` then
`srli t, t, 32-s` turns it into the scaled index (`widened_scale`:
`(widen i << 32) >> (32-s) = zext i << s`), from which `add` forms the
region as above. A raw guard on a register that is not a widened `u32`
parameter (a `u64`, a rewritten index or length), or scaled without the
zero extension, is refused. Memory through a register other than
`sp` is then admitted in exactly two shapes: inside a region
(`offset + width <= 2^s`), or at a constant offset below the proven
minimum length through the base itself, at the element width and a
multiple of it; a store needs a writable span; `ebreak` is the failure
arm's trap. The verifier resolves such a load to the element term — the
address `&v + K` names element `K / elem`, `&v + (idx << s)` element
`idx` — so `first(v) = v[0]` is proven and the QEMU differential's `vsum`
runs the element loop against the verifier's fixed memory.

**Loops over elements are proven (landed).** The loop summarizer executes
an RV64 body with the lane's own semantics, and the inductive coupling of
loop variables admits a 64-bit register carrying a 32-bit Oak variable
*widened*: `r = zext(x) + b` for a counter kept below `2^32` by the loop's
guard (`Oak.RiscV.zext_increment`, `lt_bound_ne_allOnes`), or
`r = sext(x) + b` for an accumulator the W-forms sign-extend
(`addw_sext`, `addw_sext_truncate`); the length normalization
`(len << 32) >> 32` folds to the length's zero extension. The element sum
`sum_rv` is thereby *proven equal at the bit level* to its Oak `while`
body, coupled as `i ↔ t0` (zero-extended) and `total ↔ t3`
(sign-extended) under the invariant `i <= len(v)`.

**The Sail oracle (landed).** The same differential units run under the
Sail RISC-V model's C emulator (`external/sail-riscv`, the ratified golden
model; `TestRV64SailDifferential`), the harness reporting through the
HTIF `tohost` device — device 1 for the console, device 0 to exit — which
the emulator locates by the ELF symbol. QEMU and Sail both agree with the
verifier's concrete execution on every input, so the term semantics are
now checked against two independent machines.

**The Sail bridge (landed, in two halves).** The Sail model's Lean export
(`sail --lean`) spells each instruction's `execute` as register plumbing
around a pure expression over the Sail Lean library's bit-vector
primitives and the model's prelude helpers. `spec/lean/Oak/SailRiscVBridge.lean`
restates those definitions verbatim — `asm/rv64_sail_bridge_test.go`
fails if they drift from the fetched library (lean-sail `v4`) or the
export — and proves that the expression the model computes for each
instruction the verifier decides is `Oak.RiscV`'s function of the same
register values: `addw`, `subw`, `sllw`, `srlw`, `sraw` (the
`execute_RTYPEW` result), `slt` and `sltu` (the `execute_RTYPE`
comparisons), and the six branch conditions of `execute_BTYPE`. The
register plumbing (`wX_bits rd <expression>`, `if taken then jump_to`) is
read off the generated definitions by inspection; the data semantics are
the theorems. The second half, `spec/lean-sail/`, states the theorems
against the export itself, imported as a lake dependency, so nothing is
restated there. It builds (2026-09-14) against the export of sail-riscv
497209b9 generated by Sail from git under lean-sail v5 — the last model
commit whose export compiles; the current one exports `vmem_types.sail`'s
type-level `root_level('v)` with unbound variables, and sail-riscv's own
Lean workflow is red for it — and it is the wider half: beyond the RTYPEW,
comparison and branch theorems it bridges the register ALU (`add`, `sub`,
`and`, `or`, `xor`, `sll`, `srl`, `sra` with the count the low six bits),
the immediate forms (`addi`, `andi`, `ori`, `xori`, `slti`, `sltiu`, the
immediate sign-extended), the shifts by immediate at both widths, `addiw`,
the multiplies `mul`, `mulw`, `mulh`, `mulhu` (`BitVec.ofInt` a ring
homomorphism, so the model's integer product truncated is the bit-vector
product, its high half the high half of the extended product), and the
divisions and remainders `div`, `divu`, `rem`, `remu` (the model computes
on `Int` with `tdiv`/`tmod` and spells the zero-divisor and overflow cases
out; `BitVec.toInt_sdiv`/`toInt_srem` and the bound `|a tdiv b| ≤ |a|`
carry them to Oak's totalized `sdiv`/`srem`), and their W forms through
the width-generic `divN`/`remN` — every integer instruction the
verifier's tables decide. Of the loads and stores the pure parts are
theorems: the effective address `rX rs1 + sign_extend imm`
(`ext_data_get_addr`), the alignment guard (`is_aligned_vaddr`, the
checker's multiple-of-width obligation), the loaded value's extension
(`extend_value`) and the stored data's truncation, against
`Oak.RiscV.effectiveAddress`, `loadValue`, `storeData`; the model's
address translation and memory access (`translateAddr`, `mem_read`,
`mem_write`, in the monad) are what the checker's bounds and the
verifier's flat element memory stand in for — an audited hop. 53
theorems in all. The generation
and build steps are in `spec/lean-sail/README.md`; the Go test builds the
project when the export is present and skips otherwise.

**F and D under LP64D (landed).** The floating-point file is a register
class of its own (`f0`–`f31`, `ft*`, `fs*`, `fa*`); the generated table
gains riscv-opcodes' `rv_f`, `rv64_f`, `rv_d`, `rv64_d` (127 encodings in
all), with the `rs3` field of the fused multiply-adds and the `rm` field
of the arithmetic and conversions — a trailing rounding-mode operand
(`rne`, `rtz`, `rdn`, `rup`, `rmm`, `dyn`) or, absent, `dyn` as GNU as
encodes it, and `rne` for the three exact conversions (`fcvt.d.w`,
`fcvt.d.wu`, `fcvt.d.s`) as GNU as encodes those. The contract is LP64D:
`f32`/`f64` parameters in `fa0`–`fa7` in declaration order independently
of the integer file, the result in `fa0` (`Oak.RiscV.lp64dBinding`,
`lp64dBinding_kinds`, and distinctness decided exhaustively for every
list of kinds up to the contract's width); `fs0`–`fs11` carry the
save/restore-from-the-same-slot obligation through `fsd`/`fld` on the sp
frame; `ft0`–`ft11` and the `fa` registers are clobberable; floating-point
memory is frame memory only. A unit touching the floating-point file is
checked and *trusted* — the verifier's terms are integers — and it needs
an lp64d toolchain: the hosted RISC-V targets carry it (their companion
object declares lp64d), and the stitcher refuses such a unit for the
freestanding RISC-V target, whose default processor is soft-float, naming
the alternative. Every F/D mnemonic agrees with `riscv64-elf-as
-march=rv64imfd -mabi=lp64d`, and the QEMU and Sail differentials carry an
`f64` unit (`fmul`, `fadd`, `fsub`, `fdiv`, `fsgnjx`, `fsqrt`, constants
through `fmv.d.x`) whose expected results are Go's IEEE-754 arithmetic:
both machines agree on every input, subnormal and overflowing ones
included; the harnesses enable the FPU (`mstatus.FS`) before calling in.

**The vector extension as checker state (landed).** The vector file is a
register class of its own (`v0`–`v31`), every register caller-saved and
clobberable (`clobber v1`), readable once written on the path. The
generated table gains the subset of riscv-opcodes' `rv_v` the strip-mining
idiom needs (20 encodings: `vsetvli`/`vsetivli`, `vle8.v`/`vle32.v`,
`vse8.v`/`vse32.v`, `vadd`/`vsub`/`vand`/`vor`/`vxor`/`vminu`/`vmaxu` `.vv`,
`vmv.v.x`, `vmv.x.s`, `vredsum.vs`, `vmseq.vv`, `vmsne.vx`, `vmerge.vvm`,
`vcpop.m`), unmasked, with the vtype spelled in full — `e8|e16|e32|e64,
m1, ta|tu, ma|mu` — so the configuration the checker tracks is the one the
author wrote. The configuration is straight-line state: `vsetvli` (or
`vsetivli`) sets the SEW and what is known of the AVL; every other vector
instruction needs one in effect, and a label or a call forgets it (the
psABI preserves neither `vl` nor `vtype`, so a strip-mining loop re-issues
`vsetvli` at its head — the same rule the simd realizations follow). A
vector load or store moves `vl` elements of the configured width from its
base, and `vl ≤ AVL` on every legal implementation (RVV 1.0 §6.3,
`Oak.RiscV.vsetvlOK`; QEMU's and Sail's `min(AVL, VLMAX)` is one,
`vsetvl_min_ok`). The checker admits it through a bound span base when the
AVL is the span's normalized length, or an immediate within a proven
minimum length (`immediate_access_in_bounds`); and through a guarded
element address `&v[idx]` when the AVL register holds `len - idx` —
`sub avl, len, idx` under the guard `idx < len`, a *remaining-count fact*
— over the same index at the same write generation the address was formed
from: `idx + vl ≤ idx + (len - idx) = len` (`strip_access_in_bounds`), and
the loop advances (`strip_progress`). Element width and SEW agree, and a
store needs a writable span. **Masks and groups (second increment).** A
maskable form takes a trailing `v0.t` (`vm = 0`): the checker reads `v0`,
and the bound is unchanged, since the masked-off elements are a subset of
the vl the unmasked access already covers (`masked_access_in_bounds`).
`vsetvli` with `m2`, `m4`, or `m8` makes every vector register operand a
group of LMUL registers aligned to LMUL (RVV 1.0 §3.4.2,
`group_within_file`): every register of the group is read or written, so
a group must be wholly clobbered before it is written and an unaligned
group is a finding; mask destinations and mask sources (the comparisons'
`vd`, `vcpop.m`'s source, `v0`) stay single registers. **Fractional LMUL
(fourth increment)**: `mf2`, `mf4`, and `mf8` are admitted — the checker
keeps LMUL in eighths, a fractional group is one register
(`Oak.RiscV.groupOf`), the ratio `SEW / LMUL` must stay within `ELEN = 64`
(`e64` needs `m1`, `e32` at least `mf2`, `e16` at least `mf4`, `e8` any;
otherwise the configuration would be reserved, `fractional_within_elen`),
widening from a fractional LMUL doubles the eighths and stays in one
register until `m1` (`wide_group_fractional`), and an extension's source
group below `mf8` is refused; the differentials carry the `[]u32` sum
loaded at `e32/mf2`, widened to `e64/m1`, and reduced there. **Vector
floating point (fifth increment, 2026-09-14).** The table gains
`vle64.v`/`vse64.v` and the floating-point forms `vfadd.vv`, `vfsub.vv`,
`vfmul.vv`, `vfmacc.vv` (spelled `vd, vs1, vs2`; the accumulator `vd` is
read and written), `vfmv.v.f`/`vfmv.f.s` (an `f` operand class: the F
register the scalar crosses through), `vfcvt.f.xu.v`, and the *ordered*
reduction `vfredosum.vs` — float addition is not associative, so the
unordered `vfredusum.vs`, whose grouping is implementation-defined, is
outside the table; the ordered form folds a strip left to right from the
scalar it is handed, and a strip-mining loop that hands each strip the
previous result computes the sequential fold over the whole span
whatever `vl` each `vsetvli` chose (`Oak.RiscV.ordered_strips_fold`). The
checker requires `e32` or `e64` under a floating-point form
(`floatSewOK`: Zve32f/Zve64d; `e16` would be Zvfh), reads and writes the
F operands under the F lane's rules (bound, clobbered, or written), and
treats element-0 operands as single registers whatever the LMUL — a
reduction's scalar input and result and `vmv.x.s`/`vfmv.f.s`'s source
(RVV 1.0 §14, §16) — so a read of a group's upper register after a
reduction is a finding. The differentials carry `q = x·k + (x − k)²` per
element (`vfcvt`, `vfsub`, `vfmul`, `vfmacc` with one rounding) folded in
order into an f32 sum; QEMU and Sail agree with Go's float32 arithmetic and
an exactly rounded fma. **Widening (third increment).** `vwaddu`/`vwadd`/`vwsubu`/`vwsub`/
`vwmulu`/`vwmul .vv` write `2*SEW` elements into a `2*LMUL` group,
`vzext.vf2`/`vsext.vf2` read a half-width source group, `vnsrl.wi` reads a
`2*LMUL` source, and `vle16.v`/`vse16.v` move 16-bit elements: each
operand's group is its EMUL's size, aligned and wholly clobbered; a
destination group that overlaps a source group is refused (the ISA's
overlap rule, fail-closed), as is widening past 64-bit elements or a wide
group past the file (`wide_group_within_file`, `widening_within_64`). The
differentials carry the u32 elements multiplied into u64 products and
reduced at e64/m2. A vector unit is checked and
*trusted* — the vector state is outside the term language, as the
floating-point file is — and its inline realization scopes
`.option arch, +v` to the unit so any host assembler accepts it. Every
mnemonic agrees with `riscv64-elf-as -march=rv64imv`; the QEMU
(`-cpu rv64,v=true`) and Sail (V "Full") differentials carry the
strip-mined `[]u32` sum, expected from Go's wrapping arithmetic, with the
vector unit enabled (`mstatus.VS`) beside the FPU; and `TestRV64VectorChecker`
holds the rejections — no configuration, configuration lost at a label or
across a call, width against SEW, an AVL that is not the remaining count,
the index rewritten between the address and the count, an unclobbered
vector register, a store into a view, an immediate past the minimum, an
unaligned group, a mask register never written, a group not wholly
clobbered, `e64` at `mf2` — and the differentials carry the masked
strip loop at LMUL=2 (the sum of the elements that differ from `k`,
under `mu` so the accumulator's masked-off lanes stay zero).

**RVC (landed).** Under `option rvc` a function is encoded with the C
extension's 16-bit forms wherever one exists and the operands fit — the
compressed register set `x8`–`x15` where a form names three bits, the
6-bit signed immediates (`Oak.RiscV.imm6_round_trip`), the scaled and
bounded offsets of `c.lw`/`c.ld`/`c.sw`/`c.sd` and their `sp` forms
(`scaled_offset_exact`, `lwsp_offsets`, `ldsp_offsets`), `c.addi16sp` and
`c.addi4spn` for the frame, `c.mv`, `c.add`, the `x8`–`x15` arithmetic,
`c.j`, `c.jr`, `c.jalr`, `c.beqz`/`c.bnez`, `c.ebreak`, `c.nop`; a 32-bit
`li`'s `lui` and `addiw` halves compress on their own; `call` never does.
The choice is GNU as's — compress whenever a form exists and fits — so the
bytes agree with `riscv64-elf-as -march=rv64imc` on every spelling
(`TestRV64RVCEncoderAgreesWithGNUAs`, which also holds a branch beyond the
compressed range). Branches and jumps take their size from the layout: the
function starts as four-byte instructions and shrinks each branch whose
offset fits until nothing changes, so label arithmetic converges with the
sizes. The checker and the verifier see the base instructions and are
unchanged; the object carries `EF_RISCV_RVC`; the QEMU and Sail
differentials run the strip-mined sum compressed. A compressed function
holding an odd number of 16-bit instructions ends on a half word, so the
object writer pads to the next entry in `nop` words closed by one `c.nop`
(`Oak.Assembler.gap_reaches`, `pad_halfwords_reaches`) — a word-sized pad
alone would never reach the boundary (`pad_words_misses`).

**The processor decides (landed).** The compiler reads the RISC-V
extensions of `-cpu` (`target.CPUFeatures`: `+c`/`+v` on a zig-style name
such as `generic_rv64+m+a+c+v`, or the letters of an ISA string such as
`rv64gcv`; a named processor without them carries none; the freestanding
default `generic_rv64+m` has neither; a hosted RISC-V target assumes its
toolchain's `rv64gc`). A unit that uses the vector file is refused unless
the processor has V, naming `-cpu ...+v`; and unless a unit spells
`option rvc` or `norvc` itself, its native encoding compresses exactly
when the processor has C — the same choice the C toolchain's assembler
makes for the inline realization under that `-mcpu`, so the two
realizations of a unit carry the same instruction sizes
(`compiler/e2e_rv64_cpu_test.go`).

**The native backend's RV64 lane (first increment landed; `nativegen/rv64.go`).**
The compiler's own output joins the units on this lane: `oak build -native
-target linux/riscv64` (or `freestanding/riscv64`) lowers a type-checked Oak
function of the fixed-width integer subset to an asm function of the rv64
lane — the object an `.rv64.oakasm` unit yields — so the seam checker
above holds it to the LP64 contract, the callee-saved obligation, the
frame, and the comparison-branch rule (a finding is a backend bug and
rejects the compilation), the verifier proves it equal to its Oak body
where the term language reaches (a mismatch rejects), the encoder and the
ELF writer realize it in the companion object, and the Oak body stays as
the portable realization under `!(defined(__riscv) && (__riscv_xlen ==
64))`. The subset is the AArch64 lane's first increment: parameters,
locals, and results of the fixed-width integers and `Bool`; literals;
wrapping `+ - * & | ^`; `/` and `%` with a zero divisor trapping through
`ebreak` and `MIN / -1`, `MIN % -1` as the ISA's total division gives them
(the C helpers' values); shifts whose count at or beyond the width traps;
comparisons; short-circuit `&&`/`||`; `!`, `-`, `^`; the widening
constructors and `trunc`/`bits`; the Bool conditional; typed locals and
assignment; `while`/`break`; `assert`; calls with scalar signatures through
`call`; a tail self-call as a loop. Every value is a 64-bit register in the
psABI's canonical form, which is what the W-form instructions produce: a
32-bit value sign-extended from bit 31 whatever its signedness (so
`addw`/`mulw`/`divuw`/`sllw`/… keep the form, `and`/`or`/`xor` of two
canonical values are canonical, and `sltu` orders two canonical u32 values
as the unsigned values order — sign extension is monotone on each half of
the range and keeps the halves apart), a narrow unsigned value
zero-extended, a signed one sign-extended; a `u32` widened to 64 bits is
the one conversion that moves bits (`slli 32; srli 32`), a 64-bit value
narrowed to 32 is `sext.w`. Expressions evaluate into `t0`–`t6` as an
operand stack spilled to frame slots around `call`; variables live in
`s1`–`s11` in declaration order, saved in the prologue and restored before
`ret`, with frame slots past eleven; parameters bind at `a0`–`a7` (a narrow
one arrives canonical: the psABI widens by the type's sign to 32 bits and
sign-extends, which is what the verifier's binding models) and the result
leaves in `a0`; `ra` is saved at the frame's base when the body calls; a
comparison in a condition branches on its two registers directly. A
constant beyond `li`'s 32 bits is its two halves — `li hi; slli 32; li lo;
add` — with the high half adjusted for the low half's sign. Landed with it:
the checker takes a label's displacement from the branches that reach it
when no path falls through (the trap block after `ret`), and refuses a
label reachable only by a later branch, as the AArch64 checker does; the
encoder writes the zero-operand words (`ebreak`, checked against GNU as);
and both lanes type a negated literal by its context, as the checker's
literal rule does — the verifier caught the lane reading `i64(-5000000000)`
at the negation's recorded 32-bit width, a mismatch that rejected the
build before any test ran. Executed (`compiler/e2e_native_rv64_test.go`): the AArch64 lane's
twelve-function corpus and a second corpus of what the canonical form makes
delicate — a 64-bit constant with bit 31 of its low half set, 16-bit
arithmetic and negation, variable shift counts, unsigned 32-bit and 64-bit
division and remainder, `>`/`<=` at the 32-bit sign boundary in both
signednesses, `||`, thirteen variables (frame slots), calls nested in
arguments, the u32 → u64 widening of a value with bit 31 set, truncations,
`^`, a negative 64-bit constant — lowered entirely by the backend, thirteen
of the second corpus's functions **proven** at the bit level against their
Oak bodies (`mix`, `byte_sum`, `clamp8`, `between`, `widen`, `narrow` of
the first; the u16 product agrees on every witness, the rest are trusted
for their calls, variable shift counts, and divisions), and run to their
expected exits under `qemu-system-riscv64`
(`-M virt`, the Oak companion object linked beside the C shell by zig into
a bare-metal image whose harness prints `oak_main`'s result over the UART
and lands an `ebreak` in a machine-mode handler), with the C backend alone
as the oracle and a failing assertion trapping; the hosted build runs under
user-mode QEMU where one is installed (the CI cross-targets job), and the
same second corpus runs through the AArch64 lane on an arm64 host. Loops
and callers are trusted on this lane as on the other (the verifier's
budget, `call`); the later increments of the AArch64 lane — spans and
views, owned arrays, records, unions, floating point — are the lane's next
steps, in that order.

**RV64 lane, second to fourth increments — spans, owned arrays, floating
point (landed).** *Spans and views* bind as the LP64 pair; the prologue
normalizes each length once into an argument register past the parameters
(`slli n, aL, 32; srli n, n, 32`, written exactly once so the checker
carries the fact across labels), and every element access is the checker's
guarded idiom right before the memory instruction: the index zero-extended
(a canonical u32 is sign-extended; the guard compares 64-bit values), `bgeu
idx, n, trap`, `slli` by the element's log, `add` to the bound base, then
`lw`/`lh`/`lhu`/`lb`/`lbu`/`ld` (or `sw`/`sh`/`sb`/`sd` through a writable
span) at offset 0 — so an index at or past the length traps as `oak_index`
does and the checker's own rule admits the access. `len(v)` is `sext.w` of
the normalized length. A span kernel is a leaf on this lane for now: a
call clobbers the bound pair and the checker keys the span's facts on it
(the AArch64 lane's parking of pairs in callee-saved registers is the
next port). *Owned arrays* occupy whole frame slots, zero-filled through
the zero register or stored element by element from a literal; a literal
index addresses its slot through `sp`; any other index goes through the
array's frame address under a constant guard — `addi b, sp, off; li k, N;
bgeu idx, k, trap; slli idx, idx, s; add idx, b, idx` — and `view(&buf)` /
`span(&buf)` hand a callee the {frame address, N} pair. The checker gained
the matching facts: `addi rD, sp, imm` records an entry-relative frame
address, and `add rE, rD, t` over a frame address with `t` a guarded,
scaled index below a constant K makes `rE` a writable element region when
every one of the K elements lies inside the declared frame and the base is
aligned to the element (`TestRV64SpanMemoryChecker`: the accepted array,
and the rejections past the frame, without a guard, at the wrong scale);
floating-point loads and stores through a region are admitted like integer
ones. *Floating point* under LP64D: `fa0`–`fa7` carry f32/f64 parameters
and `fa0` the result by their own count, expression temporaries live in
`ft0`–`ft11`, variables in `fs0`–`fs11` saved with `fsd` and restored with
`fld` under the checker's obligation; literals travel as their IEEE bit
pattern through the integer file and `fmv.d.x`/`fmv.w.x` (an f32 NaN-boxed);
`+ - * /` and negation are `fadd`/`fsub`/`fmul`/`fdiv`/`fsgnjn` (nothing is
contracted); comparisons are the quiet `feq`/`flt`/`fle` into an integer
register, `!=` the complement of `feq` and `>`/`>=` with the operands
swapped, so an unordered pair is unequal and neither below nor above, as
C reads them; the precisions convert through `fcvt.d.s`/`fcvt.s.d`,
integers to floats through `fcvt.d.w`/`wu`/`l`/`lu`, `bits` through `fmv`;
`iN_saturating_fM` is `fcvt` with `rtz` (which saturates at the register)
multiplied by the `feq x, x` bit, since the ISA sends NaN to the largest
positive value and the helper to 0, then clamped to a narrow target with
compare-and-branch selects; `iN_trunc_fM` traps on NaN (`feq x, x`) or
outside the target's open interval (`flt`/`fle` against the bounds) before
converting; `sqrt`, `abs`, `min_num`, `max_num`, and `fma` are `fsqrt`,
`fsgnjx`, `fmin`, `fmax`, `fmadd` (the ISA's fmin/fmax are IEEE minNum/
maxNum: the NaN-propagating `min`/`max` and the rounding intrinsics have
no single instruction and stay with C). A call's floating-point result is
readable in `fa0` as its integer result is in `a0` (the checker sees no
callee signature). The freestanding target compiles soft-float, so a
body touching floating point stays with the C backend there, with the
reason. Executed under QEMU against the C backend: the AArch64 lane's
span corpus (an index at the length traps), its array corpus without the
float function (an index at the array's length traps), and its whole float
corpus — fourteen functions including `main`, lowered for
`linux/riscv64` and run on the bare machine under lp64d with the FPU
enabled by the start code, the out-of-range `trunc` trapping. The
guarded element load is proven; the loops are trusted on this lane
(the verifier's loop coupling recognizes the AArch64 shapes — porting
the recognizer is open), floats are trusted as on AArch64.

**RV64 lane, fifth and sixth increments — record locals, tagged unions
(landed).** A declared record type is placed by `semir.RecordLayoutWithSpec`
exactly as the C backend asserts it (the shared placement of the AArch64
lane); a local occupies whole 8-byte frame slots, a literal's fields
evaluate before the name is bound and store at their offsets and widths
(a Bool field as the 4-byte enum through `sw`/`lw`), `p.f` loads at the
field's width and extension (`lw`/`lh`/`lhu`/`lb`/`lbu`/`ld`, `fld`/`flw`),
whole-record copies move the exact bytes in the widest units both offsets
are aligned to (the checker requires every `imm(sp)` access naturally
aligned), nested records and scalar array fields are places in the same
frame. A tagged union is the synthetic record of `semir.TaggedUnionLayout`
— the u32 tag at 0, payloads at the union's offset — built with every byte
zero first, the tag stored, the payload at its field; a `match` loads the
tag once and compares per arm (`li k, tag; bne tag, k, next`), binds a
scalar payload into a variable and a record payload into a fresh copy, and
falls off every unmatched arm into the trap block (the checker proved
exhaustiveness); a scalar scrutinee matches literal patterns the same way;
a record-valued match (a Bool conditional over variants) lands every arm in
one temp. Records and unions do not cross calls on this lane yet — the
psABI's composite rules and the checker's composite binding are the next
increment — so a record parameter, result, or argument leaves the function
to the C backend. Executed under QEMU against the C backend: the AArch64
lane's record corpus (lp64d, for its f64 field) and a union corpus over
locals — variants with scalar and record payloads, value and statement
matches with payload bindings and a wildcard, a record-valued conditional,
a literal-pattern match, reassignment — the latter also through the
AArch64 lane on an arm64 host.

**RV64 lane, seventh increment — spans in functions that call (landed).**
A span or view parameter arrives in its argument pair, which a `call`
clobbers; the lowering of a function that calls parks the base, the raw
length, and the normalized length in three callee-saved registers in the
prologue (`mv sB, aB; mv sL, aL; slli sN, sL, 32; srli sN, sN, 32`, saved
and restored with the variables) and walks the span from there, and a span
parameter passed on to a callee moves its parked pair into consecutive
argument registers. The checker follows the copies with facts that
separate a span's *identity* from a register's *liveness*: `mv rD, aB`
over a bound base makes `rD` a base of the same span, `mv rD, aL` over a
raw length (or a copy of one) a raw length the normalization pair may
read, and a normalized or half-normalized copy names its span by the
bound raw length register — a name, not a live dependency, since a
span's length never changes — so it survives the call that clobbers
`a0`–`a7` and stays across labels when its own register is written once
(a restore `ld sK, imm(sp)` is not a definition the body reads and does
not count; it forgets the register's facts instead). What does not
survive: the facts of every caller-saved register at a call (a pair
parked there is gone — reading the callee's result in `a0` as a base is
refused), and a clobbered raw register normalizes nothing further
(`rawDead`), so `slli t, a1, 32` after a call proves no length.
`TestRV64SpanMemoryChecker`: the parked pair walked after a call is
accepted; the bound base after a call and a clobbered raw length
normalized are refused. Executed under QEMU against the C backend: the
AArch64 lane's span-call corpus — a view forwarded twice with `len` read
after the calls, a store loop calling a helper for every element, two
views parked in six callee-saved registers with a leaf called before and
inside the loop.

**RV64 lane, eighth increment — records and unions across the call
boundary (landed).** The LP64 psABI's integer calling convention, as the
C compiler applies it: a record or union of up to 16 bytes travels as
`ceil(size/8)` consecutive argument registers, each an 8-byte chunk of its
memory image (`Point {x: i32, y: i32}` is one, `Pair {lo, hi: u64}` two),
a larger one by reference to a copy the caller owns; a result of up to 16
bytes comes back in `a0` (and `a1`), a larger one is written into the area
whose address the caller passes as a *hidden first argument* in `a0`, the
declared parameters following in `a1`… (where AAPCS64 spends `x8`). The
lowering stores a parameter's chunks into its record local in the
prologue (or copies the referenced record in, whole words then a 4/2/1
tail), loads a record argument's chunks from its local (or copies it into
a fresh temp and passes `addi aN, sp, off`), places a record result by
loading its chunks into `a0`/`a1` or copying into the area through its
address parked in a callee-saved register (a call clobbers `a0`), and
stores a callee's chunks into the temp that receives them. Records with
floating-point fields stay with the C backend (the hardware floating-point
convention passes them in `fa` registers; the AArch64 lane refuses HFAs the
same way). The checker's contract gained the composite rules: a record
parameter binds `aN` (or `aN, aN+1` for two chunks; a by-reference one
`aN` alone, which becomes a readable region of the record's size), a
two-chunk result may write `a1` and must before `ret`, the hidden result
pointer binds `a0` as a writable region and shifts the parameters, a
region in a register written once survives labels and calls (the parked
area), `mv` copies a region, and `a1` is readable after a call exactly
when the backend recorded the callee as returning two chunks
(`asm.Function.TwoChunkResults`, from the program's signatures — the
checker sees no callee signature; after any other call `a1` stays dead).
`TestRV64CheckerComposites`: one and two chunks in and out, a by-reference
read, the result area written, a two-chunk callee's `a1` read; refused: a
two-chunk record bound alone and the converse, a second chunk not
written, a store through the reference, accesses past the reference and
past the result area, `a1` after an unknown callee. Executed under QEMU
against the C backend: the AArch64 lane's record-ABI corpus (one- and
two-chunk records in and out, a 24-byte record in by reference and out
through the hidden pointer, a record argument that is a call's result, a
record result chosen by a condition) and its union corpus (unions as
parameters and results, matched by the caller on the call itself), every
function lowered natively.

**RV64 lane, ninth increment — the loop recognizer (landed).** The
verifier's loop recognizer (§8) admits this lane's shapes: an exit test
whose branch is preceded by one data-processing instruction setting up a
comparison operand (`sext.w t0, len` or `li t0, k` — the ISA compares in
the branch, so the native backend spells the exit that way), `ebreak` as
the trap block a guard inside the body branches to, a byte element
addressed by the unscaled index, and the setup register dropped from the
loop-carried set (it holds no value the loop carries). The coupling
already knew the lane's widenings (a 64-bit register carrying a 32-bit Oak
variable zero- or sign-extended). With that, the native backend's RV64
loops are proven as the AArch64 ones are: `sum`, `byte_total`, and
`count_down` couple inductively (`acc↔s1, i↔s2` under `i ≤ len(v)`), the
guarded element load `at` is proven, and `fact` agrees on every witness
(its 64-bit product's continue-condition proof exceeds the budget on both
lanes). Loops with `break` (an unconditional jump out of the body) and
bodies addressing owned arrays through a frame address stay trusted on
both lanes. `OAK_VERIFY_TRACE=1` prints each failed coupling attempt with
the two sides' terms.

**RV64 lane, tenth increment — the fixed vectors (landed 2026-09-14;
`nativegen/rv64_simd.go`).** The native backend lowers `simd.U8x16`/
`U16x8`/`U32x4`/`U64x2` on this lane when the processor carries V
(`93-simd.md` §1.4 "The RV64 lane"): one LMUL=1 register per vector under
a `vsetivli` the lowering emits before every vector instruction group,
`v8`–`v15` the operand stack, sixteen-byte frame slots for locals and
call spills. The checker gains what the lowering needs. **The slack
guard**: `li k, K; bltu len, k, trap` proves `len ≥ K` (the span's minimum
length, as before); `sub t, len, k` (or `addi t, len, -K`) under that
minimum records `t = len − K` (`deriveSlack` — the subtraction cannot
wrap); `bltu t, idx, trap` then records `idx + K ≤ len` on the
fall-through (an index fact with slack K, `Oak.RiscV.slack_guard`); the
element address `base + (idx << s)` formed from it is a region K lanes
deep, and a vector access through it with an immediate AVL at most K is
in bounds (`slack_access_in_bounds`, `slack_vector_in_bounds`). A slack
narrower than the AVL is refused. **Frame vectors**: a vector access
through a frame address (`addi t, sp, off`) with an immediate AVL of K
elements is admitted when the K·SEW bytes lie inside the declared frame
at an aligned entry-relative address (`frame_vector_in_bounds`); a
register AVL through the frame is refused. **The table** gains
`vssubu.vv`, `vsrl.vx`, `vmslt.vx`, `vmsltu.vx`, `vrgather.vv`,
`vslideup.vi`, and `vslidedown.vi` (208 encodings, GNU as agreement for
each, masked and unmasked); the gather's and the slides' destinations
must not overlap their sources (RVV 1.0 §16.3, §16.4, fail-closed), and
the less-than masks are single registers like the other comparisons. The
differentials carry `vslack` — the four elements at a guarded index summed,
or zero when the span is too short — under QEMU and Sail against Go. The
units are checked and trusted: the RV64 verifier's terms do not yet reach
the vector file.

**RV64 lane, eleventh increment — the float vectors (landed 2026-09-14;
`nativegen/rv64_simd.go`).** `simd.F32x4`/`F64x2` lower on this lane under
`e32`/`e64` configurations on a hard-float processor with V (`93-simd.md`
§1.2a): `splat` → `vfmv.v.f`; `add`/`sub`/`mul`/`div` → `vfadd`/`vfsub`/
`vfmul`/`vfdiv .vv`; `fma` → `vfmacc.vv` into the addend's register (one
rounding); `sqrt` → `vfsqrt.v`; `neg`/`abs` → `vfsgnjn`/`vfsgnjx .vv` of a
value with itself; `min`/`max` → `vfmin`/`vfmax .vv` (IEEE minimumNumber/
maximumNumber: `-0.0` below `+0.0`, a NaN operand suppressed) with the
catalog's NaN propagation restored lane by lane — `vmfne.vv v0, x, x`
marks `x`'s NaN lanes and `vmerge.vvm` puts `x` back there, for each
operand (`Oak.Simd.rvvMinMax`, `rvvMinMax_nan`, `rvvMinMax_numbers`);
`extract` at a literal lane → `vslidedown.vi` then `vfmv.f.s`; `insert`
at a literal lane → `vid.v`, `vmseq.vx` against the lane, `vfmerge.vfm`;
`reduce_add` → the specification's pairwise tree `(l0 + l1) + (l2 + l3)`
as two slide-and-add steps, `t = x + slide(x, 1)` then `(t + slide(t,
2))[0]` (`Oak.Simd.rvv_reduce4`, `rvv_reduce2`; the slides read the
register's tail past `vl` into lanes the result never reads), never
`vfredosum`'s sequential fold; loads and stores through `[]f32`/`[*]f64`
spans under the slack guard and through frame addresses as the integer
vectors. **The table** gains `vfdiv.vv`, `vfsqrt.v`, `vfmin.vv`,
`vfmax.vv`, `vfsgnjn.vv`, `vfsgnjx.vv`, `vmfne.vv`, `vid.v`, `vmseq.vx`,
and `vfmerge.vfm` (218 encodings, GNU as agreement for each, masked and
unmasked); the float forms need `e32`/`e64`, `vmfne.vv`'s and `vmseq.vx`'s
destinations are single mask registers, `vfmerge.vfm` takes its mask
from `v0` like `vmerge.vvm`. The differentials carry `vfpair` — four `u32`
elements converted, divided by `k`, negated and made absolute, rooted,
the NaN-propagating minimum against `1.0`, `2.0` inserted at lane 1, and
the pairwise tree — under QEMU and Sail against Go's `float32`
arithmetic; the float corpus (`compiler/e2e_native_rv64_float_simd_test.go`)
runs under QEMU at VLEN 128 and 256 beside the C backend. Left to the C
backend on this lane: vectors in signatures (the LP64 lane-array
contract; an `_rvv_abi` entry with a converting shim is the design, as
the AArch64 lane's `_neon_abi`), records or arrays of vectors, a
non-literal shift, `prev`, `extract`, or `insert` count, and the
ctz/popcount helpers.

**RV64 lane, twelfth increment — vectors across the call boundary (landed
2026-09-14; `nativegen/rv64.go`, `codegen/codegen.go`).** A function whose
signature carries a fixed vector lowers on the RV64 lane under the RVV
psABI's vector calling convention: its native entry is the Oak name
suffixed `_rvv_abi` (`asm.VectorEntrySuffix`, the AArch64 lane's
`_neon_abi`), vector parameters arrive in `v8`–`v23` in declaration order
— a file of their own beside `a0`–`a7` and `fa0`–`fa7`
(`Oak.RiscV.lp64dBinding` with the vector kind, `lp64dBinding_vector`,
`vectorArgReg_within`, and distinct registers decided for every list of
up to six parameters over the three files) — and a vector result leaves
in `v8`. The generator binds each vector parameter whole and stores it to
its frame slot in the prologue, moves a vector result to `v8` (`vor.vv`
over the whole register), and at a call spills every live vector
(the operand stack `v8`–`v15` is the argument file) before reloading the
vector arguments from their slots straight into `v8`, `v9`, …, copying a
vector result out of `v8` into a fresh register before the spills reload;
a call that passes or receives a vector clobbers `v16`–`v23` too. The C
backend's lane-array struct crosses a C call in the integer registers,
so the C emitter defines the Oak name as a converting shim over the entry
under `defined(__riscv_vector)`: each vector argument is
`__riscv_vle{8,16,32,64}_v_*m1( arg.lanes, lanes )`, the entry's
prototype spells `vuint8m1_t`/`vfloat32m1_t` parameters and result (the
compiler's vector calling convention for such prototypes: `v8`–`v23`, a
result in `v8`, every vector register caller-saved), and a vector result
is stored back with `__riscv_vse*`; the Oak fallback body serves where
the entry's types do not (no V). The checker binds `bind v8 = a` in
declaration order (v8–v23; a wrong register, an integer register, or an
unbound parameter is a finding), a bound register is readable on entry,
a fixed-vector result must be written to `v8` before `ret`, and `v8` is
readable after a call as `a0` and `fa0` are. The verifier binds the
lanes `p[k]` into the parameter's register, reads a vector result from
`v8` one 64-bit half at a time (the AArch64 lane's `v0`), and takes a
vector-contract callee at its Oak body through the suffixed entry name
— vector arguments read from `v8`–`v23`, the callee's lanes written to
`v8`, the vector file and configuration forgotten across the call — so
`doubled_mask` and `scaled` are proven through their calls to
`double_it_rvv_abi` and `scale_rvv_abi`, which are proven on both
halves (`compiler/e2e_native_rv64_simd_test.go`,
`compiler/e2e_native_rv64_float_simd_test.go`, exit 42 under QEMU with V
at VLEN 128 and 256 and under the C backend alone;
`asm/rv64_vector_test.go`, `asm/rv64_verify_vector_test.go`). With this
the RV64 lane lowers every function of the AArch64 simd corpora but the
`ctz`/`popcount` helpers (no Zbb), and the two lanes' native backends
stand at parity on the fixed vectors.

**RV64 lane, thirteenth increment — IEEE `min`/`max` (2026-09-14).** Oak's
`min`/`max` (754-2019 minimum/maximum: a NaN operand yields NaN, `-0.0`
below `+0.0`) had no single F/D instruction on RISC-V — `fmin`/`fmax` are
the number-selecting minNum/maxNum — and stayed with the C backend. They
now lower as `fmin`/`fmax` behind two NaN tests (`rvMinMax`: `feq` of each
operand with itself is false exactly on a NaN, which is then kept as the
result), the scalar form of the mask merge the vector lowering uses. The
verifier proves both against the Oak body up to the NaN payload (`least`,
`most` in the shared float corpus, `compiler/e2e_native_float_test.go`,
proven on both lanes), and the AArch64 lane's `fmin`/`fmax` stay the one
instruction they were.

**Executables linked by the Oak assembler (landed; `asm/executable.go`,
`oak build -link oak`).** A program whose every body the native backend
lowered links into a final ELF64 executable here, with no system linker
and no C toolchain: `Compilation.EmitExecutable` refuses — naming the
functions — unless every Oak function with a body was lowered natively
(and the program declares `main`, no globals, and no extern bindings: a
natively linked program has no C to provide them), then encodes the
functions and lays them out after a `_start` stub at the target's load
address (0x10000 on Linux; the start of RAM on the freestanding boards,
0x80000000 for RISC-V's virt machine, 0x40000000 for AArch64's), resolves
the calls between them — what the object writer would have handed a
linker as relocations — by patching the words with range checks
(`call26`/`jump26`/`condbr19` immediates on AArch64, the `auipc`/`jalr`
pair of `call` on RV64 with the high part rounded so the low part is a
signed 12-bit remainder), and writes one read-and-execute segment holding
the text at the load address itself (so the stub is the first word there:
the RISC-V virt board's reset vector jumps to the start of RAM, not to
the ELF entry) with `.symtab`, `.strtab`, and `.shstrtab` for tools. Every
offset and count is computed from the bytes and checked; a relocation
kind the writer does not resolve, an undefined symbol, or a branch out of
range is an error, never a silently wrong word. The `_start` stub is
`.oakasm` text assembled by this package's own parser and encoder — the
program's whole runtime: on Linux it calls the entry and leaves through
the `exit` system call with its result (`svc #0` / `ecall`); on the
freestanding boards it sets the stack pointer, calls the entry, and
reports the result to the machine so an emulator exits with the program's
code — the sifive_test finisher on RISC-V's virt (PASS, or FAIL carrying
the code), semihosting `SYS_EXIT` with `ADP_Stopped_ApplicationExit` and
the code on AArch64's (`hlt #0xf000`, now in the v1 table as a trap). A
failed guard traps (`brk`/`ebreak`) with no handler: the machine stops
there. Checked (`asm/executable_test.go`): the ELF parses, the entry is
the load address, every function is a symbol, and the stub's decoded call
lands on `oak_main`. Executed (`compiler/e2e_native_exec_test.go`): the
integer, span-call, array, record-ABI, union, and second integer corpora
linked for `freestanding/riscv64` and `freestanding/arm64` run under
`qemu-system-riscv64 -M virt` and `qemu-system-aarch64 -M virt
-semihosting-config` and exit with the programs' results, natively on both
lanes; the Linux executables run under user-mode QEMU where it is
installed (the CI cross-targets job); a program with a body outside the
subset is refused by name. This is the first Oak program to reach a
binary with no code but Oak's own: the lowering, the checking, the
encoding, and the linking are the compiler's. What remains for
self-hosting: the runtime the C shell still provides for the rest of the
language (strings, the assertion message, the host boundary) as Oak or
asm units, and the compiler itself in Oak.

**Constant top-level bindings.** A body's read of a constant integer
top-level binding (never assigned or addressed, a constant initializer;
`90-backend.md` §8a's `static const`) reaches the native generator and the
verifier as the typed literal `T(init)` on a copy of the body, so
`page_size` and `entries` cost nothing and leave nothing to the C backend;
the emitted C keeps the constant (`compiler/native_bodies.go`).

**Scratch overflow.** Expressions evaluate in x9–x15; when all seven are
live the generator takes x16 and x17 in a function that makes no call,
then the next unclaimed callee-saved registers (counted with the locals,
saved by the prologue, restored by the epilogue, declared as clobbers), so
a deep expression lowers rather than falling back (the OS pilot's N6).
Spilling to the frame is the step after this pool.

**Large elements.** A span or array element wider than 65 536 bytes is
addressed with its stride built as `movz` then `movk` before the `umaddl`,
and a field past 4 095 bytes into it through `add xF, xE, #hi, lsl #12`
and a small remainder in the operand; the checker keeps the stride's
constant fact through the `movk` and narrows the element region through
the shifted add — and through a second add in place (`add xA, xA, #48`),
reading the region the source held before the write (the OS pilot's N2,
a 409 600-byte regime, and N8's field at 393 264 bytes).

**Array fields of elements, read anywhere.** `pool[i].f[j]` — an owned
array inside a record element of a span, view, or array — is addressed
once, when the access is lowered: the element idiom, then the field
offset through `add`, then the constant guard `cmp wJ, #N; b.hs trap` and
the scaled load. The generator's type queries resolve the array by its
declared layout without emitting code, so the same read repeated, inside
a comparison, or in nested `?` arms costs one element address per read
and no scratch register between reads (the OS pilot's N4). Through a
view the field is readable and a store into it is refused.
When the index or the stored value calls a program function, the call is
evaluated before the place: a `bl` clobbers the scratch registers and,
to the checker, every fact about them, so an element address computed
first would return from its spill slot without provenance (the OS
pilot's N8, `s[dom].pages[cell(i, j)]`); the guard and the region
bounds are unchanged.

**Package globals.** A mutable top-level scalar (`st: u32 = u32(0)`,
assigned by some function) is addressed storage on the AArch64 lane: the
body names its cell as `adrp xA, G` then `add xA, xA, :lo12:G` and
reads or writes it with one `ldr`/`str` at the scalar's width (a `Bool`
is the C backend's 4-byte cell). The checker follows the pair — `adrp`
records the page of a global the function declares in `Function.Globals`
and refuses any other symbol, the `add :lo12:` over that page records the
address, both facts die with a write to the register and at a call — and
admits exactly `[xA]` at the width: an offset, an index, a pair, or a
narrower or wider access is refused. The verifier reads the cell as the
parameter `global:G`, the value it holds on entry, and carries every store
as the cell's new value along the path (merged at a fork like a result,
a cell written on one side meeting its entry value on the other); the
verdict compares the result and then every cell either side writes, and a
unit function that only writes state is proven in its cells alone. A
`Bool` cell is one bit, zero-extended into its word. The cells thread through
calls: a callee's summary starts from the cells as the caller's path
holds them and its writes return to the path, a unit callee is
summarized for its writes alone, and on the Oak side the inlined callee
shares the caller's cell locals; only state written around a
data-dependent loop stays trusted. The C emitter gives
an addressed global external linkage under the assembler label
`oak_0g_G` (a digit after the prefix, which no function's mangled name
can produce), the symbol the companion object's `adrp`/`add` relocations
(PAGE21/PAGEOFF12 on Mach-O, ADR_PREL_PG_HI21/ADD_ABS_LO12_NC on ELF)
name; the inline-asm mode spells the pair through `OAK_ASM_PAGE` and
`OAK_ASM_PAGEOFF`. A top-level record, or an array some statement writes
(an unwritten array is a constant table, above), is an aggregate global
(the OS pilot's N9): the same `adrp`/`add` pair names it and the body
holds it as a record or array place at that address — a field at its
offset, an element of an array field under the constant guard, an
element of an array of records through the scaled add or `umaddl` from
the field's base — while the checker reads the `add :lo12:` of an
aggregate as a writable region of the aggregate's size, bounds every
field offset inside it, and derives element regions under the guard as
it does for a frame array. The verifier leaves a body that reads or
writes an aggregate global trusted. Constant globals keep folding (above). The rv64 lane
spells the address as `la rd, G` (auipc then addi, relocated as
`R_RISCV_PCREL_HI20` and `PCREL_LO12_I`) and reads or writes the cell with
one `lw`/`sw` (or the width's load and store); its checker admits the
whole cell at offset 0 alone, and its verifier reads and writes the same
cells (the OS pilot's N3).

**Atomics.** The builtins of `65-machine-memory.md` lower on the AArch64
lane when the cell is reached through a writable span (§7a there): the
element address as a region, `ldar`/`stlr` and their narrow forms,
`dmb`, and the `ldxr`/`ldaxr` … `stxr`/`stlxr` loop for the
read-modify-writes. The checker admits the exclusive store through the
element region; the verifier reads the acquire and exclusive loads as the
element and models an atomic load as the cell's read, so straight-line
atomic reads verify while writers and retry loops are trusted against
the C oracle. The rv64 lane leaves atomics to the C backend.

**Instruction functions on the native lane (landed).** The machine
library's calls lower to the instructions they name, through the
assembler's own parser (`asm.ParseInstructionLine`), so the spelling the
checker and the encoder see is the units': `arm64.read_X()` is `mrs` and
`arm64.write_X(v)` is `msr` over the same catalog the C backend's helpers
come from (`semir/sysreg.go`, the name lowercased into the encoder's
table), `dmb`/`dsb` with their scope and `isb` for the barriers, the
event-control instructions (`msr daifset, #2`, `wfi`, `wfe`, `sev`),
`rev`/`rbit`/`clz` for the scalar functions (which the verifier proves as
the instruction terms it already knows), and a control transfer `eret_x0(v)`
as `mov x0, v` then `eret`, the end of a `never` function (which has no
epilogue and no `ret`). A body using a system instruction carries the
checker's `system` capability, so the checker's access-direction table
judges every register access as it judges a unit's; an instruction
function is an instruction, not a call, so it neither saves `x30` nor
parks a span. Executed (`compiler/e2e_native_instructions_test.go`):
`cntvct_el0`/`cntfrq_el0` reads, barriers, and the scalar functions on an
arm64 host; the hypervisor adapter's EL2 register program (the DAIF
mask, the `hcr`/`vttbr`/`vtcr`/`sp_el1`/`elr`/`spsr` writes, `isb`, and
an `eret_x0` entry) lowers, is admitted, and encodes for
`freestanding/arm64` — the bodies that kept the pilot's modules in C.

**Freestanding modules realized natively (landed).** `oak build -target
freestanding/arm64 -native -asm native` produces the one relocatable
object the build promises: the C compiles to its object and the driver's
partial link (`-r`) joins it with the Oak companion object, so the pilot
links one file as before while some bodies stay with C. `-link oak` on a
freestanding target writes the Oak object alone (`EmitNativeObject`: every
body native, no globals, no extern bindings, `main` not required — a
module exports its `pub` functions); `-link oak-image` writes the
standalone image with the start stub; on Linux `-link oak` is the static
executable. Checked (`compiler/e2e_native_object_test.go`): the native
object of the integer corpus for both lanes with every function a symbol,
the refusal by name, and the partially linked mixed module.

**Check elision under the checker's own facts (landed, AArch64 lane).**
An element access the typechecker proved in range (`IndexProven`, the
extent facts of `50-borrowing.md`) is lowered without its guard, reading
the index from the loop variable's own callee-saved register — the
register the loop's exit test compared — so the fact that test left on
the path is what admits the access; the seam checker then admits or
refuses the body, and on refusal the compiler lowers it again with every
guard (`compiler/native_bodies.go`; the diagnostic names the finding).
The optimizer never decides safety: the elision is only what the checker
already knows, and its refusal is the fallback. The span sum now has one
compare, the loop's exit test, before its load (`ldr w10, [x0, w20, uxtw
#2]`), and the verifier still proves it. On the RV64 lane the exit test
compares canonical (sign-extended) values while the guard fact needs the
zero-extended index, so its guards stay until the index representation
changes; the C backend elides through `IndexProven` as before.

**The whole standard library through the checker (2026-09-13).** Running
the native backend over every function a stdlib-bearing program carries
(`examples/stdlib_builder.oak`, some six hundred bodies) found the seam
checker refusing 68 lowerings on the AArch64 lane and 165 on the RV64 lane,
and the verifier refuting three — each a fail-closed rejection of the
whole build, none a wrong binary. The causes, now closed: (1) the verifier
read a Bool field at the start of a copied 8-byte word as zero — a 1-bit
leaf rounded to zero bytes fell out of the window — and refuted the
library's correct `!parsed.scheme.present` (`recordBytes`); (2) both lanes
wrote the result register inside each arm of a result conditional, and
the checker, which is linear, then forgot the parameters' span and record
facts for the arms after it — arms now meet in one scratch register (a
frame temporary for a record result) and `x0`/`a0` is written once at the
join (`resultInto`, `resultRecordInto`); (3) a scratch register allocated
for a value not yet computed was spilled around a call, a read the
checker knows is uninitialized — only defined registers spill
(`markDefined`; every emission path goes through it); (4) the RV64
checker dropped a by-reference record parameter's region at its first
guard-forgetting point because the register is written again by a later
arm — a parameter region now holds until that register is actually
written on the path; (5) the AArch64 checker refused the write of `x1`
for a two-chunk record result while requiring it at `ret` — the second
chunk is a result register. After: the RV64 lane admits every lowering
(the build succeeds), the AArch64 lane refuses two (`text_fold_next`,
`utf8_to_utf16_bytes`: a span base copied into another register across a
label, the checker's remaining flow-insensitivity), and the verdicts over
the lowered bodies are 92 proven, 5 witnessed, 304 trusted on AArch64 and
38, 3, 295 on RV64, with `bl` the dominant trusted reason (the verifier
does not summarize calls). Pinned: `compiler/e2e_native_bool_field_test.go`;
the tally is `docs/notes/verification-chain-2026-09.md`.

**Call summaries (2026-09-13).** A call was the largest reason a lowered
body stayed trusted (`bl` in 159 of 304 AArch64 bodies, `call` in 119 of
295 on RV64). The verifier now takes a call to a program function with a
scalar signature at the callee's Oak body (`asm.Function.Callees`, set by
the native backend from the program): the arguments are the contract
registers' terms at the parameters' widths, the callee's body lowers to a
term over them — its own calls the same way, recursion refused — and the
result register receives the term in the lane's canonical form: on RV64
widened as the psABI does; on AArch64 with the bits above the result's
width a fresh unknown, since AAPCS64 leaves them unspecified (above the
low word for a Bool, the C enum). Every caller-saved register and the
flags are forgotten, as after any call. The caller's verdict is then
relative to the callee's Oak body, which the callee's own verdict covers,
and it names the callees so taken (`proven … (callees taken at their Oak
bodies: inc)`); the Oak side inlines the same calls (`inlineCall`, the
theorem decider's rule). The model found a real gap on landing: the
AArch64 lane read a narrow call result (`u8`, `u16`) straight from `w0`,
relying on the callee's zero-extension, which the ABI does not promise —
the caller now normalizes a narrow result as it normalizes a narrow
parameter, and the summary's fresh upper bits are what holds it to that.
A call the summary cannot take — no callee known, a span or record in the
signature, a body outside the term language, a data-dependent loop —
leaves the body trusted with the reason. Pinned:
`asm/call_summary_test.go` (proven, refuted, opaque, span parameter; both
lanes), `compiler/e2e_native_call_summary_test.go`.

**The last two refusals (2026-09-13).** `text_fold_next` computed an
element address (`umaddl` over a span of records), held it across the
call that produced the value, spilled and reloaded it — and the checker
cannot carry a region through a spill, so the store was refused. Both
lanes now evaluate a calling value before its place (`placeStore`: the
place is computed once for its type and rolled back, then again after the
value). `utf8_to_utf16_bytes` parked a frame address (`add x27, sp, #168`)
and a loop bound (`movz w28, #2`) in callee-saved registers and compared
the index against the register; the checker forgot both at the call and
read the compare as a register guard. A frame address or a constant in a
callee-saved register now survives a call (the callee preserves the
register and cannot touch this frame; a later write still forgets it), a
constant is part of the label fixpoint's state (kept where every
predecessor agrees), and a compare against a register holding a known
constant is the constant guard it is (`asm/check_test.go`, "guard against
a register holding a constant"). With these, `oak build -native` of the
stdlib-bearing program succeeds on both lanes: every body the backend
lowers is admitted by the checker.

**The encoder against the Sail encoder (2026-09-13).** The Sail RISC-V
model's `encdec` mapping is the ISA's own statement of an instruction's
bits, and its Lean export spells the forward direction as one clause per
instruction form. `Oak.RiscV.Enc` restates the encoder's placement
(`placeField`, `encode`: the fixed bits, each field masked to its width and
shifted to its low bit, exactly `encodeRV64Instruction`) and the table
entries the verifier decides — thirty mnemonics across the R, RW, I,
shift-immediate, and B forms, generated from `asm/rv64_encodings_gen.go`
by `asm/rv64_encoding_lean_test.go`, which holds the Lean block to the
table. `spec/lean-sail/OakSailBridge/Encoding.lean` states, for every
register number, immediate, or branch offset, that the word Oak writes for
a mnemonic is `encdec_forwards` of the instruction it spells — so the
machine words follow from the specification, and, `encdec` being a
bijection, the decoder reads them back. The thirty statements build
against the export (2026-09-14; sail-riscv 497209b9, see above). Two
shapes mattered: `encdec_forwards` is a 232-arm match, which `simp` cannot
unfold within the heartbeat budget, so each theorem `unfold`s it and
rewrites the concrete arm; and the model's branch arm is defined only for
even offsets (it guards on bit 0 and fails the match otherwise), so the
branch theorems carry the hypothesis `delta &&& 1 = 0`, which Oak's
B-form offsets — differences of instruction addresses — satisfy by
construction.

**Statement conditionals and `i32` indices (2026-09-13).** Three statement
shapes the standard library uses stayed with the C backend on both lanes:
a conditional with no false arm in statement position (`c ? { … }`), a
chained conditional (`a ? { … } | b ? { … } | { … }`) as a statement, and
on RV64 an `i32` element index. The lanes lower the first two as the
branch structure they are (`statementConditional`, `lowerArm`: an absent
arm falls through, a chained arm is the next test), and the verifier's
lowering takes the same shapes (`asm/verify.go`, `statementConditional`).
An `i32` index is kept in its canonical sign-extended form and guarded as
an unsigned quantity: a negative index is a huge unsigned value the guard
traps, exactly as the C backend's cast does. The RV64 prologue rule for
functions that park span parameters in callee-saved registers without
frame variables is fixed en route (the saves need a frame). Pinned by
`compiler/e2e_native_statement_shapes_test.go`.

**Constant tables (2026-09-13).** A top-level array of fixed-width
integers with a literal initializer that no statement writes — no
assignment, no element assignment, no mutable borrow — is a constant
table (`nativegen.GlobalArrayOf`, `compiler.nativeGlobalArrays`). Its
bytes are a data symbol of the object (`asm.DataSymbol`, `data_<name>`
under the backend's C symbol prefix) placed in a read-only data section
after the text: `.rodata` in ELF, `__TEXT,__const` in Mach-O, and in the
executable the tail of the one loadable segment. A body takes the table's
address with one pseudo-instruction per lane — `adrl xR, sym` (`adrp` +
`add`, relocation kind `adrl21`: `R_AARCH64_ADR_PREL_PG_HI21` and
`ADD_ABS_LO12_NC`, or the Mach-O `PAGE21`/`PAGEOFF12` pair) and `la rd,
sym` (`auipc` + `addi`, kind `riscv_pcrel`: `R_RISCV_PCREL_HI20` and
`PCREL_LO12_I` against a local label) — and reads elements through it as
it reads a record's array: a literal index inside the table is a plain
offset, any other goes under the constant guard `cmp wI, #N; b.hs trap`
(a bound past the compare immediate is materialized in a register first,
which the checker reads as the same constant guard) or `li; bgeu`. The
checkers know the address as a read-only region of the table's size
(`asm.Function.Tables`): an element region derives from it as from a
frame array (`elementRegion`, `deriveTableRegion`), a store through it
is refused, a symbol the program does not declare is refused. A view of
a table (`view(&T)`) is a span whose base is the table's address and
whose length is its element count; `span(&T)` is refused, the table
being read-only. The verifier reads a table as the span its Oak name
denotes (below, "Table reads"). A constant scalar global is
folded into every body that reads it, so a natively linked program admits
both kinds of global (`allNative`). On the stdlib-bearing program the
tables lowered every body that indexed a global on both lanes with no
checker refusal, and `oak build -link oak` moved from refusing the first
global to naming the bodies still with the C backend (36 on AArch64, 120
on RV64). Pinned: `compiler/e2e_native_tables_test.go` (both lanes
native; the C build agrees; the freestanding executables carry the bytes
and run under QEMU), `asm/isa_test.go` (the `adrl` sample), the object
and executable writers' tests.

**The verified profile (2026-09-14).** `oak build -verified` holds a
program to the verified native profile: every body the program reaches is
lowered by the native backend and carries a proven verdict — none
witnessed, none trusted, none left to the C backend — and the Oak
assembler links it alone (`-link oak` is implied). The theorem such a
build stands for is the chain of this section: each body's Oak semantics
(the extraction, `Oak.LoweringRefinement`) equals the emitted assembly's
(`Oak.AssemblerSemantics`, `Oak.ArmASL`, the Sail bridges) under the
checker's memory discipline; what the chain does not yet cover is stated
where it is trusted (the checker facts and the writers in STATUS, the
RV64 export in the audit note). A program the profile refuses gets the
burn-down list: every reason with the bodies it holds back, largest
first, so the distance to the profile is a number that moves
(`Compilation.verifiedProfile`, `SemanticModel.NativeVerdicts`,
`NativeFallbacks`). On the stdlib-bearing program the first list holds
380 bodies on AArch64 and 453 on RV64; the largest reasons are record
results beyond one register chunk, vector or floating-point parameters,
the path budget, table reads (`adrl`/`la`), unit callees, and calls
returning a `Result` — the order in which the verifier grows next.
Pinned: `compiler/e2e_verified_profile_test.go` (a proven program links
on both lanes; a variable shift count is refused with its reason; a body
left to C is refused with its reason).

**Record results of two chunks, aggregate call summaries, unknown frame
bytes (2026-09-14).** The first burn-down of the verified profile. A
record or union result of 9 to 16 bytes comes back in two register chunks
(x0 and x1; a0 and a1) and is verified chunk by chunk: `Verify` runs the
paths once per chunk, each run delivering that chunk's register against
the same chunk packed from the Oak body's aggregate value
(`packAggregateChunk`, the padding masked by `leafMask`), and the verdict
is proof only when both chunks are proven (`(both result chunks)`). A
result past 16 bytes, returned through the area x8 addresses, is still
trusted, now with that reason. A call to a program function returning a
record or a sum type of up to two chunks is summarized like a scalar call:
the callee's body is lowered to its aggregate value over the argument
terms, packed into its chunks, and bound to x0 and x1 (a0 and a1), with
the padding bits fresh unknowns (`callN#padK`) as the ABI leaves them —
so a caller matching on a `Result` a callee returns is proven relative to
the callee's Oak body. A load of frame bytes no store on the path reached
— the padding of a record chunk stored at a narrower width, the payload
of a union variant not constructed — no longer refuses the body: the
bytes are fresh unknowns (`frame#<addr>`) that later loads of the same
byte see again, so a result that never reads them is unaffected and a
result that depends on them is refuted (the body computes from
uninitialized memory), never matched by accident; a witness run still
refuses such a load, since a chosen value could coincide. The RV64
frame model takes the AArch64 lane's byte-granular slots (`storeSlot`,
`loadSlot`): a record chunk stored with `sd` is read back field by field
with `lw` or `lbu`, which had been trusted as "a load whose width differs
from the slot's store". And the RV64 lane binds record and union
parameters as the AArch64 lane does (`bindRV64Params`): up to 16 bytes as
one or two register chunks assembled from the leaves, beyond that by
reference to the caller's copy, a load through which reads the leaf at
its offset — they had been trusted as "vector or non-integer parameters".
On the stdlib-bearing program the proven bodies rose from 115 to 127 on
AArch64 and from 42 to 113 on RV64, with no mismatch and no change in the
C build. Pinned:
`compiler/e2e_native_verdict_aggregates_test.go` (two-chunk results
proven chunk by chunk, a `Result`-returning callee taken at its body, a
one-chunk record parameter's padding, both lanes), `asm/frame_test.go`
(an unstored slot's bytes refute a result that reads them and leave one
that does not).

**Table reads (2026-09-14).** The verifier reads a constant table as a
span named by the table's Oak identifier: `adrl xR, sym` and `la rd, sym`
bind the register to the base `&T` (`asm.Function.Tables` carries the
element width and signedness beside the size, `asm.TableName` the Oak
name), a load through it is the element term `T[k]` — the same select
term the Oak side gives `T[k]`, with functional consistency between
reads — and `len(T)` on the Oak side is the constant element count. The
bytes themselves are not consulted: both sides read the same memory, so
the equivalence is over the same uninterpreted elements, and a witness
run draws them from the fixed element function as it does for a span.
The trusted reason `instruction adrl`/`la` is gone from the tally: the
proven bodies rose to 137 on AArch64 and 120 on RV64. With it, the
layout table a body carries (`Composites`) also spells the result types
of the program's functions, so a summarized call returning a record or
sum type finds its layout. Pinned: `compiler/e2e_native_tables_test.go`
(the table-reading bodies proven on both lanes).

**Span arguments in call summaries; a Bool's cell (2026-09-14).** The
call summary's span aliases (the twenty-ninth increment above) landed
the same day as a second implementation of the same idea, which is
dropped in its favor; what remains of it is a finding: a summarized
`Bool` field's cell is the C enum's whole word, defined 0 or 1 by the
callee, so the summary's padding unknowns must leave it alone
(`definedMask`, over `leafMask`'s single bit). The first tally with
aliased span arguments reported one mismatch (`path_get_esc`) that was
exactly that, and none after. Pinned:
`compiler/e2e_native_verdict_aggregates_test.go` (`head_sum` over
`first_two`).

**Aggregate arguments in call summaries; well-typed union tags
(2026-09-14).** A callee's record or union parameter of up to two chunks
is bound in the summary from its argument registers (`unpackAggregate`,
the inverse of `packAggregateChunk`: each leaf the slice of the chunk at
its offset and width), so `text_decode_ok(result)` and its kind are
taken at their Oak bodies; a parameter past 16 bytes, passed by
reference, is still refused. The layout table a body carries spells the
parameter types of the program's functions as well as their results.
Landing this exposed a latent gap in the decision itself: on the asm side
a union parameter's chunks are assembled with each payload leaf under its
tag (`compositeLeaf.guarded`, since the variants overlap in memory),
while the Oak side binds every payload leaf free; on a tag outside the
variants — an input no well-typed program produces — the asm traps where
the Oak match falls through its last arm, and once a summarized callee
read the payload the two sides disagreed there (`encoding_failure` and
seven more, all the `X_failure` shape). The decision is now over
well-typed inputs: `recordTagDomains` notes every union tag parameter's
variant values, `decideEqual` compares both sides under the condition
that each tag is one of them (`domainCondition`; outside it both sides
are the same zero), and the witness runs skip assignments outside it
(`inDomain`). The lowering's terms are unchanged, so
`Oak.LoweringRefinement`'s transliteration still holds; the assumption is
the decision's, and it is the typing rule of the source. Proven bodies:
149 on AArch64, 132 on RV64, no mismatch. Pinned:
`compiler/e2e_native_verdict_aggregates_test.go` (`check_ok` passing a
sum type to `is_ok`).

**RV64 stores through spans as memories (2026-09-14).** The RV64 lane
records a store through a span base in the path's write log
(`spanStoreRV64`, the address resolved as a load's is: `rv64SpanAddress`
over `&v + K` and `&v + (idx << s)`), so the Oak side's assignments are
compared as memories on RV64 as they have been on AArch64
(`decideEffects`). The trusted reason "a store through a span" is gone
from the RV64 tally: 149 bodies proven on RV64, 151 on AArch64.

**Exit tests that read memory (2026-09-14).** The path budget was the
verified profile's largest reason, and most of it was one shape: a loop
whose exit test reads an element under a guard — `while nd > 0 &&
digits[nd-1] == 48`, `while i < len(text) && text[i] == 32` — which the
recognizer did not take as a loop (its header held only pure register
instructions ending in a branch to the exit label), so the executor
unrolled it until the budget stopped it. The header is now every exit
test from the label to the last branch leaving the loop, and an exit
test may hold an element guard (a branch to the trap block, whose taken
path traps as the Oak side's element read does), the guarded load itself
(a scalar load through a span or table base, read as the executor reads
it), and — the RV64 lane's spelling of `&&` — a forward branch to a label
inside the header, which forks the header's paths (`loopShape.internal`,
`isGuardBranch`, `isHeaderLoad`). The continue condition is then the
disjunction over the header's paths of "this path is taken and no exit
test on it is taken" (`headerCondition`, a small path walk bounded by
`headerPathBudget`); the exit tests' temporaries — a compare operand's
setup, a loaded element, a short-circuit's flag — are scratch, never
paired as loop-carried and unbound past the loop, which generalizes the
one setup register the RV64 lane excused before. An undecided branch at
any header branch, internal or exit, summarizes the loop; a forward
branch after the last exit is the body's own conditional, as before. On
the stdlib-bearing program the path-budget bodies fell from 71 to 43 on
AArch64 and from 58 to 34 on RV64; proven bodies rose to 165 and 158.
Pinned: `compiler/e2e_native_loop_header_loads_test.go` (both shapes,
both lanes, the C build agreeing).

**Calls and spills inside loops (2026-09-14).** With the exit tests
reading memory, the remaining path-budget loops were, almost all of
them, loops that call a program function — in the exit test (`while i <
n && is_space(text[i])`) or in the body (`total = total + weight(t[i])`)
— and the spills the native backend places around such a call. A call
to a program function is now summarized inside the loop as it is outside
(`summarizeCallInLoop`): on the header's paths and on the body's, the
callee's result a term over the iteration's fresh symbols; a callee with
memory effects (stores through spans, package cells) is refused, since
the loop summary carries registers and frame slots, not memories. The
recognizer takes such a call in a header or a body when its target is a
function of the program (`findLoopsIn` knows the callees), and a spill
or reload of the frame in the header too (`isFrameSpill`); the call's
result registers are temporaries, never paired as loop-carried. The
loop-carried frame slots are now tracked at the store's width — a
spilled `w` register is a 4-byte slot (`s<addr>:4`), an `x` register an
8-byte one — where before a narrow store in a body refused the loop, and
the RV64 lane's body runner takes frame memory through the same slot
model instead of refusing it. `OAK_VERIFY_TRACE=1` now also reports
every back edge the recognizer does not take as a loop, with the reason
and the function, which is how these shapes were found. On the
stdlib-bearing program the path-budget bodies fell to 21 on AArch64 and
10 on RV64; what those loops leave behind is now mostly stores through
spans inside loop bodies (23 and 14 bodies), which need the span memory
carried through the summary — the next shape. Pinned:
`compiler/e2e_native_loop_header_loads_test.go` (`skip_blank`, `weigh`:
a `pub` callee in an exit test and in a body, both lanes).

**Span memories through loops (2026-09-14).** A store through a span
inside a data-dependent loop body was the last shape the loop summary
refused, and with the loops themselves recognized it was the largest
reason left after vectors and floats. The write log (`spanWrite`) now
has a marker: from a loop's marker on, a span's contents are the unknown
memory `loop<K>.<span>` — the span as some iteration of loop K sees it,
and as the loop leaves it — whose element at an index is a select over
that name (`memoryAt`). Both sides place the marker at the loop for every
span the body stores through: the asm side finds those spans by a
discovery run of the body whose other traces are undone, the Oak side by
a walk of the body (`spanStoresIn`). The iteration then runs on the
marked memory — its reads see the unknown memory, its stores layer on it
— and each side's loop event records the iteration's stores, each under
the body path it happens on (`loopEvent.writes`). The coupling proof
compares them pairwise (`coupledWrites`): the same spans, the same
number of stores, indices and values proven equal under the coupling and
the body premise, guards equal, an inner loop's marker matched by name.
The memories after the loops are then compared as `decideSpans` compares
them — the final element at a fresh index over the entry memory — under
the coupling and the exit premise; a unit function whose only effect is
the memory takes this path with no result term (its proof is the coupling
alone, with no witness run). This is an induction: equal memories at
entry, iterations proven to store alike on equal state, so the two
unknown memories are one memory. Found on landing: the executor returned
the effects of the state at a loop's exit branch, not of the run past
it, so the marker never reached the comparison. On the stdlib-bearing
program the bodies trusted for a store in a loop body (23 and 14) are
gone; proven bodies rose to 174 on AArch64 and 165 on RV64. Pinned:
`compiler/e2e_native_loop_stores_test.go` (a unit fill, a copy with a
result, a conditional store; both lanes), the `fill` case of
`compiler/e2e_native_span_effects_test.go`, now proven on both lanes.

**The loop proof's budgets (2026-09-14).** Recognizing the loops that
call functions and store through spans made the prover's native build
(the shell test's `OAK_SOLVER_NATIVE=1`) run without end on one body:
`fill_chunk`, nested loops whose bodies call the Lean emitter's large
functions, where the coupling search substituted into and walked the
summarized calls' terms for every one of thousands of candidates. The
loop proof is now bounded three ways, each deterministic: the candidates
its search tries (`loopSearchBudget`), the diagram nodes all of its
implications spend together (`loopProofNodeBudget`, `impliesEqualWithin`
drawing from one `nodeBudget`), and the size of the events' terms it
will search over at all (`loopTermNodeBudget`); past any of them the
verdict is evidence with the budget named. A coupling's description is
built only for the couplings chosen, and an implication whose two sides
are the same term (`equalTerms`, memoized over the DAG) is decided
without a diagram — in `decideEqual` too, after the linear normal form.
The two sides of the loop proof's span memories would otherwise both be
blasted though they are built from the same stores. `OAK_NATIVE_TIMING=1`
prints each body's verification time (`compiler/native_bodies.go`). The
prover's native build: 180 s before this section's loop increments, 265
s after them with the budgets, 330 bodies proven where 294 were, no
mismatch; the standard-library tally keeps its 176 and 167. Found in the
same measurement, in the zero-test rewrite of the vector reductions: the
significant-bits bound walked a term as a tree, exponential over an ite
chain whose arms share subterms, and one body took twenty minutes; it is
memoized over the DAG (`significantBitsMemo`).

**Bool loop variables (2026-09-14).** `valid = false` inside a counted
loop — `text_is_ascii`, `utf16_count`, the searches that set `found` —
left the body witnessed: the Oak variable is one bit, the register holds
it as 0 or 1 in a word, and the coupling paired only variables and
registers of one width (or a 32-bit variable in a 64-bit register). A
1-bit variable now pairs with a 32- or 64-bit general register by
zero-extension (`widen` takes the register's width), the relation
`r = zext(x) + b` as for the widened 32-bit case. On the stdlib-bearing
program the proven bodies rose from 176 to 197 on AArch64 and from 163
to 175 on RV64 — the largest single step of the day — with no mismatch.
What the witnessed verdicts leave now: bodies past the bit-level node
budget, continue conditions and results after loops the coupling does
not prove, and two stores under conditions the proof does not relate.
Pinned: `compiler/e2e_native_loop_bool_test.go` (both lanes).

**The induction's base, and what the loop memory still leaves out
(2026-09-14).** The span memories through loops were an induction with
the step alone: the two markers made the memories at the exit one unknown
memory whatever either side had stored before the loop, so a body whose
asm stored `x + 1` at `v[0]` before a fill loop where Oak stored `x` was
proven. The base is now an obligation of the coupling
(`coupledEntryMemories`): for every marked span, the stores before the
loop over the span's entry memory, at a fresh index, equal on the two
sides under the coupling and — for a nested loop — the parent's body
premise. Alongside: the concrete layer compares the memories the two
runs leave, at every index either side stored, so a wrong store in a
loop body (and a differing store before it) is a mismatch with a concrete
input rather than evidence, and a unit function's loops have witnesses
as a result's do; when the iteration's stores do not pair one for one
(`coupledWrites`), the memories they leave are compared whole at a fresh
index over the loop's unknown memory before the verdict falls to
evidence; and a callee summarized inside a loop body may store through
the caller's spans, its stores joining the iteration's log (a callee
writing package cells stays refused). On the prover the proven count is
unchanged at 354 — no body relied on the gap, and none of the bodies
still evidence pairs differently — and the gap is pinned:
`asm/effects_test.go` `TestVerifyLoopStores` (a fill loop proven, a wrong
body store a mismatch, a result after the loop, a store before the loop
read after it, and the differing store before the loop refuted) and
`compiler/e2e_native_loop_stores_test.go` (a loop storing through a
callee, both lanes).
**Asserts under the verifier (2026-09-14).** A body with an `assert`, or
a call to a unit callee whose body asserts (`text_require`), was trusted:
the Oak lowering refused the assert wherever traps are not tracked, and
the assembler verifier's lowering does not track them — it has no
obligations to prove, since the executor drops a trapping path from its
fork (`brk` delivers no result) and the equivalence is over the inputs
on which every guard holds. An assert is therefore a no-op on the Oak
side of the verifier: the trapping inputs are outside the equivalence on
both sides, exactly as an element guard's or a divisor's are. The
theorem decider's reading (a trap obligation to prove impossible) is
unchanged. Proven bodies rose to 201 on AArch64 and 179 on RV64; the
asserting callees that remain trusted do so for their span arguments,
not their asserts. Pinned: `compiler/e2e_native_assert_callee_test.go`
(a body with an assert, a caller of an asserting unit callee; both
lanes).

**Callees with loops in the call summary (2026-09-14).** A call to a
function whose body has a data-dependent loop (`sb_str`, `px_acc_list`,
the syntax walkers) left the summary at "whose body has a data-dependent
loop". The callee's loop events are now the caller's: the callee's
lowering inside the summary numbers its events after the caller's
(`oakLowering.loopBase`) and nests them under the loop being executed,
its fresh symbols are declared for the verdict, and its markers are
keyed by the caller-rooted span names (`writableSpans` with
`rootContracts`, since the callee's names are aliases). The Oak side
inlines the same body and creates the same events in the same order, so
the coupling pairs them by identity — the same fresh names on both
sides — and the obligations are the callee's own; a witness run inside
the summary takes the caller's concrete span length for the callee's
(`isSpanLength`). On the prover: proven 354 to 362 (`bytes_equal`,
`find_tdecl`, `root_ident`, `taken_inside`, the mark walkers), no
disagreement, the rows identical; the callers of `sb_str` now stop at
its `%` by a data-dependent divisor. The verifier's time is unchanged by
this, but one body, `sat_extend`, went from a fast refusal to 75 seconds
of coupling search under the Bool-variable pairings that landed the same
morning (a `satisfied` flag pairing with every register of the enclosing
loops); the search budget bounds it and the verdict is evidence either
way, and it is the next thing to tighten. Pinned: `asm/effects_test.go`
`TestVerifySummarizedLoops` (a summing callee behind a result and a
filling callee behind a unit caller proven by coupling the callee's
loop; the wrong constant to the callee a mismatch).

**The verdict cache, identity masks, and the coupling's candidates
(2026-09-14).** Three things, found in order. First, the builds were
cached but the verifications were not: every `oak build -native`
re-verified every body. A verdict is a function of what the verifier
reads — the lowered assembly as the checker sees it, the Oak body after
inlining, the bodies of the program functions the body can reach through
calls (the summaries inline them), the program's type, global, and
constant declarations, the record layouts and addressed globals of the
unit, the lane and its stack convention, and the compiler executable
itself — and `compiler/verdict_cache.go` keys a verdict on all of it and
keeps it under `$TMPDIR/oak-verify-cache`. A rebuild of an unchanged
program takes every verdict from the cache; an edit re-verifies the
edited function and the functions that reach it, no other; a changed
compiler (its size and modification time, as the solver caches key)
invalidates everything. The build reports `N of M verdicts from the
verdict cache`; `oak build -verify-fresh` and `OAK_VERIFY_CACHE=0` bypass
it for the full check. `TestVerdictCache` pins the cold build, the warm
build with identical verdicts, the callee change that re-verifies the
callee, its caller, and `main` but not an unrelated body, and the
bypass. On the prover a warm rebuild takes 30 seconds where the cold
build takes over three minutes. Second, a mask of every bit at a term's
width is now the identity in the constructors (`x & 0xFFFFFFFF` at 32
bits is `x`; a truncation of a zero-extension is the extended term), and
`x - x`, `x ^ x`, `x & x`, `x | x` fold when the two sides are the same
term to a small structural depth (two reads of one address are built as
distinct nodes): nine more bodies prove, `fact`'s 64-bit product on RV64
among them, and several proofs close as "the same term on both sides".
Third, the coupling search's candidates: a Bool variable pairs only with
a register whose header holds a 0/1 value (once an outer loop's register
is coupled, the outer variable's declared width decides; an uncoupled
one stays a candidate for the viability pass), and a variable the
iteration changes never pairs with a register the iteration leaves as it
found it, nor the reverse. `sat_extend` — three nested loops over the
SAT arena, the Bool `satisfied` inside — went from 96 seconds of search
to about a minute under this machine's load, still the slowest body by
far, still evidence; what remains there is a genuine pairing (`end` with
a register carrying `mem[l.state_at + 23]`) whose preservation is a
decision over the arena's memory terms, and it is bounded by the loop
proof's budgets. On the prover: proven 362 to 371, no disagreement, the
rows identical. **Found by the cache:** a warm rebuild missed 146 of the
979 verdicts, and the lowered assembly of those bodies differed between
two builds of one source — a register chosen as `w24` in one and `w25`
in the next — because the backend returned dead variables' registers to
its pools in map order (`popScope`, `releaseDead`). The pools are filled
in name order now; two builds produce identical assembly, verdicts, and
objects, and the warm rebuild of the prover takes fifteen seconds with
every verdict from the cache. **A counterexample reads the memory the
diagrams chose.** Integer division became an uninterpreted operation the
same afternoon, and nineteen bodies that divide by a constant the
machine shifts by (`at / 4`, `lit / 2`) were reported as mismatches —
"asm yields 51, Oak yields 51": the diagrams differ under values of the
operation that the operation never takes, and the terms agree on the
input. The bit-level difference is now confirmed by evaluating both
terms on the counterexample's input before it is a mismatch (the
thirty-first increment's rule, landed alongside). For that evaluation to
be the arbiter it must read the memory the diagrams chose, so a
counterexample reports each element read at the index its bits took
with the value its variables took (`v[k]`), and the evaluator reads such
an element from the input before the fixed memory — a compare-exchange
storing the wrong value under a symbolic index stays a mismatch
(`TestVerifyAtomicsCompareExchange`) rather than evaluating equal on the
fixed memory. On the prover the nineteen are evidence, and the native
build, which a mismatch fails, builds again: proven 376.

**The domain conjoined lazily; the coupling without a witness
(2026-09-14).** The trap domain that joined the decision the same
afternoon — the equivalence holds where the machine does not trap, and
where Oak traps on the same guard — wrapped both terms in the domain
before the diagrams saw them, and twenty-seven proofs on the prover fell
to the node budget under the wrapping. The domain is now handled as the
reads' consistency is: checked on every witness input, and conjoined at
the bit level only once a bit differs, since equality everywhere is
equality inside the domain; its own unknowns (a union tag, the operands
of the guard) join the decision's parameters — a parameter the diagrams
were not told of blasted to a constant zero, which made the domain false
and every difference a proof for the length of one test run, and the
blaster now fails closed on such a parameter, as if over budget. And a
body whose loops no concrete input decided within budget (a callee's
loop over a count the memory holds) was left trusted before the
coupling; the coupling is an induction that needs no witness, so the
decision proceeds and the verdict says how many inputs agreed, eighty
bodies among them. On the prover: proven 376 to 391, trusted 513 to 427,
evidence 63 to 134 — most of the new evidence is loops whose carried
record local (`params`) has no register image at the header, and loops
over the node budget — no disagreement, the rows identical.

**A callee's loop pairs by identity; the budgets without a witness
(2026-09-14).** The forty-seven bodies whose loop variable `params` had
"no register image at the header" were the callers of `syn_param_total`
through the call summary: a loop the summary takes from the callee's
Oak body names its variables as the Oak side does (`f`, `params`), and
the coupling read `f` as a register of the RV64 float file and never
offered it. An event a summary derived is marked (`loopEvent.oakDerived`)
and its variables pair by identity alone — the two sides lowered one
body — with no search over the others, no negated relation, and no
register-class reading of a name; a Bool variable is never paired
negated either. With the coupling proceeding without a deciding witness,
the bodies that end in evidence spent minutes under the full budgets
(a search over hopeless pairings that no witness could refute early),
so such a body gets an eighth of the proof's node and search budgets,
and every implication is now bounded by what the proof has left rather
than by its own order's budget; the coupling's valuations evaluate their
terms through the slice evaluator under the witness pass's visit budget.
On the prover: proven 391 to 429 — `type_kind`, `node_word`, the
`syn_*_at` layout accessors, and their callers — no disagreement, the
rows identical; the verifier's share of a cold build is about eight
CPU-minutes, four of them in the seventy-five witness-free bodies that
end in evidence, and a warm build takes it from the cache.

Still to come in this lane:
the sail-riscv bridge's export side (the Lean export as the semantics the
transliteration is checked against). Retried 2026-09-14 with Sail built
from git master (`dba5f00`, still versioned 0.20.2) against sail-riscv
master (`22fad38`): the export generates, and its `Defs.lean` fails as
before — `k_v` unbound at `root_level`, `PTW_Output` out of scope — a
Sail Lean-backend matter, not ours; the theorems stay checked against the
verbatim copies (`Oak.SailRiscVBridge`). The term language and the BDD
blaster carry over unchanged.

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

### 9.x Vectors on the native lane (2026-09-13)

The native backend lowers the fixed vectors (`93-simd.md` §1.4 "The native
backend"): values in the vector register file, one NEON instruction per
operation, loads and stores under the slack guard of §7 — over lanes wider
than a byte through the element address `add xE, xB, wI, uxtw #s`, which
the checker records under the slack guard `wI + K ≤ len` (and `len ≥ K`)
as a region of `K` elements (`elementRegion`, `index_access_lanes`), so
the sixteen-byte `ldr`/`str q` through `xE` is a region access proven
inside the span; the floating-point vectors landed 2026-09-14 (§1.4 of
`93-simd.md`). A function whose
signature carries a vector follows the vector register contract this
chapter's `contractClass` already assigns to `simd.*` (v0–v7), which the C
backend's lane-array struct does not (AAPCS64 passes a sixteen-byte
struct of bytes in two general registers). So such a function's native
entry is encoded under its name suffixed `_neon_abi`, native callers
reach it there, and the C emitter defines the Oak name as a converting
shim over the entry (`vld1q`/`vst1q` around the call) that the C compiler
inlines. A natively lowered function that passes vectors to a callee the
C backend realizes is itself left to the C backend, to a fixpoint
(`compiler/native_bodies.go`), so no call crosses the two contracts
unconverted. The suffix is reserved the way `__` is: no Oak identifier
ends in it.

### 9.y Vector helpers expanded, locals released at their last use (2026-09-13)

A SIMD kernel in Oak is a tree of small functions whose signatures carry
vectors — the UTF-8 validator's `check_blocks` → `check_block` →
`special_cases` — which the C compiler flattens into one loop with every
vector in a register. Through native calls the same tree spills its
arguments at every call and crosses the vector register contract, and
measured that way it ran five times slower than the C backend. Two
changes close most of that gap, and both are meaning-preserving
rewrites the verifier still checks against the original body:

- **Expansion (`nativegen/inline.go`).** Before lowering, every call to a
  function whose signature carries a fixed vector is replaced by a block
  binding the parameters to the arguments in order — an identifier
  argument the callee never assigns substitutes directly — and running the
  callee's body with its bound names renamed apart; a call in statement
  position splices the block. A call is exactly that binding, so the
  expansion changes nothing the verifier compares. Recursion, receivers,
  type parameters, variadic parameters, extern or asm bodies, and matches
  that bind payloads are left as calls, and an expansion the lowering
  refuses falls back to the body as written. The source-level inliner
  (`compiler/inline.go`, `90-backend.md` §9) covers scalar leaf helpers for
  both backends; this expansion covers the vector helpers its rule
  excludes, on the native lane only.
- **Liveness (`nativegen/liveness.go`).** A variable is dead after the
  statement of its list that mentions it last (a mention inside a nested
  loop or arm belongs to the enclosing statement, so a loop-carried
  variable lives to the loop's end, and a block's result keeps its locals
  alive), and its register or slot returns to the pool for the
  declarations that follow; closed scopes return theirs. A function without
  calls keeps vector locals in the caller-saved vector registers too,
  leaving four to expression temporaries.

Measured (`benchmarks/native/`): the flattened validator has no call and
runs at 0.28 ns/byte where the call tree ran at 0.85 and the C backend at
0.17, in one run on a loaded machine; twenty vector spills remain of a
kernel that declares some forty vector locals over its expansions. What
would take the rest: an allocator with liveness across the whole body
instead of declaration order within it.
