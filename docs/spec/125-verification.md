# Verification: theorems, models, and the discharge ladder

Status: implemented subset (§2–§5 are normative for it; §6 is direction).
Oak's verification surface is built from the language it already has. A
proposition is a `Bool` expression. Universal quantification is a parameter
list. A model is a `protocol` declaration. A contract is an `assert`. The
one new word is `theorem`, in the kind slot where `type` and `protocol`
already sit. Everything else — how a statement is discharged, what a
status means, where the proof lives — is a pipeline behind that surface,
and the pipeline reuses the pieces the compiler already trusts: the
interpreter the differential witnesses hold to the compiled program, the
extent facts and the assembler's bit-blaster with their Lean laws, and the
Lean extraction of `95-extraction.md`.

## 1. Principle: one semantic definition, many projections

The constitution (`00-constitution.md`) forbids reconstructing lost facts.
A theorem is therefore not an annotation string: it is a checked
declaration in the program's own type system, with the program's own
scoping, imports, and name resolution, so the same statement drives the
exhaustive decider, the property test, the Lean theorem, and the
documentation. Proof status is never collapsed into a `verified` bit; the
ladder of §3 names what was actually done.

## 2. Theorems

```oak
add_commutes: theorem (x: u8, y: u8) { x + y == y + x }

wraps: theorem (x: u8) = x + u8(255) == x - u8(1)

Color: type = Red | Green | Blue
next: (c: Color): Color = c ? | .Red => .Green | .Green => .Blue | .Blue => .Red
cycle: theorem (c: Color) { next(next(next(c))) == c }
```

`name: theorem (params) body` declares a theorem. `theorem` is contextual,
like `protocol` and `tag`: only `IDENT ':' theorem '('` reads as one, and
`theorem` stays a legal identifier elsewhere. The parameters use the
function grammar (`10-syntax.md` §3, grouped names included); the body is a
brace block or `= expr`, exactly as a function's. The result type is `Bool`
and is never written.

Semantics. A theorem is the claim that its body is `true` for every
assignment of its parameters over their types. It is checked as the
function `(params): Bool` it is — the body types as `Bool`, borrowing and
discipline apply — and it compiles as that function, so a program may call
it (a test, a debug assertion). The logic is Oak's `Bool`: conjunction
`&&`, disjunction `||`, negation `!`, implication spelled `!a || b` or
`a ? b | true`, equality `==` including the structural equality of sum
types and records (`30-adts-patterns.md` §14, `40-records.md` §16), and
case analysis by `match`. There is no separate proposition language and no
quantifier syntax: `∀` is the parameter list, and an existential is stated
by the function that produces the witness.

Shape (`OAK-V0001`): a theorem is monomorphic (state it at the types it is
about), has no receiver, no variadic tail, no effect clauses, and no
foreign binding. Whatever else the body may do is the deciders' concern:
each fails closed on its own subset and says so in the status.

### 2a. Protocol invariants

A protocol (`112-protocols.md`) is the model. A theorem whose parameters
are exactly its projected state and data — `(s: NameState, d: NameData)`,
or `(s: NameState)` for a machine without data — is an **invariant
candidate**, and `oak prove` reads it as a claim about the reachable
states rather than about every state. Before checking, the prover adds
the two obligations the declaration determines, as ordinary theorems over
the projections (`prove/protocols.go`):

```oak
paid: theorem (s: TurnstileState, d: TurnstileData) { s == .Locked || d.coins > u8(0) }

// generated
paid__base: theorem () { paid(turnstile_initial(), turnstile_initial_data()) }
paid__step: theorem (s: TurnstileState, d: TurnstileData, step: TurnstileStep) {
  buf: [1]TurnstileData = [1]TurnstileData{ d }
  !(paid(s, d) && turnstile_legal(s, d, step)) || paid(turnstile_next(s, span(&buf), step), buf[0])
}
```

The candidate's own row reports the obligations: `decided` when both are,
`refuted` naming which one fails and where (this turnstile's 8-bit
counter wraps: `invariant is not preserved: counterexample ... coins:
255`), `open` otherwise; the obligation rows follow with their detail.
A step obligation over a `u32` record decides at the bit level (§3):
the record and sum-type parameters are aggregates of leaves, the
projection's `next` is inlined through its span, and its `assert` is a
trap obligation on the legal path only. A candidate the inductive check
still leaves short of `decided` — a body outside the decider's subset, a
step that fails only at a state no run reaches — is then evaluated on
the reachable states themselves, the
exploration §2b uses (bounded by `-cases`): `invariant: holds on all 3
reachable states` decides a `u32` budget whose reachable values are few,
and `invariant fails at the reachable state Unlocked with {coins: 0}`
names a state a run actually reaches, the inductive detail kept in
parentheses. A graph beyond the bound keeps the inductive summary.
Steps that carry a payload enumerate it with the step (`program(compare:
u8)` is 256 steps). A candidate in the invariant subset is also stated in
the protocol's model-checker module as `Invariant_<name>` and listed in
its configuration (`112-protocols.md` §4), so TLC checks the same
statement. Nothing is added to the language: the generated
theorems are the ones a programmer would write, produced so the
preservation shape is never misspelled. The generation is a syntax
rewrite on the parsed program (`Compilation.WithSyntaxRewrite`), so a
build never sees it.

### 2b. Protocol liveness

A protocol's `eventually` entries (`112-protocols.md` §1) are checked by
`oak prove` over the reachable states of the projection, without TLC. The
prover runs `name_initial`, `name_legal`, and `name_next` in the
interpreter over every step value — payloads enumerated like a theorem's
parameters, the whole exploration bounded by `-cases` — and labels each
transition by its step and by whether it changed the state or the data.
Each entry is then a fair-trap search: `eventually T` fails when a fair
behavior avoiding `T` exists from the initial state, `eventually P -> T`
when one exists from a reachable `P` state. A behavior may stutter
forever, so every state is a candidate trap; a strongly connected set is
fair when every `fair` step is disabled somewhere in it or taken inside
it, and every `strongly fair` step is disabled everywhere in it or taken
inside it (a set that fails only through a strongly fair step is refined
by dropping the states where that step is enabled, as Emerson and Lei
do). A step that never changes the state — `signal(on): Running ->
Running` with no effects — is never enabled as a step, so fairness on it
asks nothing, as in TLA+.

```text
decided   quantum_live2: eventually Running -> Yielded: holds on all 3 reachable states under fair tick, strongly fair resume
refuted   quantum_live1: eventually Yielded: counterexample with no fairness declared: from Running with {budget: 2} a fair behavior never reaches the target, staying within {Running with {budget: 1}; Running with {budget: 2}}
```

The verdict is about the projection, whose `next` takes the first line
whose guard holds; the TLA+ module states the same entries over the
declaration's every-line reading, so a machine with several enabled
lines of one step from one state can pass here and be refuted by TLC —
never the reverse for a deterministic machine. An entry whose state
space exceeds the bound, or whose projection the interpreter cannot run,
is `open` with the reason. Each side of an entry is projected as a Bool
predicate (`name_liveK_from`, `name_liveK_to`) so the check evaluates
the same expression the guards use.

## 3. The discharge ladder

Every theorem is placed on one rung, from the strongest evidence down:

| Status | Meaning |
| --- | --- |
| `decided` | The compiler decided the statement itself, one of two ways. **Exhaustively**: it evaluated the body on every element of its finite parameter domain and every case held — domains are `Bool`, `u8`, `i8`, `u16`, `i16`, payload-free sum types, and declared records of those (the product of the field domains), with the product of the parameter domains bounded (`-cases`, 65536 by default); the evaluator is the interpreter the differential witnesses hold to the compiled program. **At the bit level**: for parameters that are fixed-width scalars or `Bool` of any width, the body was lowered to the assembler verifier's term language (`94-assembler.md` §8; wrapping arithmetic, bitwise operators, comparisons, conditionals, typed locals, counted loops, calls to program functions of the same shape inlined; no views, recursion, or data-dependent loops) and bit-blasted, and its bit is the constant true. A construct that traps on some inputs — a variable shift count reaching the width, a refinement's construction `Name(e)` whose predicate may fail — records its trap condition as an obligation the decider proves impossible first, so a theorem whose body traps is `refuted` at the trapping input rather than read as true; a parameter of a refinement type is its base under the predicate as a hypothesis (the claim is about the values the construction admits), and a callee's refined parameter or return is its base; an `f32` or `f64` is its IEEE 754 bit pattern, with the total operations, comparisons, `min`, `max`, and `total_order` as bit operations (`Oak.FloatBits`) and arithmetic outside the rung; a parameter of a record or sum type is an aggregate of scalar leaves — one symbolic parameter per field, a tag per union under the hypothesis that it names a variant — and calls pass such values by copy, a span of a local array as an alias (so a callee's write-back is seen), and return them merged leaf by leaf across match arms, so a protocol invariant's inductive step over a `u32` record decides here; an `assert` in a reached body is a trap obligation like a shift's, and every trap obligation carries the path condition under which the program reaches it (the right operand of a short-circuit or only when the left is false, a match arm only when its pattern is the first to match); the term semantics are those of `Oak.AssemblerSemantics`, proved against Arm's ASL and checked against the silicon. The blast orders the parameters' bits interleaved (bit j of every leaf adjacent, so an adder across parameters stays linear); beside it, when the parameters allow, run a second order with each root parameter's leaves in a block of their own (two aggregates related only through their normal forms are exponential interleaved and linear apart) and a third with the control parameters — those a conditional's guard or a shift count reads — before the data ones (several selectors compared to constants are exponential interleaved and linear once the selections are read first); the orders run together over the same terms and the first to decide within the node budget stops the others, the detail naming it (`parameters in blocks`, `control bits first`). A field or element may be read off a call's or a literal's value, and an array element at a data-dependent index reads as the elements merged under the index (a write, every element under it) with the bounds check as a trap obligation. The detail names which, and the case count or BDD node count. |
| `refuted` | One of the deciders found a counterexample. The theorem is false; the assignment is reported. |
| `proved` | Lean checked the theorem's statement over the extraction of the program (§5): `oak prove -lean out.lean -check` ran Lean on the projection and its statement drew no error. The compiler never awards this rung on its own; it reads Lean's diagnostics. A hand-written proof lives in a module of its own that imports the projection. |
| `open` | No decider applies (a domain too large, a parameter type that is not finite) and the statement awaits its Lean proof. The reason is reported. |

Statuses never mix: a theorem is not "verified"; it is `decided` by the
exhaustive decider, or `proved` by Lean, or `open`. Properties run by
`oak test` (`110-testing.md`) remain `tested`, a fifth and weaker status,
and a theorem is not one — though a theorem may be called from one.

The order is exhaustive first when the domain fits (a concrete count is
the plainest evidence), then the bit-level decider, then Lean — except
that a body with a counted loop, in the theorem or in a function it names,
goes to the bit level first, where the unrolled loop is one term, and falls
back to enumeration when the bit level does not apply (a 64-step product
evaluated 65536 times is the interpreter's costly case; the bit level
settles it in milliseconds). Direction
(§6): the extent facts (`50-borrowing.md`) decide a linear fragment inside
the checker and are the next `decided` rung.

## 4. `oak prove`

```text
oak prove [-lean out.lean [-check [-lean-binary lean]]] [-cases N] [dir|file.oak]
```

type-checks the package (a directory through the module loader, or one
source file), runs the ladder over its theorems in source order, and
prints one line per theorem — status, name, detail — and a summary. The
exit status is 0 when every theorem is `decided` or `proved`, 1 when any
is `refuted` or `open`, 2 on usage or compilation errors. With `-lean`,
the Lean projection of the theorems and of every function they call is
written to the named file (§5); a theorem the extractor cannot state (a
recursive callee, a construct outside its subset) stays open with the
extractor's reason and the projection carries the rest. With `-check`,
Lean is run on the projection — the named executable, `lean` by default,
invoked directly with the file as its one argument — and its diagnostics
are read back by line: an open theorem whose statement drew no error is
`proved`; one whose statement drew an error stays open with Lean's first
message; an error outside every statement leaves them all open with it.
`-cases` bounds the exhaustive decider.

`oak build` checks theorems like any declaration and does not run the
ladder; a theorem is never a build error for being open.

`-solver oak` replays every theorem decided at the bit level through the
solver written in Oak (`prove/solver/bdd.oak`, §7): the same lowered terms
under the same variable order are serialized as a word table, embedded in
a generated package with the solver, compiled through the backend, and
run on the host; the row gains `the Oak solver agrees (same N nodes)`
when the Oak solver reaches the same verdict with the same node count,
and becomes `open` naming the difference otherwise. `TestOakSolverAgrees`
runs it over the whole law corpus.

`-witness` evaluates every decided theorem in the compiled program as
well, whichever decider settled it: `main` is replaced by a generated
driver that loops over the parameter domains (u8, u16, i8, i16, `Bool`,
payload-free sum types and a protocol's state type, their product within
`-cases`) through the width-conversion rows, calls each theorem, and exits
with the index of the first theorem that fails; the row gains `witnessed
in the compiled program`, and a disagreement between the decider and the
backend is reported as `refuted` — the differential witness of
`85-discipline.md`, stated per theorem. A theorem whose parameters the
driver cannot enumerate, or whose domain exceeds the bound, is left to the
decider's verdict and named in the summary.

## 5. The Lean projection

A theorem extracts like the function it is (`95-extraction.md`), followed
by its statement:

```lean
def add_commutes (x : UInt8) (y : UInt8) (fuel : Nat) : Option (Bool) := do
  pure ((x + y) == (y + x))
theorem add_commutes_holds (x : UInt8) (y : UInt8) (fuel : Nat) :
    add_commutes x y fuel = some true := by
  unfold add_commutes
  simp only [pure, bind, Option.bind_some, Option.bind_none, oak_bind_ite, Option.ite_none_right_eq_some, Option.some.injEq, decide_eq_true_eq] at *
  first | rfl | decide | omega | bv_decide | ((repeat' split) <;> (try simp_all) <;> first | rfl | decide | omega | bv_decide)
```

The claim is over every argument and every fuel: the extracted definition
returns `some true`. The script unfolds the theorem and every extracted
function it reaches, normalizes the monad (a refinement construction's
guard becomes a conjunct through the module's own `oak_bind_ite`), and
tries the kernel's deciders in turn — `decide` for closed and small
statements, `omega` for linear arithmetic, `bv_decide` for fixed-width
bit-vector claims (the module imports `Std.Tactic.BVDecide` when it states
a theorem) — and, when none applies whole, splits the statement on its
matches and conditionals (a sum-type method's cases, a validity guard) and
sends each case to the same deciders. A parameter of a refinement type
(`20-types.md` §12) carries its predicate as a hypothesis `h_x`, which the
deciders use. A statement none
of them settles fails to check, and its proof is written by hand in a
module that imports the projection; the projection is regenerated, never
edited. The axioms of a checked statement are the standard three at most
(`propext`, `Classical.choice`, `Quot.sound`), as for every theorem in
`spec/lean`.

What the projection does not say: the extractor's and the compiler's
fidelity to the binary, which the extraction lane's tests and the
differential witnesses cover, and are stated as the assumption they are.

## 6. Self-hosted laws

The laws the checker rests on are stated in Lean (`spec/lean/Oak`) over
the naturals, and in Oak — `spec/oak/*.oak` — over the fixed-width
integers the checker actually reasons about, each as a theorem `oak prove`
discharges. The Oak statement makes the wrap-free premise explicit where
the Lean one has none to make (`i + k >= i` before `i + k < len`), so it is
the law the facts rely on, not an idealization of it. `TestSelfHostedLaws`
proves every file: the decided ones on every run of the test suite, the
`*_lean.oak` files through Lean where the Formal Verification workflow has
the toolchain.

| Lean law (`Oak.Extents`) | Oak theorem (`spec/oak/extents.oak`) | Rung |
| --- | --- | --- |
| `static_extent`, `constant_under_min_length`, `bound_transfers`, `bound_through_upper` | same names, over `u32` | decided, bit level |
| `offset_under_bound`, `guard_without_wrap`, `inclusive_guard_without_wrap` | same names, the sums wrap-free | decided, bit level |
| `subslice_extent`, `subslice_check_iff` | same names | decided, bit level |
| `literal_bound_under_length`, `subtraction_under_bounds`, `subtraction_under_length` | same names | decided, bit level |
| `scaled_under_bound` | `scaled_under_bound_4`; `scaled_under_bound_512` (`extents_lean.oak`) | decided; proved (the page scale exceeds the BDD budget) |
| `masked_under_length`, `masked_trunc_under_length`, `masked_saturating_under_length`, `loop_exit_lower_bound`, `increment_keeps_lower_bound`, `increment_without_wrap` | same names | decided, bit level |
| `decreasing_keeps_upper_bound`, `decreasing_keeps_literal_bound` | same names | decided, bit level |
| `vector_under_min_length`, `vector_under_offset_bound`, `vector_under_literal_bound` | same names | decided, bit level |
| `midpoint_under_bound`, `midpoint_under_length`, `div_bound_scaled`, `div_bound_under_length` | same names at scale 2 and 512 (`extents_lean.oak`) | proved by Lean (the decider has no division) |
| `facts_monotone`, `kill_is_conservative`, `bool_binding_*`, `loop_invariant` | — | about the fact stack, not arithmetic; Lean only |

| Lean law (`Oak.Intrinsics`) | Oak theorem (`spec/oak/intrinsics.oak`) | Rung |
| --- | --- | --- |
| `reverse_involutive` | `rev32/rev64/rbit32/rbit64_involutive` | decided, bit level |
| `clz_le_width`, `clz_zero`, `clz_leading_one`, `clz_lt_of_mem_true` | `clz32_le_width`, `clz32_zero`, `clz64_zero`, `clz32_leading_one`, `clz32_lt_of_set` | decided |
| `ctz_zero`, `ctz_lt_of_mem_true` | `ctz32_zero`, `ctz32_odd` (through `rbit`) | decided |
| `popcount_le_width`, `popcount_zero`, `popcount_ones`, `popcount_not`, `popcount_eq_zero_iff` | `popcount32/64_*` | decided, bit level |

| Witness (`spec/oak/witnesses.oak`) | Statement | Rung |
| --- | --- | --- |
| the SWAR population count | `swar_popcount32(x) == arm64.cnt32(x)`, and at 64 bits | decided, bit level |
| the byte shuffle, the swap network | `shuffle_rev32(x) == arm64.rev32(x)`, `network_rbit32(x) == arm64.rbit32(x)` | decided, bit level |
| leading zeros as thresholds | `threshold_clz32(x) == arm64.clz32(x)` | decided, bit level |
| Unicode Table 3-7, one and two bytes | `is_valid_utf8` over `[b0, b1]` equals the table's predicate | decided, all 65536 cases |
| Table 3-7, the special three- and four-byte rows | `E0`, `E1`, `ED`; `F0`, `F4` with a fixed last byte, over every continuation pair | decided, all 65536 cases each |

| Float law (`Oak.FloatBits`, `spec/oak/floats.oak`) | Statement | Rung |
| --- | --- | --- |
| `neg_involutive`, `abs_idempotent`, `abs_of_neg`, `copysign_composes`, `copysign_abs` | the total operations as bit operations on the IEEE pattern (`u32_bits_f32` states bit equality where IEEE equality would not do) | decided, bit level; `bv_decide` in Lean |
| `nan_is_unequal`, `classes_cover`, `classes_disjoint`, `normal_is_finite` | NaN is exactly the value unequal to itself; NaN, infinite, finite partition the patterns | decided; `bv_decide` |
| `less_irreflexive`, `less_asymmetric`, `trichotomy_non_nan`, `nan_below_nothing`, `neg_reverses_order` | the IEEE order over the patterns | decided; `bv_decide` |
| `total_order_*` | reflexive, total, antisymmetric, refines the IEEE order, orders the zeros | decided; `bv_decide` |
| `min_*`, `max_*` on non-NaN operands | commutative, one of the operands, below and above both, the zeros ordered | decided; `bv_decide` |

| Bound (`Oak.FloatBounds`) | Statement | Rung |
| --- | --- | --- |
| `round_error` | `2^p · \|round p x − x\| ≤ \|x\|`: one rounding moves a value by at most `u·\|x\|`, `u = 2^-p` | proved in Lean |
| `rounded_error`, `bound_closed` | any grouping of additions, depth `d`: `2^(p·d) · \|rounded − exact\| ≤ B p d · Σ\|xᵢ\|`, `B p d + 2^(p·d) = (2^p+1)^d` — the classical `((1+u)^d − 1) Σ\|xᵢ\|` | proved in Lean |
| `chain_error`, `tree_is_grouping`, `groupings_differ` | `reduce.chain` over `n` values is within `((1+u)^(n−1) − 1) Σ\|xᵢ\|`; `reduce.tree` is the rounded sum of a grouping of the leaves; two groupings differ by at most the sum of their bounds (`55-parallelism.md` §4, `order any`) | proved in Lean |

The decider models an `f32` or `f64` as its bit pattern (`asm/floats_lowering.go`): negation, abs, copysign, the classifiers, the comparisons, `min`, `max`, and `total_order` are the circuits `Oak.FloatBits` defines; a NaN operand of `min`/`max` yields a fresh symbol, since the backend's result is `a + b` and its payload the platform's, so no law about it can be proved (`TestFloatBitLevel`). Arithmetic, rounding, `sqrt`, `fma`, and width conversions are not bit operations and stay open at this rung; their laws live in `Oak.Floats`.

| Discharge law (`Oak.Discharge`, `spec/oak/discharge.oak`) | Statement | Rung |
| --- | --- | --- |
| `shift_multiple`, `mask_multiple`, `product_multiple` | a shift by log2 K, a mask with a multiple of K, a product with a multiple of K is a multiple of K, wrapping included | decided, bit level; `bv_decide` in Lean |
| `sum_of_multiples`, `difference_of_multiples`, `or_of_multiples`, `xor_of_multiples` | combinations of multiples are multiples | decided; `bv_decide` |
| `narrowing_keeps_multiple`, `widening_keeps_multiple` | a conversion keeps the low bits | decided; `bv_decide` |
| `offset_below_bound`, `lower_bound_from_guard` | the bound rules | decided |
| `product_multiple_needs_power_of_two` | `∃ x : BitVec 8, (x * 3) % 3 ≠ 0` — why the rule admits powers of two only | Lean only (a counterexample, not a law) |

| Protocol against intrinsic (`spec/oak/protocols.oak`) | Statement | Rung |
| --- | --- | --- |
| `machine_agrees_two_bytes` | the `Utf8` machine, stepped through `utf8_legal`/`utf8_next`, accepts `[b0, b1]` exactly when `is_valid_utf8` does | decided, all 65536 cases, and witnessed in the compiled program — where `utf8_next` is the shift DFA the backend lowers (`112-protocols.md` §2a) and `is_valid_utf8` the C helper |
| `machine_agrees_three_bytes_e0/ed/e1` | the same under the three-byte leads with special ranges | decided and witnessed, all 65536 cases each |
| `lowering_legal`, `lowering_next` (`Oak.Protocol`: the table computes the tree) | `utf8_legal_tree`/`utf8_next_tree`, the branch tree the projection keeps beside the lowering, agree with `utf8_legal`/`utf8_next` on every state and byte | decided (2048 cases) and witnessed in the compiled program, where `utf8_next` is the shift DFA |
| `run_is_iterated_next` (`Oak.Protocol.runSink_correct`) | `utf8_run` over a legal two-byte input is `utf8_next` iterated | decided and witnessed, all 65536 cases |

| Layout law (`Oak.RecordLayout`, `spec/oak/layout.oak`) | Statement | Rung |
| --- | --- | --- |
| `alignUp_ge`, `alignUp_aligned` | `align_up(v, 8)` and `align_up(v, 64)` are at least `v` and multiples of the alignment | decided, bit level |
| — | the rounding is minimal, idempotent, and fixes aligned values | decided, bit level |

| Library law (`Oak.Stdlib.*Laws`) | Oak theorem (`spec/oak/stdlib_*/`) | Rung |
| --- | --- | --- |
| `VarintLaws` | `roundtrip_u16` (encode then decode is the identity, in `varint_size` bytes), `size_u16`, `zigzag_roundtrip_i16`, `zigzag_small` | decided, all 65536 cases each |
| `EncodingLaws`, `Base64Laws` | `hex_roundtrip` (both alphabets), `base64_roundtrip_two` (padded), `base64_url_roundtrip_one` | decided, exhaustively |
| `SortLaws`, `PdqsortLaws` | `pair_sorted_and_permuted`, `pair_search_finds` | decided, all 65536 pairs |

Every decided law of the corpus is also witnessed in the compiled
program (`TestSelfHostedLaws` passes `-witness`), so the interpreter that
decided it and the backend that runs it agree on every case. The library laws are stated over the library itself — the packages
import `varint`, `encoding`, and `sort` — where the Lean laws are stated
over the extraction; the two meet in the faithfulness harness
(`95-extraction.md` §6). The witnesses are the three-witness rule (`92-ffi.md` §3.1) as proof
rather than test: the portable lowering, transcribed as an Oak function,
is stated equal to the instruction function and the decider settles it
for every input; the validity intrinsic is stated against the table it
implements and decided exhaustively. The instruction functions decide because the bit-level decider lowers
`arm64.rev32`, `rbit`, `clz`, and `cnt` to the verifier's own instruction
terms — the semantics the assembler lane is checked against — with `cnt`
as a population-count term (an adder tree over the operand's bits), and
divides by an unsigned constant power of two as a shift or a mask. What
is not yet restated: `Oak.Floats`' rounding contract (arithmetic is not a bit operation) (the decider has no floats), and the laws over
lists and layouts, which have no fixed-width statement.

### 6.1 The type lattice

The semantic lattice of `20-types.md` §3 and the procedure the checker
decides it with (`typechecker/lattice.go`: both sides to disjunctive normal
form over the nominal atoms, every left clause implied by some right
clause) are restated in `spec/oak/lattice.oak` over words rather than
lists — a clause is the mask of the atoms it requires, a normal form the
bitset of its clauses, a valuation the mask of the atoms holding at a point
— and the laws of `Oak.TypeLattice` and `Oak.TypeLatticeRefinement` are
decided at the bit level over every normal form and valuation of three
atoms and every lattice type of four nodes (the fewest that exercise every
law; the Lean modules prove them for any number of atoms). The word form is
also the fast form: a clause implication is one mask test, and the
procedure over up to 64 atoms is a handful of word operations per clause
pair, where the list form compares types pairwise.

| Lean law | Oak theorem (`spec/oak/lattice.oak`) | Rung |
| --- | --- | --- |
| `TypeLatticeRefinement.decide_sound`, `decide_complete` | `decide_sound`; `decide_complete` (the countermodel computed by `dnf_countermodel`); `decide_is_containment` (both at once against the pointwise semantics) | decided, bit level |
| `clauseDenote_merge`, `dnfDenote_product`, `dnfOf_denotes` | `clause_merge_denotes`, `dnf_union_denotes`, `dnf_product_denotes`, `dnf_of_denotes` | decided, bit level |
| `isSubtype_sound`, `isSubtype_complete` | same names, over two four-node types | decided, bit level (parameters in blocks) |
| `TypeLattice.subtype_refl`, `subtype_trans`, `bottom_le`, `le_top`, `le_join_left/right`, `join_least`, `meet_le_left/right`, `meet_greatest` | same names, on the procedure | decided |
| `join_comm`, `meet_comm`, `join_assoc`, `meet_assoc`, `join_idem`, `join_bottom`, `meet_top`, `meet_bottom` | same names, as equations on the normal forms | decided |
| `meet_idem`, `join_top`, `join_absorption`, `meet_absorption` | same names, as mutual containment (the meet's normal form is larger) | decided |

Every law is also witnessed in the compiled program; the file proves in
about eight seconds.

### 6.2 Effects and patterns

`spec/oak/effects.oak` restates `Oak.Effects` (the subsumption order
between broad and scoped effects that `forbids` reads) over a record
`{family, scoped, scope}`, and `Oak.EffectRows` (the rows on function
types, `60-effects-allocation.md` §2a) over a program of three functions
and two slots whose effect sets are bitsets: `bound_step` and
`perform_step` are one unfolding each of the Lean model's fuel-indexed
`bound` and `perform`, `rows_admit` the row check at a fuel, and the
soundness theorem is stated as the induction Lean runs — the step, for any
two sets standing for the fuel-n bound and performance — with the bound's
monotonicity and its fixed point beside it. `spec/oak/patterns.oak`
restates `Oak.Exhaustiveness` and `Oak.PatternAnalysis`
(`35-pattern-analysis.md` §11) over a closed universe of eight cases, sets
as bitsets, with the procedure's verdict tied to the witness it reports
(`exhaustive_or_counterexample`).

| Lean law | Oak theorem | Rung |
| --- | --- | --- |
| `Effects.broad_subsumes_scoped`, `broad_subsumes_broad`, `scoped_subsumes_same`, `scoped_does_not_subsume_broad`, `scoped_subsumes_scoped_iff`, `broad_subsumes_scoped_iff`, `overlaps_symm`, `broad_overlaps_scoped`, `distinct_scopes_do_not_overlap`, `broad_forbid_rejects_scoped_requirement` | same names (`effects.oak`) | decided |
| `EffectRows.perform_subset_bound`, `forbids_sound` | same names, as the induction step over any fuel-n sets under the row check at that fuel | decided, bit level |
| (the fuel induction's side conditions) | `bound_step_monotone`, `bound_fixed_point` | decided, bit level |
| `Exhaustiveness.wildcard_is_exhaustive`, `all_constructors_are_exhaustive`, `missing_constructor_is_not_exhaustive`, `adding_arms_preserves_exhaustiveness`, `constructor_membership_drives_coverage` | same names (`patterns.oak`) | decided |
| `PatternAnalysis.counterexample_refutes_exhaustive`, `missing_reachable_is_counterexample`, `redundant_not_useful`, `adding_redundant_preserves_exhaustive`, `refinement_excludes_other`, `unreachable_case_not_required`, `constructor_match_introduces_refinement`, `excluded_constructor_arm_is_unreachable` | same names | decided |
| (properties 1 and 2 of `35-pattern-analysis.md` §12) | `exhaustive_or_counterexample`, `wildcard_matches` | decided, bit level |

### 6.3 Shapes, dispatch, generalization, instantiation

Four more of the checker's and backend's models are restated
(`spec/oak/shapes.oak`, `adts.oak`, `generalization.oak`, `mono.oak`):
record shape satisfaction over field bitsets, with the order laws stated
through a list-to-set function so that they are about order; ADT dispatch
over up to four source-ordered arms, first match, with the value/dispatch
core the pattern laws assume; the generalization decision over its seven
blocking facts, decided exhaustively over every fact set; and generic-ADT
instantiation over a four-variant template, the injectivity law stated
with the premise it needs (agreement at the variant that references the
parameter), which the whole-instance equality implies.

| Lean law | Oak theorem | Rung |
| --- | --- | --- |
| `RecordShape.reflexive`, `empty_required`, `candidate_extension`, `transitive`, `missing_required_rejected`, `required_reverse_iff`, `candidate_reverse_iff`, `representation_irrelevant`, `required_representation_irrelevant` | same names (`shapes.oak`) | decided |
| `ADTSemantics.constructors_disjoint`, `select_head_match`, `select_head_skip`, `select_result_from_selected_handler`, `construct_then_dispatch`, `select_none_of_no_arm` | same names (`adts.oak`); `select_some_of_arm` is the converse | decided, bit level (`select_head_match` control bits first) |
| `GeneralizationSafety.decision_preserves_inferred_type`, `safe_generalizes`, the seven `*_blocks` | same names (`generalization.oak`); `generalized_iff_safe` both directions | decided, exhaustively |
| `Monomorphization.instantiate_length`, `instantiate_tags`, `instantiate_payload_shape`, `substPayload_param`, `substPayload_ground`, `instantiate_injective_on_used` | same names (`mono.oak`) | decided, bit level |

## 7. Direction

In order of payoff, each reusing a surface that exists:

- **The verifier in Oak.** The aim is a compiler whose semantics, solver,
  and proofs are Oak programs, the language's own laws stated and decided
  by the language. The order of work: the algebras of the language
  semantics first — the type lattice (§6.1), the effect algebra and rows,
  the pattern algebra of `35-pattern-analysis.md` (§6.2), record shapes,
  ADT dispatch, generalization, and instantiation (§6.3; all done) — each
  as an Oak procedure over words with its laws decided,
  the standard library's laws left in Lean; then the solver: the ROBDD and
  the bit blaster of `asm/blast.go` as an Oak program
  (`prove/solver/bdd.oak`: the node table in structure-of-arrays form, an
  open-addressing unique table, a direct-mapped apply cache, an iterative
  apply over an explicit frame stack, and the blaster operation for
  operation the Go one — done as the twin; `oak prove -solver oak` runs it
  beside the Go decider on every bit-level law and requires the same
  verdict with the same node count, which it reaches on the whole corpus),
  next made the decider `oak prove` runs by default with the Go one as the
  check; then
  proof certificates — a small checking kernel (clausal steps and
  equational rewrites) proved once in Lean, with the fast solvers untrusted
  producers of certificates, so speed and trust are separated; then an
  inductive prover, which is what the unbounded laws (the list-level layout
  laws, the fact stack, the stream proofs) need. The data layout is the
  method throughout: an algebra stated over words is word-parallel, and the
  solver is the kind of program Oak's layout, SIMD, and proof tools were
  built for.

- **Protocol invariants, further.** §2a covers safety inductively on
  finite domains and over the reachable states otherwise, so a `u32`
  budget is decided; liveness with declared fairness is decided over the
  same reachable states (§2b) and projected to the TLA+ module
  (`112-protocols.md` §1: `fair step`, `eventually from -> target`) for
  TLC. The inductive obligations decide at the bit level over record and
  sum-type parameters, so a machine whose reachable graph is not finite
  still gets its invariant decided when the step is inductive. Next:
  strengthening non-inductive candidates from the reachable states. The Boolean
  transition-model export of the verification experiment already checks
  inductive invariants through certificates; §2a is that check on the
  language's own state.
- **Refinements, further.** `Name: type = u16 where pred` is in
  (`20-types.md` §12): the predicate is a `Bool` expression over `value`,
  checked at construction, carried as extent facts by every binding of the
  type, discharged statically under a literal bound, a postcondition as a
  return type, projected to Lean as a guarded value, and generic over
  integer constants (`IrqId[N: u32]: type = u16 where value < N`, §12.1,
  specialized per application). The discharge reads lower bounds,
  power-of-two divisibility, conjunctions, and constant arguments besides
  the literal upper bound. Next: discharge from a declared theorem, and
  applications over an enclosing template's const parameter.
- **Contracts.** Leading `assert`s of a body are its preconditions; a
  caller discharges them statically or keeps the check. No `requires`
  keyword.
- **Larger decided domains.** Views and spans as the assembler verifier
  already models them, division with its zero-divisor obligation like the
  shift's, and the extent facts for linear bounds, inside the compiler,
  each with its Lean law.
- **Temporal properties.** Safety through the invariants above (§2a);
  liveness with declared fairness decided over the reachable states (§2b)
  and stated for TLC through the TLA+ module (`112-protocols.md` §4).
  Next: the every-line reading inside the compiler, and liveness over
  infinite data domains through Lean.
