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
Steps that carry a payload enumerate it with the step (`program(compare:
u8)` is 256 steps). Nothing is added to the language: the generated
theorems are the ones a programmer would write, produced so the
preservation shape is never misspelled. The generation is a syntax
rewrite on the parsed program (`Compilation.WithSyntaxRewrite`), so a
build never sees it.

## 3. The discharge ladder

Every theorem is placed on one rung, from the strongest evidence down:

| Status | Meaning |
| --- | --- |
| `decided` | The compiler decided the statement itself, one of two ways. **Exhaustively**: it evaluated the body on every element of its finite parameter domain and every case held — domains are `Bool`, `u8`, `i8`, `u16`, `i16`, payload-free sum types, and declared records of those (the product of the field domains), with the product of the parameter domains bounded (`-cases`, 65536 by default); the evaluator is the interpreter the differential witnesses hold to the compiled program. **At the bit level**: for parameters that are fixed-width scalars or `Bool` of any width, the body was lowered to the assembler verifier's term language (`94-assembler.md` §8; wrapping arithmetic, bitwise operators, comparisons, conditionals, typed locals, counted loops, calls to program functions of the same shape inlined; no views, recursion, or data-dependent loops) and bit-blasted, and its bit is the constant true. A construct that traps on some inputs — a variable shift count reaching the width — records its trap condition as an obligation the decider proves impossible first, so a theorem whose body traps is `refuted` at the trapping input rather than read as true; the term semantics are those of `Oak.AssemblerSemantics`, proved against Arm's ASL and checked against the silicon. The detail names which, and the case count or BDD node count. |
| `refuted` | One of the deciders found a counterexample. The theorem is false; the assignment is reported. |
| `proved` | Lean checked the theorem's statement over the extraction of the program (§5): `oak prove -lean out.lean -check` ran Lean on the projection and its statement drew no error. The compiler never awards this rung on its own; it reads Lean's diagnostics. A hand-written proof lives in a module of its own that imports the projection. |
| `open` | No decider applies (a domain too large, a parameter type that is not finite) and the statement awaits its Lean proof. The reason is reported. |

Statuses never mix: a theorem is not "verified"; it is `decided` by the
exhaustive decider, or `proved` by Lean, or `open`. Properties run by
`oak test` (`110-testing.md`) remain `tested`, a fifth and weaker status,
and a theorem is not one — though a theorem may be called from one.

The order is exhaustive first when the domain fits (a concrete count is
the plainest evidence), then the bit-level decider, then Lean. Direction
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

## 5. The Lean projection

A theorem extracts like the function it is (`95-extraction.md`), followed
by its statement:

```lean
def add_commutes (x : UInt8) (y : UInt8) (fuel : Nat) : Option (Bool) := do
  pure ((x + y) == (y + x))
theorem add_commutes_holds (x : UInt8) (y : UInt8) (fuel : Nat) :
    add_commutes x y fuel = some true := by
  unfold add_commutes
  simp only [pure, bind, Option.bind, Option.some.injEq, decide_eq_true_eq]
  first | rfl | decide | omega | bv_decide
```

The claim is over every argument and every fuel: the extracted definition
returns `some true`. The automatic script tries the kernel's deciders in
turn — `decide` for closed and small statements, `omega` for linear
arithmetic, `bv_decide` for fixed-width bit-vector claims (the module
imports `Std.Tactic.BVDecide` when it states a theorem). A statement none
of them settles fails to check, and its proof is written by hand in a
module that imports the projection; the projection is regenerated, never
edited. The axioms of a checked statement are the standard three at most
(`propext`, `Classical.choice`, `Quot.sound`), as for every theorem in
`spec/lean`.

What the projection does not say: the extractor's and the compiler's
fidelity to the binary, which the extraction lane's tests and the
differential witnesses cover, and are stated as the assumption they are.

## 6. Direction

In order of payoff, each reusing a surface that exists:

- **Protocol invariants, further.** §2a covers safety on finite state
  spaces. Next: the larger domains of §3 so a `u32` budget is decided
  rather than left open, and liveness with declared fairness projected to
  the TLA+ module the protocol command already renders. The Boolean
  transition-model export of the verification experiment already checks
  inductive invariants through certificates; §2a is that check on the
  language's own state.
- **Refinements.** `IrqId[N]: type = u16 where value < N`
  (`LANGUAGE_MODEL.md`): the proposition is a `Bool` expression over
  `value`, checked at construction, discharged statically where the extent
  facts or a theorem show it, and kept as a runtime check labeled
  `checked` otherwise. A refined return type is a postcondition.
- **Contracts.** Leading `assert`s of a body are its preconditions; a
  caller discharges them statically or keeps the check. No `requires`
  keyword.
- **Larger decided domains.** Views and spans as the assembler verifier
  already models them, division with its zero-divisor obligation like the
  shift's, and the extent facts for linear bounds, inside the compiler,
  each with its Lean law.
- **Temporal properties.** Safety first, through the invariants above;
  liveness with declared fairness, projected to the TLA+ module the
  protocol command already renders.
