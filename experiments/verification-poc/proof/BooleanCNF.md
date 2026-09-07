# Boolean CNF specification

`BooleanCNF.lean` specifies a Tseitin encoding for Boolean constants, inputs,
negation, conjunction, and disjunction. Its semantics are independent of Go's
circuit implementation and of any external SAT solver.

The AND clauses for output `z` and signed inputs `x`, `y` are:

- `¬z ∨ x`
- `¬z ∨ y`
- `z ∨ ¬x ∨ ¬y`

The OR clauses are:

- `z ∨ ¬x`
- `z ∨ ¬y`
- `¬z ∨ x ∨ y`

Negation flips a literal's sign. Constants use a distinguished `one` atom,
constrained by a unit clause. The encoded formula includes a unit clause
asserting the expression's root. These are the same logical gate patterns used
by `Circuit.gate` and `Circuit.dimacs` for this Boolean subset.

## Proved properties

- `andClauses_correct` and `orClauses_correct`: the clauses enforce precisely the
  corresponding gate equation, for arbitrary assignments and signed inputs.
- `body_sound`: every assignment satisfying the gate clauses and `one = true`
  gives the root the value of the source expression. It does not assume that
  auxiliary values came from an evaluator.
- `body_complete`: evaluating each auxiliary expression constructs a satisfying
  extension of any input valuation for the gate clauses.
- `encode_sound`: satisfying the full CNF implies the source expression is true.
- `encode_complete`: a true source expression has an explicitly constructed
  satisfying extension.
- `encoding_iff`: for every fixed input valuation, the source expression is true
  exactly when there is a satisfying CNF assignment agreeing on all input atoms.

The source expressions and input valuations in these theorems are arbitrary;
there is no expression-depth or variable-count bound in the proofs.

## Representation boundary

Auxiliary atoms are named by expressions, rather than numbered DIMACS variables.
The constructors for inputs, auxiliaries, and `one` are disjoint. Identical
subexpressions share a name; repeated occurrences may repeat clauses. This
keeps the semantic specification small and makes the satisfying extension
explicit. It is not a specification of Go's integer allocation algorithm,
commutative cache, constant folding, or byte-level serialization.

No theorem here connects numbered clauses to the RUP checker's database. That
requires a name-to-number preservation theorem. Go refinement, the Oak frontend,
query construction for base/step obligations, enums, and bit-vector arithmetic
also remain outside this milestone. In particular, agreement tests do not prove
that the Go encoder implements this specification.

## Executable comparison

`TestBooleanCNFSpecification` constructs all 3,244 expressions of depth at most
two over `false`, `true`, `x`, and `y`, using NOT, AND, and OR. Five deeper cases
exercise sharing, commutative reuse, and complements. Each expression is sent
through the actual Go `encode(..., "initial")` path with two Boolean fields,
and its emitted DIMACS is parsed and checked by exhaustive assignment search.
All four input valuations are compared with a separate recursive evaluator.
Auxiliary assignments are enumerated freely, so extra satisfying assignments
cannot be hidden by only checking the encoder's preferred extension.

`BooleanCNFCompare.lean` reads the generated postorder expression programs,
reconstructs the Lean expressions, and independently evaluates the symbolic
CNFs over every auxiliary valuation. The distinguished `one` atom is fixed true,
as its unit clause requires. It compares Lean expression evaluation, Lean CNF
satisfiability, Go expression evaluation, and Go DIMACS satisfiability. The JSON
adapter is test tooling and is not part of the encoding theorem.

The opt-in soundness job runs the following commands from the experiment folder:

```sh
mkdir -p build/soundness
export LEAN_PATH="$PWD/proof"
lean -DwarningAsError=true -o proof/BooleanCNF.olean proof/BooleanCNF.lean
export OAK_BOOLEAN_CNF_CORPUS_OUT="$PWD/build/soundness/boolean-cnf-cases.json"
go test -count=1 -v . -run '^TestBooleanCNFSpecification$'
lean -DwarningAsError=true --run proof/BooleanCNFCompare.lean "$OAK_BOOLEAN_CNF_CORPUS_OUT"
```

The ordinary Go tests need no Lean installation. The opt-in job retains the
proof diagnostics, corpus, and comparison output with its soundness artifacts.
