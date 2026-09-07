# Boolean expressions to checked refutations

`NumberedCNF.lean` connects the symbolic Boolean encoder to the executable RUP
checker. An accepted refutation now implies a property of the Boolean expression,
not just a property of an independently supplied clause database.

## Proved properties

- `numbering_iff`: the symbolic CNF has a satisfying assignment exactly when its
  numbered clause database has a model.
- `numbered_bounds`: every emitted variable ID is positive and within the declared
  variable bound.
- `checkEncoded_sound`: if `checkEncoded expression commands` accepts, the
  expression evaluates to false under every input valuation.
- `checkValid_sound`: if `checkValid expression commands` accepts, the expression
  evaluates to true under every input valuation. This checks a refutation of its
  negation.

These statements cover arbitrary expressions built from Boolean constants,
inputs, NOT, AND, and OR, and arbitrary decoded proof streams. They compose
`BooleanCNF.encode_complete`, the numbering preservation proof, and
`RUPExecutable.checkProof_sound`. No solver-correctness assumption is needed.

The allocator uses an atom's first occurrence in the flattened CNF, plus one,
as its numeric ID. The table deliberately retains duplicate atoms; unused ID
slots are harmless. Lookup recovers the original atom, and lifting a symbolic
assignment preserves each clause. Pulling a numeric assignment back establishes
the reverse direction. This simple allocator is separate from Go's optimized
allocation and caching algorithm.

## Real solver exercise

After provisioning the pinned tools, run from the experiment folder:

```sh
bash ci/check-boolean-proofs.sh
```

The script compiles all required Lean modules with warnings treated as errors,
emits the numbered encodings, and asks CaDiCaL for ASCII LRAT proofs. The
`BooleanProof.lean` fixture runner reconstructs the expression's CNF when checking
its proof. It does not read the DIMACS file back or trust the solver's SAT status
as evidence of validity.

The six refutations cover false, contradiction, excluded middle, De Morgan's law,
distributivity, and a repeated-subexpression contradiction. Three satisfiable
targets must be rejected. Each successful proof is also checked against the
satisfiable expression `true`, and with an unjustified empty-clause suffix.
Negative tests require a structured rejection and the expected exit code; a
compiler error or crash cannot count as rejection. The suffix must reach the
checker rather than fail parsing.

Reports, CNF/proof hashes, solver output, proof diagnostics, and rejection output
are retained under `build/boolean-proofs/`. A fresh attempt starts with a failed
report, so a retry cannot leave an old success report in place.

The existing `BooleanCNFCompare.lean` corpus also compares numbered and symbolic
clause satisfaction for every enumerated auxiliary assignment, checks ID bounds,
and retains its independent Go/Lean comparison across 3,249 expressions and
12,996 input valuations. These finite tests supplement the general theorems.

## Remaining boundary

The proved source is the Lean Boolean expression datatype. Oak parsing, type
checking, obligation construction, Go's encoder and checker, enums, arithmetic,
and transition-system semantics remain outside this proof. The fixture CLI and
JSON output are test tooling. Running compiled Lean also relies on Lean's compiler
and runtime; the mathematical theorem is checked by Lean's kernel.

Proof text is decoded before checking; the theorem applies to every decoded
instruction stream. CNF reconstruction avoids a DIMACS-parser assumption in this
expression-level acceptance path. It does not retroactively strengthen the
separate `RUPCheck.lean` gate, which accepts a supplied DIMACS file.

The prototype remains isolated under `experiments/verification-poc`. This is a
proved Boolean encoding/checking path, not verification of Oak or its toolchain.
