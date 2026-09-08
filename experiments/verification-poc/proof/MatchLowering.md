# Statement-match compiler correction

The ASCII checker exposed a C backend defect in nested Boolean statement
matches. Some matches bypassed the ordinary conditional lowering and reached
`emitMatchStatement`, which emitted separate guard checks for each arm. A true
arm that changed its own guard's inputs could activate the false arm too. The
scanner could even read beyond a byte view when the first arm advanced its cursor
and the second guard reread the cursor.

The same emitter could run later ADT/scalar arms after a matched variable changed,
and emitted wildcard fallbacks unconditionally. This also affected value matches
that lowering had converted to a declaration followed by statement assignments.

## Correction

The C backend now recognizes Boolean statement matches and emits a single
`if/else`: the condition executes once, and only the selected body executes.
Other statement matches use an exclusive `if/else if/else` chain. Existing
hoisting of non-identifier ADT scrutinees and guarded payload extraction remain
in place. Return-position matching retains its existing terminating-arm path.

`self_hosted_text.oak` no longer snapshots the current byte and parser phases to
work around the compiler defect. Its ordinary state-dependent guards now exercise
the corrected backend throughout the complete text corpus and certificate gate.
No syntax or verification API changes are needed.

## Regression coverage

`codegen/match_statement_e2e_test.go` runs six cases through the actual Oak
frontend, compiles generated C with `-std=c99 -O2`, and executes native assertions:

- A nested true guard mutates the value used by the condition.
- A side-effecting false condition increments a counter exactly once.
- A nested byte guard advances its cursor to the view boundary.
- A scalar arm changes the matched value without activating a later arm or fallback.
- An ADT arm changes its tag without activating the next arm.
- An ADT payload is bound before mutation and its fallback is not executed.

Compilation errors, timeouts, unsupported lowering, traps, and unexpected process
exit codes fail these tests. Three golden C expectations record the corrected
branch structures for arithmetic, conditionals, and generic ADTs.

The verification gate additionally checks the unmodified 729-case text corpus,
14 resource-boundary cases, and one real CaDiCaL certificate with two corruptions
using the parser without its workaround. Go and Lean remain the independent
reference implementations for these comparisons.

[Validation run](https://github.com/SCKelemen/oak/actions/runs/34203595256):
the six native regressions passed, and the parser without snapshots agreed with
Go and Lean on 729 inputs (119 accepted, 610 rejected). All 14 resource-boundary
cases passed as well.

The solver job accepted the real CaDiCaL certificate and rejected both
corruptions, with Lean agreeing on all three decisions. Repository CI,
standard-library, formal-verification, and golden-file checks all passed.

## Proof boundary

This is a compiler correctness fix with native regression and differential
validation, not a formal semantics-preservation theorem. It does not establish
universal refinement of the Oak checker or verify the entire compiler.
`validation-self-hosted-text.json` remains the historical record of the earlier
workaround-based implementation. `validation-match-lowering.json` records this
subsequent correction and the new tested commit.

The next proof milestone is a refinement specification for bounded decimal
parsing and its buffer invariants, followed by the complete Oak decoder.
