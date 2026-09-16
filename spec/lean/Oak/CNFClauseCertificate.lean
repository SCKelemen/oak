import Oak.CNFClauseTrace
import Oak.CNFBitwiseWordRoot

/-!
# Checked signed clause traces in the native certificate contract

The clause-trace checker identifies the actual signed clause list with a
well-formed gate sequence followed by its supplied obligation. This discharges
the CNF-completeness field of the native direct-word certificate contract.

The result-to-root equality remains an explicit premise. These theorems do not
refine the Go term/root construction, source lowering, symbolic execution,
DIMACS byte writer, or LRAT parser, and do not authorize compiler verdicts.
-/

set_option autoImplicit false

namespace Oak.CNFClauseCertificate

open Oak.RupCheck Oak.TseitinCNF Oak.CNFBuilderTrace
open Oak.CNFClauseTrace

/-- A checked RUP refutation of the actual decoded clauses rules out the
supplied final obligation under every evaluation of the checked gate trace. -/
theorem accepted_refutes_obligation {snapshot : Snapshot} {checked : Checked}
    {database : Database} (traceAccepted : check snapshot = some checked)
    (decoded : emittedDatabase? snapshot = some database)
    (certificateAccepted : Oak.RupCheck.Accepted database) (initial : Assignment) :
    clauseValue (evalSequence checked.gates initial) checked.obligation = false := by
  cases value : clauseValue (evalSequence checked.gates initial) checked.obligation with
  | false => rfl
  | true =>
      have finalClause := (clauseValue_eq_true_iff _ _).mp value
      exact False.elim (accepted_unsatisfiable certificateAccepted _
        (check_evalSequence_models_of_obligation traceAccepted decoded initial finalClause))

/-- Build the existing direct-word encoding from a checked trace. In contrast
to an arbitrary encoding, its `cnf_complete` field is proved here from the
actual emitted clauses. Only the connection from the two words to the final
obligation is supplied by the caller. -/
def directEncoding {snapshot : Snapshot} {checked : Checked} {database : Database}
    (traceAccepted : check snapshot = some checked)
    (decoded : emittedDatabase? snapshot = some database)
    {n width : Nat} (lhs rhs : Oak.CNFBitwiseWordRoot.Inputs n → BitVec width)
    (initial : Oak.CNFBitwiseWordRoot.Inputs n → Assignment)
    (differenceExact : ∀ input,
      clauseValue (evalSequence checked.gates (initial input)) checked.obligation =
        Oak.CNFBitwiseWordRoot.differs (lhs input) (rhs input)) :
    Oak.CNFBitwiseWordRoot.DirectEncoding n width Nat where
  lhs := lhs
  rhs := rhs
  circuit := fun input => evalSequence checked.gates (initial input)
  obligation := fun _ assignment => clauseValue assignment checked.obligation
  database := database
  difference_exact := differenceExact
  cnf_complete := by
    intro satisfiable
    obtain ⟨input, rootTrue⟩ := (Oak.Tseitin.determined _ _).mp satisfiable
    exact ⟨evalSequence checked.gates (initial input),
      check_evalSequence_models_of_obligation traceAccepted decoded (initial input)
        ((clauseValue_eq_true_iff _ _).mp rootTrue)⟩

/-- RUP acceptance implies word equality when the checked trace's final
obligation is exactly their direct disequality root. No abstract
CNF-completeness hypothesis is needed at this trace boundary. -/
theorem accepted_implies_equal {snapshot : Snapshot} {checked : Checked}
    {database : Database} (traceAccepted : check snapshot = some checked)
    (decoded : emittedDatabase? snapshot = some database)
    {n width : Nat} (lhs rhs : Oak.CNFBitwiseWordRoot.Inputs n → BitVec width)
    (initial : Oak.CNFBitwiseWordRoot.Inputs n → Assignment)
    (differenceExact : ∀ input,
      clauseValue (evalSequence checked.gates (initial input)) checked.obligation =
        Oak.CNFBitwiseWordRoot.differs (lhs input) (rhs input))
    (certificateAccepted : Oak.RupCheck.Accepted database) :
    ∀ input, lhs input = rhs input :=
  Oak.CNFBitwiseWordRoot.accepted_implies_equal
    (directEncoding traceAccepted decoded lhs rhs initial differenceExact) certificateAccepted

end Oak.CNFClauseCertificate
