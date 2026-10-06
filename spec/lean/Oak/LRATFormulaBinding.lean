import Oak.RupCheck

/-!
# Bind a solver's record to an independent formula

The record contains both initial clauses and proof steps. Checking the latter
against the former alone does not bind a solver result to its caller's problem.
This gate compares the exact ordered clause words, not a digest or dimensions.

The model uses natural-number projections of u32 words. The production Go and
compiled Oak decisions are pinned on the same raw-word corpus. This is bounded
correspondence, not universal refinement of their loops, memory, or compiler.
The composition theorem explicitly requires RUP acceptance of a decoded record;
it does not assert soundness of a concrete decoder or proof-checker program.
-/

set_option autoImplicit false

namespace Oak.LRATFormulaBinding

def word (words : List Nat) (index : Nat) : Nat := words[index]?.getD 0

structure FormulaKey where
  variables : Nat
  clauses : Nat
  literalWords : Nat
  body : List Nat
  deriving DecidableEq, BEq, Repr

def formulaKey (words : List Nat) : FormulaKey :=
  ⟨word words 1, word words 2, word words 3,
    (words.drop 8).take (word words 3)⟩

def Framed (words : List Nat) : Prop :=
  8 ≤ words.length ∧ word words 0 = 1280459348 ∧
  word words 3 ≤ words.length - 8 ∧
  word words 4 = words.length - 8 - word words 3

instance (words : List Nat) : Decidable (Framed words) := by
  unfold Framed
  infer_instance

def matchesFormula (formula record : List Nat) : Bool :=
  decide (Framed formula ∧ word formula 4 = 0 ∧ Framed record ∧
    formulaKey formula = formulaKey record)

theorem matches_exact {formula record : List Nat}
    (h : matchesFormula formula record = true) :
    formulaKey formula = formulaKey record := by
  unfold matchesFormula at h
  have accepted := of_decide_eq_true h
  exact accepted.2.2.2

theorem matches_framed {formula record : List Nat}
    (h : matchesFormula formula record = true) :
    Framed formula ∧ word formula 4 = 0 ∧ Framed record := by
  unfold matchesFormula at h
  have accepted := of_decide_eq_true h
  exact ⟨accepted.1, accepted.2.1, accepted.2.2.1⟩

theorem matches_body {formula record : List Nat}
    (h : matchesFormula formula record = true) :
    (formulaKey formula).body = (formulaKey record).body :=
  congrArg FormulaKey.body (matches_exact h)

/-- Exact identity preserves any interpretation of the numbered initial
database. The interpretation is explicit: no parser correctness is assumed
or proved by this identity theorem. -/
theorem matches_decode (decode : FormulaKey → Oak.RupCheck.Database)
    {formula record : List Nat} (h : matchesFormula formula record = true) :
    decode (formulaKey formula) = decode (formulaKey record) :=
  congrArg decode (matches_exact h)

/-- Accepted RUP steps now refute the independent expected database, under
the same explicit decoding used for the record's initial database. -/
theorem bound_accepted_unsatisfiable
    (decode : FormulaKey → Oak.RupCheck.Database)
    {formula record : List Nat} (bound : matchesFormula formula record = true)
    (accepted : Oak.RupCheck.Accepted (decode (formulaKey record))) :
    Oak.RupCheck.Unsatisfiable (decode (formulaKey formula)) := by
  rw [matches_decode decode bound]
  exact Oak.RupCheck.accepted_unsatisfiable accepted

end Oak.LRATFormulaBinding
