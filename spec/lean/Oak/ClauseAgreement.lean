import Oak.RupCheck

/-!
# Checked clause-engine agreement

The verification driver compares checked evidence kinds, not raw SAT solver
flags. Codes are shared with `clause_agreement.go`: unknown = 0, SAT = 1,
UNSAT = 2; comparison gives unavailable = 0, agrees = 1, disagrees = 2.
Unknown and out-of-profile values must never count as agreement.

These theorems cover the finite admission policy and its semantic composition
with sound evidence. Concrete LRAT/model checking, constant folding, formula
identity, source lowering, and the Go control flow are separate obligations.
The production decision table is kernel-replayed by the formal CI lane.
-/

set_option autoImplicit false

namespace Oak.ClauseAgreement

def compare (expected observed : Nat) : Nat :=
  if (expected = 1 ∨ expected = 2) ∧ (observed = 1 ∨ observed = 2) then
    if expected = observed then 1 else 2
  else 0

theorem agreement_known {expected observed : Nat}
    (h : compare expected observed = 1) :
    expected = observed ∧ (expected = 1 ∨ expected = 2) := by
  unfold compare at h
  split at h
  · rename_i known
    split at h
    · rename_i same
      exact ⟨same, known.1⟩
    · contradiction
  · contradiction

theorem unknown_left (observed : Nat) : compare 0 observed = 0 := by
  simp [compare]

theorem unknown_right (expected : Nat) : compare expected 0 = 0 := by
  simp [compare]

theorem disagreement_known {expected observed : Nat}
    (h : compare expected observed = 2) :
    expected ≠ observed ∧ (expected = 1 ∨ expected = 2) ∧
      (observed = 1 ∨ observed = 2) := by
  unfold compare at h
  split at h
  · rename_i known
    split at h
    · contradiction
    · rename_i different
      exact ⟨different, known.1, known.2⟩
  · contradiction

/-- Evidence is about the exact database checked, never a solver status bit.
UNSAT evidence can come from accepted RUP, or a separately justified constant
fold. This definition does not assert that either production implementation
has already been refined to its specification. -/
def Evidence (db : Oak.RupCheck.Database) (kind : Nat) : Prop :=
  if kind = 1 then ∃ assignment, Oak.RupCheck.Models assignment db
  else if kind = 2 then Oak.RupCheck.Unsatisfiable db
  else False

theorem rup_evidence {db : Oak.RupCheck.Database}
    (accepted : Oak.RupCheck.Accepted db) : Evidence db 2 := by
  simpa [Evidence] using Oak.RupCheck.accepted_unsatisfiable accepted

/-- A cross-engine UNSAT agreement entails UNSAT of the independent expected
database when that database's evidence has been established. No equivalence
of two different encoders is assumed from matching sizes or status bits. -/
theorem agreeing_unsat {db : Oak.RupCheck.Database} {expected : Nat}
    (agree : compare expected 2 = 1) (evidence : Evidence db expected) :
    Oak.RupCheck.Unsatisfiable db := by
  have same := (agreement_known agree).1
  simpa [Evidence, same] using evidence

theorem agreeing_sat {db : Oak.RupCheck.Database} {expected : Nat}
    (agree : compare expected 1 = 1) (evidence : Evidence db expected) :
    ∃ assignment, Oak.RupCheck.Models assignment db := by
  have same := (agreement_known agree).1
  simpa [Evidence, same] using evidence

end Oak.ClauseAgreement
