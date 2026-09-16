import Oak.TseitinCNF

/-!
# Total construction of the final CNF obligation

This module models the total post-decoding decision in `asm/exportTermCNF`:
trap roots remain in supplied order, constant-false traps disappear, a
constant-true trap produces the trap-refutation outcome, and a nonconstant
claim contributes its negated literal after every nonconstant trap.  The four
outcomes preserve production precedence: a true trap wins over a false claim.

The roots here are already decoded as Boolean constants or RUP literals.  This
is not a proof that the Go builder produces these roots, preserves their source
provenance or order, or implements this Lean function.  It does not connect
roots to bit-blaster terms, source traps, or the source claim; compare actual
emitted clauses; establish settled-path control flow; verify DIMACS
serialization/parsing, solving, or LRAT checking; or discharge `cnf_complete`.
Those Go, lowering, and representation correspondences remain separate.
-/

set_option autoImplicit false

namespace Oak.CNFFinalObligation

open Oak.RupCheck
open Oak.TseitinCNF

inductive Root where
  | constant (value : Bool)
  | literal (value : Literal)
  deriving Repr

def Root.eval (assignment : Assignment) : Root → Bool
  | .constant value => value
  | .literal value => evalLiteral assignment value

/-- Nonconstant trap roots, in their supplied order. -/
def trapClause : List Root → Clause
  | [] => []
  | .constant _ :: rest => trapClause rest
  | .literal literal :: rest => literal :: trapClause rest

def hasTrueTrap : List Root → Bool
  | [] => false
  | .constant true :: _ => true
  | _ :: rest => hasTrueTrap rest

def Counterexample (assignment : Assignment) (traps : List Root) (claim : Root) : Prop :=
  (∃ trap ∈ traps, trap.eval assignment = true) ∨ claim.eval assignment = false

inductive Outcome where
  | trapRefuted
  | claimRefuted
  | proven
  | pending (clause : Clause)
  deriving Repr

/-- The exact precedence and clause construction after all roots are decoded. -/
def build (traps : List Root) (claim : Root) : Outcome :=
  if hasTrueTrap traps = true then .trapRefuted
  else
    match claim with
    | .constant false => .claimRefuted
    | .constant true =>
        match trapClause traps with
        | [] => .proven
        | head :: tail => .pending (head :: tail)
    | .literal literal => .pending (trapClause traps ++ [negate literal])

theorem satisfiesClause_append (assignment : Assignment) (left right : Clause) :
    SatisfiesClause assignment (left ++ right) ↔
      SatisfiesClause assignment left ∨ SatisfiesClause assignment right := by
  constructor
  · rintro ⟨literal, member, holds⟩
    rcases List.mem_append.mp member with member | member
    · exact Or.inl ⟨literal, member, holds⟩
    · exact Or.inr ⟨literal, member, holds⟩
  · rintro (satisfies | satisfies)
    · rcases satisfies with ⟨literal, member, holds⟩
      exact ⟨literal, List.mem_append_left right member, holds⟩
    · rcases satisfies with ⟨literal, member, holds⟩
      exact ⟨literal, List.mem_append_right left member, holds⟩

theorem satisfiesClause_singleton_negate_iff (assignment : Assignment)
    (literal : Literal) :
    SatisfiesClause assignment [negate literal] ↔
      evalLiteral assignment literal = false := by
  cases literal with
  | mk index positive =>
      cases positive <;> cases assignment index <;>
        simp [SatisfiesClause, Holds, negate, evalLiteral]

/-- A trap fires exactly when it is the constant true or its retained literal
is satisfied. -/
theorem trap_fires_iff (assignment : Assignment) (traps : List Root) :
    (hasTrueTrap traps = true ∨ SatisfiesClause assignment (trapClause traps)) ↔
      ∃ trap ∈ traps, trap.eval assignment = true := by
  induction traps with
  | nil => simp [hasTrueTrap, trapClause, SatisfiesClause]
  | cons trap rest ih =>
      cases trap with
      | constant value =>
          cases value <;>
            simp [hasTrueTrap, trapClause, Root.eval, ih]
      | literal literal =>
          change
            (hasTrueTrap rest = true ∨
              SatisfiesClause assignment (literal :: trapClause rest)) ↔
            ∃ trap ∈ Root.literal literal :: rest,
              trap.eval assignment = true
          constructor
          · rintro (trueTrap | satisfies)
            · rcases ih.mp (Or.inl trueTrap) with ⟨trap, member, fires⟩
              exact ⟨trap, by simp [member], fires⟩
            · rcases (show Holds assignment literal ∨
                  SatisfiesClause assignment (trapClause rest) by
                    simpa [SatisfiesClause] using satisfies) with holds | tailSatisfies
              · exact ⟨.literal literal, by simp,
                  (evalLiteral_eq_true_iff assignment literal).mpr holds⟩
              · rcases ih.mp (Or.inr tailSatisfies) with ⟨trap, member, fires⟩
                exact ⟨trap, by simp [member], fires⟩
          · rintro ⟨trap, member, fires⟩
            rcases List.mem_cons.mp member with rfl | member
            · apply Or.inr
              exact ⟨literal, by simp,
                (evalLiteral_eq_true_iff assignment literal).mp fires⟩
            · rcases ih.mpr ⟨trap, member, fires⟩ with trueTrap | tailSatisfies
              · exact Or.inl trueTrap
              · apply Or.inr
                rcases tailSatisfies with ⟨value, valueMember, valueHolds⟩
                exact ⟨value, by simp [valueMember], valueHolds⟩

theorem satisfies_trapClause_iff (assignment : Assignment) (traps : List Root)
    (noTrueTrap : hasTrueTrap traps = false) :
    SatisfiesClause assignment (trapClause traps) ↔
      ∃ trap ∈ traps, trap.eval assignment = true := by
  rw [← trap_fires_iff]
  simp [noTrueTrap]

theorem build_trapRefuted_iff (traps : List Root) (claim : Root) :
    build traps claim = .trapRefuted ↔ hasTrueTrap traps = true := by
  cases trueTrap : hasTrueTrap traps with
  | false =>
      cases claim with
      | constant value =>
          cases value with
          | false => simp [build, trueTrap]
          | true => cases symbolic : trapClause traps <;> simp [build, trueTrap, symbolic]
      | literal literal => simp [build, trueTrap]
  | true => simp [build, trueTrap]

theorem build_claimRefuted_iff (traps : List Root) (claim : Root) :
    build traps claim = .claimRefuted ↔
      hasTrueTrap traps = false ∧ claim = .constant false := by
  cases trueTrap : hasTrueTrap traps with
  | false =>
      cases claim with
      | constant value =>
          cases value with
          | false => simp [build, trueTrap]
          | true => cases symbolic : trapClause traps <;> simp [build, trueTrap, symbolic]
      | literal literal => simp [build, trueTrap]
  | true => simp [build, trueTrap]

theorem build_proven_iff (traps : List Root) (claim : Root) :
    build traps claim = .proven ↔
      hasTrueTrap traps = false ∧ claim = .constant true ∧ trapClause traps = [] := by
  cases trueTrap : hasTrueTrap traps with
  | false =>
      cases claim with
      | constant value =>
          cases value with
          | false => simp [build, trueTrap]
          | true =>
              cases symbolic : trapClause traps <;> simp [build, trueTrap, symbolic]
      | literal literal => simp [build, trueTrap]
  | true => simp [build, trueTrap]

/-- Exact pending shape: symbolic traps retain supplied order, and only a
symbolic claim appends one final literal with reversed polarity. -/
theorem build_pending_iff (traps : List Root) (claim : Root) (clause : Clause) :
    build traps claim = .pending clause ↔
      hasTrueTrap traps = false ∧
        ((claim = .constant true ∧ trapClause traps ≠ [] ∧ trapClause traps = clause) ∨
         ∃ literal, claim = .literal literal ∧
           trapClause traps ++ [negate literal] = clause) := by
  cases trueTrap : hasTrueTrap traps with
  | false =>
      cases claim with
      | constant value =>
          cases value with
          | false => simp [build, trueTrap]
          | true =>
              cases symbolic : trapClause traps <;> simp [build, trueTrap, symbolic]
      | literal literal => simp [build, trueTrap]
  | true => simp [build, trueTrap]

theorem pending_clause_ne_nil {traps : List Root} {claim : Root} {clause : Clause}
    (pending : build traps claim = .pending clause) : clause ≠ [] := by
  rcases (build_pending_iff traps claim clause).mp pending with
    ⟨_, constantClaim | literalClaim⟩
  · rcases constantClaim with ⟨_, nonempty, rfl⟩
    exact nonempty
  · rcases literalClaim with ⟨literal, _, rfl⟩
    simp

/-- A true trap is a counterexample for every assignment, independently of
the claim. -/
theorem trapRefuted_counterexample {traps : List Root} {claim : Root}
    (refuted : build traps claim = .trapRefuted) (assignment : Assignment) :
    Counterexample assignment traps claim := by
  apply Or.inl
  apply (trap_fires_iff assignment traps).mp
  exact Or.inl ((build_trapRefuted_iff traps claim).mp refuted)

/-- With no true trap, a constant-false claim is a counterexample for every
assignment. -/
theorem claimRefuted_counterexample {traps : List Root} {claim : Root}
    (refuted : build traps claim = .claimRefuted) (assignment : Assignment) :
    Counterexample assignment traps claim := by
  rcases (build_claimRefuted_iff traps claim).mp refuted with ⟨_, rfl⟩
  exact Or.inr rfl

/-- A proven outcome has only false constant traps and a true constant claim. -/
theorem proven_not_counterexample {traps : List Root} {claim : Root}
    (proven : build traps claim = .proven) (assignment : Assignment) :
    ¬ Counterexample assignment traps claim := by
  rcases (build_proven_iff traps claim).mp proven with
    ⟨noTrueTrap, rfl, noSymbolicTraps⟩
  rintro (trapFires | claimFalse)
  · have satisfies := (satisfies_trapClause_iff assignment traps noTrueTrap).mpr trapFires
    simp [noSymbolicTraps, SatisfiesClause] at satisfies
  · contradiction

/-- The pending clause is true exactly on the counterexample condition: some
trap fires, or the claim is false. -/
theorem pending_satisfies_iff {traps : List Root} {claim : Root} {clause : Clause}
    (pending : build traps claim = .pending clause) (assignment : Assignment) :
    SatisfiesClause assignment clause ↔ Counterexample assignment traps claim := by
  rcases (build_pending_iff traps claim clause).mp pending with
    ⟨noTrueTrap, constantClaim | literalClaim⟩
  · rcases constantClaim with ⟨rfl, _, rfl⟩
    simp only [Counterexample, Root.eval, Bool.true_eq_false, or_false]
    exact satisfies_trapClause_iff assignment traps noTrueTrap
  · rcases literalClaim with ⟨literal, rfl, rfl⟩
    rw [satisfiesClause_append,
      satisfies_trapClause_iff assignment traps noTrueTrap,
      satisfiesClause_singleton_negate_iff]
    rfl

/-- Compose the exact pending-clause meaning with the existing gate/database
characterization. -/
theorem pending_builderDatabase_iff (assignment : Assignment) (gates : List RawGate)
    {traps : List Root} {claim : Root} {clause : Clause}
    (pending : build traps claim = .pending clause) :
    Models assignment (databaseOfClauses (builderClauses gates clause)) ↔
      GateConsistent assignment gates ∧ Counterexample assignment traps claim := by
  rw [models_builderDatabase_iff, pending_satisfies_iff pending]

theorem evalSequence_models_pending_iff {bound : Nat} {gates : List RawGate}
    (wellFormed : WellFormedFrom bound gates) (assignment : Assignment)
    {traps : List Root} {claim : Root} {clause : Clause}
    (pending : build traps claim = .pending clause) :
    Models (evalSequence gates assignment)
      (databaseOfClauses (builderClauses gates clause)) ↔
      Counterexample (evalSequence gates assignment) traps claim := by
  rw [pending_builderDatabase_iff _ gates pending]
  constructor
  · exact fun modeled => modeled.2
  · exact fun counterexample =>
      ⟨evalSequence_gateConsistent wellFormed assignment, counterexample⟩

namespace Examples

private def trapOne : Literal := ⟨1, true⟩
private def trapTwo : Literal := ⟨2, false⟩
private def claimPos : Literal := ⟨3, true⟩
private def claimNeg : Literal := ⟨3, false⟩

example : build
    [.constant false, .literal trapOne, .literal trapTwo] (.literal claimPos) =
    .pending [trapOne, trapTwo, negate claimPos] := by
  rfl

example : build [] (.literal claimNeg) = .pending [⟨3, true⟩] := by
  rfl

/-- The production precedence/message distinction: the true trap wins even
when the claim is also the constant false. -/
example : build [.literal trapOne, .constant true] (.constant false) =
    .trapRefuted := by
  rfl

example : build [.constant false] (.constant false) = .claimRefuted := by
  rfl

example : build [.constant false, .constant false] (.constant true) = .proven := by
  rfl

example : build [.constant false, .literal trapOne] (.constant true) =
    .pending [trapOne] := by
  rfl

private def assignment : Assignment
  | 1 => false
  | 2 => false
  | 3 => true
  | _ => false

example :
    SatisfiesClause assignment [trapOne, trapTwo, negate claimPos] ↔
      Counterexample assignment
        [.constant false, .literal trapOne, .literal trapTwo] (.literal claimPos) :=
  pending_satisfies_iff (by rfl) assignment

end Examples

end Oak.CNFFinalObligation
