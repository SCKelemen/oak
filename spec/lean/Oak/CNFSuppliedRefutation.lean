import Oak.TseitinCNF

/-!
# Kernel-checked local RUP implications for a supplied certificate

This small proof constructor uses the same unit/falsified-clause rules as
RupCheck. Each supplied hint clause must already be a logical consequence of
the original ordered CNF. Deletions therefore need not erase logical facts.
The external projector must bind each original ID to its exact ordered clause,
reject ID reuse/forward or deleted hints, and preserve the authenticated input.
No parser execution, Go receipt, solver verdict or native evaluator is trusted
by the theorem: every addition's Boolean check reduces in the Lean kernel.
-/
set_option autoImplicit false
namespace Oak.CNFSuppliedRefutation
open Oak.RupCheck Oak.TseitinCNF

def residual (assigned clause : List Literal) : List Literal :=
  clause.filter fun literal => decide (negate literal ∉ assigned)

theorem mem_residual {assigned clause : List Literal} {literal : Literal} :
    literal ∈ residual assigned clause ↔ literal ∈ clause ∧ negate literal ∉ assigned := by
  simp [residual]

theorem residual_nil {assigned clause : List Literal}
    (empty : residual assigned clause = []) : Falsified assigned clause := by
  intro literal member
  by_cases present : negate literal ∈ assigned
  · exact present
  · have impossible := mem_residual.mpr ⟨member, present⟩
    rw [empty] at impossible
    contradiction

theorem residual_unit {assigned clause : List Literal} {unit : Literal} {rest : List Literal}
    (shape : residual assigned clause = unit :: rest)
    (same : rest.all (fun literal => decide (literal = unit)) = true) :
    UnitUnder assigned clause unit := by
  have present : unit ∈ residual assigned clause := by simp [shape]
  refine ⟨(mem_residual.mp present).1, ?_⟩
  intro literal member
  by_cases opposite : negate literal ∈ assigned
  · exact Or.inr opposite
  · have found := mem_residual.mpr ⟨member, opposite⟩
    rw [shape] at found
    rcases List.mem_cons.mp found with equal | member
    · exact Or.inl equal
    · have equal := (List.all_eq_true.mp same) literal member
      exact Or.inl (of_decide_eq_true equal)

/-- Conflict is required at the final supplied hint; every earlier hint is
unit under the growing assumptions. Repeated occurrences of the same unit
are admitted; distinct residual literals refuse. -/
def propagate : List Literal → List Clause → Bool
  | _, [] => false
  | assigned, clause :: rest =>
      match residual assigned clause with
      | [] => rest.isEmpty
      | unit :: remaining =>
          if remaining.all (fun literal => decide (literal = unit)) then
            propagate (unit :: assigned) rest else false

theorem propagate_sound {assignment : Assignment} {assigned : List Literal}
    {hints : List Clause} (checked : propagate assigned hints = true)
    (models : SatisfiesClauses assignment hints) : ¬ Assigned assignment assigned := by
  induction hints generalizing assigned with
  | nil => simp [propagate] at checked
  | cons clause rest ih =>
      cases remaining : residual assigned clause with
      | nil =>
          intro assumed
          obtain ⟨literal, member, holds⟩ := models clause (by simp)
          exact holds_not_negate holds (assumed _ (residual_nil remaining literal member))
      | cons unit tail =>
          simp only [propagate, remaining] at checked
          split at checked
          · rename_i allSame
            intro assumed
            apply ih checked (fun next member => models next (List.mem_cons_of_mem _ member))
            have unitHolds := unit_sound (models clause (by simp))
              (residual_unit remaining allSame) assumed
            intro literal member
            rcases List.mem_cons.mp member with rfl | member
            · exact unitHolds
            · exact assumed literal member
          · contradiction

def inconsistent (assigned : List Literal) : Bool :=
  assigned.any fun literal => decide (negate literal ∈ assigned)

theorem inconsistent_sound {assignment : Assignment} {assigned : List Literal}
    (checked : inconsistent assigned = true) : ¬ Assigned assignment assigned := by
  simp only [inconsistent, List.any_eq_true, decide_eq_true_eq] at checked
  obtain ⟨literal, present, opposite⟩ := checked
  intro assumed
  exact holds_not_negate (assumed literal present) (assumed _ opposite)

def checkRup (clause : Clause) (hints : List Clause) : Bool :=
  inconsistent (clause.map negate) || propagate (clause.map negate) hints

theorem checkRup_sound {assignment : Assignment} {clause : Clause} {hints : List Clause}
    (checked : checkRup clause hints = true) (models : SatisfiesClauses assignment hints) :
    SatisfiesClause assignment clause := by
  classical
  apply Classical.byContradiction
  intro absent
  have assumed : Assigned assignment (clause.map negate) := by
    intro literal member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact (negate_holds_iff assignment original).mpr
      (fun holds => absent ⟨original, originalMember, holds⟩)
  simp only [checkRup, Bool.or_eq_true] at checked
  rcases checked with clash | propagated
  · exact inconsistent_sound clash assumed
  · exact propagate_sound propagated models assumed

def Consequence (original : List Clause) (clause : Clause) : Prop :=
  ∀ assignment, SatisfiesClauses assignment original → SatisfiesClause assignment clause

inductive HintConsequences (original : List Clause) : List Clause → Prop where
  | nil : HintConsequences original []
  | cons {clause : Clause} {rest : List Clause}
      (head : Consequence original clause) (tail : HintConsequences original rest) :
      HintConsequences original (clause :: rest)

theorem HintConsequences.models {original hints : List Clause}
    (known : HintConsequences original hints) (assignment : Assignment)
    (model : SatisfiesClauses assignment original) : SatisfiesClauses assignment hints := by
  induction known with
  | nil => intro clause member; contradiction
  | cons head tail ih =>
      intro clause member
      rcases List.mem_cons.mp member with rfl | member
      · exact head assignment model
      · exact ih clause member

/-- A balanced, order-preserving carrier avoids linear clause-ID lookup in
large supplied proofs. It is only a representation of the original list. -/
inductive Original where
  | empty
  | leaf (clause : Clause)
  | branch (left right : Original)

def Original.toList : Original → List Clause
  | .empty => []
  | .leaf clause => [clause]
  | .branch left right => left.toList ++ right.toList

def Original.lookup : Original → List Bool → Option Clause
  | .leaf clause, [] => some clause
  | .branch left _, false :: rest => left.lookup rest
  | .branch _ right, true :: rest => right.lookup rest
  | _, _ => none

theorem Original.lookup_mem {original : Original} {path : List Bool} {clause : Clause}
    (found : original.lookup path = some clause) : clause ∈ original.toList := by
  induction original generalizing path with
  | empty => simp [Original.lookup] at found
  | leaf entry =>
      cases path with
      | nil => cases Option.some.inj found; simp [Original.toList]
      | cons step rest => simp [Original.lookup] at found
  | branch left right leftIH rightIH =>
      cases path with
      | nil => simp [Original.lookup] at found
      | cons step rest =>
          cases step with
          | false => exact List.mem_append_left _ (leftIH found)
          | true => exact List.mem_append_right _ (rightIH found)

theorem original_consequence (original : Original) (path : List Bool) (clause : Clause)
    (found : original.lookup path = some clause) : Consequence original.toList clause := by
  intro assignment model
  exact model clause (Original.lookup_mem found)

theorem checked_addition {original : List Clause} {clause : Clause} {hints : List Clause}
    (checked : checkRup clause hints = true) (known : HintConsequences original hints) :
    Consequence original clause := by
  intro assignment model
  exact checkRup_sound checked (known.models assignment model)

theorem empty_refutes {original : List Clause} (empty : Consequence original []) :
    Unsatisfiable (databaseOfClauses original) := by
  intro assignment model
  obtain ⟨literal, impossible, _⟩ := empty assignment
    ((models_databaseOfClauses_iff assignment original).mp model)
  contradiction

end Oak.CNFSuppliedRefutation
