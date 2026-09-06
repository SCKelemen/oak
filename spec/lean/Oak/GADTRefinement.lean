import Oak.PatternAnalysis

namespace Oak.GADTRefinement

/-- Constructor result indices are either quantified parameters or fixed
    semantic type identities. -/
inductive Index where
  | param : Nat → Index
  | atom : Nat → Index
  deriving DecidableEq, Repr

abbrev Substitution := List (Nat × Nat)

def Lookup (parameter : Nat) : Substitution → Option Nat
  | [] => none
  | (name, value) :: rest =>
      if name = parameter then some value else Lookup parameter rest

/-- Executable equality solving mirrored by the checker: a parameter binds on
    first occurrence and every later occurrence must equal that binding. -/
def UnifyIndex (substitution : Substitution) (expected : Index) (actual : Nat) :
    Option Substitution :=
  match expected with
  | .atom value => if value = actual then some substitution else none
  | .param parameter =>
      match Lookup parameter substitution with
      | none => some ((parameter, actual) :: substitution)
      | some prior => if prior = actual then some substitution else none

def Solve : Substitution → List Index → List Nat → Option Substitution
  | substitution, [], [] => some substitution
  | substitution, expected :: expectedRest, actual :: actualRest =>
      match UnifyIndex substitution expected actual with
      | none => none
      | some next => Solve next expectedRest actualRest
  | _, _, _ => none

structure Constructor where
  name : Nat
  result : List Index
  deriving DecidableEq, Repr

def Reachable (constructors : List Constructor) (actual : List Nat) :
    List Constructor :=
  constructors.filter fun constructor =>
    (Solve [] constructor.result actual).isSome

def ReachableNames (constructors : List Constructor) (actual : List Nat) :
    List Nat :=
  (Reachable constructors actual).map Constructor.name

theorem fixed_index_succeeds (value : Nat) (substitution : Substitution) :
    UnifyIndex substitution (.atom value) value = some substitution := by
  simp [UnifyIndex]

theorem fixed_index_mismatch_rejected
    (expected actual : Nat)
    (substitution : Substitution)
    (hne : expected ≠ actual) :
    UnifyIndex substitution (.atom expected) actual = none := by
  simp [UnifyIndex, hne]

theorem fresh_parameter_introduces_equality
    (parameter actual : Nat) :
    UnifyIndex [] (.param parameter) actual = some [(parameter, actual)] := by
  simp [UnifyIndex, Lookup]

/-- Reusing a constructor result parameter is an equality proposition: the
    second actual index is accepted exactly when it equals the first. -/
theorem repeated_parameter_iff_equal
    (parameter first second : Nat) :
    Solve [] [.param parameter, .param parameter] [first, second] =
        some [(parameter, first)] ↔
      first = second := by
  by_cases h : first = second
  · simp [Solve, UnifyIndex, Lookup, h]
  · simp [Solve, UnifyIndex, Lookup, h]

theorem arity_mismatch_rejected
    (index : Index)
    (actual : Nat) :
    Solve [] [index] [actual, actual] = none := by
  cases index with
  | param parameter => simp [Solve, UnifyIndex, Lookup]
  | atom expected =>
      by_cases h : expected = actual
      · simp [Solve, UnifyIndex, Lookup, h]
      · simp [Solve, UnifyIndex, Lookup, h]

/-- A constructor with a contradictory fixed result index is absent from the
    reachable semantic case provider consumed by pattern analysis. -/
theorem fixed_mismatch_excluded_from_reachable
    (name expected actual : Nat)
    (hne : expected ≠ actual) :
    name ∉ ReachableNames [{ name := name, result := [.atom expected] }] [actual] := by
  simp [ReachableNames, Reachable, Solve, UnifyIndex, hne]

/-- A matching fixed result index contributes the constructor to the reachable
    case set. -/
theorem fixed_match_in_reachable (name index : Nat) :
    name ∈ ReachableNames [{ name := name, result := [.atom index] }] [index] := by
  simp [ReachableNames, Reachable, Solve, UnifyIndex]

/-- The solver's reachable set plugs directly into the abstract coverage law:
    constructors excluded by index solving are not required for exhaustiveness. -/
theorem solver_excluded_case_not_required
    (constructors : List Constructor)
    (actual : List Nat)
    (name : Nat)
    (hexcluded : name ∉ ReachableNames constructors actual) :
    ¬ Oak.PatternAnalysis.ReachableCase
        (constructors.map Constructor.name)
        (ReachableNames constructors actual)
        name := by
  exact Oak.PatternAnalysis.unreachable_case_not_required hexcluded

end Oak.GADTRefinement
