import Oak.CheckerRefinement

/-!
# Refinement of the seam checker's index-fact meet

`asm/check.go` meets the facts at a control-flow join one register at a
time.  Equal index facts survive directly.  `meetIdx` also reconciles the
shape produced by a bottom-tested loop: one predecessor knows `i < K` and
that the other predecessor's bound register contains `k ≥ K`; the other
knows `i < boundReg`.  The register form is therefore true on both paths.

This file transliterates that per-register decision and proves it sound over
two possibly different predecessor register files.  The Go test in
`asm/check_meet_test.go` renders the production decision table as the
examples at the end, pinning `meetIdx` to this model.
-/

namespace Oak.CheckerMeetRefinement

open Oak.CheckerRefinement

abbrev Reg := Int
abbrev RegFile := Reg → Int
abbrev Consts := List (Reg × Int)

/-- Lookup in the finite rendering of `guardState.consts`.  Go maps have
unique keys; the association-list form makes the refinement executable. -/
def Consts.get : Consts → Reg → Option Int
  | [], _ => none
  | (reg, value) :: rest, query =>
      if query = reg then some value else Consts.get rest query

/-- Every recorded constant is the value in the predecessor's register. -/
def ConstsMean (constants : Consts) (σ : RegFile) : Prop :=
  ∀ reg value, constants.get reg = some value → σ reg = value

/-- Semantic meaning of an index fact.  `meetIdx` only reconciles the first
and third cases with a zero offset, but spelling the slack case keeps this
predicate faithful to `idxFact`. -/
def IdxMeans (σ : RegFile) (index : Reg) (fact : IdxFact) : Prop :=
  if fact.boundReg < 0 then
    σ index < fact.bound
  else if fact.slack = true then
    σ index + fact.bound ≤ σ fact.boundReg
  else
    σ index < σ fact.boundReg

/-- The accepting branch of `reconcileIdx`: `constFact` is an immediate,
non-slack bound; `regFact` is a plain register bound; and the constant-side
predecessor says that bound register contains at least the immediate. -/
def CanReconcile (constants : Consts) (constFact regFact : IdxFact) : Prop :=
  constFact.boundReg < 0 ∧
  constFact.slack = false ∧
  0 ≤ regFact.boundReg ∧
  regFact.slack = false ∧
  regFact.bound = 0 ∧
  match constants.get regFact.boundReg with
  | some value => constFact.bound ≤ value
  | none => False

/-- Executable spelling of `CanReconcile`, matching the guards in Go. -/
def canReconcile (constants : Consts) (constFact regFact : IdxFact) : Bool :=
  decide (constFact.boundReg < 0) &&
  decide (constFact.slack = false) &&
  decide (0 ≤ regFact.boundReg) &&
  decide (regFact.slack = false) &&
  decide (regFact.bound = 0) &&
  match constants.get regFact.boundReg with
  | some value => decide (constFact.bound ≤ value)
  | none => false

theorem canReconcile_eq_true (constants : Consts) (constFact regFact : IdxFact) :
    canReconcile constants constFact regFact = true ↔
      CanReconcile constants constFact regFact := by
  unfold canReconcile CanReconcile
  cases hget : constants.get regFact.boundReg with
  | none => simp
  | some value => simp [and_assoc]

/-- The per-register decision made by `meetIdx`: equality, then reconciliation
in either orientation, otherwise refusal. -/
def meetFact (aConstants : Consts) (aFact : IdxFact)
    (bConstants : Consts) (bFact : IdxFact) : Option IdxFact :=
  if aFact = bFact then
    some aFact
  else if canReconcile aConstants aFact bFact = true then
    some bFact
  else if canReconcile bConstants bFact aFact = true then
    some aFact
  else
    none

/-- Transitivity justifies `reconcileIdx` on its constant predecessor. -/
theorem canReconcile_sound (constants : Consts) (constFact regFact : IdxFact)
    (σ : RegFile) (index : Reg)
    (hcan : CanReconcile constants constFact regFact)
    (hconstants : ConstsMean constants σ)
    (hindex : IdxMeans σ index constFact) :
    IdxMeans σ index regFact := by
  rcases hcan with ⟨hconstReg, hconstSlack, hregReg, hregSlack, hregBound, hvalue⟩
  cases hget : constants.get regFact.boundReg with
  | none => simp [hget] at hvalue
  | some value =>
      have hregValue : σ regFact.boundReg = value :=
        hconstants regFact.boundReg value hget
      have hbound : constFact.bound ≤ value := by
        simpa [hget] using hvalue
      have himmediate : σ index < constFact.bound := by
        simpa [IdxMeans, hconstReg] using hindex
      have hregister : σ index < σ regFact.boundReg := by
        omega
      simpa [IdxMeans, show ¬regFact.boundReg < 0 by omega, hregSlack] using hregister

/-- **Index-meet refinement.** Whenever the checker retains a fact at a
join, that fact holds on both predecessor states. -/
theorem meetFact_sound (aConstants bConstants : Consts) (aFact bFact out : IdxFact)
    (aσ bσ : RegFile) (index : Reg)
    (hmeet : meetFact aConstants aFact bConstants bFact = some out)
    (haConstants : ConstsMean aConstants aσ)
    (hbConstants : ConstsMean bConstants bσ)
    (ha : IdxMeans aσ index aFact)
    (hb : IdxMeans bσ index bFact) :
    IdxMeans aσ index out ∧ IdxMeans bσ index out := by
  unfold meetFact at hmeet
  split at hmeet
  · rename_i hequal
    subst bFact
    simp only [Option.some.injEq] at hmeet
    subst out
    exact ⟨ha, hb⟩
  · split at hmeet
    · rename_i hab
      simp only [Option.some.injEq] at hmeet
      subst out
      exact ⟨canReconcile_sound aConstants aFact bFact aσ index
        ((canReconcile_eq_true aConstants aFact bFact).mp hab) haConstants ha, hb⟩
    · split at hmeet
      · rename_i hba
        simp only [Option.some.injEq] at hmeet
        subst out
        exact ⟨ha, canReconcile_sound bConstants bFact aFact bσ index
          ((canReconcile_eq_true bConstants bFact aFact).mp hba) hbConstants hb⟩
      · simp at hmeet

/-! ## Production decision pins

Each line is rendered from `meetIdx` by `asm/check_meet_test.go`. -/

example : meetFact [(23, 512)] ⟨(-1), 512, false, 0⟩ [] ⟨23, 0, false, 0⟩ = some ⟨23, 0, false, 0⟩ := by decide
example : meetFact [] ⟨23, 0, false, 0⟩ [(23, 512)] ⟨(-1), 512, false, 0⟩ = some ⟨23, 0, false, 0⟩ := by decide
example : meetFact [(23, 511)] ⟨(-1), 512, false, 0⟩ [] ⟨23, 0, false, 0⟩ = none := by decide
example : meetFact [(23, 512)] ⟨(-1), 512, false, 0⟩ [] ⟨23, 4, true, 0⟩ = none := by decide
example : meetFact [(23, 512)] ⟨(-1), 512, false, 0⟩ [] ⟨(-1), 512, false, 0⟩ = some ⟨(-1), 512, false, 0⟩ := by decide

end Oak.CheckerMeetRefinement
