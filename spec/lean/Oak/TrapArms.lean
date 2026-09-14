/-!
# Oak.TrapArms — an assert as a trap arm of the comparison

The assembler-unit verifier compares an asm unit with its Oak body on the
paths that deliver a result: a branch to a trap block (the checker's
element guard, the lowering's `cbz <cond>, trap` for an `assert`) is an
arm the executor drops, so the asm side's term is the fall-through path's
(docs/spec/94-assembler.md §9, "Asserts under the verifier"). The Oak side
lowers an `assert(cond)` the same way — the condition for its shape, then
nothing: an assert has no value and, where it holds, no effect. The
theorems below are that reading: a computation that traps unless `c`
holds and otherwise yields `v` agrees with the total `v` exactly on the
inputs where `c` holds, and two such computations under the same guard
agree exactly when their values do. The verifier's obligation is the
second: equal values on the surviving paths.
-/

namespace Oak.TrapArms

/-- A guarded computation: `none` is the trap. -/
def guarded {α : Type} (c : Bool) (v : α) : Option α := if c then some v else none

/-- Where the guard holds, the guarded computation is the value. -/
theorem guarded_eq_of_holds {α : Type} (c : Bool) (v : α) (h : c = true) : guarded c v = some v := by
  simp [guarded, h]

/-- Where it does not, the computation traps: no value to compare. -/
theorem guarded_eq_none {α : Type} (c : Bool) (v : α) (h : c = false) : guarded c v = none := by
  simp [guarded, h]

/-- Two computations under one guard agree exactly when their values do
    where the guard holds — the comparison the verifier makes after both
    sides drop the arm. -/
theorem guarded_congr {α : Type} (c : Bool) (v w : α) :
    guarded c v = guarded c w ↔ (c = true → v = w) := by
  cases c <;> simp [guarded]

end Oak.TrapArms
