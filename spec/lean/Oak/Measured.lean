/-!
# Oak.Measured — measured constants

Model of `docs/spec/60-effects-allocation.md` section 10b (the ml pilot's
ask 5.21). A measured constant is declared with an inclusive range and a
pinned value inside it: `TILE: u32 (measured: 16, 1024) = 128`. At load the
program asks the host for a value; the answer is admitted only inside the
range, and a value outside it stops the program before any code that reads
the constant runs. `load` is that rule, and the theorems are what a program
may rely on: whatever the host supplies, the constant a run computes with
lies in the declared range (`load_in_range`), a host that supplies nothing
gives the pinned value (`load_none`), and the pinned value is always
admitted (`load_pinned`). The Lean extraction therefore renders the
constant as an opaque value with the range as a hypothesis
(`95-extraction.md` section 3): a theorem over the range covers every run
the program can have.
-/

namespace Oak.Measured

/-- A measured constant's declaration: the range and the pinned value. -/
structure Decl where
  lo : Int
  hi : Int
  pinned : Int
  pinned_in : lo ≤ pinned ∧ pinned ≤ hi

/-- Whether a value lies in the declared range. -/
def InRange (d : Decl) (v : Int) : Prop := d.lo ≤ v ∧ v ≤ d.hi

/-- The load: the host's answer (none when it supplies nothing) becomes the
constant's value when it lies in the range; otherwise the program stops. -/
def load (d : Decl) : Option Int → Option Int
  | none => some d.pinned
  | some v => if d.lo ≤ v ∧ v ≤ d.hi then some v else none

/-- A host that supplies nothing gives the pinned value. -/
theorem load_none (d : Decl) : load d none = some d.pinned := rfl

/-- The pinned value is always admitted. -/
theorem load_pinned (d : Decl) : load d (some d.pinned) = some d.pinned := by
  simp [load, d.pinned_in]

/-- A value outside the range stops the program. -/
theorem load_outside (d : Decl) (v : Int) (h : ¬ (d.lo ≤ v ∧ v ≤ d.hi)) :
    load d (some v) = none := by
  simp [load, h]

/-- **The constant a run computes with is in the range**, whatever the host
supplied: the hypothesis every theorem over the range may take. -/
theorem load_in_range (d : Decl) (supplied : Option Int) (v : Int)
    (h : load d supplied = some v) : InRange d v := by
  unfold InRange
  cases supplied with
  | none =>
    simp [load] at h
    rw [← h]
    exact d.pinned_in
  | some w =>
    by_cases hw : d.lo ≤ w ∧ w ≤ d.hi
    · simp [load, hw] at h
      rw [← h]
      exact hw
    · simp [load, hw] at h

/-- A run either computes with a value in the range or does not run: there
is no third outcome. -/
theorem load_dichotomy (d : Decl) (supplied : Option Int) :
    (∃ v, load d supplied = some v ∧ InRange d v) ∨ load d supplied = none := by
  cases h : load d supplied with
  | none => exact Or.inr rfl
  | some v => exact Or.inl ⟨v, rfl, load_in_range d supplied v h⟩

end Oak.Measured
