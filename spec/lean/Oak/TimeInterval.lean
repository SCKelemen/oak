/-!
# Oak.TimeInterval — interval time readings under an attested bound

`stdlib/time.oak` gives a `TimeSource` an attested error bound and an
interval reading `[wall - bound, wall + bound]`; `stdlib/timesim.oak`
tracks the wall clock's true departure (`skew`) from the skew-free
timeline and can break the bound or withdraw the attestation as faults
(`docs/spec/110-testing.md`, "Simulated time"). This module states what
the reading means and proves what a clock-ordered consumer relies on:

* `honest_iff`: the interval contains the true time exactly when the
  departure is within the bound — so a bound break is precisely a
  dishonest interval, which `timesim_interval_honest` detects.
* `before_sound`: two honest intervals that are definitely ordered
  (`a.latest < b.earliest`) order their true times the same way.
* `overlap_unordered`: overlapping intervals prove nothing about order.
* `refusal_claims_nothing`: an unattested source yields no ordering at all,
  so a consumer that refuses never orders what it cannot.
-/

namespace Oak.TimeInterval

structure Interval where
  earliest : Int
  latest : Int
  deriving DecidableEq, Repr

/-- The reading `time_interval` returns for an attested bound. -/
def interval (wall bound : Int) : Interval := ⟨wall - bound, wall + bound⟩

/-- The simulation's true time: the wall reading less its recorded skew. -/
def truth (wall skew : Int) : Int := wall - skew

def contains (i : Interval) (t : Int) : Prop := i.earliest ≤ t ∧ t ≤ i.latest

/-- Definitely-before, as `time_interval_before` computes it. -/
def before (a b : Interval) : Prop := a.latest < b.earliest

theorem honest_iff (wall bound skew : Int) :
    contains (interval wall bound) (truth wall skew) ↔ (-bound ≤ skew ∧ skew ≤ bound) := by
  simp only [contains, interval, truth]
  constructor
  · intro h; omega
  · intro h; omega

/-- A bound break — skew beyond the bound — is a dishonest interval. -/
theorem bound_break_dishonest (wall bound skew : Int) (h : bound < skew ∨ skew < -bound) :
    ¬ contains (interval wall bound) (truth wall skew) := by
  intro hc
  have := (honest_iff wall bound skew).mp hc
  omega

theorem before_sound (a b : Interval) (ta tb : Int)
    (ha : contains a ta) (hb : contains b tb) (hab : before a b) : ta < tb := by
  simp only [contains] at ha hb
  simp only [before] at hab
  omega

/-- Overlapping intervals can hold true times in either order. -/
theorem overlap_unordered (a b : Interval) (hover : b.earliest ≤ a.latest) (hover' : a.earliest ≤ b.latest)
    (hwf : a.earliest ≤ a.latest) (hwf' : b.earliest ≤ b.latest) :
    ∃ ta tb, contains a ta ∧ contains b tb ∧ tb ≤ ta := by
  refine ⟨a.latest, b.earliest, ⟨hwf, Int.le_refl _⟩, ⟨Int.le_refl _, hwf'⟩, hover⟩

/-- A consumer's ordering decision: available only under attestation. -/
def order (attested : Bool) (a b : Interval) : Option Bool :=
  if attested then some (decide (a.latest < b.earliest)) else none

theorem refusal_claims_nothing (a b : Interval) : order false a b = none := rfl

theorem order_sound (a b : Interval) (h : order true a b = some true) : before a b := by
  unfold order at h
  simp at h
  exact h

end Oak.TimeInterval
