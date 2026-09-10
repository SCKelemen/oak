/-!
# Oak.Regions — writable-region disjointness obligations

The REPL's `:lean` command states every `OAK-B0110` obligation — a
writable-disjointness fact an `unsafe` block admitted rather than proved
(`Oak.Unsafe`, docs/spec/50-borrowing.md section 6) — as a theorem over
half-open element regions `[lo, hi)`. When the borrow checker knew both
regions statically the statement is decidable and the REPL emits `decide`,
so an admitted assumption that is in fact false fails to elaborate rather
than passing silently; when a bound was symbolic the statement carries the
regions as variables for the programmer to constrain.
-/

namespace Oak.Regions

/-- A half-open region of element indices `[lo, hi)`. -/
structure Region where
  lo : Int
  hi : Int
  deriving Repr, DecidableEq

/-- Two regions are disjoint when one ends before the other begins. Empty
regions are disjoint from everything. -/
def Disjoint (a b : Region) : Prop :=
  a.hi ≤ b.lo ∨ b.hi ≤ a.lo ∨ a.hi ≤ a.lo ∨ b.hi ≤ b.lo

instance (a b : Region) : Decidable (Disjoint a b) := by
  unfold Disjoint; infer_instance

theorem disjoint_symm {a b : Region} (h : Disjoint a b) : Disjoint b a := by
  unfold Disjoint at *
  omega

/-- No index lies in both of two disjoint regions. -/
theorem disjoint_no_common (a b : Region) (h : Disjoint a b) (i : Int) :
    ¬ (a.lo ≤ i ∧ i < a.hi ∧ b.lo ≤ i ∧ i < b.hi) := by
  unfold Disjoint at h
  omega

/-- Two regions sharing an index are not disjoint: the converse, so a
concrete overlap refutes an admitted assumption. -/
theorem not_disjoint_of_common (a b : Region) (i : Int)
    (h : a.lo ≤ i ∧ i < a.hi ∧ b.lo ≤ i ∧ i < b.hi) : ¬ Disjoint a b := by
  intro hd
  exact disjoint_no_common a b hd i h

end Oak.Regions
