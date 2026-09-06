namespace Oak.BorrowRegions

/-- A half-open element region `[offset, offset + length)`. -/
structure Region where
  offset : Nat
  length : Nat
  deriving DecidableEq, Repr

def Region.finish (r : Region) : Nat := r.offset + r.length

/-- Two known regions overlap exactly when each starts before the other's end. -/
def Overlap (a b : Region) : Prop :=
  a.offset < b.finish ∧ b.offset < a.finish

/-- Disjointness is the dual half-open ordering relation. -/
def Disjoint (a b : Region) : Prop :=
  a.finish ≤ b.offset ∨ b.finish ≤ a.offset

/-- Region overlap does not depend on argument order. -/
theorem overlap_symmetric {a b : Region} : Overlap a b ↔ Overlap b a := by
  constructor <;> intro h <;> exact ⟨h.2, h.1⟩

/-- Region disjointness does not depend on argument order. -/
theorem disjoint_symmetric {a b : Region} : Disjoint a b ↔ Disjoint b a := by
  constructor <;> intro h
  · cases h with
    | inl hab => exact Or.inr hab
    | inr hba => exact Or.inl hba
  · cases h with
    | inl hba => exact Or.inr hba
    | inr hab => exact Or.inl hab

/-- Provably disjoint regions cannot overlap. -/
theorem disjoint_not_overlap {a b : Region} (h : Disjoint a b) : ¬ Overlap a b := by
  intro hov
  cases h with
  | inl hab => exact (Nat.not_lt_of_ge hab) hov.1
  | inr hba => exact (Nat.not_lt_of_ge hba) hov.2

/-- Adjacent half-open regions are disjoint. -/
theorem adjacent_disjoint (offset leftLen rightLen : Nat) :
    Disjoint
      { offset := offset, length := leftLen }
      { offset := offset + leftLen, length := rightLen } := by
  left
  simp [Region.finish]

/-- A zero-length region overlaps nothing under half-open semantics. -/
theorem zero_length_not_overlap (offset : Nat) (other : Region) :
    ¬ Overlap { offset := offset, length := 0 } other := by
  intro h
  simp [Overlap, Region.finish] at h
  exact (Nat.not_lt_of_ge (Nat.le_refl offset)) h.2

/-- `none` represents a region the compiler cannot establish statically. -/
def MayOverlap : Option Region -> Option Region -> Prop
  | some a, some b => Overlap a b
  | _, _ => True

/-- Unknown region information fails closed: the compiler must assume conflict. -/
theorem unknown_left_may_overlap (known : Option Region) : MayOverlap none known := by
  cases known <;> trivial

/-- Unknown region information fails closed regardless of which span is unknown. -/
theorem unknown_right_may_overlap (known : Option Region) : MayOverlap known none := by
  cases known <;> trivial

/-- Two known disjoint regions are not conservatively classified as overlapping. -/
theorem known_disjoint_not_may_overlap {a b : Region} (h : Disjoint a b) :
    ¬ MayOverlap (some a) (some b) := by
  exact disjoint_not_overlap h

end Oak.BorrowRegions
