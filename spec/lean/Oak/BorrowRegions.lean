namespace Oak.BorrowRegions

/-- A half-open element region `[offset, offset + length)`. -/
structure Region where
  offset : Nat
  length : Nat
  deriving DecidableEq, Repr

def Region.finish (r : Region) : Nat := r.offset + r.length

/-- Two known half-open regions overlap only when both contain elements and
    each begins before the other's end. Empty regions overlap nothing. -/
def Overlap (a b : Region) : Prop :=
  0 < a.length ∧
  0 < b.length ∧
  a.offset < b.finish ∧
  b.offset < a.finish

/-- Constructive reasons two half-open regions are disjoint. Empty regions are
    disjoint regardless of where their offset lies. -/
def Disjoint (a b : Region) : Prop :=
  a.length = 0 ∨
  b.length = 0 ∨
  a.finish ≤ b.offset ∨
  b.finish ≤ a.offset

/-- Region overlap does not depend on argument order. -/
theorem overlap_symmetric {a b : Region} : Overlap a b ↔ Overlap b a := by
  constructor
  · intro h
    exact ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩
  · intro h
    exact ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩

/-- Region disjointness does not depend on argument order. -/
theorem disjoint_symmetric {a b : Region} : Disjoint a b ↔ Disjoint b a := by
  constructor <;> intro h
  · rcases h with ha | hb | hab | hba
    · exact Or.inr (Or.inl ha)
    · exact Or.inl hb
    · exact Or.inr (Or.inr (Or.inr hab))
    · exact Or.inr (Or.inr (Or.inl hba))
  · rcases h with hb | ha | hba | hab
    · exact Or.inr (Or.inl hb)
    · exact Or.inl ha
    · exact Or.inr (Or.inr (Or.inr hba))
    · exact Or.inr (Or.inr (Or.inl hab))

/-- Provably disjoint regions cannot overlap. -/
theorem disjoint_not_overlap {a b : Region} (h : Disjoint a b) : ¬ Overlap a b := by
  intro hov
  have haPos : 0 < a.length := hov.1
  have hbPos : 0 < b.length := hov.2.1
  have habStart : a.offset < b.finish := hov.2.2.1
  have hbaStart : b.offset < a.finish := hov.2.2.2
  rcases h with ha | hb | hab | hba
  · simp [ha] at haPos
  · simp [hb] at hbPos
  · exact (Nat.not_lt_of_ge hab) habStart
  · exact (Nat.not_lt_of_ge hba) hbaStart

/-- Adjacent half-open regions are disjoint. -/
theorem adjacent_disjoint (offset leftLen rightLen : Nat) :
    Disjoint
      { offset := offset, length := leftLen }
      { offset := offset + leftLen, length := rightLen } := by
  right
  right
  left
  simp [Region.finish]

/-- A zero-length region is constructively disjoint from every region. -/
theorem zero_length_disjoint (offset : Nat) (other : Region) :
    Disjoint { offset := offset, length := 0 } other := by
  left
  rfl

/-- A zero-length region overlaps nothing under half-open semantics. -/
theorem zero_length_not_overlap (offset : Nat) (other : Region) :
    ¬ Overlap { offset := offset, length := 0 } other := by
  exact disjoint_not_overlap (zero_length_disjoint offset other)

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
