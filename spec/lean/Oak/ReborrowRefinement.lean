import Oak.Reborrow

/-! # Compiler correspondence for disjoint sibling reborrows

This module transliterates the concrete decision procedure implemented in
`borrowchecker` (`regionEnd`, `regionsOverlap`, `admitReborrow` in
`borrowchecker/borrowchecker.go` and `borrowchecker/derived_region.go`) and
proves it equivalent, on the compiler's representable inputs, to the abstract
admission law `Oak.Reborrow.Split.admits` over `Oak.BorrowRegions.Disjoint`.

The correspondence is scoped: it covers the pure admission decision — region
validity, overlap classification, and the sibling loop — not the checker's
traversal or borrow-state bookkeeping. The Go functions are maintained as
line-for-line transliterations of the definitions below, and differential
tests in `borrowchecker/derived_borrow_test.go` exercise the same laws
against brute-force element semantics. -/

namespace Oak.ReborrowRefinement

open Oak.BorrowRegions (Disjoint Overlap Region)
open Oak.Reborrow

/-- A region exactly as the compiler stores it: signed 64-bit offset and
    length in elements, before any validation. `Int` models Go `int64`; the
    64-bit bound is enforced by the explicit overflow checks below, exactly
    as the Go code enforces it. -/
structure ConcreteRegion where
  offset : Int
  length : Int
  deriving DecidableEq, Repr

/-- Go's `math.MaxInt64`, the bound `regionEnd` checks against. -/
def maxInt64 : Int := 9223372036854775807

/-- Transliteration of `borrowchecker.regionEnd`: validates a region and
    returns its exclusive end, refusing negative fields and int64 overflow. -/
def regionEnd? (r : ConcreteRegion) : Option Int :=
  if r.offset < 0 || r.length < 0 then none
  else if r.length > maxInt64 - r.offset then none
  else some (r.offset + r.length)

/-- Transliteration of `borrowchecker.regionsOverlap`, branch for branch:
    unknown (nil) regions overlap everything; malformed regions overlap
    everything; zero-length regions overlap nothing; regions whose end
    cannot be validated overlap everything; otherwise the half-open
    interval test decides. -/
def regionsOverlap : Option ConcreteRegion → Option ConcreteRegion → Bool
  | none, _ => true
  | _, none => true
  | some a, some b =>
    if a.offset < 0 || a.length < 0 || b.offset < 0 || b.length < 0 then true
    else if a.length == 0 || b.length == 0 then false
    else
      match regionEnd? a, regionEnd? b with
      | some endA, some endB => a.offset < endB && b.offset < endA
      | _, _ => true

/-- Transliteration of `borrowchecker.admitReborrow`: a candidate child is
    admitted only when it may not overlap any live sibling. Unknown regions
    on either side of any comparison reject conservatively. -/
def admitReborrow : List (Option ConcreteRegion) → Option ConcreteRegion → Bool
  | [], _ => true
  | sibling :: rest, newRegion =>
    !regionsOverlap newRegion sibling && admitReborrow rest newRegion

/-- The compiler's validity predicate for a stored region: exactly the
    inputs `regionEnd?` accepts. -/
def Valid (r : ConcreteRegion) : Prop :=
  0 ≤ r.offset ∧ 0 ≤ r.length ∧ r.offset + r.length ≤ maxInt64

instance (r : ConcreteRegion) : Decidable (Valid r) := by
  unfold Valid; exact inferInstance

/-- Abstraction of a validated concrete region into the model's coordinates. -/
def toAbstract (r : ConcreteRegion) : Region :=
  { offset := r.offset.toNat, length := r.length.toNat }

theorem regionEnd?_eq_some_iff_valid {r : ConcreteRegion} :
    regionEnd? r = some (r.offset + r.length) ↔ Valid r := by
  unfold regionEnd? Valid maxInt64
  constructor
  · intro h
    by_cases h1 : r.offset < 0 || r.length < 0
    · simp [h1] at h
    · by_cases h2 : r.length > 9223372036854775807 - r.offset
      · simp [h1, h2] at h
      · simp at h1
        omega
  · intro ⟨h1, h2, h3⟩
    have c1 : (r.offset < 0 || r.length < 0) = false := by simp; omega
    have c2 : (r.length > (9223372036854775807 : Int) - r.offset) = False := by simp; omega
    simp [c1, c2]

/-- Validation fails closed: an invalid region has no end and therefore
    conservatively overlaps every known non-empty region. -/
theorem regionEnd?_eq_none_of_invalid {r : ConcreteRegion} (h : ¬ Valid r) :
    regionEnd? r = none := by
  unfold regionEnd? Valid maxInt64 at *
  by_cases h1 : r.offset < 0 || r.length < 0
  · simp [h1]
  · simp at h1
    have h2 : r.length > 9223372036854775807 - r.offset := by omega
    simp [h2]

/-- **Overlap correspondence.** For every pair of regions the compiler can
    actually store as known (validated) regions, the concrete overlap test
    answers `false` exactly when the abstract regions are provably disjoint. -/
theorem regionsOverlap_eq_false_iff_disjoint {a b : ConcreteRegion}
    (ha : Valid a) (hb : Valid b) :
    regionsOverlap (some a) (some b) = false ↔
      Disjoint (toAbstract a) (toAbstract b) := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, hb3⟩ := hb
  have ea := regionEnd?_eq_some_iff_valid.mpr ⟨ha1, ha2, ha3⟩
  have eb := regionEnd?_eq_some_iff_valid.mpr ⟨hb1, hb2, hb3⟩
  have c1 : (a.offset < 0 || a.length < 0 || b.offset < 0 || b.length < 0) = false := by
    simp; omega
  simp only [regionsOverlap, ea, eb, c1, Bool.false_eq_true, if_false]
  unfold Oak.BorrowRegions.Disjoint Oak.BorrowRegions.Region.finish toAbstract
  by_cases hz : a.length == 0 || b.length == 0
  · simp [hz]
    simp at hz
    omega
  · simp [hz]
    simp at hz
    omega

/-- **Overlap soundness restated at the element level**: a `false` answer
    from the concrete test implies the abstract regions cannot overlap. -/
theorem regionsOverlap_sound {a b : ConcreteRegion}
    (ha : Valid a) (hb : Valid b)
    (h : regionsOverlap (some a) (some b) = false) :
    ¬ Overlap (toAbstract a) (toAbstract b) :=
  Oak.BorrowRegions.disjoint_not_overlap
    ((regionsOverlap_eq_false_iff_disjoint ha hb).mp h)

/-- An unknown region on either side conservatively overlaps. -/
theorem regionsOverlap_unknown_left (r : Option ConcreteRegion) :
    regionsOverlap none r = true := rfl

theorem regionsOverlap_unknown_right (r : Option ConcreteRegion) :
    regionsOverlap r none = true := by
  cases r <;> rfl

/-- A malformed (negative-field) region conservatively overlaps. -/
theorem regionsOverlap_malformed {a : ConcreteRegion} (b : ConcreteRegion)
    (h : a.offset < 0 ∨ a.length < 0) :
    regionsOverlap (some a) (some b) = true := by
  have c : (a.offset < 0 || a.length < 0 || b.offset < 0 || b.length < 0) = true := by
    simp; omega
  unfold regionsOverlap
  simp [c]

/-- An overflowing region conservatively overlaps every non-empty region:
    its end cannot be validated, so the interval test is never reached. -/
theorem regionsOverlap_overflow {a b : ConcreteRegion}
    (hpos : 0 < a.length ∧ 0 < b.length)
    (hnonneg : 0 ≤ a.offset ∧ 0 ≤ b.offset)
    (hover : a.offset + a.length > maxInt64) :
    regionsOverlap (some a) (some b) = true := by
  obtain ⟨hal, hbl⟩ := hpos
  obtain ⟨hao, hbo⟩ := hnonneg
  have hinvalid : ¬ Valid a := by unfold Valid; omega
  have ea := regionEnd?_eq_none_of_invalid hinvalid
  have c1 : (a.offset < 0 || a.length < 0 || b.offset < 0 || b.length < 0) = false := by
    simp; omega
  have cz : (a.length == 0 || b.length == 0) = false := by simp; omega
  simp only [regionsOverlap, ea, c1, cz, Bool.false_eq_true, if_false]

/-- **Admission correspondence.** On the compiler's known validated inputs,
    the concrete sibling loop decides exactly the abstract admission law. -/
theorem admitReborrow_refines {siblings : List ConcreteRegion} {r : ConcreteRegion}
    (hr : Valid r) (hs : ∀ s ∈ siblings, Valid s) :
    admitReborrow (siblings.map some) (some r) =
      Split.admits (siblings.map toAbstract) (toAbstract r) := by
  induction siblings with
  | nil => rfl
  | cons s rest ih =>
    have hvs : Valid s := hs s (by simp)
    have hrest : ∀ x ∈ rest, Valid x := fun x hx => hs x (by simp [hx])
    have hiff := regionsOverlap_eq_false_iff_disjoint hr hvs
    have head : (!regionsOverlap (some r) (some s)) =
        Split.disjointB (toAbstract r) (toAbstract s) := by
      cases hov : regionsOverlap (some r) (some s) with
      | false =>
        have hd : Disjoint (toAbstract r) (toAbstract s) := hiff.mp hov
        simp [Split.disjointB, hd]
      | true =>
        have hd : ¬ Disjoint (toAbstract r) (toAbstract s) := by
          intro hdis
          have hfalse := hiff.mpr hdis
          rw [hov] at hfalse
          exact Bool.noConfusion hfalse
        simp [Split.disjointB, hd]
    simp [admitReborrow, Split.admits, head, ih hrest]

/-- **Fail-closed, unknown candidate**: with any live sibling, a candidate
    whose region is unknown is rejected. -/
theorem admitReborrow_unknown_new_rejected (s : Option ConcreteRegion)
    (rest : List (Option ConcreteRegion)) :
    admitReborrow (s :: rest) none = false := by
  simp [admitReborrow, regionsOverlap_unknown_left]

/-- **Fail-closed, unknown sibling**: a live sibling with unknown region
    rejects every candidate. -/
theorem admitReborrow_unknown_sibling_rejected {siblings : List (Option ConcreteRegion)}
    (h : none ∈ siblings) (r : Option ConcreteRegion) :
    admitReborrow siblings r = false := by
  induction siblings with
  | nil => cases h
  | cons s rest ih =>
    cases h with
    | head =>
      simp [admitReborrow, regionsOverlap_unknown_right]
    | tail _ hmem =>
      simp [admitReborrow, ih hmem]

/-- The first child is always admitted, even with an unknown region: a sole
    reborrow conservatively takes the whole parent authority. -/
theorem admitReborrow_first_child (r : Option ConcreteRegion) :
    admitReborrow [] r = true := rfl

end Oak.ReborrowRefinement
