import Oak.ProblemShapeExtracted

set_option autoImplicit false
namespace Oak.ProblemShape

-- This module proves only the header/storage/layout admission prerequisite.
-- It does not yet prove the complete leaf/term/root structural predicate.
-- Array reads and fuel retain the extraction choices in docs/spec/95-extraction.md.
-- Native use additionally requires a live view and live, correctly described
-- arena; this theorem does not manufacture ownership or addressability.
def requiredWords (p : Array UInt32) : Nat :=
  8 + (p.getD 1 0).toNat * 65 + (p.getD 0 0).toNat * 8 +
    (p.getD 2 0).toNat + (p.getD 4 0).toNat * 64

def headerWords64 (p : Array UInt32) : UInt64 :=
  8 + (p.getD 1 0).toUInt64 * 65 + (p.getD 0 0).toUInt64 * 8 +
    (p.getD 2 0).toUInt64 + (p.getD 4 0).toUInt64 * 64

def headerGuard (l : Layout) (p : Array UInt32) : Bool :=
  decide (p.getD 2 0 > 0) && decide (headerWords64 p ≤ p.size.toUInt32.toUInt64) &&
    decide (l.selects_at ≥ l.bits_at) &&
    decide ((p.getD 0 0).toUInt64 * 64 ≤ (l.selects_at - l.bits_at).toUInt64)

-- A checked equational bridge, not a second validator: loop bodies remain the
-- compiler-generated production functions, including their early refusal.
theorem production_header (l : Layout) (p : Array UInt32) (fuel : Nat) :
    problem_shape_valid l p fuel =
      (if p.size.toUInt32 ≥ 8 then do
        let (ok, _) ← problem_shape_valid.loop1 p (headerGuard l p) (p.getD 1 0) 0 fuel
        let (ok, _) ← problem_shape_valid.loop2 p ok (p.getD 0 0) (p.getD 1 0) 0 fuel
        let (ok, _) ← problem_shape_valid.loop3 p ok (p.getD 0 0) (p.getD 2 0) 0 fuel
        pure ok
      else some false) := by
  simp [problem_shape_valid, problem_terms, problem_leaves, problem_roots,
    problem_select_slots, headerGuard, headerWords64, HEADER_WORDS, LEAF_WORDS, TERM_WORDS]

-- No loop can turn initial header refusal back into admission: each loop
-- stops before its reads when ok is false. Zero fuel remains none, not false.
theorem header_required (l : Layout) (p : Array UInt32) (fuel : Nat)
    (accepted : problem_shape_valid l p fuel = some true) :
    p.size.toUInt32 ≥ 8 ∧ headerGuard l p = true := by
  rw [production_header] at accepted
  by_cases size : p.size.toUInt32 ≥ 8
  · refine ⟨size, ?_⟩
    cases guard : headerGuard l p with
    | true => rfl
    | false =>
      cases fuel <;>
        simp [size, guard, problem_shape_valid.loop1, problem_shape_valid.loop2,
          problem_shape_valid.loop3] at accepted
  · simp [size] at accepted

-- Every count is a u32; widening before the arithmetic rules out u64 wrap.
theorem words_exact (p : Array UInt32) : (headerWords64 p).toNat = requiredWords p := by
  have hl := (p.getD 1 0).toNat_lt
  have hn := (p.getD 0 0).toNat_lt
  have hr := (p.getD 2 0).toNat_lt
  have hs := (p.getD 4 0).toNat_lt
  simp only [headerWords64, UInt64.toNat_add, UInt64.toNat_mul, UInt32.toNat_toUInt64]
  unfold requiredWords
  change ((((((8 + ((p.getD 1 0).toNat * 65) % 18446744073709551616) % 18446744073709551616 +
    ((p.getD 0 0).toNat * 8) % 18446744073709551616) % 18446744073709551616 +
    (p.getD 2 0).toNat) % 18446744073709551616 +
    ((p.getD 4 0).toNat * 64) % 18446744073709551616) % 18446744073709551616) = _)
  omega

-- The array-size premise prevents the model's len-to-u32 conversion from
-- truncating. It is explicit rather than assuming arbitrarily large arrays
-- correspond to native Oak views. This is an implication, not a full iff.
theorem admitted_header (l : Layout) (p : Array UInt32) (fuel : Nat)
    (size : p.size < 4294967296)
    (accepted : problem_shape_valid l p fuel = some true) :
    8 ≤ p.size ∧ 0 < (p.getD 2 0).toNat ∧ requiredWords p ≤ p.size ∧
      l.bits_at.toNat + (p.getD 0 0).toNat * 64 ≤ l.selects_at.toNat := by
  obtain ⟨header, guard⟩ := header_required l p fuel accepted
  simp only [headerGuard, Bool.and_eq_true, decide_eq_true_eq] at guard
  rcases guard with ⟨⟨⟨roots, words⟩, order⟩, room⟩
  have len : p.size.toUInt32.toNat = p.size := by
    change p.size % 4294967296 = p.size
    exact Nat.mod_eq_of_lt size
  change (8 : UInt32) ≤ p.size.toUInt32 at header
  rw [UInt32.le_iff_toNat_le, len] at header
  change (0 : UInt32) < p.getD 2 0 at roots
  rw [UInt32.lt_iff_toNat_lt] at roots
  rw [UInt64.le_iff_toNat_le, words_exact, UInt32.toNat_toUInt64, len] at words
  change l.bits_at ≤ l.selects_at at order
  rw [UInt32.le_iff_toNat_le] at order
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_mul, UInt32.toNat_toUInt64,
    UInt32.toNat_toUInt64] at room
  have hn := (p.getD 0 0).toNat_lt
  have hb := l.bits_at.toNat_lt
  have hs := l.selects_at.toNat_lt
  refine ⟨header, roots, words, ?_⟩
  change ((p.getD 0 0).toNat * 64) % 18446744073709551616 ≤
    (l.selects_at - l.bits_at).toNat at room
  rw [UInt32.toNat_sub] at room
  omega

end Oak.ProblemShape
