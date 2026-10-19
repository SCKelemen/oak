import Oak.Stdlib.BytesExtracted

/-!
# Oak.Stdlib.BytesLaws — laws of the extracted `bytes` package

`BytesExtracted.lean` is generated from `stdlib/bytes.oak`. These theorems are
about the extracted array-value semantics. The extractor and compiler
correspondence described by `docs/spec/95-extraction.md` remains trusted;
these are not implementation-refinement or runtime aliasing proofs.
-/

namespace Oak.Stdlib.Bytes

/-- An offset beyond the logical length is rejected without ever forming the
potentially wrapping sum `offset + width`. -/
theorem range_fits_offset_past_end (length offset width : UInt32) (fuel : Nat)
    (h : offset > length) :
    range_fits length offset width fuel = some false := by
  simp [range_fits, h]

/-- A zero-width range at the end is valid. -/
theorem range_fits_empty_at_end (length : UInt32) (fuel : Nat) :
    range_fits length length 0 fuel = some true := by
  simp [range_fits]

/-- A short destination is rejected before the copy loop and is returned
byte-for-byte unchanged, independently of the available loop fuel. -/
theorem copy_short_atomic (dst src : Array UInt8) (fuel : Nat)
    (h : dst.size.toUInt32 < src.size.toUInt32) :
    copy_into dst src fuel = some (.Err .DestinationTooSmall, dst) := by
  simp [copy_into, h]

/-- Different logical lengths compare unequal without entering the comparison
loop, independently of the available loop fuel. -/
theorem equal_length_mismatch (left right : Array UInt8) (fuel : Nat)
    (h : left.size.toUInt32 ≠ right.size.toUInt32) :
    equal left right fuel = some false := by
  simp [equal, h]

/-- Searching an empty byte sequence completes immediately and reports ordinary
absence. One fuel step is enough to evaluate the loop guard. -/
theorem find_empty (needle : UInt8) (fuel : Nat) :
    find #[] needle (fuel + 1) = some .None := by
  simp [find, find.loop1]

/-- Copying an empty byte sequence succeeds without changing the destination.
One fuel step is enough to evaluate the loop guard. -/
theorem copy_empty (dst : Array UInt8) (fuel : Nat) :
    copy_into dst #[] (fuel + 1) = some (.Ok 0, dst) := by
  simp [copy_into, copy_into.loop1]

/-- A rejected offset copy returns every destination byte unchanged. The
hypothesis is the exact guard computed by the extracted Oak implementation. -/
theorem copy_at_failure_atomic (dst src : Array UInt8) (offset : UInt32)
    (fuel : Nat)
    (h : range_fits dst.size.toUInt32 offset src.size.toUInt32 fuel =
      some false) :
    copy_at dst offset src fuel = some (.Err .OutOfBounds, dst) := by
  simp [copy_at, h]

/-- An invalid destination range prevents either overlap loop from starting,
so a failed move returns the complete original storage. -/
theorem move_invalid_destination_atomic (storage : Array UInt8)
    (dst src count : UInt32) (fuel : Nat)
    (h : dst > storage.size.toUInt32) :
    move_within storage dst src count fuel =
      some (.Err .OutOfBounds, storage) := by
  simp [move_within, range_fits, h]

/-- Empty byte sequences compare equal. One fuel step evaluates the loop
guard, independently of the remaining budget. -/
theorem compare_empty (fuel : Nat) :
    compare #[] #[] (fuel + 1) = some 0 := by
  simp [compare, compare.loop1]

/-! ## Successful copies and destination frames

Array lengths must fit the Oak `u32` length domain. The fit hypotheses are
natural-number forms of the extracted successful guards, so they also exclude
wrapping destination indices. Each loop needs one fuel step per copied byte
and one final guard step, including for an empty source.
-/

private theorem toUInt32_toNat_of_lt (n : Nat) (h : n < 2 ^ 32) :
    n.toUInt32.toNat = n := by
  show (UInt32.ofNat _).toNat = _
  rw [UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

/-- The range guard is exactly a nonwrapping natural-number range check.
The sum here is in `Nat`, not wrapping `UInt32` arithmetic. -/
theorem range_fits_success_iff (length offset width : UInt32) (fuel : Nat) :
    range_fits length offset width fuel = some true ↔
      offset.toNat + width.toNat ≤ length.toNat := by
  by_cases hoff : offset > length
  · have hnat : length.toNat < offset.toNat := UInt32.lt_iff_toNat_lt.mp hoff
    simp [range_fits, hoff]
    omega
  · have hle : offset ≤ length := by
      change ¬ length < offset at hoff
      rw [UInt32.lt_iff_toNat_lt] at hoff
      rw [UInt32.le_iff_toNat_le]
      omega
    have hsub : (length - offset).toNat = length.toNat - offset.toNat :=
      UInt32.toNat_sub_of_le _ _ hle
    simp only [range_fits, hoff, decide_false, Bool.false_eq_true, ↓reduceIte,
      pure, Option.some.injEq, decide_eq_true_eq]
    rw [UInt32.le_iff_toNat_le, hsub]
    have : offset.toNat ≤ length.toNat := UInt32.le_iff_toNat_le.mp hle
    omega

/-- The remaining suffix of the offset-copy loop writes only its own interval. -/
private theorem copy_at_loop_spec (src : Array UInt8) (offset : UInt32)
    (hsrc : src.size < 2 ^ 32) (fuel : Nat) :
    ∀ (dst : Array UInt8) (i : UInt32),
      offset.toNat + src.size ≤ dst.size → dst.size < 2 ^ 32 →
      i.toNat ≤ src.size → src.size - i.toNat < fuel →
      ∃ dst' i', copy_at.loop1 dst offset src src.size.toUInt32 i fuel =
          some (dst', i') ∧
        dst'.size = dst.size ∧
        ∀ k, dst'.getD k 0 =
          if offset.toNat + i.toNat ≤ k ∧ k < offset.toNat + src.size
          then src.getD (k - offset.toNat) 0 else dst.getD k 0 := by
  induction fuel with
  | zero => intro dst i _ _ _ hf; omega
  | succ fuel ih =>
    intro dst i hfit hsmall hi hf
    unfold copy_at.loop1
    have hsz : src.size.toUInt32.toNat = src.size := toUInt32_toNat_of_lt _ hsrc
    by_cases hlt : i.toNat < src.size
    · have hc : decide (i < src.size.toUInt32) = true := by
        apply decide_eq_true
        rw [UInt32.lt_iff_toNat_lt, hsz]
        exact hlt
      simp only [hc, ↓reduceIte]
      have hi1 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add, show (1 : UInt32).toNat = 1 by decide]
        exact Nat.mod_eq_of_lt (by omega)
      have hindex : (offset + i).toNat = offset.toNat + i.toNat := by
        rw [UInt32.toNat_add]
        exact Nat.mod_eq_of_lt (by omega)
      obtain ⟨dst', i', heq, hsize, hget⟩ :=
        ih (dst.setIfInBounds (offset + i).toNat (src.getD i.toNat 0)) (i + 1)
          (by simpa only [Array.size_setIfInBounds] using hfit)
          (by simpa only [Array.size_setIfInBounds] using hsmall)
          (by omega) (by omega)
      refine ⟨dst', i', heq, by simpa only [Array.size_setIfInBounds] using hsize, ?_⟩
      intro k
      rw [hget k]
      by_cases hk : offset.toNat + (i + 1).toNat ≤ k ∧ k < offset.toNat + src.size
      · rw [if_pos hk, if_pos ⟨by omega, hk.2⟩]
      · rw [if_neg hk, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, hindex]
        by_cases hki : offset.toNat + i.toNat = k
        · rw [if_pos hki, if_pos (by omega), Option.getD_some,
            if_pos ⟨by omega, by omega⟩, show k - offset.toNat = i.toNat by omega]
        · rw [if_neg hki, ← Array.getD_eq_getD_getElem?, if_neg (by omega)]
    · have hc : decide (i < src.size.toUInt32) = false := by
        apply decide_eq_false
        rw [UInt32.lt_iff_toNat_lt, hsz]
        exact hlt
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      refine ⟨dst, i, rfl, rfl, ?_⟩
      intro k
      rw [if_neg (by omega)]

/-- Every successful in-domain offset copy returns the source length, writes
exactly the source at `offset`, and preserves the full destination frame.
`src.size < fuel` is exactly at least `src.size + 1` loop steps. -/
theorem copy_at_spec (dst src : Array UInt8) (offset : UInt32) (fuel : Nat)
    (hsmall : dst.size < 2 ^ 32)
    (hfit : offset.toNat + src.size ≤ dst.size) (hf : src.size < fuel) :
    ∃ dst', copy_at dst offset src fuel = some (.Ok src.size.toUInt32, dst') ∧
      dst'.size = dst.size ∧
      ∀ k, dst'.getD k 0 =
        if offset.toNat ≤ k ∧ k < offset.toNat + src.size
        then src.getD (k - offset.toNat) 0 else dst.getD k 0 := by
  have hsrc : src.size < 2 ^ 32 := by omega
  have hdst : dst.size.toUInt32.toNat = dst.size := toUInt32_toNat_of_lt _ hsmall
  have hsz : src.size.toUInt32.toNat = src.size := toUInt32_toNat_of_lt _ hsrc
  have hguard : range_fits dst.size.toUInt32 offset src.size.toUInt32 fuel = some true := by
    rw [range_fits_success_iff, hdst, hsz]
    exact hfit
  obtain ⟨dst', i', heq, hsize, hget⟩ :=
    copy_at_loop_spec src offset hsrc fuel dst 0 hfit hsmall (by simp) (by simpa using hf)
  refine ⟨dst', ?_, hsize, ?_⟩
  · simp [copy_at, hguard, heq]
  · simpa using hget

/-- The extracted prefix-copy loop is the offset-copy loop at zero. This is
an equality of existing executable definitions, not a replacement model. -/
private theorem copy_into_loop_eq (dst src : Array UInt8) (n i : UInt32) (fuel : Nat) :
    copy_into.loop1 dst src n i fuel = copy_at.loop1 dst 0 src n i fuel := by
  induction fuel generalizing dst i with
  | zero => rfl
  | succ fuel ih =>
    simp only [copy_into.loop1, copy_at.loop1, UInt32.zero_add]
    split <;> simp_all

/-- A prefix copy writes every source byte and preserves every destination
byte beyond the source, along with the complete destination size. -/
theorem copy_into_spec (dst src : Array UInt8) (fuel : Nat)
    (hsmall : dst.size < 2 ^ 32) (hfit : src.size ≤ dst.size)
    (hf : src.size < fuel) :
    ∃ dst', copy_into dst src fuel = some (.Ok src.size.toUInt32, dst') ∧
      dst'.size = dst.size ∧
      ∀ k, dst'.getD k 0 = if k < src.size then src.getD k 0 else dst.getD k 0 := by
  have hsrc : src.size < 2 ^ 32 := by omega
  have hnotshort : ¬ dst.size.toUInt32 < src.size.toUInt32 := by
    rw [UInt32.lt_iff_toNat_lt, toUInt32_toNat_of_lt _ hsmall, toUInt32_toNat_of_lt _ hsrc]
    omega
  obtain ⟨dst', i', heq, hsize, hget⟩ :=
    copy_at_loop_spec src 0 hsrc fuel dst 0 (by simpa using hfit) hsmall
      (by simp) (by simpa using hf)
  refine ⟨dst', ?_, hsize, ?_⟩
  · simp [copy_into, hnotshort, copy_into_loop_eq, heq]
  · simpa using hget

end Oak.Stdlib.Bytes
