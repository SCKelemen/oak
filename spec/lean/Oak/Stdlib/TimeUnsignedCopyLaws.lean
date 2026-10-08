import Oak.Stdlib.TimeUnsignedDigitsLaws
namespace Oak.Stdlib.Time
set_option maxHeartbeats 1000000

private theorem reverse_copy_loop (digits : Array UInt8) (at_ count : UInt32) (fuel : Nat) :
    ∀ (dst : Array UInt8) (i : UInt32),
      at_.toNat+count.toNat ≤ dst.size → at_.toNat+count.toNat < 4294967296 →
      i.toNat ≤ count.toNat → count.toNat-i.toNat < fuel →
      ∃ out, put_u64.loop2 dst at_ digits count i fuel = some (out, count) ∧
        out.size = dst.size ∧ ∀ k, out[k]? =
          if at_.toNat+i.toNat ≤ k ∧ k < at_.toNat+count.toNat
          then some (digits.getD (count.toNat-1-(k-at_.toNat)) 0) else dst[k]? := by
  induction fuel with
  | zero => intro dst i hs hc hi hf; omega
  | succ fuel ih =>
    intro dst i hs hc hi hf
    unfold put_u64.loop2
    by_cases hlt : i < count
    · simp only [hlt, decide_true, ite_true]
      have hin := UInt32.lt_iff_toNat_lt.mp hlt
      have hnext : (i+1).toNat = i.toNat+1 := by
        rw [UInt32.toNat_add]
        change (i.toNat+1)%4294967296 = i.toNat+1
        omega
      have hpos : (at_+i).toNat = at_.toNat+i.toNat := by
        rw [UInt32.toNat_add]
        exact Nat.mod_eq_of_lt (by omega)
      have hsub : (count-i-1).toNat = count.toNat-1-i.toNat := by
        have hci : (1 : UInt32) ≤ count-i := by
          rw [UInt32.le_iff_toNat_le, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr hi)]
          change 1 ≤ count.toNat-i.toNat
          omega
        rw [UInt32.toNat_sub_of_le _ _ hci, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr hi)]
        change count.toNat-i.toNat-1 = count.toNat-1-i.toNat
        omega
      obtain ⟨out, ho, hsize, hk⟩ := ih
        (dst.setIfInBounds (at_+i).toNat (digits.getD (count-i-1).toNat 0)) (i+1)
        (by simpa using hs) hc (by rw [hnext]; omega) (by rw [hnext]; omega)
      refine ⟨out, ho, by simpa using hsize, ?_⟩
      intro k
      rw [hk, hnext, Array.getElem?_setIfInBounds, hpos, hsub]
      by_cases he : at_.toNat+i.toNat = k
      · subst k
        simp [show at_.toNat+i.toNat < dst.size by omega, show ¬at_.toNat+(i.toNat+1) ≤ at_.toNat+i.toNat by omega,
          show at_.toNat+i.toNat < at_.toNat+count.toNat by omega]
      · by_cases hr : at_.toNat+(i.toNat+1) ≤ k ∧ k < at_.toNat+count.toNat
        · simp [hr, show at_.toNat+i.toNat ≤ k ∧ k < at_.toNat+count.toNat by omega]
        · simp [hr, he, show ¬(at_.toNat+i.toNat ≤ k ∧ k < at_.toNat+count.toNat) by omega]
    · have he : i = count := UInt32.toNat_inj.mp (by
        have := UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp hlt)
        omega)
      subst i
      refine ⟨dst, by simp, rfl, ?_⟩
      intro k
      simp [show ¬(at_.toNat+count.toNat ≤ k ∧ k < at_.toNat+count.toNat) by omega]

/-- UInt64 serialization succeeds in a twenty-byte window and emits the exact
reverse-buffer digits in reading order, preserving every byte outside it. -/
theorem put_u64_encoding (dst : Array UInt8) (at_ : UInt32) (value : UInt64) (extra : Nat)
    (hs : at_.toNat+20 ≤ dst.size) (hc : at_.toNat+20 < 4294967296) :
    ∃ (out digits : Array UInt8) (count : UInt32),
      put_u64 dst at_ value (21+extra) = some (at_+count, out) ∧
      0 < count.toNat ∧ count.toNat ≤ 20 ∧
      (at_+count).toNat = at_.toNat+count.toNat ∧ out.size = dst.size ∧
      reverse_digits_valid digits count.toNat ∧
      reverse_decimal_value digits count.toNat 0 = value.toNat ∧
      (∀ j, j < count.toNat → out.getD (at_.toNat+j) 0 = digits.getD (count.toNat-1-j) 0) ∧
      (∀ k, k < at_.toNat ∨ at_.toNat+count.toNat ≤ k → out[k]? = dst[k]?) := by
  obtain ⟨digits, count, hd, hpos, hcount, _, hv, he⟩ := put_u64_digits_complete value extra
  obtain ⟨out, ho, hsize, hk⟩ := reverse_copy_loop digits at_ count (21+extra) dst 0
    (by omega) (by omega) (by simp) (by simpa using (show count.toNat < 21+extra by omega))
  refine ⟨out, digits, count, ?_, hpos, hcount, ?_, hsize, hv, he, ?_, ?_⟩
  · unfold put_u64
    simp only [bind, pure]
    rw [hd]
    simp only [Option.bind_some]
    rw [ho]
    rfl
  · rw [UInt32.toNat_add]
    exact Nat.mod_eq_of_lt (by omega)
  · intro j hj
    rw [Array.getD_eq_getD_getElem?, hk]
    simp [show at_.toNat+j < at_.toNat+count.toNat by omega]
  · intro k hregion
    rw [hk]
    simp only [UInt32.toNat_zero, Nat.add_zero]
    rw [if_neg (by omega : ¬(at_.toNat ≤ k ∧ k < at_.toNat+count.toNat))]
end Oak.Stdlib.Time
