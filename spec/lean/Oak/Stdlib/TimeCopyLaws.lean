import Oak.Stdlib.TimeBufferLaws
namespace Oak.Stdlib.Time
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

private theorem copy_loop_complete (text : Array UInt8) (size : UInt32) (fuel : Nat) :
    ∀ (dst : Array UInt8) (pos : UInt32), size.toNat ≤ dst.size → pos.toNat ≤ size.toNat →
      size.toNat - pos.toNat < fuel →
      ∃ out, copy_time_text.loop1 dst text size pos fuel = some (out, size) ∧
        out.size = dst.size ∧ ∀ k, out[k]? =
          if pos.toNat ≤ k ∧ k < size.toNat then some (text.getD k 0) else dst[k]? := by
  induction fuel with
  | zero => intro dst pos hd hp hf; omega
  | succ fuel ih =>
    intro dst pos hd hp hf
    unfold copy_time_text.loop1
    by_cases hc : pos < size
    · simp only [hc, decide_true, ite_true]
      have hlt := UInt32.lt_iff_toNat_lt.mp hc
      have hsize := size.toNat_lt
      have hnext : (pos + 1).toNat = pos.toNat + 1 := by
        rw [UInt32.toNat_add]
        exact Nat.mod_eq_of_lt (by simpa using (show pos.toNat + 1 < 4294967296 by omega))
      obtain ⟨out, he, hs, hk⟩ := ih
        (dst.setIfInBounds pos.toNat (text.getD pos.toNat 0)) (pos + 1)
        (by simpa using hd) (by rw [hnext]; omega) (by rw [hnext]; omega)
      refine ⟨out, he, by simpa using hs, ?_⟩
      intro k
      rw [hk, hnext, Array.getElem?_setIfInBounds]
      by_cases heq : pos.toNat = k
      · subst k
        simp [show pos.toNat < dst.size by omega, hlt]
      · by_cases hregion : pos.toNat + 1 ≤ k ∧ k < size.toNat
        · simp [hregion, show pos.toNat ≤ k ∧ k < size.toNat by omega]
        · simp [hregion, heq, show ¬ (pos.toNat ≤ k ∧ k < size.toNat) by omega]
    · have heq : pos = size := UInt32.toNat_inj.mp (by
        have := UInt32.not_lt.mp hc
        have := UInt32.le_iff_toNat_le.mp this
        omega)
      subst pos
      refine ⟨dst, ?_, rfl, ?_⟩
      · simp
      · intro k
        simp only [show ¬ (size.toNat ≤ k ∧ k < size.toNat) by omega, ite_false]

/-- A sufficiently large destination receives the complete requested prefix.
    The length bound states the extractor's u32 slice-length assumption. -/
theorem copy_time_text_complete (dst text : Array UInt8) (size : UInt32) (fuel : Nat)
    (hd : size.toNat ≤ dst.size) (hs : dst.size < 4294967296)
    (ht : size.toNat ≤ text.size) (hf : size.toNat < fuel) :
    ∃ out, copy_time_text dst text size fuel = some (.Ok size, out) ∧
      out.size = dst.size ∧ out.extract 0 size.toNat = text.extract 0 size.toNat := by
  obtain ⟨out, he, ho, hk⟩ := copy_loop_complete text size fuel dst 0 hd (by simp) (by simpa using hf)
  have hguard : ¬ dst.size.toUInt32 < size := by
    simp only [UInt32.lt_iff_toNat_lt, Nat.toUInt32]
    rw [UInt32.toNat_ofNat_of_lt' hs]
    omega
  refine ⟨out, ?_, ho, ?_⟩
  · unfold copy_time_text
    simp only [bind, pure]
    simp only [hguard, decide_false, Bool.false_eq_true, ite_false]
    rw [he]
    rfl
  · apply Array.ext_getElem?
    intro k
    simp only [Array.getElem?_extract, ho, Nat.min_eq_left hd, Nat.min_eq_left ht, Nat.sub_zero, Nat.zero_add]
    by_cases hlt : k < size.toNat
    · simp only [hlt, ite_true]
      rw [hk]
      simp only [UInt32.toNat_zero, Nat.zero_le, hlt, and_self, ite_true]
      rw [Array.getD_eq_getD_getElem?]
      have hktext : k < text.size := by omega
      simp [Array.getElem?_eq_getElem hktext]
    · simp [hlt]

end Oak.Stdlib.Time
