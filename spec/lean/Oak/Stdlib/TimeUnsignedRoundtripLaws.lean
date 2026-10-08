import Oak.Stdlib.TimeUnsignedReaderLaws
namespace Oak.Stdlib.Time
set_option maxHeartbeats 800000

/-- The actual UInt64 writer and integer scanner round-trip every value.
The scanner's explicit limit ends at the written number, independent of the
unused buffer contents. Both loops terminate with any fuel at least 21. -/
theorem iso_unsigned_decimal_roundtrip (dst : Array UInt8) (at_ : UInt32) (value : UInt64) (extra : Nat)
    (hs : at_.toNat+20 ≤ dst.size) (hc : at_.toNat+20 < 4294967296) :
    ∃ (end_ : UInt32) (out : Array UInt8),
      put_u64 dst at_ value (21+extra) = some (end_, out) ∧
      parse_iso_components.loop2 out end_ at_ false 0 (21+extra) = some (end_, false, value) ∧
      at_.toNat < end_.toNat ∧ end_.toNat ≤ at_.toNat+20 ∧ out.size = dst.size ∧
      (∀ k, k < at_.toNat ∨ end_.toNat ≤ k → out[k]? = dst[k]?) := by
  obtain ⟨out, digits, count, hw, hp, hn, he, hsize, hv, hm, hbytes, hframe⟩ := put_u64_encoding dst at_ value extra hs hc
  have hb : value.toNat ≤ 18446744073709551615 := by have := value.toNat_lt; omega
  have hr := read_reverse_decimal_complete out digits (at_+count) count.toNat at_ 0 (21+extra)
    hv hbytes (by rw [he]; exact Nat.le_refl _) (by omega) (by simpa only [UInt64.toNat_zero, hm] using hb) (Or.inl he.symm)
  have hend : UInt32.ofNat (at_.toNat+count.toNat) = at_+count := by rw [← he, UInt32.ofNat_toNat]
  simp only [UInt64.toNat_zero, hm, UInt64.ofNat_toNat, hend] at hr
  exact ⟨at_+count, out, hw, hr, by rw [he]; omega, by rw [he]; omega, hsize,
    fun k hk => hframe k (by rwa [he] at hk)⟩

/-- Writing a numeric ISO unit leaves a nondigit delimiter that the real
integer scanner stops before, even when the buffer contains later text. -/
theorem write_iso_unit_integer_roundtrip (dst : Array UInt8) (at_ : UInt32) (value : UInt64)
    (unit : UInt8) (extra : Nat) (hu : is_digit unit 0 = some false)
    (hs : at_.toNat+21 ≤ dst.size) (hsize : dst.size < 4294967296) :
    ∃ (end_ : UInt32) (out : Array UInt8),
      write_iso_unit dst at_ value unit (21+extra) = some (end_+1, out) ∧
      parse_iso_components.loop2 out out.size.toUInt32 at_ false 0 (21+extra) = some (end_, false, value) ∧
      out.getD end_.toNat 0 = unit ∧ out.size = dst.size ∧
      at_.toNat < end_.toNat ∧ end_.toNat ≤ at_.toNat+20 ∧
      (end_+1).toNat = end_.toNat+1 := by
  obtain ⟨written, digits, count, hw, hp, hn, he, hwsize, hv, hm, hbytes, _⟩ :=
    put_u64_encoding dst at_ value extra (by omega) (by omega)
  let out := written.setIfInBounds (at_+count).toNat unit
  have hend : (at_+count).toNat < written.size := by rw [he, hwsize]; omega
  have hunit : out.getD (at_+count).toNat 0 = unit := by
    simp only [out, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self_of_lt hend, Option.getD_some]
  have hos : out.size = dst.size := by simpa only [out, Array.size_setIfInBounds] using hwsize
  have hlen : out.size.toUInt32.toNat = dst.size := by
    rw [hos, Nat.toUInt32, UInt32.toNat_ofNat_of_lt' hsize]
  have hmap : ∀ j, j < count.toNat → out.getD (at_.toNat+j) 0 = digits.getD (count.toNat-1-j) 0 := by
    intro j hj
    have hne : (at_+count).toNat ≠ at_.toNat+j := by rw [he]; omega
    simpa only [out, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne hne] using hbytes j hj
  have hb : value.toNat ≤ 18446744073709551615 := by have := value.toNat_lt; omega
  have hr := read_reverse_decimal_complete out digits out.size.toUInt32 count.toNat at_ 0 (21+extra)
    hv hmap (by rw [hlen]; omega) (by omega) (by simpa only [UInt64.toNat_zero, hm] using hb)
    (Or.inr (by rw [← he, hunit]; exact hu))
  have hcast : UInt32.ofNat (at_.toNat+count.toNat) = at_+count := by rw [← he, UInt32.ofNat_toNat]
  simp only [UInt64.toNat_zero, hm, UInt64.ofNat_toNat, hcast] at hr
  refine ⟨at_+count, out, ?_, hr, hunit, hos, by rw [he]; omega, by rw [he]; omega, ?_⟩
  · unfold write_iso_unit
    simp only [bind, pure]
    rw [hw]
    rfl
  · rw [UInt32.toNat_add]
    change ((at_+count).toNat+1)%4294967296 = (at_+count).toNat+1
    exact Nat.mod_eq_of_lt (by rw [he]; omega)
end Oak.Stdlib.Time
