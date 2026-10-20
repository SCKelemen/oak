import Oak.Stdlib.TimePeriodFractionWriterLaws
import Oak.Stdlib.TimePeriodFractionReaderLaws
import Oak.Stdlib.TimeUnsignedRoundtripLaws
namespace Oak.Stdlib.Time
set_option maxHeartbeats 1000000

/-- Both actual numeric scanners recover the integer and nanosecond fraction
emitted by `put_frac`, including leading zeroes and trimmed trailing zeroes.
This is the numeric component bridge; the enclosing period grammar is separate. -/
theorem iso_fraction_decimal_roundtrip (dst : Array UInt8) (at_ : UInt32)
    (whole fraction : UInt64) (extra : Nat)
    (hp : 0 < fraction.toNat) (hf : fraction.toNat < 1000000000)
    (hs : at_.toNat+30 ≤ dst.size) (hc : at_.toNat+30 < 4294967296) :
    ∃ (out : Array UInt8) (count width : UInt32) (finalScale : UInt64),
      put_frac dst at_ whole fraction 9 (21+extra) = some (at_+count+1+width, out) ∧
      parse_iso_components.loop2 out (at_+count+1+width) at_ false 0 (21+extra) =
        some (at_+count, false, whole) ∧
      out.getD (at_+count).toNat 0 = 46 ∧
      parse_iso_components.loop3 out (at_+count+1+width) (at_+count+1) 0 0 100000000 (21+extra) =
        some (at_+count+1+width, fraction, width, finalScale) ∧
      0 < count.toNat ∧ count.toNat ≤ 20 ∧ 0 < width.toNat ∧ width.toNat ≤ 9 ∧
      out.size = dst.size ∧
      (∀ k, k < at_.toNat ∨ at_.toNat+count.toNat+1+width.toNat ≤ k → out[k]? = dst[k]?) := by
  obtain ⟨out, digits, count, width, hw, hcp, hcb, hwp, hwb, hsize, hvalue, hvalid,
    hchars, hdot, hfv, hfe, _, hend, hframe⟩ := put_frac_encoding dst at_ whole fraction extra hp hf hs hc
  have hcn : (at_+count).toNat = at_.toNat+count.toNat := by
    rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hstart : (at_+count+1).toNat = at_.toNat+count.toNat+1 := by
    rw [UInt32.toNat_add, hcn]
    change (at_.toNat+count.toNat+1)%4294967296 = _
    omega
  have hi := read_reverse_decimal_complete out digits (at_+count+1+width) count.toNat at_ 0 (21+extra)
    hvalid hchars (by rw [hend]; omega) (by omega)
    (by rw [show (0 : UInt64).toNat = 0 from rfl, hvalue]; have := whole.toNat_lt; omega)
    (Or.inr (by rw [hdot]; rfl))
  rw [show (0 : UInt64).toNat = 0 from rfl, hvalue, ← hcn, UInt32.ofNat_toNat, UInt64.ofNat_toNat] at hi
  obtain ⟨finalScale, hr⟩ := read_fixed_fraction_complete out (at_+count+1+width) width.toNat
    (at_+count+1) 0 0 100000000 (10^(9-width.toNat)) (21+extra)
    (by rw [hstart]; exact hfv) (by rw [hstart, hend]; omega)
    (by change 0+width.toNat ≤ 9; omega) (by omega)
    (by
      intro _
      change 100000000 = 10^(width.toNat-1)*10^(9-width.toNat)
      rw [← Nat.pow_add, show width.toNat-1+(9-width.toNat) = 8 by omega])
    (by rw [hstart]; change 0+_ < _; rw [Nat.zero_add, hfe]; omega)
    (Or.inl (by rw [hstart, hend]))
  rw [hstart, ← hend, UInt32.ofNat_toNat, show (0 : UInt64).toNat = 0 from rfl,
    Nat.zero_add, hfe, UInt64.ofNat_toNat, show (0 : UInt32).toNat = 0 from rfl,
    Nat.zero_add, UInt32.ofNat_toNat] at hr
  exact ⟨out, count, width, finalScale, hw, hi, by rw [hcn]; exact hdot, hr,
    hcp, hcb, hwp, hwb, hsize, hframe⟩
/-- A zero fraction emits only the integer field, whose scanner still roundtrips. -/
theorem iso_zero_fraction_roundtrip (dst : Array UInt8) (at_ : UInt32) (whole : UInt64)
    (extra : Nat) (hs : at_.toNat+20 ≤ dst.size) (hc : at_.toNat+20 < 4294967296) :
    ∃ (end_ : UInt32) (out : Array UInt8),
      put_frac dst at_ whole 0 9 (21+extra) = some (end_, out) ∧
      parse_iso_components.loop2 out end_ at_ false 0 (21+extra) = some (end_, false, whole) ∧
      at_.toNat < end_.toNat ∧ end_.toNat ≤ at_.toNat+20 ∧ out.size = dst.size ∧
      (∀ k, k < at_.toNat ∨ end_.toNat ≤ k → out[k]? = dst[k]?) := by
  obtain ⟨end_, out, hw, hr⟩ := iso_unsigned_decimal_roundtrip dst at_ whole extra hs hc
  refine ⟨end_, out, ?_, hr⟩
  unfold put_frac
  simp only [bind, pure, hw, Option.bind_some]
  rfl
end Oak.Stdlib.Time
