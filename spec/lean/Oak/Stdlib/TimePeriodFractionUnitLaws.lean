import Oak.Stdlib.TimePeriodFractionRoundtripLaws
namespace Oak.Stdlib.Time
set_option maxHeartbeats 1000000

/-- Appending an ISO unit delimiter lets both actual numeric scanners recover
fractional seconds from a larger buffer, without consuming the unit or suffix. -/
theorem iso_fraction_unit_roundtrip (dst : Array UInt8) (at_ : UInt32)
    (whole fraction : UInt64) (unit : UInt8) (extra : Nat)
    (hu : is_digit unit 0 = some false)
    (hp : 0 < fraction.toNat) (hf : fraction.toNat < 1000000000)
    (hs : at_.toNat+31 ≤ dst.size) (hsize : dst.size < 4294967296) :
    ∃ (written out : Array UInt8) (count width : UInt32) (finalScale : UInt64),
      put_frac dst at_ whole fraction 9 (21+extra) = some (at_+count+1+width, written) ∧
      out = written.setIfInBounds (at_+count+1+width).toNat unit ∧
      parse_iso_components.loop2 out out.size.toUInt32 at_ false 0 (21+extra) =
        some (at_+count, false, whole) ∧
      out.getD (at_+count).toNat 0 = 46 ∧
      parse_iso_components.loop3 out out.size.toUInt32 (at_+count+1) 0 0 100000000 (21+extra) =
        some (at_+count+1+width, fraction, width, finalScale) ∧
      0 < count.toNat ∧ count.toNat ≤ 20 ∧ 0 < width.toNat ∧ width.toNat ≤ 9 ∧
      out.getD (at_+count+1+width).toNat 0 = unit ∧
      out.size = dst.size ∧
      (at_+count+1+width+1).toNat = at_.toNat+count.toNat+2+width.toNat ∧
      (∀ k, k < at_.toNat ∨ at_.toNat+count.toNat+2+width.toNat ≤ k → out[k]? = dst[k]?) := by
  obtain ⟨written, digits, count, width, hw, hcp, hcb, hwp, hwb, hwsize, hvalue, hvalid,
    hchars, hdot, hfv, hfe, _, hend, hframe⟩ := put_frac_encoding dst at_ whole fraction extra hp hf (by omega) (by omega)
  have hcn : (at_+count).toNat = at_.toNat+count.toNat := by
    rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hstart : (at_+count+1).toNat = at_.toNat+count.toNat+1 := by
    rw [UInt32.toNat_add, hcn]
    change (at_.toNat+count.toNat+1)%4294967296 = _
    omega
  let out := written.setIfInBounds (at_+count+1+width).toNat unit
  have hbound : (at_+count+1+width).toNat < written.size := by rw [hend, hwsize]; omega
  have hos : out.size = dst.size := by simp only [out, Array.size_setIfInBounds, hwsize]
  have hlen : out.size.toUInt32.toNat = dst.size := by
    rw [hos, Nat.toUInt32, UInt32.toNat_ofNat_of_lt' hsize]
  have hunit : out.getD (at_+count+1+width).toNat 0 = unit := by
    simp only [out, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self_of_lt hbound, Option.getD_some]
  have hprefix (k : Nat) (hk : k < (at_+count+1+width).toNat) : out.getD k 0 = written.getD k 0 := by
    simp only [out, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne (by omega : (at_+count+1+width).toNat ≠ k)]
  have hchars' : ∀ j, j < count.toNat → out.getD (at_.toNat+j) 0 = digits.getD (count.toNat-1-j) 0 := by
    intro j hj
    rw [hprefix _ (by rw [hend]; omega)]
    exact hchars j hj
  have hdot' : out.getD (at_.toNat+count.toNat) 0 = 46 := by
    rw [hprefix _ (by rw [hend]; omega), hdot]
  have hfv' : fixed_decimal_valid out (at_.toNat+count.toNat+1) width.toNat := by
    intro j hj
    rw [hprefix _ (by rw [hend]; omega)]
    exact hfv j hj
  have hfe' : fixed_decimal_value out (at_.toNat+count.toNat+1) width.toNat * 10^(9-width.toNat) = fraction.toNat := by
    rw [fixed_decimal_congr out written _ _ (fun j hj => hprefix _ (by rw [hend]; omega))]
    exact hfe
  have hi := read_reverse_decimal_complete out digits out.size.toUInt32 count.toNat at_ 0 (21+extra)
    hvalid hchars' (by rw [hlen]; omega) (by omega)
    (by rw [show (0 : UInt64).toNat = 0 from rfl, hvalue]; have := whole.toNat_lt; omega)
    (Or.inr (by rw [hdot']; rfl))
  rw [show (0 : UInt64).toNat = 0 from rfl, hvalue, ← hcn, UInt32.ofNat_toNat, UInt64.ofNat_toNat] at hi
  obtain ⟨finalScale, hr⟩ := read_fixed_fraction_complete out out.size.toUInt32 width.toNat
    (at_+count+1) 0 0 100000000 (10^(9-width.toNat)) (21+extra)
    (by rw [hstart]; exact hfv') (by rw [hstart, hlen]; omega)
    (by change 0+width.toNat ≤ 9; omega) (by omega)
    (by
      intro _
      change 100000000 = 10^(width.toNat-1)*10^(9-width.toNat)
      rw [← Nat.pow_add, show width.toNat-1+(9-width.toNat) = 8 by omega])
    (by rw [hstart]; change 0+_ < _; rw [Nat.zero_add, hfe']; omega)
    (Or.inr (by rw [hstart, ← hend, hunit]; exact hu))
  rw [hstart, ← hend, UInt32.ofNat_toNat, show (0 : UInt64).toNat = 0 from rfl,
    Nat.zero_add, hfe', UInt64.ofNat_toNat, show (0 : UInt32).toNat = 0 from rfl,
    Nat.zero_add, UInt32.ofNat_toNat] at hr
  refine ⟨written, out, count, width, finalScale, hw, rfl, hi, by rw [hcn]; exact hdot', hr,
    hcp, hcb, hwp, hwb, hunit, hos, ?_, ?_⟩
  · rw [UInt32.toNat_add, hend]
    change (at_.toNat+count.toNat+1+width.toNat+1)%4294967296 = _
    omega
  intro k hk
  dsimp [out]
  rw [Array.getElem?_setIfInBounds_ne (by rw [hend]; omega), hframe k (by omega)]


/-- The zero-fraction branch uses the same unit delimiter without a decimal
point. This is the exact `put_frac` plus unit-store sequence used for seconds. -/
theorem iso_zero_fraction_unit_roundtrip (dst : Array UInt8) (at_ : UInt32)
    (whole : UInt64) (unit : UInt8) (extra : Nat) (hu : is_digit unit 0 = some false)
    (hs : at_.toNat+21 ≤ dst.size) (hsize : dst.size < 4294967296) :
    ∃ (end_ : UInt32) (written out : Array UInt8),
      put_frac dst at_ whole 0 9 (21+extra) = some (end_, written) ∧
      out = written.setIfInBounds end_.toNat unit ∧
      parse_iso_components.loop2 out out.size.toUInt32 at_ false 0 (21+extra) = some (end_, false, whole) ∧
      out.getD end_.toNat 0 = unit ∧ out.size = dst.size ∧
      at_.toNat < end_.toNat ∧ end_.toNat ≤ at_.toNat+20 ∧
      (end_+1).toNat = end_.toNat+1 ∧
      (∀ k, k < at_.toNat ∨ end_.toNat+1 ≤ k → out[k]? = dst[k]?) := by
  obtain ⟨written, digits, count, hw, hp, hn, he, hwsize, hv, hm, hbytes, hframe⟩ :=
    put_u64_encoding dst at_ whole extra (by omega) (by omega)
  let out := written.setIfInBounds (at_+count).toNat unit
  have hwrite : write_iso_unit dst at_ whole unit (21+extra) = some (at_+count+1, out) := by
    unfold write_iso_unit
    simp only [bind, pure, hw, Option.bind_some]
    rfl
  obtain ⟨end_, found, hfound, hr, hunit, hos, hlo, hhi, hnext⟩ :=
    write_iso_unit_integer_roundtrip dst at_ whole unit extra hu hs hsize
  rw [hwrite] at hfound
  have hpair := Option.some.inj hfound
  have ho : out = found := congrArg Prod.snd hpair
  have hend : at_+count = end_ := by
    have h := congrArg Prod.fst hpair
    exact UInt32.toNat_inj.mp (by
      have hword : (at_+count+1).toNat = (at_+count).toNat+1 := by
        rw [UInt32.toNat_add]
        change ((at_+count).toNat+1)%4294967296 = _
        exact Nat.mod_eq_of_lt (by rw [he]; omega)
      have ht := congrArg UInt32.toNat h
      rw [hword, hnext] at ht
      omega)
  refine ⟨end_, written, found, ?_, ?_, hr, hunit, hos, hlo, hhi, hnext, ?_⟩
  · unfold put_frac
    simp only [bind, pure, hw, Option.bind_some]
    simp only [hend]
    rfl
  · rw [← ho, ← hend]
  · intro k hk
    rw [← ho]
    dsimp [out]
    rw [Array.getElem?_setIfInBounds_ne (by rw [hend]; omega), hframe k (by rw [hend] at he; omega)]
end Oak.Stdlib.Time
