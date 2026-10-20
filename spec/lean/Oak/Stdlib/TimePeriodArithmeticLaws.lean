import Oak.Stdlib.TimeMagnitudeLaws
namespace Oak.Stdlib.Time
set_option maxHeartbeats 400000

/-- Each canonical duration prefix fits in its unsigned accumulator. Together
    with component_sum_exact, these bounds rule out wrapping at every addition. -/
theorem duration_prefix_guards (n limit : UInt64) (fuel : Nat) (hn : n ≤ limit) :
    let hours := n/3600000000000
    let minutes := (n/60000000000)%60
    let seconds := (n/1000000000)%60
    let fraction := n%1000000000
    let a := hours.toNat*3600000000000
    let b := a+minutes.toNat*60000000000
    iso_component_overflows 0 hours 3600000000000 0 limit fuel = some false ∧
    iso_component_overflows (UInt64.ofNat a) minutes 60000000000 0 limit fuel = some false ∧
    iso_component_overflows (UInt64.ofNat b) seconds 1000000000 fraction limit fuel = some false ∧
    b+seconds.toNat*1000000000+fraction.toNat = n.toNat := by
  dsimp only
  have hnl := UInt64.le_iff_toNat_le.mp hn
  have hbound := UInt64.toNat_lt n
  obtain ⟨hh, hm, hs⟩ := duration_units_fit n
  have he := duration_units_reconstruct n
  have ha : (UInt64.ofNat ((n/3600000000000).toNat*3600000000000)).toNat = (n/3600000000000).toNat*3600000000000 :=
    UInt64.toNat_ofNat_of_lt' (by change (n/3600000000000).toNat*3600000000000 < 18446744073709551616; omega)
  have hb : (UInt64.ofNat ((n/3600000000000).toNat*3600000000000 + ((n/60000000000)%60).toNat*60000000000)).toNat = (n/3600000000000).toNat*3600000000000 + ((n/60000000000)%60).toNat*60000000000 :=
    UInt64.toNat_ofNat_of_lt' (by change (n/3600000000000).toNat*3600000000000 + ((n/60000000000)%60).toNat*60000000000 < 18446744073709551616; omega)
  refine ⟨?_, ?_, ?_, he⟩
  · apply iso_component_accept_of_fit _ _ _ _ _ fuel (by decide)
    change 0 + (n/3600000000000).toNat*3600000000000 + 0 ≤ limit.toNat
    simpa only [Nat.zero_add, Nat.add_zero] using Nat.le_trans hh hnl
  · apply iso_component_accept_of_fit _ _ _ _ _ fuel (by decide)
    change (UInt64.ofNat ((n/3600000000000).toNat*3600000000000)).toNat + ((n/60000000000)%60).toNat*60000000000 + 0 ≤ limit.toNat
    rw [ha, Nat.add_zero]
    exact Nat.le_trans hm hnl
  · apply iso_component_accept_of_fit _ _ _ _ _ fuel (by decide)
    change (UInt64.ofNat ((n/3600000000000).toNat*3600000000000 + ((n/60000000000)%60).toNat*60000000000)).toNat + ((n/1000000000)%60).toNat*1000000000 + (n%1000000000).toNat ≤ limit.toNat
    rw [hb, he]
    exact hnl

end Oak.Stdlib.Time
