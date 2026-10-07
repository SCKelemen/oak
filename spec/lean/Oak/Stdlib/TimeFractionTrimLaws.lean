import Oak.Stdlib.TimeFractionLaws
namespace Oak.Stdlib.Time
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

theorem trim_arithmetic_0 (n : UInt32) (hn : n < 1000000000)
    : (n) < 1000000000 ∧ n = (n) * 1 := by
  constructor
  · simp only [UInt32.lt_iff_toNat_lt] at hn ⊢
    simp [Nat.div_div_eq_div_mul] at hn ⊢
    omega
  · apply UInt32.toNat_inj.mp
    have hn' := UInt32.lt_iff_toNat_lt.mp hn
    simp only [UInt32.toNat_mul]
    simp [Nat.div_div_eq_div_mul] at hn' ⊢

theorem trim_arithmetic_1 (n : UInt32) (hn : n < 1000000000)
    (h0 : (n) % 10 = 0)
    : (n/10) < 100000000 ∧ n = (n/10) * 10 := by
  constructor
  · simp only [UInt32.lt_iff_toNat_lt, UInt32.toNat_div] at hn ⊢
    simp [Nat.div_div_eq_div_mul] at hn ⊢
    omega
  · apply UInt32.toNat_inj.mp
    have hn' := UInt32.lt_iff_toNat_lt.mp hn
    simp only [UInt32.toNat_mul, UInt32.toNat_div]
    simp [Nat.div_div_eq_div_mul] at hn' ⊢
    have z0 := congrArg UInt32.toNat h0
    simp [UInt32.toNat_mod] at z0
    have e0 := Nat.mod_add_div (n.toNat / 1) 10
    simp [Nat.div_div_eq_div_mul] at e0
    omega

theorem trim_arithmetic_2 (n : UInt32) (hn : n < 1000000000)
    (h0 : (n) % 10 = 0)
    (h1 : (n/10) % 10 = 0)
    : (n/10/10) < 10000000 ∧ n = (n/10/10) * 100 := by
  constructor
  · simp only [UInt32.lt_iff_toNat_lt, UInt32.toNat_div] at hn ⊢
    simp [Nat.div_div_eq_div_mul] at hn ⊢
    omega
  · apply UInt32.toNat_inj.mp
    have hn' := UInt32.lt_iff_toNat_lt.mp hn
    simp only [UInt32.toNat_mul, UInt32.toNat_div]
    simp [Nat.div_div_eq_div_mul] at hn' ⊢
    have z0 := congrArg UInt32.toNat h0
    simp [UInt32.toNat_mod] at z0
    have e0 := Nat.mod_add_div (n.toNat / 1) 10
    simp [Nat.div_div_eq_div_mul] at e0
    have z1 := congrArg UInt32.toNat h1
    simp [UInt32.toNat_mod, UInt32.toNat_div] at z1
    have e1 := Nat.mod_add_div (n.toNat / 10) 10
    simp [Nat.div_div_eq_div_mul] at e1
    omega

theorem trim_arithmetic_3 (n : UInt32) (hn : n < 1000000000)
    (h0 : (n) % 10 = 0)
    (h1 : (n/10) % 10 = 0)
    (h2 : (n/10/10) % 10 = 0)
    : (n/10/10/10) < 1000000 ∧ n = (n/10/10/10) * 1000 := by
  constructor
  · simp only [UInt32.lt_iff_toNat_lt, UInt32.toNat_div] at hn ⊢
    simp [Nat.div_div_eq_div_mul] at hn ⊢
    omega
  · apply UInt32.toNat_inj.mp
    have hn' := UInt32.lt_iff_toNat_lt.mp hn
    simp only [UInt32.toNat_mul, UInt32.toNat_div]
    simp [Nat.div_div_eq_div_mul] at hn' ⊢
    have z0 := congrArg UInt32.toNat h0
    simp [UInt32.toNat_mod] at z0
    have e0 := Nat.mod_add_div (n.toNat / 1) 10
    simp [Nat.div_div_eq_div_mul] at e0
    have z1 := congrArg UInt32.toNat h1
    simp [UInt32.toNat_mod, UInt32.toNat_div] at z1
    have e1 := Nat.mod_add_div (n.toNat / 10) 10
    simp [Nat.div_div_eq_div_mul] at e1
    have z2 := congrArg UInt32.toNat h2
    simp [UInt32.toNat_mod, UInt32.toNat_div, Nat.div_div_eq_div_mul] at z2
    have e2 := Nat.mod_add_div (n.toNat / 100) 10
    simp [Nat.div_div_eq_div_mul] at e2
    omega

theorem trim_arithmetic_4 (n : UInt32) (hn : n < 1000000000)
    (h0 : (n) % 10 = 0)
    (h1 : (n/10) % 10 = 0)
    (h2 : (n/10/10) % 10 = 0)
    (h3 : (n/10/10/10) % 10 = 0)
    : (n/10/10/10/10) < 100000 ∧ n = (n/10/10/10/10) * 10000 := by
  constructor
  · simp only [UInt32.lt_iff_toNat_lt, UInt32.toNat_div] at hn ⊢
    simp [Nat.div_div_eq_div_mul] at hn ⊢
    omega
  · apply UInt32.toNat_inj.mp
    have hn' := UInt32.lt_iff_toNat_lt.mp hn
    simp only [UInt32.toNat_mul, UInt32.toNat_div]
    simp [Nat.div_div_eq_div_mul] at hn' ⊢
    have z0 := congrArg UInt32.toNat h0
    simp [UInt32.toNat_mod] at z0
    have e0 := Nat.mod_add_div (n.toNat / 1) 10
    simp [Nat.div_div_eq_div_mul] at e0
    have z1 := congrArg UInt32.toNat h1
    simp [UInt32.toNat_mod, UInt32.toNat_div] at z1
    have e1 := Nat.mod_add_div (n.toNat / 10) 10
    simp [Nat.div_div_eq_div_mul] at e1
    have z2 := congrArg UInt32.toNat h2
    simp [UInt32.toNat_mod, UInt32.toNat_div, Nat.div_div_eq_div_mul] at z2
    have e2 := Nat.mod_add_div (n.toNat / 100) 10
    simp [Nat.div_div_eq_div_mul] at e2
    have z3 := congrArg UInt32.toNat h3
    simp [UInt32.toNat_mod, UInt32.toNat_div, Nat.div_div_eq_div_mul] at z3
    have e3 := Nat.mod_add_div (n.toNat / 1000) 10
    simp [Nat.div_div_eq_div_mul] at e3
    omega

theorem trim_arithmetic_5 (n : UInt32) (hn : n < 1000000000)
    (h0 : (n) % 10 = 0)
    (h1 : (n/10) % 10 = 0)
    (h2 : (n/10/10) % 10 = 0)
    (h3 : (n/10/10/10) % 10 = 0)
    (h4 : (n/10/10/10/10) % 10 = 0)
    : (n/10/10/10/10/10) < 10000 ∧ n = (n/10/10/10/10/10) * 100000 := by
  constructor
  · simp only [UInt32.lt_iff_toNat_lt, UInt32.toNat_div] at hn ⊢
    simp [Nat.div_div_eq_div_mul] at hn ⊢
    omega
  · apply UInt32.toNat_inj.mp
    have hn' := UInt32.lt_iff_toNat_lt.mp hn
    simp only [UInt32.toNat_mul, UInt32.toNat_div]
    simp [Nat.div_div_eq_div_mul] at hn' ⊢
    have z0 := congrArg UInt32.toNat h0
    simp [UInt32.toNat_mod] at z0
    have e0 := Nat.mod_add_div (n.toNat / 1) 10
    simp [Nat.div_div_eq_div_mul] at e0
    have z1 := congrArg UInt32.toNat h1
    simp [UInt32.toNat_mod, UInt32.toNat_div] at z1
    have e1 := Nat.mod_add_div (n.toNat / 10) 10
    simp [Nat.div_div_eq_div_mul] at e1
    have z2 := congrArg UInt32.toNat h2
    simp [UInt32.toNat_mod, UInt32.toNat_div, Nat.div_div_eq_div_mul] at z2
    have e2 := Nat.mod_add_div (n.toNat / 100) 10
    simp [Nat.div_div_eq_div_mul] at e2
    have z3 := congrArg UInt32.toNat h3
    simp [UInt32.toNat_mod, UInt32.toNat_div, Nat.div_div_eq_div_mul] at z3
    have e3 := Nat.mod_add_div (n.toNat / 1000) 10
    simp [Nat.div_div_eq_div_mul] at e3
    have z4 := congrArg UInt32.toNat h4
    simp [UInt32.toNat_mod, UInt32.toNat_div, Nat.div_div_eq_div_mul] at z4
    have e4 := Nat.mod_add_div (n.toNat / 10000) 10
    simp [Nat.div_div_eq_div_mul] at e4
    omega

theorem trim_arithmetic_6 (n : UInt32) (hn : n < 1000000000)
    (h0 : (n) % 10 = 0)
    (h1 : (n/10) % 10 = 0)
    (h2 : (n/10/10) % 10 = 0)
    (h3 : (n/10/10/10) % 10 = 0)
    (h4 : (n/10/10/10/10) % 10 = 0)
    (h5 : (n/10/10/10/10/10) % 10 = 0)
    : (n/10/10/10/10/10/10) < 1000 ∧ n = (n/10/10/10/10/10/10) * 1000000 := by
  constructor
  · simp only [UInt32.lt_iff_toNat_lt, UInt32.toNat_div] at hn ⊢
    simp [Nat.div_div_eq_div_mul] at hn ⊢
    omega
  · apply UInt32.toNat_inj.mp
    have hn' := UInt32.lt_iff_toNat_lt.mp hn
    simp only [UInt32.toNat_mul, UInt32.toNat_div]
    simp [Nat.div_div_eq_div_mul] at hn' ⊢
    have z0 := congrArg UInt32.toNat h0
    simp [UInt32.toNat_mod] at z0
    have e0 := Nat.mod_add_div (n.toNat / 1) 10
    simp [Nat.div_div_eq_div_mul] at e0
    have z1 := congrArg UInt32.toNat h1
    simp [UInt32.toNat_mod, UInt32.toNat_div] at z1
    have e1 := Nat.mod_add_div (n.toNat / 10) 10
    simp [Nat.div_div_eq_div_mul] at e1
    have z2 := congrArg UInt32.toNat h2
    simp [UInt32.toNat_mod, UInt32.toNat_div, Nat.div_div_eq_div_mul] at z2
    have e2 := Nat.mod_add_div (n.toNat / 100) 10
    simp [Nat.div_div_eq_div_mul] at e2
    have z3 := congrArg UInt32.toNat h3
    simp [UInt32.toNat_mod, UInt32.toNat_div, Nat.div_div_eq_div_mul] at z3
    have e3 := Nat.mod_add_div (n.toNat / 1000) 10
    simp [Nat.div_div_eq_div_mul] at e3
    have z4 := congrArg UInt32.toNat h4
    simp [UInt32.toNat_mod, UInt32.toNat_div, Nat.div_div_eq_div_mul] at z4
    have e4 := Nat.mod_add_div (n.toNat / 10000) 10
    simp [Nat.div_div_eq_div_mul] at e4
    have z5 := congrArg UInt32.toNat h5
    simp [UInt32.toNat_mod, UInt32.toNat_div, Nat.div_div_eq_div_mul] at z5
    have e5 := Nat.mod_add_div (n.toNat / 100000) 10
    simp [Nat.div_div_eq_div_mul] at e5
    omega

theorem trim_arithmetic_7 (n : UInt32) (hn : n < 1000000000)
    (h0 : (n) % 10 = 0)
    (h1 : (n/10) % 10 = 0)
    (h2 : (n/10/10) % 10 = 0)
    (h3 : (n/10/10/10) % 10 = 0)
    (h4 : (n/10/10/10/10) % 10 = 0)
    (h5 : (n/10/10/10/10/10) % 10 = 0)
    (h6 : (n/10/10/10/10/10/10) % 10 = 0)
    : (n/10/10/10/10/10/10/10) < 100 ∧ n = (n/10/10/10/10/10/10/10) * 10000000 := by
  constructor
  · simp only [UInt32.lt_iff_toNat_lt, UInt32.toNat_div] at hn ⊢
    simp [Nat.div_div_eq_div_mul] at hn ⊢
    omega
  · apply UInt32.toNat_inj.mp
    have hn' := UInt32.lt_iff_toNat_lt.mp hn
    simp only [UInt32.toNat_mul, UInt32.toNat_div]
    simp [Nat.div_div_eq_div_mul] at hn' ⊢
    have z0 := congrArg UInt32.toNat h0
    simp [UInt32.toNat_mod] at z0
    have e0 := Nat.mod_add_div (n.toNat / 1) 10
    simp [Nat.div_div_eq_div_mul] at e0
    have z1 := congrArg UInt32.toNat h1
    simp [UInt32.toNat_mod, UInt32.toNat_div] at z1
    have e1 := Nat.mod_add_div (n.toNat / 10) 10
    simp [Nat.div_div_eq_div_mul] at e1
    have z2 := congrArg UInt32.toNat h2
    simp [UInt32.toNat_mod, UInt32.toNat_div, Nat.div_div_eq_div_mul] at z2
    have e2 := Nat.mod_add_div (n.toNat / 100) 10
    simp [Nat.div_div_eq_div_mul] at e2
    have z3 := congrArg UInt32.toNat h3
    simp [UInt32.toNat_mod, UInt32.toNat_div, Nat.div_div_eq_div_mul] at z3
    have e3 := Nat.mod_add_div (n.toNat / 1000) 10
    simp [Nat.div_div_eq_div_mul] at e3
    have z4 := congrArg UInt32.toNat h4
    simp [UInt32.toNat_mod, UInt32.toNat_div, Nat.div_div_eq_div_mul] at z4
    have e4 := Nat.mod_add_div (n.toNat / 10000) 10
    simp [Nat.div_div_eq_div_mul] at e4
    have z5 := congrArg UInt32.toNat h5
    simp [UInt32.toNat_mod, UInt32.toNat_div, Nat.div_div_eq_div_mul] at z5
    have e5 := Nat.mod_add_div (n.toNat / 100000) 10
    simp [Nat.div_div_eq_div_mul] at e5
    have z6 := congrArg UInt32.toNat h6
    simp [UInt32.toNat_mod, UInt32.toNat_div, Nat.div_div_eq_div_mul] at z6
    have e6 := Nat.mod_add_div (n.toNat / 1000000) 10
    simp [Nat.div_div_eq_div_mul] at e6
    omega

theorem trim_arithmetic_8 (n : UInt32) (hn : n < 1000000000)
    (h0 : (n) % 10 = 0)
    (h1 : (n/10) % 10 = 0)
    (h2 : (n/10/10) % 10 = 0)
    (h3 : (n/10/10/10) % 10 = 0)
    (h4 : (n/10/10/10/10) % 10 = 0)
    (h5 : (n/10/10/10/10/10) % 10 = 0)
    (h6 : (n/10/10/10/10/10/10) % 10 = 0)
    (h7 : (n/10/10/10/10/10/10/10) % 10 = 0)
    : (n/10/10/10/10/10/10/10/10) < 10 ∧ n = (n/10/10/10/10/10/10/10/10) * 100000000 := by
  constructor
  · simp only [UInt32.lt_iff_toNat_lt, UInt32.toNat_div] at hn ⊢
    simp [Nat.div_div_eq_div_mul] at hn ⊢
    omega
  · apply UInt32.toNat_inj.mp
    have hn' := UInt32.lt_iff_toNat_lt.mp hn
    simp only [UInt32.toNat_mul, UInt32.toNat_div]
    simp [Nat.div_div_eq_div_mul] at hn' ⊢
    have z0 := congrArg UInt32.toNat h0
    simp [UInt32.toNat_mod] at z0
    have e0 := Nat.mod_add_div (n.toNat / 1) 10
    simp [Nat.div_div_eq_div_mul] at e0
    have z1 := congrArg UInt32.toNat h1
    simp [UInt32.toNat_mod, UInt32.toNat_div] at z1
    have e1 := Nat.mod_add_div (n.toNat / 10) 10
    simp [Nat.div_div_eq_div_mul] at e1
    have z2 := congrArg UInt32.toNat h2
    simp [UInt32.toNat_mod, UInt32.toNat_div, Nat.div_div_eq_div_mul] at z2
    have e2 := Nat.mod_add_div (n.toNat / 100) 10
    simp [Nat.div_div_eq_div_mul] at e2
    have z3 := congrArg UInt32.toNat h3
    simp [UInt32.toNat_mod, UInt32.toNat_div, Nat.div_div_eq_div_mul] at z3
    have e3 := Nat.mod_add_div (n.toNat / 1000) 10
    simp [Nat.div_div_eq_div_mul] at e3
    have z4 := congrArg UInt32.toNat h4
    simp [UInt32.toNat_mod, UInt32.toNat_div, Nat.div_div_eq_div_mul] at z4
    have e4 := Nat.mod_add_div (n.toNat / 10000) 10
    simp [Nat.div_div_eq_div_mul] at e4
    have z5 := congrArg UInt32.toNat h5
    simp [UInt32.toNat_mod, UInt32.toNat_div, Nat.div_div_eq_div_mul] at z5
    have e5 := Nat.mod_add_div (n.toNat / 100000) 10
    simp [Nat.div_div_eq_div_mul] at e5
    have z6 := congrArg UInt32.toNat h6
    simp [UInt32.toNat_mod, UInt32.toNat_div, Nat.div_div_eq_div_mul] at z6
    have e6 := Nat.mod_add_div (n.toNat / 1000000) 10
    simp [Nat.div_div_eq_div_mul] at e6
    have z7 := congrArg UInt32.toNat h7
    simp [UInt32.toNat_mod, UInt32.toNat_div, Nat.div_div_eq_div_mul] at z7
    have e7 := Nat.mod_add_div (n.toNat / 10000000) 10
    simp [Nat.div_div_eq_div_mul] at e7
    omega

/-- Trimming terminates within nine loop steps, retains a nonzero last digit,
    and preserves the exact nanosecond value. -/
theorem trim_time_fraction (n : UInt32) (fuel : Nat)
    (hp : 0 < n) (hn : n < 1000000000) :
    ∃ (f : UInt32) (w : Nat), 1 ≤ w ∧ w ≤ 9 ∧
      f < (10 ^ w).toUInt32 ∧ n = f * (10 ^ (9-w)).toUInt32 ∧
      f % 10 ≠ 0 ∧ write_time.loop1 n 9 (fuel + 40) = some (f, w.toUInt32) := by
  by_cases h0 : (n) % 10 = 0
  case neg =>
    obtain ⟨hb, he⟩ := trim_arithmetic_0 n hn 
    refine ⟨n, 9, by decide, by decide, hb, he, h0, ?_⟩
    simp [write_time.loop1, h0]
  by_cases h1 : (n/10) % 10 = 0
  case neg =>
    obtain ⟨hb, he⟩ := trim_arithmetic_1 n hn h0
    refine ⟨n/10, 8, by decide, by decide, hb, he, h1, ?_⟩
    simp [write_time.loop1, h0, h1]
  by_cases h2 : (n/10/10) % 10 = 0
  case neg =>
    obtain ⟨hb, he⟩ := trim_arithmetic_2 n hn h0 h1
    refine ⟨n/10/10, 7, by decide, by decide, hb, he, h2, ?_⟩
    simp [write_time.loop1, h0, h1, h2]
  by_cases h3 : (n/10/10/10) % 10 = 0
  case neg =>
    obtain ⟨hb, he⟩ := trim_arithmetic_3 n hn h0 h1 h2
    refine ⟨n/10/10/10, 6, by decide, by decide, hb, he, h3, ?_⟩
    simp [write_time.loop1, h0, h1, h2, h3]
  by_cases h4 : (n/10/10/10/10) % 10 = 0
  case neg =>
    obtain ⟨hb, he⟩ := trim_arithmetic_4 n hn h0 h1 h2 h3
    refine ⟨n/10/10/10/10, 5, by decide, by decide, hb, he, h4, ?_⟩
    simp [write_time.loop1, h0, h1, h2, h3, h4]
  by_cases h5 : (n/10/10/10/10/10) % 10 = 0
  case neg =>
    obtain ⟨hb, he⟩ := trim_arithmetic_5 n hn h0 h1 h2 h3 h4
    refine ⟨n/10/10/10/10/10, 4, by decide, by decide, hb, he, h5, ?_⟩
    simp [write_time.loop1, h0, h1, h2, h3, h4, h5]
  by_cases h6 : (n/10/10/10/10/10/10) % 10 = 0
  case neg =>
    obtain ⟨hb, he⟩ := trim_arithmetic_6 n hn h0 h1 h2 h3 h4 h5
    refine ⟨n/10/10/10/10/10/10, 3, by decide, by decide, hb, he, h6, ?_⟩
    simp [write_time.loop1, h0, h1, h2, h3, h4, h5, h6]
  by_cases h7 : (n/10/10/10/10/10/10/10) % 10 = 0
  case neg =>
    obtain ⟨hb, he⟩ := trim_arithmetic_7 n hn h0 h1 h2 h3 h4 h5 h6
    refine ⟨n/10/10/10/10/10/10/10, 2, by decide, by decide, hb, he, h7, ?_⟩
    simp [write_time.loop1, h0, h1, h2, h3, h4, h5, h6, h7]
  by_cases h8 : (n/10/10/10/10/10/10/10/10) % 10 = 0
  case neg =>
    obtain ⟨hb, he⟩ := trim_arithmetic_8 n hn h0 h1 h2 h3 h4 h5 h6 h7
    refine ⟨n/10/10/10/10/10/10/10/10, 1, by decide, by decide, hb, he, h8, ?_⟩
    simp [write_time.loop1, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  have hd := fraction_digits_9 n hn
  simp [h0, h1, h2, h3, h4, h5, h6, h7, h8] at hd
  have : n = 0 := hd.symm
  subst n
  simp at hp

end Oak.Stdlib.Time
