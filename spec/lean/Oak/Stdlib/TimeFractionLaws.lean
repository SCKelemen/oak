import Oak.Stdlib.TimeCodecLaws

/-! # Decimal reconstruction for fractional seconds
These arithmetic identities are proved over natural-number division, then
lifted to the machine integers used by the extracted implementation.
-/
namespace Oak.Stdlib.Time
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

theorem fraction_digits_1 (n : UInt32) (hn : n < 10) :
    ((n) % 10) * 100000000 = n * 100000000 := by
  apply UInt32.toNat_inj.mp
  have hn' := UInt32.lt_iff_toNat_lt.mp hn
  simp only [ UInt32.toNat_mul, UInt32.toNat_mod]
  simp [Nat.div_div_eq_div_mul] at hn' ⊢
  have h0 := Nat.mod_add_div (n.toNat / 1) 10
  simp [Nat.div_div_eq_div_mul] at h0
  have htop : n.toNat / 10 = 0 := Nat.div_eq_of_lt hn'
  have hs : n.toNat * 100000000 < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hs]
  omega

theorem fraction_digits_2 (n : UInt32) (hn : n < 100) :
    ((n/10) % 10) * 100000000 + ((n) % 10) * 10000000 = n * 10000000 := by
  apply UInt32.toNat_inj.mp
  have hn' := UInt32.lt_iff_toNat_lt.mp hn
  simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_mod, UInt32.toNat_div]
  simp [Nat.div_div_eq_div_mul] at hn' ⊢
  have h0 := Nat.mod_add_div (n.toNat / 1) 10
  simp [Nat.div_div_eq_div_mul] at h0
  have h1 := Nat.mod_add_div (n.toNat / 10) 10
  simp [Nat.div_div_eq_div_mul] at h1
  have htop : n.toNat / 100 = 0 := Nat.div_eq_of_lt hn'
  have hs : n.toNat * 10000000 < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hs]
  omega

theorem fraction_digits_3 (n : UInt32) (hn : n < 1000) :
    ((n/10/10) % 10) * 100000000 + ((n/10) % 10) * 10000000 + ((n) % 10) * 1000000 = n * 1000000 := by
  apply UInt32.toNat_inj.mp
  have hn' := UInt32.lt_iff_toNat_lt.mp hn
  simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_mod, UInt32.toNat_div]
  simp [Nat.div_div_eq_div_mul] at hn' ⊢
  have h0 := Nat.mod_add_div (n.toNat / 1) 10
  simp [Nat.div_div_eq_div_mul] at h0
  have h1 := Nat.mod_add_div (n.toNat / 10) 10
  simp [Nat.div_div_eq_div_mul] at h1
  have h2 := Nat.mod_add_div (n.toNat / 100) 10
  simp [Nat.div_div_eq_div_mul] at h2
  have htop : n.toNat / 1000 = 0 := Nat.div_eq_of_lt hn'
  have hs : n.toNat * 1000000 < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hs]
  omega

theorem fraction_digits_4 (n : UInt32) (hn : n < 10000) :
    ((n/10/10/10) % 10) * 100000000 + ((n/10/10) % 10) * 10000000 + ((n/10) % 10) * 1000000 + ((n) % 10) * 100000 = n * 100000 := by
  apply UInt32.toNat_inj.mp
  have hn' := UInt32.lt_iff_toNat_lt.mp hn
  simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_mod, UInt32.toNat_div]
  simp [Nat.div_div_eq_div_mul] at hn' ⊢
  have h0 := Nat.mod_add_div (n.toNat / 1) 10
  simp [Nat.div_div_eq_div_mul] at h0
  have h1 := Nat.mod_add_div (n.toNat / 10) 10
  simp [Nat.div_div_eq_div_mul] at h1
  have h2 := Nat.mod_add_div (n.toNat / 100) 10
  simp [Nat.div_div_eq_div_mul] at h2
  have h3 := Nat.mod_add_div (n.toNat / 1000) 10
  simp [Nat.div_div_eq_div_mul] at h3
  have htop : n.toNat / 10000 = 0 := Nat.div_eq_of_lt hn'
  have hs : n.toNat * 100000 < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hs]
  omega

theorem fraction_digits_5 (n : UInt32) (hn : n < 100000) :
    ((n/10/10/10/10) % 10) * 100000000 + ((n/10/10/10) % 10) * 10000000 + ((n/10/10) % 10) * 1000000 + ((n/10) % 10) * 100000 + ((n) % 10) * 10000 = n * 10000 := by
  apply UInt32.toNat_inj.mp
  have hn' := UInt32.lt_iff_toNat_lt.mp hn
  simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_mod, UInt32.toNat_div]
  simp [Nat.div_div_eq_div_mul] at hn' ⊢
  have h0 := Nat.mod_add_div (n.toNat / 1) 10
  simp [Nat.div_div_eq_div_mul] at h0
  have h1 := Nat.mod_add_div (n.toNat / 10) 10
  simp [Nat.div_div_eq_div_mul] at h1
  have h2 := Nat.mod_add_div (n.toNat / 100) 10
  simp [Nat.div_div_eq_div_mul] at h2
  have h3 := Nat.mod_add_div (n.toNat / 1000) 10
  simp [Nat.div_div_eq_div_mul] at h3
  have h4 := Nat.mod_add_div (n.toNat / 10000) 10
  simp [Nat.div_div_eq_div_mul] at h4
  have htop : n.toNat / 100000 = 0 := Nat.div_eq_of_lt hn'
  have hs : n.toNat * 10000 < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hs]
  omega

theorem fraction_digits_6 (n : UInt32) (hn : n < 1000000) :
    ((n/10/10/10/10/10) % 10) * 100000000 + ((n/10/10/10/10) % 10) * 10000000 + ((n/10/10/10) % 10) * 1000000 + ((n/10/10) % 10) * 100000 + ((n/10) % 10) * 10000 + ((n) % 10) * 1000 = n * 1000 := by
  apply UInt32.toNat_inj.mp
  have hn' := UInt32.lt_iff_toNat_lt.mp hn
  simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_mod, UInt32.toNat_div]
  simp [Nat.div_div_eq_div_mul] at hn' ⊢
  have h0 := Nat.mod_add_div (n.toNat / 1) 10
  simp [Nat.div_div_eq_div_mul] at h0
  have h1 := Nat.mod_add_div (n.toNat / 10) 10
  simp [Nat.div_div_eq_div_mul] at h1
  have h2 := Nat.mod_add_div (n.toNat / 100) 10
  simp [Nat.div_div_eq_div_mul] at h2
  have h3 := Nat.mod_add_div (n.toNat / 1000) 10
  simp [Nat.div_div_eq_div_mul] at h3
  have h4 := Nat.mod_add_div (n.toNat / 10000) 10
  simp [Nat.div_div_eq_div_mul] at h4
  have h5 := Nat.mod_add_div (n.toNat / 100000) 10
  simp [Nat.div_div_eq_div_mul] at h5
  have htop : n.toNat / 1000000 = 0 := Nat.div_eq_of_lt hn'
  have hs : n.toNat * 1000 < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hs]
  omega

theorem fraction_digits_7 (n : UInt32) (hn : n < 10000000) :
    ((n/10/10/10/10/10/10) % 10) * 100000000 + ((n/10/10/10/10/10) % 10) * 10000000 + ((n/10/10/10/10) % 10) * 1000000 + ((n/10/10/10) % 10) * 100000 + ((n/10/10) % 10) * 10000 + ((n/10) % 10) * 1000 + ((n) % 10) * 100 = n * 100 := by
  apply UInt32.toNat_inj.mp
  have hn' := UInt32.lt_iff_toNat_lt.mp hn
  simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_mod, UInt32.toNat_div]
  simp [Nat.div_div_eq_div_mul] at hn' ⊢
  have h0 := Nat.mod_add_div (n.toNat / 1) 10
  simp [Nat.div_div_eq_div_mul] at h0
  have h1 := Nat.mod_add_div (n.toNat / 10) 10
  simp [Nat.div_div_eq_div_mul] at h1
  have h2 := Nat.mod_add_div (n.toNat / 100) 10
  simp [Nat.div_div_eq_div_mul] at h2
  have h3 := Nat.mod_add_div (n.toNat / 1000) 10
  simp [Nat.div_div_eq_div_mul] at h3
  have h4 := Nat.mod_add_div (n.toNat / 10000) 10
  simp [Nat.div_div_eq_div_mul] at h4
  have h5 := Nat.mod_add_div (n.toNat / 100000) 10
  simp [Nat.div_div_eq_div_mul] at h5
  have h6 := Nat.mod_add_div (n.toNat / 1000000) 10
  simp [Nat.div_div_eq_div_mul] at h6
  have htop : n.toNat / 10000000 = 0 := Nat.div_eq_of_lt hn'
  have hs : n.toNat * 100 < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hs]
  omega

theorem fraction_digits_8 (n : UInt32) (hn : n < 100000000) :
    ((n/10/10/10/10/10/10/10) % 10) * 100000000 + ((n/10/10/10/10/10/10) % 10) * 10000000 + ((n/10/10/10/10/10) % 10) * 1000000 + ((n/10/10/10/10) % 10) * 100000 + ((n/10/10/10) % 10) * 10000 + ((n/10/10) % 10) * 1000 + ((n/10) % 10) * 100 + ((n) % 10) * 10 = n * 10 := by
  apply UInt32.toNat_inj.mp
  have hn' := UInt32.lt_iff_toNat_lt.mp hn
  simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_mod, UInt32.toNat_div]
  simp [Nat.div_div_eq_div_mul] at hn' ⊢
  have h0 := Nat.mod_add_div (n.toNat / 1) 10
  simp [Nat.div_div_eq_div_mul] at h0
  have h1 := Nat.mod_add_div (n.toNat / 10) 10
  simp [Nat.div_div_eq_div_mul] at h1
  have h2 := Nat.mod_add_div (n.toNat / 100) 10
  simp [Nat.div_div_eq_div_mul] at h2
  have h3 := Nat.mod_add_div (n.toNat / 1000) 10
  simp [Nat.div_div_eq_div_mul] at h3
  have h4 := Nat.mod_add_div (n.toNat / 10000) 10
  simp [Nat.div_div_eq_div_mul] at h4
  have h5 := Nat.mod_add_div (n.toNat / 100000) 10
  simp [Nat.div_div_eq_div_mul] at h5
  have h6 := Nat.mod_add_div (n.toNat / 1000000) 10
  simp [Nat.div_div_eq_div_mul] at h6
  have h7 := Nat.mod_add_div (n.toNat / 10000000) 10
  simp [Nat.div_div_eq_div_mul] at h7
  have htop : n.toNat / 100000000 = 0 := Nat.div_eq_of_lt hn'
  have hs : n.toNat * 10 < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hs]
  omega

theorem fraction_digits_9 (n : UInt32) (hn : n < 1000000000) :
    ((n/10/10/10/10/10/10/10/10) % 10) * 100000000 + ((n/10/10/10/10/10/10/10) % 10) * 10000000 + ((n/10/10/10/10/10/10) % 10) * 1000000 + ((n/10/10/10/10/10) % 10) * 100000 + ((n/10/10/10/10) % 10) * 10000 + ((n/10/10/10) % 10) * 1000 + ((n/10/10) % 10) * 100 + ((n/10) % 10) * 10 + ((n) % 10) * 1 = n * 1 := by
  apply UInt32.toNat_inj.mp
  have hn' := UInt32.lt_iff_toNat_lt.mp hn
  simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_mod, UInt32.toNat_div]
  simp [Nat.div_div_eq_div_mul] at hn' ⊢
  have h0 := Nat.mod_add_div (n.toNat / 1) 10
  simp [Nat.div_div_eq_div_mul] at h0
  have h1 := Nat.mod_add_div (n.toNat / 10) 10
  simp [Nat.div_div_eq_div_mul] at h1
  have h2 := Nat.mod_add_div (n.toNat / 100) 10
  simp [Nat.div_div_eq_div_mul] at h2
  have h3 := Nat.mod_add_div (n.toNat / 1000) 10
  simp [Nat.div_div_eq_div_mul] at h3
  have h4 := Nat.mod_add_div (n.toNat / 10000) 10
  simp [Nat.div_div_eq_div_mul] at h4
  have h5 := Nat.mod_add_div (n.toNat / 100000) 10
  simp [Nat.div_div_eq_div_mul] at h5
  have h6 := Nat.mod_add_div (n.toNat / 1000000) 10
  simp [Nat.div_div_eq_div_mul] at h6
  have h7 := Nat.mod_add_div (n.toNat / 10000000) 10
  simp [Nat.div_div_eq_div_mul] at h7
  have h8 := Nat.mod_add_div (n.toNat / 100000000) 10
  simp [Nat.div_div_eq_div_mul] at h8
  have htop : n.toNat / 1000000000 = 0 := Nat.div_eq_of_lt hn'
  omega

/-- A finite-width decimal suffix, with leading zeroes retained. -/
def fraction_text (n : UInt32) : Nat → Array UInt8
  | 0 => #[]
  | 1 => #[decimal_byte (n)]
  | 2 => #[decimal_byte (n/10), decimal_byte (n)]
  | 3 => #[decimal_byte (n/10/10), decimal_byte (n/10), decimal_byte (n)]
  | 4 => #[decimal_byte (n/10/10/10), decimal_byte (n/10/10), decimal_byte (n/10), decimal_byte (n)]
  | 5 => #[decimal_byte (n/10/10/10/10), decimal_byte (n/10/10/10), decimal_byte (n/10/10), decimal_byte (n/10), decimal_byte (n)]
  | 6 => #[decimal_byte (n/10/10/10/10/10), decimal_byte (n/10/10/10/10), decimal_byte (n/10/10/10), decimal_byte (n/10/10), decimal_byte (n/10), decimal_byte (n)]
  | 7 => #[decimal_byte (n/10/10/10/10/10/10), decimal_byte (n/10/10/10/10/10), decimal_byte (n/10/10/10/10), decimal_byte (n/10/10/10), decimal_byte (n/10/10), decimal_byte (n/10), decimal_byte (n)]
  | 8 => #[decimal_byte (n/10/10/10/10/10/10/10), decimal_byte (n/10/10/10/10/10/10), decimal_byte (n/10/10/10/10/10), decimal_byte (n/10/10/10/10), decimal_byte (n/10/10/10), decimal_byte (n/10/10), decimal_byte (n/10), decimal_byte (n)]
  | 9 => #[decimal_byte (n/10/10/10/10/10/10/10/10), decimal_byte (n/10/10/10/10/10/10/10), decimal_byte (n/10/10/10/10/10/10), decimal_byte (n/10/10/10/10/10), decimal_byte (n/10/10/10/10), decimal_byte (n/10/10/10), decimal_byte (n/10/10), decimal_byte (n/10), decimal_byte (n)]
  | _ => #[]

/-- Canonical extended clock text, parameterized by the trimmed fraction. -/
def clock_text (t : Time) (fraction : UInt32) (width : Nat) : Array UInt8 :=
  #[decimal_byte (t.hour.toUInt32 / 10), decimal_byte t.hour.toUInt32, 58,
    decimal_byte (t.minute.toUInt32 / 10), decimal_byte t.minute.toUInt32, 58,
    decimal_byte (t.second.toUInt32 / 10), decimal_byte t.second.toUInt32] ++
    (if width = 0 then #[] else #[46] ++ fraction_text fraction width)

end Oak.Stdlib.Time
