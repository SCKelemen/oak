import Oak.Stdlib.TimeUnsignedWriterLaws
namespace Oak.Stdlib.Time
set_option maxHeartbeats 800000
private theorem digits_terminate (budget extra : Nat) :
    ∀ (digits : Array UInt8) (count : UInt32) (value : UInt64),
      value.toNat < 10^(budget+1) →
      ∃ out, put_u64.loop1 digits count value true (extra+budget+2) = some out := by
  induction budget with
  | zero =>
    intro digits count value hv
    have hz : value/10 = 0 := UInt64.toNat_inj.mp (by
      simp only [UInt64.toNat_div, UInt64.toNat_zero]
      change value.toNat/10 = 0
      exact Nat.div_eq_of_lt hv)
    simp [put_u64.loop1, hz ]
  | succ budget ih =>
    intro digits count value hv
    have hd : (value/10).toNat < 10^(budget+1) := by
      rw [UInt64.toNat_div]
      change value.toNat/10 < 10^(budget+1)
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      simpa only [Nat.pow_succ] using hv
    by_cases hz : value/10 = 0
    · simp [put_u64.loop1, hz ]
    · obtain ⟨out, ho⟩ := ih (digits.setIfInBounds count.toNat (unsigned_decimal_byte value)) (count+1) (value/10) hd
      refine ⟨out, ?_⟩
      have hf : extra+(budget+1)+2 = (extra+budget+2)+1 := by omega
      rw [hf, put_u64.loop1]
      have hne : (value/10 != 0) = true := by simpa using hz
      simpa only [hne, ite_true, unsigned_decimal_byte] using ho

private theorem digits_more_fuel (fuel extra : Nat) :
    ∀ (digits : Array UInt8) (count : UInt32) (value : UInt64) (more : Bool) (out),
      put_u64.loop1 digits count value more fuel = some out →
      put_u64.loop1 digits count value more (fuel+extra) = some out := by
  induction fuel with
  | zero => intros; contradiction
  | succ fuel ih =>
    intro digits count value more out h
    have hf : fuel+1+extra = (fuel+extra)+1 := by omega
    rw [hf, put_u64.loop1]
    unfold put_u64.loop1 at h
    cases more with
    | false => simpa using h
    | true => exact ih _ _ _ _ _ h

/-- Every UInt64 has a nonempty decimal expansion of at most twenty bytes.
The extracted reverse-digit writer terminates with any fuel of at least 21. -/
theorem put_u64_digits_complete (value : UInt64) (extra : Nat) :
    ∃ (digits : Array UInt8) (count : UInt32),
      put_u64.loop1 (Array.replicate 20 0) 0 value true (21+extra) = some (digits, count, 0, false) ∧
      0 < count.toNat ∧ count.toNat ≤ 20 ∧ digits.size = 20 ∧
      reverse_digits_valid digits count.toNat ∧
      reverse_decimal_value digits count.toNat 0 = value.toNat := by
  have hv : value.toNat < 10^(19+1) := by have := value.toNat_lt; omega
  obtain ⟨⟨digits, count, remaining, more⟩, ho⟩ := digits_terminate 19 0 (Array.replicate 20 0) 0 value hv
  have he := put_u64_digits_exact 21 (Array.replicate 20 0) 0 value true
    (digits, count, remaining, more) (by decide) (by decide)
    (by intro k hk; simp at hk) (by simp) ho
  have hr := he.2.2.2.1
  have hm := he.2.2.2.2.1
  change remaining = 0 at hr
  change more = false at hm
  subst remaining more
  refine ⟨digits, count, digits_more_fuel 21 extra _ _ _ _ _ ho,
    he.2.2.1 rfl, ?_, ?_, he.2.2.2.2.2.2.1, he.2.2.2.2.2.2.2⟩
  · simpa using he.2.1
  · simpa using he.2.2.2.2.2.1
end Oak.Stdlib.Time
