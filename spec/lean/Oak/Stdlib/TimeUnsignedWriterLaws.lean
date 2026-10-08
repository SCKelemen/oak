import Oak.Stdlib.TimeUnsignedDecimalLaws
namespace Oak.Stdlib.Time
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

/-- Every populated reverse-buffer byte is an ASCII decimal digit. -/
def reverse_digits_valid (digits : Array UInt8) (count : Nat) : Prop :=
  ∀ k, k < count → 48 ≤ digits.getD k 0 ∧ digits.getD k 0 ≤ 57

private theorem digit_store_prefix (digits : Array UInt8) (count : Nat) (byte : UInt8) (acc : Nat) :
    reverse_decimal_value (digits.setIfInBounds count byte) count acc =
      reverse_decimal_value digits count acc := by
  apply reverse_decimal_value_congr
  intro k hk
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne (by omega : count ≠ k)]

/-- A returning reverse-digit loop preserves the exact mathematical value.
Capacity and counter assumptions rule out dropped writes and index wrap. -/
theorem put_u64_digits_exact (fuel : Nat) :
    ∀ (digits : Array UInt8) (count : UInt32) (remaining : UInt64) (more : Bool)
      (out : Array UInt8 × UInt32 × UInt64 × Bool),
      count.toNat+fuel ≤ digits.size+1 → count.toNat+fuel ≤ 4294967296 →
      reverse_digits_valid digits count.toNat → (more = false → remaining = 0) →
      put_u64.loop1 digits count remaining more fuel = some out →
      count.toNat ≤ out.2.1.toNat ∧ out.2.1.toNat ≤ count.toNat+fuel-1 ∧
      (more = true → count.toNat < out.2.1.toNat) ∧
      out.2.2.1 = 0 ∧ out.2.2.2 = false ∧ out.1.size = digits.size ∧
      reverse_digits_valid out.1 out.2.1.toNat ∧
      reverse_decimal_value out.1 out.2.1.toNat 0 = reverse_decimal_value digits count.toNat remaining.toNat := by
  induction fuel with
  | zero => intros; contradiction
  | succ fuel ih =>
    intro digits count remaining more out hs hc hv hr h
    unfold put_u64.loop1 at h
    cases more with
    | false =>
      simp only [Bool.false_eq_true, ite_false, pure, Option.some.injEq] at h
      subst out
      have hz := hr rfl
      subst remaining
      exact ⟨Nat.le_refl _, by change count.toNat ≤ count.toNat+(fuel+1)-1; omega, by simp, rfl, rfl, rfl, hv, rfl⟩
    | true =>
      simp only [ite_true] at h
      have hcount : (count+1).toNat = count.toNat+1 := by
        have hf : 0 < fuel := by cases fuel <;> simp_all [put_u64.loop1]
        rw [UInt32.toNat_add]
        change (count.toNat+1)%4294967296 = count.toNat+1
        omega
      have hsize : count.toNat < digits.size := by
        have hf : 0 < fuel := by cases fuel <;> simp_all [put_u64.loop1]
        omega
      have hb := unsigned_decimal_byte_exact remaining
      have hvalid : reverse_digits_valid (digits.setIfInBounds count.toNat (unsigned_decimal_byte remaining)) (count+1).toNat := by
        intro k hk
        rw [hcount] at hk
        by_cases he : count.toNat = k
        · subst k
          simpa [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self_of_lt hsize] using (And.intro hb.1 hb.2.1)
        · simpa [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne he] using hv k (by omega)
      have hrem : ((remaining/10 != 0) = false) → remaining/10 = 0 := by simp
      have hi := ih (digits.setIfInBounds count.toNat (unsigned_decimal_byte remaining))
        (count+1) (remaining/10) (remaining/10 != 0) out
        (by simp only [Array.size_setIfInBounds, hcount]; omega)
        (by rw [hcount]; omega) hvalid hrem h
      have hstep : reverse_decimal_value (digits.setIfInBounds count.toNat (unsigned_decimal_byte remaining))
          (count+1).toNat (remaining/10).toNat = reverse_decimal_value digits count.toNat remaining.toNat := by
        rw [hcount, reverse_decimal_value]
        have hget : (digits.setIfInBounds count.toNat (unsigned_decimal_byte remaining)).getD count.toNat 0 = unsigned_decimal_byte remaining := by
          simp [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self_of_lt hsize]
        rw [hget, hb.2.2, UInt64.toNat_div]
        have hn : remaining.toNat/10*10+remaining.toNat%10 = remaining.toNat := by omega
        change reverse_decimal_value _ count.toNat (remaining.toNat/10*10+remaining.toNat%10) = _
        rw [hn, digit_store_prefix]
      refine ⟨?_, ?_, ?_, hi.2.2.2.1, hi.2.2.2.2.1, ?_, hi.2.2.2.2.2.2.1, ?_⟩
      · have := hi.1; rw [hcount] at this; omega
      · have := hi.2.1; rw [hcount] at this; omega
      · intro _; have := hi.1; rw [hcount] at this; omega
      · simpa using hi.2.2.2.2.2.1
      · exact hi.2.2.2.2.2.2.2.trans hstep
end Oak.Stdlib.Time
