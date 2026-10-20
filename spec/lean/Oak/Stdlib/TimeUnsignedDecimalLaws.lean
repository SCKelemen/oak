import Oak.Stdlib.TimeComponentLaws
/-! # UInt64 decimal value model
The model and byte conversion facts use unbounded natural arithmetic and are
kernel checked. They support the actual extracted writer/scanner bridge.
-/
namespace Oak.Stdlib.Time
set_option maxHeartbeats 800000

/-- Unbounded value of the writer's little-endian digit buffer, read from the
highest populated index down to zero, starting with a supplied accumulator. -/
def reverse_decimal_value (digits : Array UInt8) : Nat → Nat → Nat
  | 0, acc => acc
  | count+1, acc => reverse_decimal_value digits count
      (acc*10 + (digits.getD count 0 - 48).toNat)

theorem reverse_decimal_value_ge (digits : Array UInt8) (count acc : Nat) :
    acc ≤ reverse_decimal_value digits count acc := by
  induction count generalizing acc with
  | zero => exact Nat.le_refl _
  | succ count ih =>
    have h := ih (acc*10+(digits.getD count 0-48).toNat)
    simp only [reverse_decimal_value]
    omega

theorem reverse_decimal_value_congr (a b : Array UInt8) (count acc : Nat)
    (h : ∀ k, k < count → a.getD k 0 = b.getD k 0) :
    reverse_decimal_value a count acc = reverse_decimal_value b count acc := by
  induction count generalizing acc with
  | zero => rfl
  | succ count ih =>
    simp only [reverse_decimal_value, h count (by omega)]
    exact ih _ (fun k hk => h k (by omega))

/-- Exact ASCII digit emitted by the extracted UInt64 writer. -/
def unsigned_decimal_byte (value : UInt64) : UInt8 := 48+(value%10).toUInt8

theorem unsigned_decimal_byte_exact (value : UInt64) :
    48 ≤ unsigned_decimal_byte value ∧ unsigned_decimal_byte value ≤ 57 ∧
    (unsigned_decimal_byte value - 48).toNat = value.toNat%10 := by
  have hr : value.toNat%10 < 10 := Nat.mod_lt _ (by decide)
  have he : (unsigned_decimal_byte value).toNat = 48+value.toNat%10 := by
    simp only [unsigned_decimal_byte, UInt8.toNat_add, UInt64.toNat_toUInt8, UInt64.toNat_mod]
    change (48+(value.toNat%10)%256)%256 = 48+value.toNat%10
    omega
  have hlo : 48 ≤ unsigned_decimal_byte value := UInt8.le_iff_toNat_le.mpr (by rw [he]; change 48 ≤ _; omega)
  refine ⟨hlo, UInt8.le_iff_toNat_le.mpr (by rw [he]; change _ ≤ 57; omega), ?_⟩
  rw [UInt8.toNat_sub_of_le _ _ hlo, he]
  change 48+value.toNat%10-48 = value.toNat%10
  omega

end Oak.Stdlib.Time
