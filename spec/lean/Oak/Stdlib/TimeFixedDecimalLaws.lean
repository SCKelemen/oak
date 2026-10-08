import Oak.Stdlib.TimeUnsignedDecimalLaws
namespace Oak.Stdlib.Time
set_option maxHeartbeats 1000000

/-- Unbounded decimal value of a fixed-width ASCII field. -/
def fixed_decimal_value (src : Array UInt8) (start : Nat) : Nat → Nat
  | 0 => 0
  | width+1 => fixed_decimal_value src start width*10 + (src.getD (start+width) 0-48).toNat

def fixed_decimal_valid (src : Array UInt8) (start width : Nat) : Prop :=
  ∀ j, j < width → 48 ≤ src.getD (start+j) 0 ∧ src.getD (start+j) 0 ≤ 57

theorem fixed_decimal_congr (a b : Array UInt8) (start width : Nat)
    (h : ∀ j, j < width → a.getD (start+j) 0 = b.getD (start+j) 0) :
    fixed_decimal_value a start width = fixed_decimal_value b start width := by
  induction width with
  | zero => rfl
  | succ width ih =>
    simp only [fixed_decimal_value, ih (fun j hj => h j (by omega)), h width (by omega)]

theorem fixed_decimal_cons (src : Array UInt8) (start width : Nat) :
    fixed_decimal_value src start (width+1) =
      (src.getD start 0-48).toNat*10^width + fixed_decimal_value src (start+1) width := by
  induction width with
  | zero => simp [fixed_decimal_value]
  | succ width ih =>
    rw [fixed_decimal_value, ih, fixed_decimal_value, Nat.pow_succ]
    simp only [Nat.add_mul, Nat.mul_assoc]
    have hp : start+1+width = start+(width+1) := by omega
    rw [hp, Nat.add_assoc]

/-- The fixed-width writer's byte conversion is exact. -/
theorem fixed_decimal_byte_exact (value : UInt32) :
    48 ≤ (48+(value%10).toUInt8 : UInt8) ∧ (48+(value%10).toUInt8 : UInt8) ≤ 57 ∧
    ((48+(value%10).toUInt8 : UInt8)-48).toNat = value.toNat%10 := by
  have hr : value.toNat%10 < 10 := Nat.mod_lt _ (by decide)
  have he : (48+(value%10).toUInt8 : UInt8).toNat = 48+value.toNat%10 := by
    simp only [UInt8.toNat_add, UInt32.toNat_toUInt8, UInt32.toNat_mod]
    change (48+(value.toNat%10)%256)%256 = 48+value.toNat%10
    omega
  have hlo : 48 ≤ (48+(value%10).toUInt8 : UInt8) := UInt8.le_iff_toNat_le.mpr (by rw [he]; change 48 ≤ _; omega)
  refine ⟨hlo, UInt8.le_iff_toNat_le.mpr (by rw [he]; change _ ≤ 57; omega), ?_⟩
  rw [UInt8.toNat_sub_of_le _ _ hlo, he]
  change 48+value.toNat%10-48 = value.toNat%10
  omega
end Oak.Stdlib.Time
