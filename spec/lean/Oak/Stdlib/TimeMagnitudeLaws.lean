import Oak.Stdlib.TimeComponentLaws
import Std.Tactic.BVDecide

/-! # Signed ISO component reconstruction
Unsigned magnitudes preserve signed minima. The bit-vector facts in this file
use the pinned native LRAT checker, unlike the component overflow proofs.
-/
namespace Oak.Stdlib.Time
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def signed_time_component (negative : Bool) (n : UInt64) : Int64 :=
  (if negative then 0-n else n).toInt64

def signed_calendar_component (negative : Bool) (n : UInt64) : Int32 :=
  (if negative then 0-n else n).toUInt32.toInt32

theorem magnitude_i64_roundtrip (n : Int64) (fuel : Nat) :
    ∃ m, magnitude_i64 n fuel = some m ∧
      m ≤ (if n < 0 then 9223372036854775808 else 9223372036854775807) ∧
      signed_time_component (decide (n < 0)) m = n := by
  refine ⟨if n < 0 then 0-n.toUInt64 else n.toUInt64, by simp [magnitude_i64], ?_⟩
  unfold signed_time_component
  bv_decide

theorem magnitude_i32_roundtrip (n : Int32) (fuel : Nat) :
    ∃ m, magnitude_i64 n.toInt64 fuel = some m ∧
      m ≤ (if n < 0 then 2147483648 else 2147483647) ∧
      signed_calendar_component (decide (n < 0)) m = n := by
  refine ⟨if n.toInt64 < 0 then 0-n.toInt64.toUInt64 else n.toInt64.toUInt64,
    by simp [magnitude_i64], ?_⟩
  unfold signed_calendar_component
  bv_decide

/-- Unit splitting is exact in unbounded arithmetic, for every UInt64. -/
theorem duration_units_reconstruct (n : UInt64) :
    (n/3600000000000).toNat*3600000000000 +
      ((n/60000000000)%60).toNat*60000000000 +
      ((n/1000000000)%60).toNat*1000000000 + (n%1000000000).toNat = n.toNat := by
  simp only [UInt64.toNat_div, UInt64.toNat_mod, UInt64.toNat_ofNat]
  have h0 := Nat.mod_add_div n.toNat 1000000000
  have h1 := Nat.mod_add_div (n.toNat/1000000000) 60
  have h2 := Nat.mod_add_div (n.toNat/60000000000) 60
  simp [Nat.div_div_eq_div_mul] at h0 h1 h2 ⊢
  omega

/-- Every formatter unit accumulation fits under the original magnitude. -/
theorem duration_units_fit (n : UInt64) :
    (n/3600000000000).toNat*3600000000000 ≤ n.toNat ∧
    (n/3600000000000).toNat*3600000000000 + ((n/60000000000)%60).toNat*60000000000 ≤ n.toNat ∧
    (n/3600000000000).toNat*3600000000000 + ((n/60000000000)%60).toNat*60000000000 +
      ((n/1000000000)%60).toNat*1000000000 ≤ n.toNat := by
  have h := duration_units_reconstruct n
  omega


end Oak.Stdlib.Time
