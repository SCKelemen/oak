import Oak.LRATBounds
import Std.Tactic.BVDecide

/-!
Scalar expressions of the checked `lrat.arm64.oakasm` / `lrat.rv64.oakasm`
units. The required Go gate verifies the actual units against the production
Oak definitions and encodes both. These expressions expose the width seam:
ARM64 uses W-register subtraction and unsigned comparisons; RV64 normalizes
all u32 inputs and the subtraction result before its 64-bit comparisons.
This is not a theorem about the entire checker binary, instruction decoding,
ABI linkage, the Go verifier, or the C compiler.
-/
namespace Oak.LRATNativeGuards

-- cmp/cset ls; sub at width 32; cmp/cset ls; and.
def armFits (at_ count limit : BitVec 32) : Bool :=
  decide (at_ ≤ limit) && decide (count ≤ limit - at_)

-- slli/srli 32, including the low-word subtraction result.
def lowWord (x : BitVec 64) : BitVec 64 := (x <<< 32) >>> 32

def rvFits (at_ count limit : BitVec 64) : Bool :=
  !(decide (lowWord limit < lowWord at_)) &&
    !(decide (lowWord (lowWord limit - lowWord at_) < lowWord count))

def armAlloc (count : BitVec 32) : Bool := decide (count < 1073741823)
def rvAlloc (count : BitVec 64) : Bool := decide (lowWord count < 1073741823)

theorem arm_fits_extracted (at_ count limit : UInt32) (fuel : Nat) :
    Oak.LRATBounds.lrat_fits at_ count limit fuel = some (armFits at_.toBitVec count.toBitVec limit.toBitVec) := by
  rfl

theorem rv_fits_width (at_ count limit : BitVec 64) :
    rvFits at_ count limit = armFits (at_.truncate 32) (count.truncate 32) (limit.truncate 32) := by
  unfold rvFits armFits lowWord
  bv_decide

theorem arm_alloc_extracted (count : UInt32) (fuel : Nat) :
    Oak.LRATBounds.lrat_alloc_fits count fuel = some (armAlloc count.toBitVec) := by
  rfl

theorem rv_alloc_width (count : BitVec 64) :
    rvAlloc count = armAlloc (count.truncate 32) := by
  unfold rvAlloc armAlloc lowWord
  bv_decide

-- Compose the scalar realization with the existing mathematical bounds.
theorem arm_fits_sound (at_ count limit : UInt32)
    (h : armFits at_.toBitVec count.toBitVec limit.toBitVec = true) :
    at_.toNat + count.toNat ≤ limit.toNat := by
  apply (Oak.LRATBounds.fits_iff at_ count limit 0).mp
  rw [arm_fits_extracted, h]

theorem rv_fits_sound (at_ count limit : BitVec 64)
    (h : rvFits at_ count limit = true) :
    (at_.truncate 32).toNat + (count.truncate 32).toNat ≤ (limit.truncate 32).toNat := by
  rw [rv_fits_width] at h
  exact arm_fits_sound (UInt32.ofBitVec (at_.truncate 32))
    (UInt32.ofBitVec (count.truncate 32)) (UInt32.ofBitVec (limit.truncate 32)) h

theorem arm_alloc_sound (count : UInt32)
    (h : armAlloc count.toBitVec = true) :
    (count + 1).toNat = count.toNat + 1 ∧
    ((count + 1) * 4).toNat = (count.toNat + 1) * 4 ∧
    0 < ((count + 1) * 4).toNat := by
  apply Oak.LRATBounds.allocation_exact count 0
  rw [arm_alloc_extracted, h]

theorem rv_alloc_sound (count : BitVec 64) (h : rvAlloc count = true) :
    ((count.truncate 32).toNat + 1) * 4 < 4294967296 := by
  rw [rv_alloc_width] at h
  apply (Oak.LRATBounds.alloc_fits_iff (UInt32.ofBitVec (count.truncate 32)) 0).mp
  rw [arm_alloc_extracted]
  exact congrArg some h

end Oak.LRATNativeGuards
