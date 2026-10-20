import Oak.LRATARM64Bytes
import Oak.LRATRV64Compressed
import Oak.LRATPreflight

/-! Caller-facing contracts for the pinned native guard bytes. These relate
returned register values to the extracted production predicates for every
fuel, including rejection, and transfer existing index/allocation guarantees.
They do not prove compiled call sites, linkage, memory access, or allocation. -/
set_option autoImplicit false
namespace Oak.LRATNativeRefinement

private theorem accepted_iff (result : Option (BitVec 64)) (guard : Option Bool)
    (h : result = guard.map (fun b => if b then 1 else 0)) :
    result = some 1 ↔ guard = some true := by
  rw [h]
  cases guard with
  | none => simp
  | some b => cases b <;> decide

namespace ARM64
open Oak.LRATARM64Bytes
open Oak.AArch64BitwiseFunction (readW)
def atWord (s : State) : UInt32 := UInt32.ofBitVec (readW s.regs 0)
def countWord (s : State) : UInt32 := UInt32.ofBitVec (readW s.regs 1)
def limitWord (s : State) : UInt32 := UInt32.ofBitVec (readW s.regs 2)

/-- Full Boolean refinement, including rejection and arbitrary upper input bits. -/
theorem fits_refines (s : State) (fuel : Nat) :
    (executeBytes fitsBytes s).map (fun out => out.regs 0) =
      (LRATBounds.lrat_fits (atWord s) (countWord s) (limitWord s) fuel).map bit := by
  exact (fits_bytes_result s).trans (by
    rfl)

theorem fits_accepted_iff (s : State) (fuel : Nat) :
    (executeBytes fitsBytes s).map (fun out => out.regs 0) = some 1 ↔
      LRATBounds.lrat_fits (atWord s) (countWord s) (limitWord s) fuel = some true :=
  accepted_iff _ _ (fits_refines s fuel)

/-- Full Boolean refinement, including rejection and arbitrary upper input bits. -/
theorem alloc_refines (s : State) (fuel : Nat) :
    (executeBytes allocBytes s).map (fun out => out.regs 0) =
      (LRATBounds.lrat_alloc_fits (atWord s) fuel).map bit := by
  exact (alloc_bytes_result s).trans (by
    rfl)

theorem alloc_accepted_iff (s : State) (fuel : Nat) :
    (executeBytes allocBytes s).map (fun out => out.regs 0) = some 1 ↔
      LRATBounds.lrat_alloc_fits (atWord s) fuel = some true :=
  accepted_iff _ _ (alloc_refines s fuel)

/-- A successful native guard justifies exact endpoint and interior index arithmetic. -/
theorem fits_index (s : State) (index : UInt32)
    (accepted : (executeBytes fitsBytes s).map (fun out => out.regs 0) = some 1)
    (inside : index < countWord s) :
    (atWord s + countWord s).toNat = (atWord s).toNat + (countWord s).toNat ∧
    (atWord s + index).toNat = (atWord s).toNat + index.toNat ∧
    atWord s + index < limitWord s := by
  have h := (fits_accepted_iff s 0).mp accepted
  exact ⟨LRATBounds.fits_no_wrap _ _ _ 0 h, LRATBounds.fits_index _ _ _ _ 0 h inside⟩

/-- Native acceptance supplies the same exact, positive requests as preflight. -/
theorem allocation_safe (s : State)
    (accepted : (executeBytes allocBytes s).map (fun out => out.regs 0) = some 1) :
    LRATPreflight.AllocationSafe (atWord s) := by
  have h := (LRATBounds.alloc_fits_iff _ 0).mp ((alloc_accepted_iff s 0).mp accepted)
  apply LRATPreflight.allocation_safe
  omega

end ARM64

namespace RV64
open Oak.LRATRV64Bytes
open Oak.RiscVCallExecution
open Oak.LRATRV64Bytes (bit)
def atWord (s : State) : UInt32 := UInt32.ofBitVec ((read s 10).truncate 32)
def countWord (s : State) : UInt32 := UInt32.ofBitVec ((read s 11).truncate 32)
def limitWord (s : State) : UInt32 := UInt32.ofBitVec ((read s 12).truncate 32)

/-- Full Boolean refinement, including rejection and arbitrary upper input bits. -/
theorem fits_refines (s : State) (fuel : Nat) :
    (executeBytes fitsBytes s).map (fun out => read out 10) =
      (LRATBounds.lrat_fits (atWord s) (countWord s) (limitWord s) fuel).map bit := by
  exact (fits_bytes_result s).trans (by
    rw [Oak.LRATNativeGuards.rv_fits_width]
    rfl)

theorem fits_accepted_iff (s : State) (fuel : Nat) :
    (executeBytes fitsBytes s).map (fun out => read out 10) = some 1 ↔
      LRATBounds.lrat_fits (atWord s) (countWord s) (limitWord s) fuel = some true :=
  accepted_iff _ _ (fits_refines s fuel)

/-- Full Boolean refinement, including rejection and arbitrary upper input bits. -/
theorem alloc_refines (s : State) (fuel : Nat) :
    (executeBytes allocBytes s).map (fun out => read out 10) =
      (LRATBounds.lrat_alloc_fits (atWord s) fuel).map bit := by
  exact (alloc_bytes_result s).trans (by
    rw [Oak.LRATNativeGuards.rv_alloc_width]
    rfl)

theorem alloc_accepted_iff (s : State) (fuel : Nat) :
    (executeBytes allocBytes s).map (fun out => read out 10) = some 1 ↔
      LRATBounds.lrat_alloc_fits (atWord s) fuel = some true :=
  accepted_iff _ _ (alloc_refines s fuel)

/-- A successful native guard justifies exact endpoint and interior index arithmetic. -/
theorem fits_index (s : State) (index : UInt32)
    (accepted : (executeBytes fitsBytes s).map (fun out => read out 10) = some 1)
    (inside : index < countWord s) :
    (atWord s + countWord s).toNat = (atWord s).toNat + (countWord s).toNat ∧
    (atWord s + index).toNat = (atWord s).toNat + index.toNat ∧
    atWord s + index < limitWord s := by
  have h := (fits_accepted_iff s 0).mp accepted
  exact ⟨LRATBounds.fits_no_wrap _ _ _ 0 h, LRATBounds.fits_index _ _ _ _ 0 h inside⟩

/-- Native acceptance supplies the same exact, positive requests as preflight. -/
theorem allocation_safe (s : State)
    (accepted : (executeBytes allocBytes s).map (fun out => read out 10) = some 1) :
    LRATPreflight.AllocationSafe (atWord s) := by
  have h := (LRATBounds.alloc_fits_iff _ 0).mp ((alloc_accepted_iff s 0).mp accepted)
  apply LRATPreflight.allocation_safe
  omega

end RV64

namespace RV64Compressed
open Oak.LRATRV64Compressed
open Oak.RiscVCallExecution
open Oak.LRATRV64Bytes (bit)
def atWord (s : State) : UInt32 := UInt32.ofBitVec ((read s 10).truncate 32)
def countWord (s : State) : UInt32 := UInt32.ofBitVec ((read s 11).truncate 32)
def limitWord (s : State) : UInt32 := UInt32.ofBitVec ((read s 12).truncate 32)

/-- Full Boolean refinement, including rejection and arbitrary upper input bits. -/
theorem fits_refines (s : State) (fuel : Nat) :
    (executeBytes fitsBytes s).map (fun out => read out 10) =
      (LRATBounds.lrat_fits (atWord s) (countWord s) (limitWord s) fuel).map bit := by
  exact (fits_bytes_result s).trans (by
    rw [Oak.LRATNativeGuards.rv_fits_width]
    rfl)

theorem fits_accepted_iff (s : State) (fuel : Nat) :
    (executeBytes fitsBytes s).map (fun out => read out 10) = some 1 ↔
      LRATBounds.lrat_fits (atWord s) (countWord s) (limitWord s) fuel = some true :=
  accepted_iff _ _ (fits_refines s fuel)

/-- Full Boolean refinement, including rejection and arbitrary upper input bits. -/
theorem alloc_refines (s : State) (fuel : Nat) :
    (executeBytes allocBytes s).map (fun out => read out 10) =
      (LRATBounds.lrat_alloc_fits (atWord s) fuel).map bit := by
  exact (alloc_bytes_result s).trans (by
    rw [Oak.LRATNativeGuards.rv_alloc_width]
    rfl)

theorem alloc_accepted_iff (s : State) (fuel : Nat) :
    (executeBytes allocBytes s).map (fun out => read out 10) = some 1 ↔
      LRATBounds.lrat_alloc_fits (atWord s) fuel = some true :=
  accepted_iff _ _ (alloc_refines s fuel)

/-- A successful native guard justifies exact endpoint and interior index arithmetic. -/
theorem fits_index (s : State) (index : UInt32)
    (accepted : (executeBytes fitsBytes s).map (fun out => read out 10) = some 1)
    (inside : index < countWord s) :
    (atWord s + countWord s).toNat = (atWord s).toNat + (countWord s).toNat ∧
    (atWord s + index).toNat = (atWord s).toNat + index.toNat ∧
    atWord s + index < limitWord s := by
  have h := (fits_accepted_iff s 0).mp accepted
  exact ⟨LRATBounds.fits_no_wrap _ _ _ 0 h, LRATBounds.fits_index _ _ _ _ 0 h inside⟩

/-- Native acceptance supplies the same exact, positive requests as preflight. -/
theorem allocation_safe (s : State)
    (accepted : (executeBytes allocBytes s).map (fun out => read out 10) = some 1) :
    LRATPreflight.AllocationSafe (atWord s) := by
  have h := (LRATBounds.alloc_fits_iff _ 0).mp ((alloc_accepted_iff s 0).mp accepted)
  apply LRATPreflight.allocation_safe
  omega

end RV64Compressed

end Oak.LRATNativeRefinement
