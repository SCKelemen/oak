import OakSailStrictImageEntry

/-!
# Strict original bundle to the existing actual entry execution theorem

This thin corollary retains the existing full-state equality, initialized
Machine/Bare platform/ABI premises and strict five-tick deadline. It finishes
at e_entry+8 before ADDI/ECALL. No new execution model or Linux/process claim.

This module requires the real pinned Lean 4.29 external-model build and audit.
It is not validated by the separate 4.33 pure-expression diagnostic.
-/
set_option autoImplicit false
noncomputable section
namespace OakSailStrictImageEntryExecution
open LeanRV64D LeanRV64D.Functions
open OakSailBridge.BitwiseDecoded OakSailFetchedCode
open OakSailSteppedState OakSailSteppedFetch OakSailSteppedFrame
open OakSailClockTick OakSailClockedState OakSailPlatformCallback OakSailClockedPrefix
open OakSailImageLoad OakSailImageSource OakSailEntryInstructions OakSailEntrySource Oak.MinimalELF

theorem strict_typed_entry_clocked_prefix
    {source wasm : List UInt8} {claim : Oak.BitwiseSource.Decl} {arm image : Bytes} {sp : Nat}
    (checked : Oak.BitwiseSourceImageParity.check source wasm arm image = some claim)
    (layout : OakSailImageLoad.ImageLayout image sp)
    (left right : BitVec 32) (fuel : Nat) (s : State)
    (saved1 saved2 : BitVec 64) (step : Nat) (c t d : BitVec 64)
    (previous : List PMA_Region)
    (hc : MemoryConfig s previous) (hp : StepProfile s)
    (hclock : ClockProfile s c t d) (hdeadline : t.toNat + 5 < d.toNat)
    (hsp : s.regs.get? Register.x2 = some (BitVec.ofNat 64 sp))
    (h1 : s.regs.get? Register.x9 = some saved1)
    (h2 : s.regs.get? Register.x18 = some saved2)
    (hl : s.regs.get? Register.x10 = some (Oak.RiscV.widen 32 false left))
    (hr : s.regs.get? Register.x11 = some (Oak.RiscV.widen 32 false right)) :
    Oak.BitwiseSource.Grammar source claim ∧
    Oak.LoweringRefinement.evalX (Oak.BitwiseSourceLowering.toExpr claim)
      (Oak.BitwiseSourceLowering.inputs left right) (fun _ => 0) fuel =
        some (Oak.BitwiseFunction.eval claim.op left right) ∧
    (boundedPlatform 11 (0,step)).run (entryState s image sp) = .ok (1,step)
      (clockState (finalSteppedState (bodyEntryState s image sp) (BitVec.ofNat 64 sp) saved1 saved2
        (Oak.RiscV.widen 32 false (Oak.BitwiseFunction.eval claim.op left right)) (returnAddress image))
        (c+5#64) (t+5#64)) := by
  exact OakSailEntrySource.accepted_typed_entry_clocked_prefix
    (OakSailStrictImageEntry.strict_source_entry_admitted_of_layout checked layout)
    left right fuel s saved1 saved2 step c t d previous
    hc hp hclock hdeadline hsp h1 h2 hl hr

end OakSailStrictImageEntryExecution
