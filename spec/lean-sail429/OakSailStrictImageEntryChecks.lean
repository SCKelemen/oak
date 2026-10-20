import OakSailStrictImageEntryExecution
import OakSailEntryChecks

/-! Constructive witness using the unchanged existing explicit initialized state.
All original bytes are rechecked in this same 4.29 environment. No 4.33 receipt
or proof object is consumed. The execution claim still ends at e_entry+8. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailStrictImageEntryChecks
open LeanRV64D LeanRV64D.Functions
open OakSailBridge.BitwiseDecoded OakSailFetchedCode OakSailSteppedState OakSailSteppedFrame
open OakSailClockTick OakSailPlatformCallback OakSailSteppedChecks OakSailClockedState OakSailEntryInstructions
open OakSailImageLoad OakSailImageSource OakSailEntrySource OakSailEntryChecks Oak.MinimalELF

theorem strict_layout_below {source wasm : List UInt8} {arm image : Bytes}
    {claim : Oak.BitwiseSource.Decl}
    (checked : Oak.BitwiseSourceImageParity.check source wasm arm image = some claim) :
    ImageLayout image 65536 := by
  obtain ⟨_, _, _, _, _, hs, _⟩ := Oak.StrictImageEntryContract.source_entry_binding checked
  rw [ImageLayout, hs]
  decide

theorem strict_layout_above {source wasm : List UInt8} {arm image : Bytes}
    {claim : Oak.BitwiseSource.Decl}
    (checked : Oak.BitwiseSourceImageParity.check source wasm arm image = some claim) :
    ImageLayout image 65696 := by
  obtain ⟨_, _, _, _, _, hs, _⟩ := Oak.StrictImageEntryContract.source_entry_binding checked
  rw [ImageLayout, hs]
  decide

theorem initialized_strict_entry_clocked_prefix
    {source wasm : List UInt8} {claim : Oak.BitwiseSource.Decl} {arm image : Bytes} {sp : Nat}
    (checked : Oak.BitwiseSourceImageParity.check source wasm arm image = some claim)
    (layout : OakSailImageLoad.ImageLayout image sp)
    (left right : BitVec 32) (fuel : Nat) (s : State) (saved1 saved2 : BitVec 64) (step : Nat) :
    Oak.BitwiseSource.Grammar source claim ∧
    Oak.LoweringRefinement.evalX (Oak.BitwiseSourceLowering.toExpr claim)
      (Oak.BitwiseSourceLowering.inputs left right) (fun _ => 0) fuel =
        some (Oak.BitwiseFunction.eval claim.op left right) ∧
    (boundedPlatform 11 (0,step)).run
      (entryState (initialState s sp left right saved1 saved2) image sp) = .ok (1,step)
      (clockState (finalSteppedState
        (bodyEntryState (initialState s sp left right saved1 saved2) image sp)
        (BitVec.ofNat 64 sp) saved1 saved2
        (Oak.RiscV.widen 32 false (Oak.BitwiseFunction.eval claim.op left right)) (returnAddress image))
        (3#64) (5#64)) := by
  obtain ⟨hm, hp, hc⟩ := initial_profiles s sp left right saved1 saved2
  apply OakSailStrictImageEntryExecution.strict_typed_entry_clocked_prefix checked layout
    left right fuel (initialState s sp left right saved1 saved2) saved1 saved2
    step (0xfffffffffffffffe#64) (0#64) (100#64) [witnessRegion] hm hp hc (by decide)
  all_goals simp [initialState, setRegister, Std.ExtDHashMap.get?_insert]

end OakSailStrictImageEntryChecks
