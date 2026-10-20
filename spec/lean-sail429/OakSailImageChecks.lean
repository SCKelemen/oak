import OakSailImageSource
import OakSailSteppedChecks

/-! Constructive nonvacuity of the loaded source theorem, with explicit
initialization rather than an assertion that reset/startup reaches this state. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailImageChecks
open LeanRV64D LeanRV64D.Functions
open OakSailBridge.BitwiseDecoded OakSailFetchedCode OakSailSteppedState OakSailSteppedFrame
open OakSailClockTick OakSailPlatformCallback OakSailSteppedChecks
open OakSailImageLoad OakSailImageSource Oak.MinimalELF

/-- A described, explicitly initialized invocation state. It may start from
arbitrary RAM and nonregister state; only listed registers are initialized.
This is not a generated Sail reset or ELF startup execution. -/
def invocationState (s : State) (address sp : Nat) (left right : BitVec 32)
    (saved1 saved2 : BitVec 64) : State :=
  controlState
    (setRegister (setRegister (setRegister (setRegister (setRegister (setRegister
      (clockProfileState (witnessProfile s) (0xfffffffffffffffe#64) (0#64) (100#64))
      .x2 (BitVec.ofNat 64 sp)) .x9 saved1) .x18 saved2)
      .x10 (Oak.RiscV.widen 32 false left)) .x11 (Oak.RiscV.widen 32 false right))
      .x1 (0x12000#64)) (BitVec.ofNat 64 address) (BitVec.ofNat 64 address)

theorem invocation_profiles (s : State) (address sp : Nat) (left right : BitVec 32)
    (saved1 saved2 : BitVec 64) :
    MemoryConfig (invocationState s address sp left right saved1 saved2) [witnessRegion] ∧
    StepProfile (invocationState s address sp left right saved1 saved2) ∧
    ClockProfile (invocationState s address sp left right saved1 saved2)
      (0xfffffffffffffffe#64) (0#64) (100#64) := by
  obtain ⟨hp, hm, _⟩ := witness_combined_profile s
  have hc := clockProfileState_profile (witnessProfile s) (0xfffffffffffffffe#64) (0#64) (100#64)
  have hpc := clockProfileState_stepProfile (witnessProfile s) (0xfffffffffffffffe#64) (0#64) (100#64) hp
  have hmc := clockProfileState_memoryConfig (witnessProfile s) (0xfffffffffffffffe#64) (0#64) (100#64) [witnessRegion] hm
  rcases hc with ⟨c1,c2,c3,c4,c5,c6⟩
  rcases hpc with ⟨p1,p2,p3,p4,p5,p6,p7,p8,p9,p10⟩
  rcases hmc with ⟨m1,m2,m3,m4,m5,m6,m7⟩
  refine ⟨?_, ?_, ?_⟩ <;> constructor <;>
    simpa [invocationState, controlState, setRegister, Std.ExtDHashMap.get?_insert] using ‹_›

/-- For every accepted actual image and all u32 arguments, the complete
platform/invocation/loader premises coexist and the nine iterations succeed.
The cycle counter deliberately wraps, while the timer stays below deadline. -/
theorem initialized_image_clocked_prefix
    {source : List UInt8} {claim : Oak.BitwiseSource.Decl} {image : Bytes} {address sp : Nat}
    (accepted : accepts source claim image address sp = true)
    (left right : BitVec 32) (fuel : Nat) (s : State) (saved1 saved2 : BitVec 64) (step : Nat) :
    Oak.BitwiseSource.Grammar source claim ∧
    Oak.LoweringRefinement.evalX (Oak.BitwiseSourceLowering.toExpr claim)
      (Oak.BitwiseSourceLowering.inputs left right) (fun _ => 0) fuel =
        some (Oak.BitwiseFunction.eval claim.op left right) ∧
    (boundedPlatform 9 (0,step)).run
      (installImage (invocationState s address sp left right saved1 saved2) image sp) = .ok (1,step)
      (clockState (finalSteppedState
        (installImage (invocationState s address sp left right saved1 saved2) image sp)
        (BitVec.ofNat 64 sp) saved1 saved2
        (Oak.RiscV.widen 32 false (Oak.BitwiseFunction.eval claim.op left right)) (0x12000#64))
        (2#64) (4#64)) := by
  obtain ⟨hm,hp,hc⟩ := invocation_profiles s address sp left right saved1 saved2
  apply accepted_typed_image_clocked_prefix accepted left right fuel
    (invocationState s address sp left right saved1 saved2) saved1 saved2 (0x12000#64)
    step (0xfffffffffffffffe#64) (0#64) (100#64) [witnessRegion] hm hp hc (by decide)
  all_goals first
    | (unfold ReturnAligned; decide +kernel)
    | simp [invocationState, controlState, setRegister, Std.ExtDHashMap.get?_insert]

/-- Installing the image cannot overwrite any byte in the reserved frame. -/
theorem loaded_stack_unchanged (s : State) (image : Bytes) (sp query : Nat)
    (h : ImageLayout image sp) (hq : sp-96 ≤ query ∧ query < sp) :
    (installImage s image sp).mem.get? query = s.mem.get? query := by
  apply loaded_memory_other
  rcases h with ⟨_,_,_,_,hsep⟩
  omega

theorem rx_rw_permissions (image : Bytes) (sp : Nat) :
    (imageRegion image).attributes.readable = true ∧
    (imageRegion image).attributes.writable = false ∧
    (imageRegion image).attributes.executable = true ∧
    (stackRegion sp).attributes.readable = true ∧
    (stackRegion sp).attributes.writable = true ∧
    (stackRegion sp).attributes.executable = false := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

end OakSailImageChecks
