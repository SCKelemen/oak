import OakSailEntrySource
import OakSailSteppedChecks

/-! Constructive nonvacuity of the loaded source theorem, with explicit
initialization rather than an assertion that reset/startup reaches this state. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailEntryChecks
open LeanRV64D LeanRV64D.Functions
open OakSailBridge.BitwiseDecoded OakSailFetchedCode OakSailSteppedState OakSailSteppedFrame
open OakSailClockTick OakSailPlatformCallback OakSailSteppedChecks OakSailClockedState OakSailEntryInstructions
open OakSailImageLoad OakSailImageSource OakSailEntrySource Oak.MinimalELF

/-- Explicit Machine/Bare/CSR/timer and ABI initialization. Initial x1,
PC and nextPC are not initialized here; entryState installs entry PC, and the
executed call pair derives x1. No generated reset reachability is asserted. -/
def initialState (s : State) (sp : Nat) (left right : BitVec 32)
    (saved1 saved2 : BitVec 64) : State :=
  setRegister (setRegister (setRegister (setRegister (setRegister
    (clockProfileState (witnessProfile s) (0xfffffffffffffffe#64) (0#64) (100#64))
    .x2 (BitVec.ofNat 64 sp)) .x9 saved1) .x18 saved2)
    .x10 (Oak.RiscV.widen 32 false left)) .x11 (Oak.RiscV.widen 32 false right)

theorem initial_profiles (s : State) (sp : Nat) (left right : BitVec 32)
    (saved1 saved2 : BitVec 64) :
    MemoryConfig (initialState s sp left right saved1 saved2) [witnessRegion] ∧
    StepProfile (initialState s sp left right saved1 saved2) ∧
    ClockProfile (initialState s sp left right saved1 saved2)
      (0xfffffffffffffffe#64) (0#64) (100#64) := by
  obtain ⟨hp, hm, _⟩ := witness_combined_profile s
  have hc := clockProfileState_profile (witnessProfile s) (0xfffffffffffffffe#64) (0#64) (100#64)
  have hpc := clockProfileState_stepProfile (witnessProfile s) (0xfffffffffffffffe#64) (0#64) (100#64) hp
  have hmc := clockProfileState_memoryConfig (witnessProfile s) (0xfffffffffffffffe#64) (0#64) (100#64) [witnessRegion] hm
  rcases hc with ⟨c1,c2,c3,c4,c5,c6⟩
  rcases hpc with ⟨p1,p2,p3,p4,p5,p6,p7,p8,p9,p10⟩
  rcases hmc with ⟨m1,m2,m3,m4,m5,m6,m7⟩
  refine ⟨?_, ?_, ?_⟩ <;> constructor <;>
    simpa [initialState, controlState, setRegister, Std.ExtDHashMap.get?_insert] using ‹_›

/-- Constructive nonvacuity for all accepted original compiler images and
u32 arguments, with arbitrary previous x1. Eleven callbacks produce five
actual ticks, including the startup tick; the cycle counter wraps to three. -/
theorem initialized_entry_clocked_prefix
    {source : List UInt8} {claim : Oak.BitwiseSource.Decl} {image : Bytes} {sp : Nat}
    (accepted : acceptsEntry source claim image sp = true)
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
  obtain ⟨hm,hp,hc⟩ := initial_profiles s sp left right saved1 saved2
  apply accepted_typed_entry_clocked_prefix accepted left right fuel
    (initialState s sp left right saved1 saved2) saved1 saved2
    step (0xfffffffffffffffe#64) (0#64) (100#64) [witnessRegion] hm hp hc (by decide)
  all_goals simp [initialState, setRegister, Std.ExtDHashMap.get?_insert]

/-- The constructive witness does not silently pre-initialize the link register. -/
theorem initial_ra_unchanged (s : State) (sp : Nat) (left right : BitVec 32)
    (saved1 saved2 : BitVec 64) :
    (initialState s sp left right saved1 saved2).regs.get? Register.x1 =
      s.regs.get? Register.x1 := by
  simp [initialState, clockProfileState, clockState, witnessProfile, stepProfileState,
    setRegister, Std.ExtDHashMap.get?_insert]

/-- Final return PC, link register, five ticks, and phase in the execution
 theorem are derived; no caller-supplied return address can replace entry+8. -/
theorem returned_control {source : List UInt8} {claim : Oak.BitwiseSource.Decl}
    {image : Bytes} {sp : Nat} (accepted : acceptsEntry source claim image sp = true)
    (s : State) (saved1 saved2 result c t : BitVec 64) :
    let final := clockState (finalSteppedState (bodyEntryState s image sp)
      (BitVec.ofNat 64 sp) saved1 saved2 result (returnAddress image)) c t
    final.regs.get? Register.PC = some (returnAddress image) ∧
    final.regs.get? Register.nextPC = some (returnAddress image) ∧
    final.regs.get? Register.x1 = some (returnAddress image) ∧
    final.regs.get? Register.mcycle = some c ∧
    final.regs.get? Register.mtime = some t := by
  have code := accepted_entry_code s accepted
  have aligned := entry_add_aligned (entryAddress image) 8 code.2.2 code.2.1 (by decide) (by decide)
  have pc := clocked_pc_and_next (bodyEntryState s image sp) (BitVec.ofNat 64 sp)
    saved1 saved2 result (returnAddress image) c t
  rw [clear_aligned (returnAddress image) aligned] at pc
  refine ⟨pc.1, pc.2.1, ?_, (clockState_counters _ c t).1, (clockState_counters _ c t).2⟩
  rw [clocked_register_other _ _ _ _ _ _ _ _ Register.x1 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)]
  exact (called_control _ _).2.2.1

/-- At the fifth tick's exact deadline the generated CLINT operation sets
MTIP; treating the original four-tick body deadline as sufficient is invalid. -/
theorem fifth_tick_at_deadline (s : State) (c : BitVec 64)
    (hp : StepProfile s) (hc : ClockProfile s c (4#64) (5#64)) :
    (tick_clock ()).run s = .ok ()
      (setRegister (clockState s (c+1#64) (5#64)) Register.mip (128#64)) ∧
    (tick_clock ()).run s ≠ .ok () (clockState s (c+1#64) (5#64)) := by
  exact ⟨tick_clock_at_deadline s c (4#64) (5#64) hp hc (by decide),
    tick_clock_at_deadline_not_below s c (4#64) (5#64) hp hc (by decide)⟩

end OakSailEntryChecks
