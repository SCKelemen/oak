import OakSailExitSource

/-! Constructive all-u32 readiness, ABI representation and preservation checks.
The initialized witness is not a claim about reset or Linux process startup. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailExitChecks
open LeanRV64D LeanRV64D.Functions
open OakSailBridge.BitwiseDecoded OakSailSteppedState OakSailSteppedFrame
open OakSailClockTick OakSailClockedState OakSailPlatformCallback OakSailSteppedChecks
open OakSailImageLoad OakSailEntryInstructions OakSailEntrySource OakSailEntryChecks
open OakSailExitInstructions OakSailExitSource Oak.MinimalELF

theorem initialized_exit_ready
    {source : List UInt8} {claim : Oak.BitwiseSource.Decl} {image : Bytes} {sp : Nat}
    (accepted : acceptsExit source claim image sp = true)
    (left right : BitVec 32) (fuel : Nat) (s : State) (saved1 saved2 : BitVec 64) (step : Nat) :
    Oak.BitwiseSource.Grammar source claim ∧
    Oak.LoweringRefinement.evalX (Oak.BitwiseSourceLowering.toExpr claim)
      (Oak.BitwiseSourceLowering.inputs left right) (fun _ => 0) fuel =
        some (Oak.BitwiseFunction.eval claim.op left right) ∧
    (boundedPlatform 12 (0,step)).run
      (entryState (initialState s sp left right saved1 saved2) image sp) = .ok (0,step)
      (readyState (initialState s sp left right saved1 saved2) image sp saved1 saved2
        (Oak.RiscV.widen 32 false (Oak.BitwiseFunction.eval claim.op left right)) (4#64) (6#64)) ∧
    ExitReady (readyState (initialState s sp left right saved1 saved2) image sp saved1 saved2
      (Oak.RiscV.widen 32 false (Oak.BitwiseFunction.eval claim.op left right)) (4#64) (6#64))
      (entryAddress image) (Oak.BitwiseFunction.eval claim.op left right) := by
  obtain ⟨hm,hp,hk⟩ := initial_profiles s sp left right saved1 saved2
  apply accepted_typed_exit_ready accepted left right fuel
    (initialState s sp left right saved1 saved2) saved1 saved2 step
    (0xfffffffffffffffe#64) (0#64) (100#64) [witnessRegion] hm hp hk (by decide)
  all_goals simp [initialState, setRegister, Std.ExtDHashMap.get?_insert]

/-- No hidden a7 initialization supplies the syscall-number register. -/
theorem initial_a7_unchanged (s : State) (sp : Nat) (left right : BitVec 32)
    (saved1 saved2 : BitVec 64) :
    (initialState s sp left right saved1 saved2).regs.get? Register.x17 = s.regs.get? Register.x17 := by
  simp [initialState, clockProfileState, clockState, witnessProfile, stepProfileState,
    setRegister, Std.ExtDHashMap.get?_insert]

/-- The extra readiness instruction/tick never alters the body's saved RAM. -/
theorem ready_memory (s : State) (image : Bytes) (sp : Nat)
    (saved1 saved2 result c t : BitVec 64) :
    (readyState s image sp saved1 saved2 result c t).mem =
      (returnedState s image sp saved1 saved2 result).mem := rfl

/-- In particular SP, x9/x18 and all unlisted registers retain their original
maps. The explicitly loaded PMA regions and derived x1 are listed exceptions. -/
theorem ready_register_other (s : State) (image : Bytes) (sp : Nat)
    (saved1 saved2 result c t : BitVec 64) (r : Register)
    (h17 : Register.x17 ≠ r) (h10 : Register.x10 ≠ r) (h1 : Register.x1 ≠ r)
    (hpc : Register.PC ≠ r) (hn : Register.nextPC ≠ r)
    (hi : Register.minstret_increment ≠ r) (hc : Register.mcycle ≠ r)
    (ht : Register.mtime ≠ r) (hpma : Register.pma_regions ≠ r) :
    (readyState s image sp saved1 saved2 result c t).regs.get? r = s.regs.get? r := by
  unfold readyState
  rw [clockState_lookup_other _ _ _ r hc ht]
  unfold controlState
  rw [lookup_set_other _ _ _ _ hi, lookup_set_other _ _ _ _ hn,
    lookup_set_other _ _ _ _ hpc, lookup_set_other _ _ _ _ h17]
  unfold returnedState
  rw [stepped_register_other _ _ _ _ _ _ r h10 hn hpc hi]
  unfold bodyEntryState
  rw [called_register_other _ _ r h1 hpc hn hi]
  exact loaded_register_other s image sp r (Ne.symm hpma)

theorem ready_nonregister_state (s : State) (image : Bytes) (sp : Nat)
    (saved1 saved2 result c t : BitVec 64) :
    (readyState s image sp saved1 saved2 result c t).cycleCount = s.cycleCount ∧
    (readyState s image sp saved1 saved2 result c t).sailOutput = s.sailOutput ∧
    (readyState s image sp saved1 saved2 result c t).choiceState = s.choiceState ∧
    (readyState s image sp saved1 saved2 result c t).tags = s.tags := by
  simpa only [readyState, returnedState, bodyEntryState, calledState,
    finalSteppedState, finalFrameState, frameSavedMemory, store64, setByte,
    clockState, controlState, setRegister] using loaded_nonregister_state s image sp

/-- RV64's existing u32 ABI representation sign-extends the final 32 bits.
This is not equality of the 64-bit register with the raw natural u32 value. -/
theorem high_bit_result_representation :
    Oak.RiscV.widen 32 false (0x80000000#32) = (0xffffffff80000000#64) ∧
    Oak.RiscV.widen 32 false (0xffffffff#32) = (0xffffffffffffffff#64) := by decide +kernel

/-- The sixth tick's strict deadline cannot be weakened to equality. -/
theorem sixth_tick_at_deadline (s : State) (c : BitVec 64)
    (hp : StepProfile s) (hk : ClockProfile s c (5#64) (6#64)) :
    (tick_clock ()).run s = .ok ()
      (setRegister (clockState s (c+1#64) (6#64)) Register.mip (128#64)) ∧
    (tick_clock ()).run s ≠ .ok () (clockState s (c+1#64) (6#64)) := by
  exact ⟨tick_clock_at_deadline s c (5#64) (6#64) hp hk (by decide),
    tick_clock_at_deadline_not_below s c (5#64) (6#64) hp hk (by decide)⟩

end OakSailExitChecks
