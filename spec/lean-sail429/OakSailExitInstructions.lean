import OakSailEntryChecks

/-! Actual post-return ADDI followed by a fetched/decoded ECALL boundary.
ECALL is not executed, and no external system call handling is assumed. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailExitInstructions
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1
open OakSailBridge.BitwiseDecoded OakSailFetchedCode OakSailFetchedFrame
open OakSailSteppedState OakSailSteppedFetch OakSailSteppedFrame
open OakSailClockTick OakSailClockedState OakSailPlatformCallback OakSailEntryInstructions

def exitBytes : Oak.MinimalELF.Bytes := [0x93,0x08,0xd0,0x05,0x73,0,0,0]

theorem decode_exit_addi : encdec_backwards 0x05d00893 =
    decoderChecks (.ITYPE (93, .Regidx 0, .Regidx 17, .ADDI)) := by
  unfold encdec_backwards decoderChecks
  simp [encdec_reg_backwards, encdec_reg_backwards_matches,
    encdec_cbop_zicbop_backwards_matches, encdec_ntl_backwards_matches,
    encdec_bop_backwards_matches, encdec_iop_backwards, encdec_iop_backwards_matches,
    encdec_uop_backwards_matches, Sail.BitVec.extractLsb, Functions.base_E_enabled,
    Functions.regidx_bit_width, Functions.not]

theorem decode_exit_ecall : encdec_backwards 0x00000073 = decoderChecks (.ECALL ()) := by
  unfold encdec_backwards decoderChecks
  simp [encdec_reg_backwards, encdec_reg_backwards_matches,
    encdec_cbop_zicbop_backwards_matches, encdec_ntl_backwards_matches,
    encdec_bop_backwards_matches, encdec_iop_backwards_matches,
    encdec_uop_backwards_matches, Sail.BitVec.extractLsb, Functions.base_E_enabled,
    Functions.regidx_bit_width, Functions.not]

theorem execute_exit_addi_run (s : State) :
    (execute_ITYPE 93 (.Regidx 0) (.Regidx 17) .ADDI).run s =
      .ok RETIRE_SUCCESS (setRegister s Register.x17 (93#64)) := by rfl

theorem x17_memoryConfig (s : State) (v : BitVec 64) (regions : List PMA_Region)
    (h : MemoryConfig s regions) : MemoryConfig (setRegister s .x17 v) regions := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  constructor <;> simpa [setRegister, Std.ExtDHashMap.get?_insert] using ‹_›

theorem x17_config (s : State) (v : BitVec 64) (h : ConfigOK s) :
    ConfigOK (setRegister s .x17 v) := by
  simpa [ConfigOK, setRegister, Std.ExtDHashMap.get?_insert] using h

theorem x17_stepProfile (s : State) (v : BitVec 64) (h : StepProfile s) :
    StepProfile (setRegister s .x17 v) := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
  constructor <;> simpa [setRegister, Std.ExtDHashMap.get?_insert] using ‹_›

theorem x17_clockProfile (s : State) (v c t d : BitVec 64) (h : ClockProfile s c t d) :
    ClockProfile (setRegister s .x17 v) c t d := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6⟩
  constructor <;> simpa [setRegister, Std.ExtDHashMap.get?_insert] using ‹_›

theorem control_x17 (s : State) (pc next v : BitVec 64) :
    setRegister (controlState s pc next) .x17 v = controlState (setRegister s .x17 v) pc next := by
  unfold controlState
  rw [setRegister_comm _ .minstret_increment .x17 false v (by decide),
    setRegister_comm _ .nextPC .x17 next v (by decide),
    setRegister_comm _ .PC .x17 pc v (by decide)]

/-- The actual generated ADDI step; it writes no other data register or RAM. -/
theorem exit_addi_step (s : State) (pc : BitVec 64) (step : Nat)
    (regions : List PMA_Region) (region : PMA_Region)
    (hc : MemoryConfig s regions) (hcfg : ConfigOK s) (hp : StepProfile s)
    (halign : pc.toNat % 4 = 0)
    (hbytes : ∀ i : Fin 4, s.mem.get? (pc.toNat + i.val) =
      some ((0x05d00893#32).extractLsb' (8 * i.val) 8))
    (hexec : ExecutableRegion regions pc region) (hlow : LowCodeRAM pc) :
    (try_step step true).run (controlState s pc pc) =
      .ok false (controlState (setRegister s .x17 (93#64)) (pc+4#64) (pc+4#64)) := by
  apply word_step s (setRegister s .x17 (93#64)) pc (pc+4#64) 0x05d00893
    (.ITYPE (93,.Regidx 0,.Regidx 17,.ADDI)) step regions region hc hcfg hp
    (x17_stepProfile s _ hp) halign hbytes hexec hlow (by decide +kernel) decode_exit_addi
  simpa only [control_x17] using execute_exit_addi_run (controlState s pc (pc+4#64))

end OakSailExitInstructions
