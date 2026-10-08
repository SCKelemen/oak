import OakSailSteppedFrame
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailSteppedChecks
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1
open OakSailBridge.BitwiseDecoded
open OakSailFetchedCode OakSailSteppedState OakSailSteppedFrame

theorem nonexecutable_fetch_fault (s : State) (addr : BitVec 64)
    (regions : List PMA_Region) (region : PMA_Region)
    (hr : s.regs.get? Register.pma_regions = some regions)
    (hm : matching_pma_region regions (.Physaddr addr) 4 = some region)
    (hx : region.attributes.executable = false) :
    (pmaCheck (.Physaddr addr) 4 (.InstructionFetch ()) .PBMT_PMA false).run s =
      .ok (.Err (.E_Fetch_Access_Fault ())) s := by
  unfold pmaCheck
  simp [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind,
    ExceptT.map, ExceptT.lift, ExceptT.mk, ExceptT.bindCont, liftM, monadLift,
    MonadLift.monadLift, Bind.bind, Functor.map, EStateM.bind, EStateM.map, EStateM.run,
    PreSail.readReg, MonadState.get, getThe, MonadStateOf.get, EStateM.get,
    Pure.pure, EStateM.pure, hr, hm, override_PMA, hx, Functions.not,
    accessFaultFromAccessType, get_config_print_pma, ExceptT.pure]

def witnessRegion : PMA_Region :=
  { base := 0x10000, size := 0x3000,
    attributes := { (default : PMA) with readable := true, writable := true, executable := true },
    include_in_device_tree := false }

/-- The step and physical-memory profiles coexist constructively, rather than
being individually satisfiable but contradictory configuration assumptions. -/
def witnessProfile (s : State) : State :=
  setRegister (setRegister (setRegister (setRegister (setRegister
    (stepProfileState s) Register.mseccfg (0#64)) Register.pma_regions [witnessRegion])
    Register.htif_tohost_base none) Register.pmpcfg_n openPMPConfig) Register.pmpaddr_n openPMPAddress

theorem witness_combined_profile (s : State) :
    StepProfile (witnessProfile s) ∧ MemoryConfig (witnessProfile s) [witnessRegion] ∧
      ConfigOK (witnessProfile s) := by
  have hp := stepProfileState_profile s
  rcases hp with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
  constructor
  · constructor <;> simpa [witnessProfile, setRegister, Std.ExtDHashMap.get?_insert] using ‹_›
  constructor
  · constructor <;> simp [witnessProfile, setRegister, Std.ExtDHashMap.get?_insert, h1, h2] <;> rfl
  · simp [ConfigOK, witnessProfile, setRegister, Std.ExtDHashMap.get?_insert, h1, h3]

theorem witness_frame_access :
    OakSailFramedComposition.FrameAccess [witnessRegion] (0x11000#64) witnessRegion witnessRegion := by
  constructor
  · decide +kernel
  · decide +kernel
  · exact ⟨rfl,rfl,rfl,rfl⟩
  · exact ⟨rfl,rfl,rfl,rfl⟩
  · unfold LowRAM; decide +kernel
  · unfold LowRAM; decide +kernel

theorem witness_executable (i : Fin 9) :
    ExecutableRegion [witnessRegion] (codePC (0x10000#64) i) witnessRegion ∧
      LowCodeRAM (codePC (0x10000#64) i) := by
  have hi := i.isLt
  have cases : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 ∨
    i.val=5 ∨ i.val=6 ∨ i.val=7 ∨ i.val=8 := by omega
  rcases cases with hi|hi|hi|hi|hi|hi|hi|hi|hi <;>
    simp only [codePC, hi]
  all_goals refine ⟨⟨rfl,rfl,rfl⟩, ?_⟩
  all_goals unfold LowCodeRAM; decide +kernel

theorem witness_disjoint : CodeStackDisjoint (0x10000#64) (0x11000#64-96#64) := by
  unfold CodeStackDisjoint
  decide +kernel

theorem changed_body_rejected :
    OakSailFramedComposition.acceptsFrame
      (Oak.BitwiseSource.render (Oak.BitwiseSource.fixture .and)) (Oak.BitwiseSource.fixture .and)
      ((Oak.RiscVFramedBitwise.functionBytes .and).set 16 0x13) = false := by decide +kernel

/-- A changed actual RAM byte cannot satisfy the source-bound code placement,
even when the surrounding memory is otherwise arbitrary. -/
theorem changed_ram_byte_rejected (s : State) (code : BitVec 64) :
    ¬ FrameCodeAt (setByte s (code.toNat+16) (0x13#8)) code .and := by
  intro h
  have b := placed_frame_word (setByte s (code.toNat+16) (0x13#8)) code .and
    ⟨4,by decide⟩ h ⟨0,by decide⟩
  change (setByte s (code.toNat+16) (0x13#8)).mem.get? (code.toNat+16+0) = some (0x33#8) at b
  simp [setByte, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert] at b

theorem changed_source_rejected :
    OakSailFramedComposition.acceptsFrame
      (Oak.BitwiseSource.render (Oak.BitwiseSource.fixture .or)) (Oak.BitwiseSource.fixture .and)
      (Oak.RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel

end OakSailSteppedChecks
