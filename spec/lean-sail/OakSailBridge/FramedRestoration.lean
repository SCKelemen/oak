import OakSailBridge.FramedState

/-! Exact state cleanup after the generated frame restores its saved
registers. The saved stack bytes remain observable in the final memory. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000
noncomputable section
namespace OakSailBridge.BitwiseDecoded
open LeanRV64D Sail Sail.ConcurrencyInterfaceV1

-- Use the already checked projection/effect lemmas instead of repeatedly
-- expanding sixteen nested state-record updates during elaboration.
attribute [local irreducible] store64

def frameSavedMemory (s : State) (base saved1 saved2 : BitVec 64) : State :=
  store64 (store64 s base.toNat saved1) (base + (8#64)).toNat saved2

def finalFrameState (s : State) (base saved1 saved2 result target : BitVec 64) : State :=
  setRegister (setRegister (frameSavedMemory s base saved1 saved2)
    Register.x10 result) Register.nextPC target

/-- The nine effects in execution order, including both temporary register
writes and all three register restorations. -/
def stagedFrameState (s : State) (base originalSP saved1 saved2 right result target : BitVec 64) : State :=
  let s1 := setRegister s Register.x2 base
  let s2 := store64 s1 base.toNat saved1
  let s3 := store64 s2 (base + (8#64)).toNat saved2
  let s4 := setRegister s3 Register.x18 right
  let s5 := setRegister s4 Register.x10 result
  let s6 := setRegister s5 Register.x9 saved1
  let s7 := setRegister s6 Register.x18 saved2
  let s8 := setRegister s7 Register.x2 originalSP
  setRegister s8 Register.nextPC target

@[simp] theorem frameSavedMemory_regs (s : State) (base saved1 saved2 : BitVec 64) :
    (frameSavedMemory s base saved1 saved2).regs = s.regs := by
  simp only [frameSavedMemory, store64_regs]

theorem stagedFrameState_eq_finalFrameState (s : State)
    (base originalSP saved1 saved2 right result target : BitVec 64)
    (hsp : s.regs.get? Register.x2 = some originalSP)
    (h1 : s.regs.get? Register.x9 = some saved1)
    (h2 : s.regs.get? Register.x18 = some saved2) :
    stagedFrameState s base originalSP saved1 saved2 right result target =
      finalFrameState s base saved1 saved2 result target := by
  unfold stagedFrameState finalFrameState
  dsimp only
  rw [store64_setRegister s base.toNat saved1 Register.x2 base]
  rw [store64_setRegister (store64 s base.toNat saved1)
    (base + (8#64)).toNat saved2 Register.x2 base]
  rw [setRegister_comm _ Register.x10 Register.x9 result saved1 (by decide)]
  rw [setRegister_comm _ Register.x18 Register.x9 right saved1 (by decide)]
  rw [setRegister_comm _ Register.x2 Register.x9 base saved1 (by decide)]
  rw [setRegister_self (store64 (store64 s base.toNat saved1) (base + (8#64)).toNat saved2)
    Register.x9 saved1 (by simpa only [store64_regs] using h1)]
  rw [setRegister_comm _ Register.x10 Register.x18 result saved2 (by decide)]
  rw [setRegister_same]
  rw [setRegister_comm _ Register.x2 Register.x18 base saved2 (by decide)]
  rw [setRegister_self (store64 (store64 s base.toNat saved1) (base + (8#64)).toNat saved2)
    Register.x18 saved2 (by simpa only [store64_regs] using h2)]
  rw [setRegister_comm _ Register.x10 Register.x2 result originalSP (by decide)]
  rw [setRegister_same]
  rw [setRegister_self (store64 (store64 s base.toNat saved1) (base + (8#64)).toNat saved2)
    Register.x2 originalSP (by simpa only [store64_regs] using hsp)]
  rfl

@[simp] theorem finalFrameState_result (s : State) (base saved1 saved2 result target : BitVec 64) :
    (finalFrameState s base saved1 saved2 result target).regs.get? Register.x10 = some result := by
  unfold finalFrameState
  rw [lookup_set_other _ _ _ _ (by decide), lookup_set_same]

@[simp] theorem finalFrameState_target (s : State) (base saved1 saved2 result target : BitVec 64) :
    (finalFrameState s base saved1 saved2 result target).regs.get? Register.nextPC = some target := by
  exact lookup_set_same _ _ _

theorem finalFrameState_register_other (s : State) (base saved1 saved2 result target : BitVec 64)
    (r : Register) (hresult : Register.x10 ≠ r) (htarget : Register.nextPC ≠ r) :
    (finalFrameState s base saved1 saved2 result target).regs.get? r = s.regs.get? r := by
  unfold finalFrameState
  rw [lookup_set_other _ _ _ _ htarget, lookup_set_other _ _ _ _ hresult]
  rw [frameSavedMemory_regs]

@[simp] theorem finalFrameState_mem (s : State) (base saved1 saved2 result target : BitVec 64) :
    (finalFrameState s base saved1 saved2 result target).mem =
      (frameSavedMemory s base saved1 saved2).mem := rfl

theorem frameSavedMemory_other (s : State) (base saved1 saved2 : BitVec 64) (query : Nat)
    (h1 : query < base.toNat ∨ base.toNat + 8 ≤ query)
    (h2 : query < (base + (8#64)).toNat ∨ (base + (8#64)).toNat + 8 ≤ query) :
    (frameSavedMemory s base saved1 saved2).mem.get? query = s.mem.get? query := by
  unfold frameSavedMemory
  rw [lookup_store64_other _ _ _ _ h2, lookup_store64_other _ _ _ _ h1]

theorem frame_slots_disjoint (base : BitVec 64) :
    base.toNat + 8 ≤ (base + (8#64)).toNat ∨
      (base + (8#64)).toNat + 8 ≤ base.toNat := by
  have hb := base.isLt
  simp [_root_.BitVec.toNat_add]
  omega

theorem frameSavedMemory_first_byte (s : State) (base saved1 saved2 : BitVec 64)
    (i : Fin 8) :
    (frameSavedMemory s base saved1 saved2).mem.get? (base.toNat + i.val) =
      some (saved1.extractLsb' (8 * i.val) 8) := by
  apply store64_preserves_disjoint_bytes
  · exact frame_slots_disjoint base
  · exact lookup_store64_byte s base.toNat saved1

theorem frameSavedMemory_second_byte (s : State) (base saved1 saved2 : BitVec 64)
    (i : Fin 8) :
    (frameSavedMemory s base saved1 saved2).mem.get? ((base + (8#64)).toNat + i.val) =
      some (saved2.extractLsb' (8 * i.val) 8) := by
  exact lookup_store64_byte _ _ _ i

theorem memoryConfig_frameSavedMemory (s : State) (regions : List PMA_Region)
    (base saved1 saved2 : BitVec 64) (hc : MemoryConfig s regions) :
    MemoryConfig (frameSavedMemory s base saved1 saved2) regions := by
  exact memoryConfig_store64 _ _ _ _ (memoryConfig_store64 s regions _ _ hc)

theorem memoryConfig_finalFrameState (s : State) (regions : List PMA_Region)
    (base saved1 saved2 result target : BitVec 64) (hc : MemoryConfig s regions) :
    MemoryConfig (finalFrameState s base saved1 saved2 result target) regions := by
  apply memoryConfig_set _ regions Register.nextPC target (by simp [FrameRegister])
  apply memoryConfig_set _ regions Register.x10 result (by simp [FrameRegister])
  exact memoryConfig_frameSavedMemory s regions base saved1 saved2 hc

theorem config_finalFrameState (s : State) (base saved1 saved2 result target : BitVec 64)
    (hc : ConfigOK s) : ConfigOK (finalFrameState s base saved1 saved2 result target) := by
  apply config_set_frame _ Register.nextPC target (by simp [FrameRegister])
  apply config_set_frame _ Register.x10 result (by simp [FrameRegister])
  exact config_store64 _ _ _ (config_store64 s _ _ hc)

@[simp] theorem finalFrameState_choiceState (s : State) (base saved1 saved2 result target : BitVec 64) :
    (finalFrameState s base saved1 saved2 result target).choiceState = s.choiceState := by
  simp only [finalFrameState, frameSavedMemory, setRegister, store64_choiceState]

@[simp] theorem finalFrameState_cycleCount (s : State) (base saved1 saved2 result target : BitVec 64) :
    (finalFrameState s base saved1 saved2 result target).cycleCount = s.cycleCount := by
  simp only [finalFrameState, frameSavedMemory, setRegister, store64_cycleCount]

@[simp] theorem finalFrameState_sailOutput (s : State) (base saved1 saved2 result target : BitVec 64) :
    (finalFrameState s base saved1 saved2 result target).sailOutput = s.sailOutput := by
  simp only [finalFrameState, frameSavedMemory, setRegister, store64_sailOutput]

end OakSailBridge.BitwiseDecoded
