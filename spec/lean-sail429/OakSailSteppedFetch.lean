import OakSailSteppedState
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailSteppedFetch
open LeanRV64D LeanRV64D.Functions
open OakSailBridge.BitwiseDecoded
open OakSailFetchedCode OakSailFetchedFrame OakSailSteppedState
open Oak.BitwiseFunction (Op)
attribute [local irreducible] store64

theorem control_memoryConfig (s : State) (pc next : BitVec 64) (regions : List PMA_Region)
    (h : MemoryConfig s regions) : MemoryConfig (controlState s pc next) regions := by
  rcases h with ⟨hp,hm,hmask,hr,ht,hc,ha⟩
  constructor <;> simpa [controlState, setRegister, Std.ExtDHashMap.get?_insert] using ‹_›

theorem control_stepProfile (s : State) (pc next : BitVec 64) (h : StepProfile s) :
    StepProfile (controlState s pc next) := by
  unfold controlState
  repeat first | apply stepProfile_set _ _ _ (by simp [StepWriteRegister, FrameRegister]) | exact h

theorem control_config (s : State) (pc next : BitVec 64) (h : ConfigOK s) :
    ConfigOK (controlState s pc next) := by
  simpa [ConfigOK, controlState, setRegister, Std.ExtDHashMap.get?_insert] using h

theorem control_code (s : State) (code pc next : BitVec 64) (op : Op)
    (h : FrameCodeAt s code op) : FrameCodeAt (controlState s pc next) code op := h

theorem body_memoryConfig (s : State) (sp saved1 saved2 left right ra : BitVec 64)
    (op : Op) (regions : List PMA_Region) (h : MemoryConfig s regions) (n : Fin 10) :
    MemoryConfig (bodyStage s sp saved1 saved2 left right ra op n.val) regions := by
  have hn := n.isLt
  have cases : n.val = 0 ∨ n.val = 1 ∨ n.val = 2 ∨ n.val = 3 ∨ n.val = 4 ∨
      n.val = 5 ∨ n.val = 6 ∨ n.val = 7 ∨ n.val = 8 ∨ n.val = 9 := by omega
  rcases cases with hn|hn|hn|hn|hn|hn|hn|hn|hn|hn <;> simp only [hn, bodyStage]
  all_goals repeat first
    | apply memoryConfig_store64
    | apply memoryConfig_set _ _ _ _ (by simp [FrameRegister])
    | exact h

theorem body_stepProfile (s : State) (sp saved1 saved2 left right ra : BitVec 64)
    (op : Op) (h : StepProfile s) (n : Fin 10) :
    StepProfile (bodyStage s sp saved1 saved2 left right ra op n.val) := by
  have hn := n.isLt
  have cases : n.val = 0 ∨ n.val = 1 ∨ n.val = 2 ∨ n.val = 3 ∨ n.val = 4 ∨
      n.val = 5 ∨ n.val = 6 ∨ n.val = 7 ∨ n.val = 8 ∨ n.val = 9 := by omega
  rcases cases with hn|hn|hn|hn|hn|hn|hn|hn|hn|hn <;> simp only [hn, bodyStage]
  all_goals repeat first
    | apply stepProfile_store64
    | apply stepProfile_set _ _ _ (by simp [StepWriteRegister, FrameRegister])
    | exact h

theorem body_config (s : State) (sp saved1 saved2 left right ra : BitVec 64)
    (op : Op) (h : ConfigOK s) (n : Fin 10) :
    ConfigOK (bodyStage s sp saved1 saved2 left right ra op n.val) := by
  have hn := n.isLt
  have cases : n.val = 0 ∨ n.val = 1 ∨ n.val = 2 ∨ n.val = 3 ∨ n.val = 4 ∨
      n.val = 5 ∨ n.val = 6 ∨ n.val = 7 ∨ n.val = 8 ∨ n.val = 9 := by omega
  rcases cases with hn|hn|hn|hn|hn|hn|hn|hn|hn|hn <;> simp only [hn, bodyStage]
  all_goals repeat first
    | apply config_store64
    | apply config_set_frame _ _ _ (by simp [FrameRegister])
    | exact h

theorem body_code (s : State) (sp saved1 saved2 left right ra code : BitVec 64)
    (op : Op) (h : FrameCodeAt s code op) (sep : CodeStackDisjoint code (sp - 96#64))
    (n : Fin 10) : FrameCodeAt (bodyStage s sp saved1 saved2 left right ra op n.val) code op := by
  have len : (Oak.RiscVFramedBitwise.functionBytes op).length = 36 := by cases op <;> rfl
  have b1 := bytesAt_store64 s code.toNat (sp - 96#64).toNat _ saved1 h.1
    (by simpa only [len] using sep.1)
  have b2 := bytesAt_store64 (store64 s (sp - 96#64).toNat saved1) code.toNat
    (sp - 96#64 + 8#64).toNat _ saved2 b1 (by simpa only [len] using sep.2)
  refine ⟨?_, h.2⟩
  have hn := n.isLt
  have cases : n.val = 0 ∨ n.val = 1 ∨ n.val = 2 ∨ n.val = 3 ∨ n.val = 4 ∨
      n.val = 5 ∨ n.val = 6 ∨ n.val = 7 ∨ n.val = 8 ∨ n.val = 9 := by omega
  rcases cases with hn|hn|hn|hn|hn|hn|hn|hn|hn|hn <;>
    simp only [hn, bodyStage, store64_setRegister]
  all_goals first | exact h.1 | exact b1 | exact b2

/-- Actual external decode of each fetched word. -/
theorem frame_decode (s : State) (op : Op) (i : Fin 9) (h : ConfigOK s) :
    (ext_decode (frameWord op i)).run s = .ok (frameInst op i) s := by
  have hand : Oak.RiscVBitwiseFunction.bodyWord .and = 0x00b57533 := rfl
  have hor : Oak.RiscVBitwiseFunction.bodyWord .or = 0x00b56533 := rfl
  have hxor : Oak.RiscVBitwiseFunction.bodyWord .xor = 0x00b54533 := rfl
  have hi := i.isLt
  have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨
      i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 := by omega
  rcases cases with hi|hi|hi|hi|hi|hi|hi|hi|hi <;> cases op <;>
    simp only [frameWord, frameInst, hi, framedWords, framedInstructions,
      OakSailComposition.sailOp, hand, hor, hxor, List.getElem_cons_zero,
      List.getElem_cons_succ, ext_decode, decode_allocate, decode_save_s1, decode_save_s2,
      decode_copy_right, decode_and, decode_or, decode_xor, decode_restore_s1,
      decode_restore_s2, decode_release_sp, decode_ret] <;>
    exact decoderChecks_run s _ h

end OakSailSteppedFetch
