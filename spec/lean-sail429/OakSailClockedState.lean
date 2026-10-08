import OakSailClockTick
import OakSailSteppedFrame

/-! State commutations for interleaving the generated clock callback with the
actual frame body. These equalities describe state; they do not replace either
generated operation with a projected implementation. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailClockedState
open LeanRV64D LeanRV64D.Functions
open OakSailBridge.BitwiseDecoded
open OakSailFetchedCode OakSailFetchedFrame OakSailSteppedState OakSailSteppedFrame
open OakSailClockTick
open Oak.BitwiseFunction (Op)
attribute [local irreducible] store64

theorem set_clockState (s : State) (c t : BitVec 64)
    (r : Register) (v : RegisterType r)
    (hc : Register.mcycle ≠ r) (ht : Register.mtime ≠ r) :
    setRegister (clockState s c t) r v = clockState (setRegister s r v) c t := by
  unfold clockState
  rw [setRegister_comm _ Register.mtime r t v ht,
    setRegister_comm _ Register.mcycle r c v hc]

theorem store_clockState (s : State) (c t : BitVec 64) (addr : Nat) (value : BitVec 64) :
    store64 (clockState s c t) addr value = clockState (store64 s addr value) c t := by
  simp only [clockState, store64_setRegister]

theorem control_clockState (s : State) (c t pc next : BitVec 64) :
    controlState (clockState s c t) pc next = clockState (controlState s pc next) c t := by
  unfold controlState
  rw [set_clockState _ _ _ Register.PC _ (by decide) (by decide),
    set_clockState _ _ _ Register.nextPC _ (by decide) (by decide),
    set_clockState _ _ _ Register.minstret_increment _ (by decide) (by decide)]

theorem body_clockState (s : State) (sp saved1 saved2 left right ra c t : BitVec 64)
    (op : Op) (n : Fin 10) :
    bodyStage (clockState s c t) sp saved1 saved2 left right ra op n.val =
      clockState (bodyStage s sp saved1 saved2 left right ra op n.val) c t := by
  have hn := n.isLt
  have cases : n.val = 0 ∨ n.val = 1 ∨ n.val = 2 ∨ n.val = 3 ∨ n.val = 4 ∨
      n.val = 5 ∨ n.val = 6 ∨ n.val = 7 ∨ n.val = 8 ∨ n.val = 9 := by omega
  rcases cases with hn|hn|hn|hn|hn|hn|hn|hn|hn|hn <;> simp only [hn, bodyStage]
  all_goals simp only [store_clockState,
    set_clockState _ _ _ Register.x2 _ (by decide) (by decide),
    set_clockState _ _ _ Register.x9 _ (by decide) (by decide),
    set_clockState _ _ _ Register.x18 _ (by decide) (by decide),
    set_clockState _ _ _ Register.x10 _ (by decide) (by decide),
    set_clockState _ _ _ Register.nextPC _ (by decide) (by decide)]

theorem finalFrame_clockState (s : State) (base saved1 saved2 result target c t : BitVec 64) :
    finalFrameState (clockState s c t) base saved1 saved2 result target =
      clockState (finalFrameState s base saved1 saved2 result target) c t := by
  simp only [finalFrameState, frameSavedMemory, store_clockState,
    set_clockState _ _ _ Register.x10 _ (by decide) (by decide),
    set_clockState _ _ _ Register.nextPC _ (by decide) (by decide)]

theorem finalStepped_clockState (s : State) (sp saved1 saved2 result ra c t : BitVec 64) :
    finalSteppedState (clockState s c t) sp saved1 saved2 result ra =
      clockState (finalSteppedState s sp saved1 saved2 result ra) c t := by
  simp only [finalSteppedState, finalFrame_clockState, control_clockState]

/-- The clock changes exactly its two mapped counters. -/
theorem clockState_counters (s : State) (c t : BitVec 64) :
    (clockState s c t).regs.get? Register.mcycle = some c ∧
    (clockState s c t).regs.get? Register.mtime = some t := by
  simp [clockState, setRegister, Std.ExtDHashMap.get?_insert]

theorem clocked_register_other (s : State) (sp saved1 saved2 result ra c t : BitVec 64)
    (r : Register) (hx : Register.x10 ≠ r) (hn : Register.nextPC ≠ r)
    (hp : Register.PC ≠ r) (hi : Register.minstret_increment ≠ r)
    (hc : Register.mcycle ≠ r) (ht : Register.mtime ≠ r) :
    (clockState (finalSteppedState s sp saved1 saved2 result ra) c t).regs.get? r =
      s.regs.get? r := by
  rw [clockState_lookup_other _ _ _ r hc ht,
    stepped_register_other _ _ _ _ _ _ r hx hn hp hi]

theorem clocked_result (s : State) (sp saved1 saved2 result ra c t : BitVec 64) :
    (clockState (finalSteppedState s sp saved1 saved2 result ra) c t).regs.get? Register.x10 =
      some result := by
  rw [clockState_lookup_other _ _ _ Register.x10 (by decide) (by decide)]
  simp [finalSteppedState, controlState, setRegister, Std.ExtDHashMap.get?_insert,
    finalFrameState, frameSavedMemory_regs]

theorem clocked_pc_and_next (s : State) (sp saved1 saved2 result ra c t : BitVec 64) :
    (clockState (finalSteppedState s sp saved1 saved2 result ra) c t).regs.get? Register.PC =
      some (Sail.BitVec.update ra 0 0#1) ∧
    (clockState (finalSteppedState s sp saved1 saved2 result ra) c t).regs.get? Register.nextPC =
      some (Sail.BitVec.update ra 0 0#1) ∧
    (clockState (finalSteppedState s sp saved1 saved2 result ra) c t).regs.get?
      Register.minstret_increment = some false := by
  simpa only [clockState_lookup_other _ _ _ Register.PC (by decide) (by decide),
    clockState_lookup_other _ _ _ Register.nextPC (by decide) (by decide),
    clockState_lookup_other _ _ _ Register.minstret_increment (by decide) (by decide)] using
    stepped_pc_and_next s sp saved1 saved2 result ra

theorem clocked_memory_other (s : State) (sp saved1 saved2 result ra c t : BitVec 64)
    (query : Nat)
    (h1 : query < (sp-96#64).toNat ∨ (sp-96#64).toNat+8 ≤ query)
    (h2 : query < (sp-96#64+8#64).toNat ∨ (sp-96#64+8#64).toNat+8 ≤ query) :
    (clockState (finalSteppedState s sp saved1 saved2 result ra) c t).mem.get? query =
      s.mem.get? query :=
  stepped_memory_other s sp saved1 saved2 result ra query h1 h2

/-- The platform counters are register-map fields, separate from cycleCount. -/
theorem clocked_nonregister_state (s : State) (sp saved1 saved2 result ra c t : BitVec 64) :
    (clockState (finalSteppedState s sp saved1 saved2 result ra) c t).cycleCount = s.cycleCount ∧
    (clockState (finalSteppedState s sp saved1 saved2 result ra) c t).sailOutput = s.sailOutput ∧
    (clockState (finalSteppedState s sp saved1 saved2 result ra) c t).choiceState = s.choiceState ∧
    (clockState (finalSteppedState s sp saved1 saved2 result ra) c t).tags = s.tags :=
  stepped_nonregister_state s sp saved1 saved2 result ra

end OakSailClockedState
