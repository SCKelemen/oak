import OakSailSteppedState

/-! The actual generated execute dispatcher on all nine framed instruction
bodies. Every memory read below is obtained from the two prior concrete stores. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailSteppedBody
open LeanRV64D LeanRV64D.Functions
open OakSailBridge.BitwiseDecoded
open OakSailComposition (sailOp)
open OakSailFramedComposition (FrameAccess execute_bitwise_run)
open OakSailSteppedState
open Oak.BitwiseFunction (Op)
attribute [local irreducible] store64

private theorem control_set (s : State) (pc next : BitVec 64)
    (r : Register) (v : RegisterType r)
    (hp : Register.PC ≠ r) (hn : Register.nextPC ≠ r)
    (hi : Register.minstret_increment ≠ r) :
    setRegister (controlState s pc next) r v =
      controlState (setRegister s r v) pc next := by
  unfold controlState
  rw [setRegister_comm _ Register.minstret_increment r false v hi,
    setRegister_comm _ Register.nextPC r next v hn,
    setRegister_comm _ Register.PC r pc v hp]

private theorem control_store (s : State) (pc next value : BitVec 64) (addr : Nat) :
    store64 (controlState s pc next) addr value =
      controlState (store64 s addr value) pc next := by
  simp only [controlState, store64_setRegister]

private theorem control_next (s : State) (pc next target : BitVec 64) :
    setRegister (controlState s pc next) Register.nextPC target =
      controlState (setRegister s Register.nextPC target) pc target := by
  unfold controlState
  rw [setRegister_comm _ Register.minstret_increment Register.nextPC false target (by decide),
    setRegister_same,
    setRegister_comm s Register.nextPC Register.PC target pc (by decide),
    setRegister_same]

private theorem control_memory (s : State) (pc next : BitVec 64)
    (regions : List PMA_Region) (h : MemoryConfig s regions) :
    MemoryConfig (controlState s pc next) regions := by
  rcases h with ⟨hp, hm, hmask, hr, ht, hc, ha⟩
  constructor <;> simpa [controlState, setRegister, Std.ExtDHashMap.get?_insert] using ‹_›

private theorem control_config (s : State) (pc next : BitVec 64)
    (h : ConfigOK s) : ConfigOK (controlState s pc next) := by
  simpa [controlState, ConfigOK, setRegister, Std.ExtDHashMap.get?_insert] using h

/-- Each generated body executes at any already prepared PC/nextPC. The last
body derives its return target from x1 and the actual JALR semantics. -/
theorem frame_body_execute (op : Op) (s : State)
    (sp saved1 saved2 left right ra pc next : BitVec 64)
    (regions : List PMA_Region) (first second : PMA_Region)
    (hc : MemoryConfig s regions) (hcfg : ConfigOK s)
    (ha : FrameAccess regions sp first second)
    (hsp : s.regs.get? Register.x2 = some sp)
    (h1 : s.regs.get? Register.x9 = some saved1)
    (h2 : s.regs.get? Register.x18 = some saved2)
    (hl : s.regs.get? Register.x10 = some left)
    (hr : s.regs.get? Register.x11 = some right)
    (hra : s.regs.get? Register.x1 = some ra)
    (halign : ReturnAligned ra) (i : Fin 9) :
    (execute (frameInst op i)).run
        (controlState (bodyStage s sp saved1 saved2 left right ra op i.val) pc next) =
      .ok RETIRE_SUCCESS
        (controlState (bodyStage s sp saved1 saved2 left right ra op (i.val + 1)) pc
          (if i.val < 8 then next else Sail.BitVec.update ra 0 0#1)) := by
  let base := sp - (96#64)
  let result := Oak.RiscVBitwiseFunction.eval64 op left right
  let s1 := setRegister s Register.x2 base
  let s2 := store64 s1 base.toNat saved1
  let s3 := store64 s2 (base + (8#64)).toNat saved2
  let s4 := setRegister s3 Register.x18 right
  let s5 := setRegister s4 Register.x10 result
  let s6 := setRegister s5 Register.x9 saved1
  let s7 := setRegister s6 Register.x18 saved2
  let s8 := setRegister s7 Register.x2 sp
  have cm1 : MemoryConfig s1 regions := memoryConfig_set _ _ _ _ (by simp [FrameRegister]) hc
  have cm2 : MemoryConfig s2 regions := memoryConfig_store64 _ _ _ _ cm1
  have cm3 : MemoryConfig s3 regions := memoryConfig_store64 _ _ _ _ cm2
  have cm4 : MemoryConfig s4 regions := memoryConfig_set _ _ _ _ (by simp [FrameRegister]) cm3
  have cm5 : MemoryConfig s5 regions := memoryConfig_set _ _ _ _ (by simp [FrameRegister]) cm4
  have cm6 : MemoryConfig s6 regions := memoryConfig_set _ _ _ _ (by simp [FrameRegister]) cm5
  have sp1 : s1.regs.get? Register.x2 = some base := lookup_set_same _ _ _
  have sp2 : s2.regs.get? Register.x2 = some base := by simpa only [s2, store64_regs] using sp1
  have sp5 : s5.regs.get? Register.x2 = some base := by
    simpa [s5, s4, s3, setRegister, Std.ExtDHashMap.get?_insert] using sp2
  have sp6 : s6.regs.get? Register.x2 = some base := by
    simpa [s6, setRegister, Std.ExtDHashMap.get?_insert] using sp5
  have sp7 : s7.regs.get? Register.x2 = some base := by
    simpa [s7, setRegister, Std.ExtDHashMap.get?_insert] using sp6
  have hzero : (0 : BitVec 12).signExtend 64 = (0#64) := rfl
  have height : (8 : BitVec 12).signExtend 64 = (8#64) := rfl
  have halloc : sp + (0xfa0 : BitVec 12).signExtend 64 = base := by
    change sp + (-(96#64)) = sp - (96#64)
    exact (_root_.BitVec.sub_eq_add_neg sp 96).symm
  have hrelease : base + (96 : BitVec 12).signExtend 64 = sp := by
    change (sp - (96#64)) + 96 = sp
    exact _root_.BitVec.sub_add_cancel sp 96
  have e1 := execute_sp_add_run (controlState s pc next) sp 0xfa0
    (by simpa [controlState, setRegister, Std.ExtDHashMap.get?_insert] using hsp)
  rw [halloc, control_set _ _ _ _ _ (by decide) (by decide) (by decide)] at e1
  have e2 := execute_save_x9_run (controlState s1 pc next) base saved1 0 regions first
    (control_memory s1 pc next regions cm1)
    (by simpa [controlState, setRegister, Std.ExtDHashMap.get?_insert] using sp1)
    (by simpa [controlState, s1, setRegister, Std.ExtDHashMap.get?_insert] using h1)
    (by simpa only [hzero, _root_.BitVec.add_zero, base] using ha.first)
    (by simpa only [hzero, _root_.BitVec.add_zero, base] using ha.lowFirst)
  simp only [hzero, _root_.BitVec.add_zero, control_store] at e2
  have e3 := execute_save_x18_run (controlState s2 pc next) base saved2 8 regions second
    (control_memory s2 pc next regions cm2)
    (by simpa [controlState, setRegister, Std.ExtDHashMap.get?_insert] using sp2)
    (by simpa [controlState, s2, s1, setRegister, Std.ExtDHashMap.get?_insert] using h2)
    (by simpa only [height, base] using ha.second)
    (by simpa only [height, base] using ha.lowSecond)
  simp only [height, control_store] at e3
  have e4 := execute_copy_right_run (controlState s3 pc next) right
    (by simpa [controlState, s3, s2, s1, setRegister, Std.ExtDHashMap.get?_insert] using hr)
  rw [control_set _ _ _ _ _ (by decide) (by decide) (by decide)] at e4
  have e5 := execute_bitwise_run op (controlState s4 pc next) left right
    (by simpa [controlState, s4, s3, s2, s1, setRegister, Std.ExtDHashMap.get?_insert] using hl)
    (by simpa [controlState, s4, s3, s2, s1, setRegister, Std.ExtDHashMap.get?_insert] using hr)
  rw [control_set _ _ _ _ _ (by decide) (by decide) (by decide)] at e5
  have e6 := execute_restore_x9_run (controlState s5 pc next) base saved1 0 regions first
    (control_memory s5 pc next regions cm5)
    (by simpa [controlState, setRegister, Std.ExtDHashMap.get?_insert] using sp5)
    (by simpa only [hzero, _root_.BitVec.add_zero, base] using ha.first)
    (by simpa only [hzero, _root_.BitVec.add_zero, base] using ha.lowFirst)
    (by simpa only [hzero, _root_.BitVec.add_zero, controlState, s5, s4, s3, s2,
      setRegister, frameSavedMemory] using (frameSavedMemory_first_byte s1 base saved1 saved2))
  rw [control_set _ _ _ _ _ (by decide) (by decide) (by decide)] at e6
  have e7 := execute_restore_x18_run (controlState s6 pc next) base saved2 8 regions second
    (control_memory s6 pc next regions cm6)
    (by simpa [controlState, setRegister, Std.ExtDHashMap.get?_insert] using sp6)
    (by simpa only [height, base] using ha.second)
    (by simpa only [height, base] using ha.lowSecond)
    (by simpa only [height, controlState, s6, s5, s4, s3, s2, setRegister,
      frameSavedMemory] using (frameSavedMemory_second_byte s1 base saved1 saved2))
  rw [control_set _ _ _ _ _ (by decide) (by decide) (by decide)] at e7
  have e8 := execute_sp_add_run (controlState s7 pc next) base 96
    (by simpa [controlState, setRegister, Std.ExtDHashMap.get?_insert] using sp7)
  rw [hrelease, control_set _ _ _ _ _ (by decide) (by decide) (by decide)] at e8
  have e9 := execute_ret_run (controlState s8 pc next) ra next
    (control_config s8 pc next (by
      simpa [s8, s7, s6, s5, s4, s3, s2, s1, ConfigOK, setRegister,
        Std.ExtDHashMap.get?_insert] using hcfg))
    (by simpa [controlState, s8, s7, s6, s5, s4, s3, s2, s1, setRegister,
      Std.ExtDHashMap.get?_insert] using hra)
    (by simp [controlState, setRegister, Std.ExtDHashMap.get?_insert]) halign
  rw [control_next] at e9
  have hi := i.isLt
  have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨
      i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 := by omega
  rcases cases with hi | hi | hi | hi | hi | hi | hi | hi | hi
  · simpa only [frameInst, hi, framedInstructions, List.getElem_cons_zero, bodyStage,
      Nat.reduceAdd, Nat.reduceLT, if_true] using e1
  · simpa only [frameInst, hi, framedInstructions, List.getElem_cons_succ,
      List.getElem_cons_zero, bodyStage, Nat.reduceAdd, Nat.reduceLT, if_true] using e2
  · simpa only [frameInst, hi, framedInstructions, List.getElem_cons_succ,
      List.getElem_cons_zero, bodyStage, Nat.reduceAdd, Nat.reduceLT, if_true] using e3
  · simpa only [frameInst, hi, framedInstructions, List.getElem_cons_succ,
      List.getElem_cons_zero, bodyStage, Nat.reduceAdd, Nat.reduceLT, if_true] using e4
  · simpa only [frameInst, hi, framedInstructions, List.getElem_cons_succ,
      List.getElem_cons_zero, bodyStage, Nat.reduceAdd, Nat.reduceLT, if_true] using e5
  · simpa only [frameInst, hi, framedInstructions, List.getElem_cons_succ,
      List.getElem_cons_zero, bodyStage, Nat.reduceAdd, Nat.reduceLT, if_true] using e6
  · simpa only [frameInst, hi, framedInstructions, List.getElem_cons_succ,
      List.getElem_cons_zero, bodyStage, Nat.reduceAdd, Nat.reduceLT, if_true] using e7
  · simpa only [frameInst, hi, framedInstructions, List.getElem_cons_succ,
      List.getElem_cons_zero, bodyStage, Nat.reduceAdd, Nat.reduceLT, if_true] using e8
  · simpa only [frameInst, hi, framedInstructions, List.getElem_cons_succ,
      List.getElem_cons_zero, bodyStage, Nat.reduceAdd, Nat.reduceLT, if_false] using e9

/-- Bodies in the stepped frame consume the generated sequential nextPC;
only the actual return body replaces it with the aligned x1 target. -/
theorem frame_body_step (op : Op) (s : State)
    (sp saved1 saved2 left right ra code : BitVec 64)
    (regions : List PMA_Region) (first second : PMA_Region)
    (hc : MemoryConfig s regions) (hcfg : ConfigOK s)
    (ha : FrameAccess regions sp first second)
    (hsp : s.regs.get? Register.x2 = some sp)
    (h1 : s.regs.get? Register.x9 = some saved1)
    (h2 : s.regs.get? Register.x18 = some saved2)
    (hl : s.regs.get? Register.x10 = some left)
    (hr : s.regs.get? Register.x11 = some right)
    (hra : s.regs.get? Register.x1 = some ra)
    (halign : ReturnAligned ra) (i : Fin 9) :
    (execute (frameInst op i)).run
        (controlState (bodyStage s sp saved1 saved2 left right ra op i.val)
          (code + BitVec.ofNat 64 (4 * i.val))
          (code + BitVec.ofNat 64 (4 * (i.val + 1)))) =
      .ok RETIRE_SUCCESS
        (controlState (bodyStage s sp saved1 saved2 left right ra op (i.val + 1))
          (code + BitVec.ofNat 64 (4 * i.val)) (progressionPC code ra (i.val + 1))) := by
  have h := frame_body_execute op s sp saved1 saved2 left right ra
    (code + BitVec.ofNat 64 (4 * i.val))
    (code + BitVec.ofNat 64 (4 * (i.val + 1))) regions first second
    hc hcfg ha hsp h1 h2 hl hr hra halign i
  simpa only [progressionPC, show (i.val + 1 < 9) = (i.val < 8) by apply propext; omega] using h

end OakSailSteppedBody
