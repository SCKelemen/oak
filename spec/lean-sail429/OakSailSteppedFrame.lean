import OakSailSteppedFetch
import OakSailSteppedBody
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailSteppedFrame
open LeanRV64D LeanRV64D.Functions
open OakSailBridge.BitwiseDecoded
open OakSailFetchedCode OakSailFetchedFrame OakSailSteppedState OakSailSteppedFetch
open Oak.BitwiseFunction (Op)
attribute [local irreducible] store64

theorem control_increment (s : State) (pc next : BitVec 64) :
    setRegister (controlState s pc next) Register.minstret_increment false = controlState s pc next := by
  unfold controlState
  rw [setRegister_same]

theorem control_next (s : State) (pc next newNext : BitVec 64) :
    setRegister (controlState s pc next) Register.nextPC newNext = controlState s pc newNext := by
  unfold controlState
  rw [setRegister_comm _ Register.minstret_increment Register.nextPC _ _ (by decide), setRegister_same]

theorem control_pc (s : State) (pc next newPC : BitVec 64) :
    setRegister (controlState s pc next) Register.PC newPC = controlState s newPC next := by
  unfold controlState
  rw [setRegister_comm _ Register.minstret_increment Register.PC _ _ (by decide)]
  rw [setRegister_comm _ Register.nextPC Register.PC _ _ (by decide), setRegister_same]

/-- Compositional actual step rule. The final nine-step theorem supplies the
body transition from the generated dispatcher, not an execution assumption. -/
theorem frame_word_step (s t : State) (code target : BitVec 64) (op : Op) (i : Fin 9)
    (step : Nat) (exitWait : Bool) (regions : List PMA_Region) (region : PMA_Region)
    (hc : MemoryConfig s regions) (hcfg : ConfigOK s) (hp : StepProfile s)
    (ht : StepProfile t) (hcode : FrameCodeAt s code op)
    (hexec : ExecutableRegion regions (codePC code i) region)
    (hlow : LowCodeRAM (codePC code i))
    (hbody : (execute (frameInst op i)).run
      (controlState s (codePC code i) (codePC code i + 4#64)) =
      .ok RETIRE_SUCCESS (controlState t (codePC code i) target)) :
    (try_step step exitWait).run (controlState s (codePC code i) (codePC code i)) =
      .ok false (controlState t target target) := by
  let pc := codePC code i
  let start := controlState s pc pc
  let finish := controlState t pc target
  have hsp : StepProfile start := control_stepProfile s pc pc hp
  have htp : StepProfile finish := control_stepProfile t pc target ht
  have hmem : MemoryConfig start regions := control_memoryConfig s pc pc regions hc
  have hconf : ConfigOK start := control_config s pc pc hcfg
  have hplace : FrameCodeAt start code op := control_code s code pc pc op hcode
  have hf : (fetch ()).run start = .ok (.F_Base (frameWord op i)) start := by
    apply fetch_base_run start pc (frameWord op i) regions region hmem hsp.isa
    · simp [start, controlState, setRegister, Std.ExtDHashMap.get?_insert]
    · exact codePC_aligned code i hcode.2.2 hcode.2.1
    · exact hexec
    · exact hlow
    · exact codePC_bytes start code op i hplace
    · exact frame_word_not_compressed op i
  have he : (execute (frameInst op i)).run (setRegister start Register.nextPC (pc+4#64)) =
      .ok RETIRE_SUCCESS finish := by
    simpa only [start, finish, control_next] using hbody
  have hactive := run_hart_active_success start finish step pc (frameWord op i) (frameInst op i)
    hsp.privilege (by simp [start, controlState, setRegister, Std.ExtDHashMap.get?_insert])
    (hsp.dispatch start) hf (frame_decode start op i hconf) (hsp.landing_pad start) he
  have hrun := try_step_success start finish step exitWait (frameWord op i) target
    hsp.privilege (hsp.counter start) hsp.active
    (by simpa only [start, control_increment] using hactive) htp.active
    (by simp [finish, controlState, setRegister, Std.ExtDHashMap.get?_insert])
    (by simp [finish, controlState, setRegister, Std.ExtDHashMap.get?_insert])
  simpa only [start, finish, control_pc] using hrun

/-- A bounded sequence of actual generated steps, retaining every returned
waiting flag. No tick_clock or outer platform-loop operation is inserted. -/
def steps : Nat → Nat → Bool → SailM (List Bool)
  | 0, _, _ => pure []
  | count + 1, step, exitWait => do
      let flag ← try_step step exitWait
      let rest ← steps count (step + 1) exitWait
      pure (flag :: rest)

theorem steps_of_transitions (count start : Nat) (exitWait : Bool) (states : Nat → State)
    (h : ∀ k, k < count → (try_step (start+k) exitWait).run (states k) =
      .ok false (states (k+1))) :
    (steps count start exitWait).run (states 0) =
      .ok (List.replicate count false) (states count) := by
  induction count generalizing start states with
  | zero => rfl
  | succ count ih =>
      have first := h 0 (by omega)
      simp only [Nat.add_zero] at first
      simp only [steps]
      rw [bind_run_ok _ _ first]
      have tail := ih (start+1) (fun k => states (k+1)) (by
        intro k hk
        simpa only [Nat.add_assoc, Nat.add_comm 1 k] using h (k+1) (by omega))
      rw [bind_run_ok _ _ tail]
      rfl

theorem next_codePC (code : BitVec 64) (i : Fin 9) :
    codePC code i + 4#64 = code + BitVec.ofNat 64 (4*(i.val+1)) := by
  simp [codePC, Nat.mul_add, _root_.BitVec.ofNat_add, _root_.BitVec.add_assoc]

/-- Exact nine-step execution, with all actual fetch, interrupt, decoder,
body, bookkeeping and PC updates derived from explicit configuration facts. -/
theorem nine_steps (op : Op) (s : State)
    (sp saved1 saved2 left right ra code : BitVec 64) (step : Nat) (exitWait : Bool)
    (regions : List PMA_Region) (first second : PMA_Region)
    (codeRegion : Fin 9 → PMA_Region)
    (hc : MemoryConfig s regions) (hcfg : ConfigOK s) (hp : StepProfile s)
    (ha : OakSailFramedComposition.FrameAccess regions sp first second)
    (hsp : s.regs.get? Register.x2 = some sp)
    (h1 : s.regs.get? Register.x9 = some saved1)
    (h2 : s.regs.get? Register.x18 = some saved2)
    (hl : s.regs.get? Register.x10 = some left)
    (hr : s.regs.get? Register.x11 = some right)
    (hra : s.regs.get? Register.x1 = some ra) (halign : ReturnAligned ra)
    (hcode : FrameCodeAt s code op) (hsep : CodeStackDisjoint code (sp-96#64))
    (hexec : ∀ i : Fin 9, ExecutableRegion regions (codePC code i) (codeRegion i))
    (hlow : ∀ i : Fin 9, LowCodeRAM (codePC code i)) :
    (steps 9 step exitWait).run (controlState s code code) =
      .ok (List.replicate 9 false)
        (controlState (finalFrameState s (sp-96#64) saved1 saved2
          (Oak.RiscVBitwiseFunction.eval64 op left right) (Sail.BitVec.update ra 0 0#1))
          (Sail.BitVec.update ra 0 0#1) (Sail.BitVec.update ra 0 0#1)) := by
  let states := fun n => controlState (bodyStage s sp saved1 saved2 left right ra op n)
    (progressionPC code ra n) (progressionPC code ra n)
  have allSteps : ∀ k, k < 9 → (try_step (step+k) exitWait).run (states k) =
      .ok false (states (k+1)) := by
    intro k hk
    let i : Fin 9 := ⟨k,hk⟩
    have hbody := OakSailSteppedBody.frame_body_step op s sp saved1 saved2 left right ra code
      regions first second hc hcfg ha hsp h1 h2 hl hr hra halign i
    have done := frame_word_step (bodyStage s sp saved1 saved2 left right ra op k)
      (bodyStage s sp saved1 saved2 left right ra op (k+1)) code
      (progressionPC code ra (k+1)) op i (step+k) exitWait regions (codeRegion i)
      (body_memoryConfig s sp saved1 saved2 left right ra op regions hc ⟨k,by omega⟩)
      (body_config s sp saved1 saved2 left right ra op hcfg ⟨k,by omega⟩)
      (body_stepProfile s sp saved1 saved2 left right ra op hp ⟨k,by omega⟩)
      (body_stepProfile s sp saved1 saved2 left right ra op hp ⟨k+1,by omega⟩)
      (body_code s sp saved1 saved2 left right ra code op hcode hsep ⟨k,by omega⟩)
      (hexec i) (hlow i) (by rw [next_codePC]; exact hbody)
    simpa only [states, progressionPC, if_pos hk, codePC, i] using done
  have run := steps_of_transitions 9 step exitWait states allSteps
  have final := stagedFrameState_eq_finalFrameState s (sp-96#64) sp saved1 saved2 right
    (Oak.RiscVBitwiseFunction.eval64 op left right) (Sail.BitVec.update ra 0 0#1) hsp h1 h2
  have bodyFinal : bodyStage s sp saved1 saved2 left right ra op 9 =
      finalFrameState s (sp-96#64) saved1 saved2
        (Oak.RiscVBitwiseFunction.eval64 op left right) (Sail.BitVec.update ra 0 0#1) := by
    simpa only [bodyStage, stagedFrameState] using final
  simpa only [states, bodyStage, progressionPC, Nat.zero_lt_succ, if_true,
    Nat.lt_irrefl, if_false, Nat.mul_zero, _root_.BitVec.add_zero,
    ← bodyFinal] using run

def finalSteppedState (s : State) (sp saved1 saved2 result ra : BitVec 64) : State :=
  controlState (finalFrameState s (sp-96#64) saved1 saved2 result (Sail.BitVec.update ra 0 0#1))
    (Sail.BitVec.update ra 0 0#1) (Sail.BitVec.update ra 0 0#1)

theorem control_self (s : State) (pc : BitVec 64)
    (hp : s.regs.get? Register.PC = some pc)
    (hn : s.regs.get? Register.nextPC = some pc)
    (hi : s.regs.get? Register.minstret_increment = some false) :
    controlState s pc pc = s := by
  unfold controlState
  rw [setRegister_self s Register.PC pc hp, setRegister_self s Register.nextPC pc hn,
    setRegister_self s Register.minstret_increment false hi]

/-- All original source bytes and all compiler bytes are checked before the
actual nine generated steps. Initial PC/nextPC and increment-flag mappings are
explicit premises, not a claimed loader or startup operation. -/
theorem accepted_typed_steps {source : List UInt8} {claim : Oak.BitwiseSource.Decl}
    {complete : List (BitVec 8)}
    (accepted : OakSailFramedComposition.acceptsFrame source claim complete = true)
    (left right : BitVec 32) (fuel : Nat) (s : State)
    (sp saved1 saved2 ra code : BitVec 64) (step : Nat) (exitWait : Bool)
    (regions : List PMA_Region) (first second : PMA_Region)
    (codeRegion : Fin 9 → PMA_Region)
    (hc : MemoryConfig s regions) (hcfg : ConfigOK s) (hp : StepProfile s)
    (ha : OakSailFramedComposition.FrameAccess regions sp first second)
    (hsp : s.regs.get? Register.x2 = some sp)
    (h1 : s.regs.get? Register.x9 = some saved1)
    (h2 : s.regs.get? Register.x18 = some saved2)
    (hl : s.regs.get? Register.x10 = some (Oak.RiscV.widen 32 false left))
    (hr : s.regs.get? Register.x11 = some (Oak.RiscV.widen 32 false right))
    (hra : s.regs.get? Register.x1 = some ra) (halign : ReturnAligned ra)
    (hpc : s.regs.get? Register.PC = some code)
    (hn : s.regs.get? Register.nextPC = some code)
    (hi : s.regs.get? Register.minstret_increment = some false)
    (placed : BytesAt s code.toNat complete) (aligned : code.toNat % 4 = 0)
    (bounded : code.toNat + 36 ≤ 2^64)
    (hsep : CodeStackDisjoint code (sp-96#64))
    (hexec : ∀ i : Fin 9, ExecutableRegion regions (codePC code i) (codeRegion i))
    (hlow : ∀ i : Fin 9, LowCodeRAM (codePC code i)) :
    Oak.BitwiseSource.Grammar source claim ∧
    Oak.LoweringRefinement.evalX (Oak.BitwiseSourceLowering.toExpr claim)
      (Oak.BitwiseSourceLowering.inputs left right) (fun _ => 0) fuel =
        some (Oak.BitwiseFunction.eval claim.op left right) ∧
    (steps 9 step exitWait).run s = .ok (List.replicate 9 false)
      (finalSteppedState s sp saved1 saved2
        (Oak.RiscV.widen 32 false (Oak.BitwiseFunction.eval claim.op left right)) ra) := by
  have checked : Oak.BitwiseSource.parse source = some claim ∧
      Oak.RiscVFramedBitwise.accepts .rv64 .lp64d [32,32] 32 claim.op complete = true := by
    simpa [OakSailFramedComposition.acceptsFrame, OakSailComposition.acceptsProjection] using accepted
  have grammar := Oak.BitwiseSource.parse_sound checked.1
  have typed := (Oak.BitwiseSourceLowering.means_iff_existing source claim left right
    (Oak.BitwiseFunction.eval claim.op left right) fuel).mp
      ⟨grammar, Oak.BitwiseSource.grammar_evaluation grammar left right⟩
  have bytes := ((Oak.RiscVFramedBitwise.accepts_iff _ _ _ _ _ _).mp checked.2).2.2.2.2
  have hcode : FrameCodeAt s code claim.op :=
    ⟨by simpa only [bytes] using placed, aligned, bounded⟩
  have run := nine_steps claim.op s sp saved1 saved2 (Oak.RiscV.widen 32 false left)
    (Oak.RiscV.widen 32 false right) ra code step exitWait regions first second codeRegion
    hc hcfg hp ha hsp h1 h2 hl hr hra halign hcode hsep hexec hlow
  rw [control_self s code hpc hn hi, Oak.RiscVBitwiseFunction.eval64_widen] at run
  exact ⟨grammar, typed.2, run⟩

theorem stepped_pc_and_next (s : State) (sp saved1 saved2 result ra : BitVec 64) :
    (finalSteppedState s sp saved1 saved2 result ra).regs.get? Register.PC =
      some (Sail.BitVec.update ra 0 0#1) ∧
    (finalSteppedState s sp saved1 saved2 result ra).regs.get? Register.nextPC =
      some (Sail.BitVec.update ra 0 0#1) ∧
    (finalSteppedState s sp saved1 saved2 result ra).regs.get? Register.minstret_increment = some false := by
  simp [finalSteppedState, controlState, setRegister, Std.ExtDHashMap.get?_insert]

theorem stepped_register_other (s : State) (sp saved1 saved2 result ra : BitVec 64)
    (r : Register) (hx : Register.x10 ≠ r) (hn : Register.nextPC ≠ r)
    (hp : Register.PC ≠ r) (hi : Register.minstret_increment ≠ r) :
    (finalSteppedState s sp saved1 saved2 result ra).regs.get? r = s.regs.get? r := by
  unfold finalSteppedState controlState
  rw [lookup_set_other _ _ _ _ hi, lookup_set_other _ _ _ _ hn,
    lookup_set_other _ _ _ _ hp, finalFrameState_register_other _ _ _ _ _ _ r hx hn]

theorem stepped_memory_other (s : State) (sp saved1 saved2 result ra : BitVec 64)
    (query : Nat)
    (h1 : query < (sp-96#64).toNat ∨ (sp-96#64).toNat+8 ≤ query)
    (h2 : query < (sp-96#64+8#64).toNat ∨ (sp-96#64+8#64).toNat+8 ≤ query) :
    (finalSteppedState s sp saved1 saved2 result ra).mem.get? query = s.mem.get? query :=
  frameSavedMemory_other s (sp-96#64) saved1 saved2 query h1 h2

/-- No clock/platform-loop operation is hidden in the bounded step sequence. -/
theorem stepped_nonregister_state (s : State) (sp saved1 saved2 result ra : BitVec 64) :
    (finalSteppedState s sp saved1 saved2 result ra).cycleCount = s.cycleCount ∧
    (finalSteppedState s sp saved1 saved2 result ra).sailOutput = s.sailOutput ∧
    (finalSteppedState s sp saved1 saved2 result ra).choiceState = s.choiceState ∧
    (finalSteppedState s sp saved1 saved2 result ra).tags = s.tags := by
  simp [finalSteppedState, controlState, setRegister, finalFrameState, frameSavedMemory, store64, setByte]

end OakSailSteppedFrame
