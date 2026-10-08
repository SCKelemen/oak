import OakSailComposition
import OakSailBridge.FramedInstructions
import OakSailBridge.FramedRestoration

/-! Complete supplied nine-instruction execution in the pinned sequential
Sail interpreter. Fetch, PC ticking, loader and platform initialization remain
outside this supplied-instruction driver. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailFramedComposition
open Oak.BitwiseFunction (Op eval)
open LeanRV64D LeanRV64D.Functions
open OakSailBridge.BitwiseDecoded
open OakSailComposition (sailOp unpackWords)
attribute [local irreducible] store64

def executeFrameInstruction : instruction → SailM ExecutionResult
  | .ITYPE (imm, rs1, rd, op) => execute_ITYPE imm rs1 rd op
  | .STORE (imm, rs2, rs1, width) => execute_STORE imm rs2 rs1 width
  | .LOAD (imm, rs1, rd, unsigned, width) => execute_LOAD imm rs1 rd unsigned width
  | .RTYPE (rs2, rs1, rd, op) => execute_RTYPE rs2 rs1 rd op
  | .JALR (imm, rs1, rd) => execute_JALR imm rs1 rd
  | _ => EStateM.throw Sail.Error.Unreachable

def runFrameInstructions : List instruction → SailM ExecutionResult
  | [] => pure RETIRE_SUCCESS
  | i :: rest => do
      let result ← executeFrameInstruction i
      match result with
      | .Retire_Success () => runFrameInstructions rest
      | other => pure other

def suppliedFrame (bytes : List (BitVec 8)) : SailM ExecutionResult :=
  match unpackWords 9 bytes with
  | none => EStateM.throw Sail.Error.Unreachable
  | some words => do
      let instructions ← decodeWords words
      runFrameInstructions instructions

/-- The reserved 96-byte frame does not wrap; only its two actually accessed
slots need readable/writable PMA containment. The supplied driver does not
fetch code from RAM, so it has no code/data-disjointness premise. -/
structure FrameAccess (regions : List PMA_Region) (sp : BitVec 64)
    (first second : PMA_Region) : Prop where
  nonwrapping : 96 ≤ sp.toNat
  aligned : sp.toNat % 16 = 0
  first : RAMRegion regions (sp - (96#64)) first
  second : RAMRegion regions (sp - (96#64) + (8#64)) second
  lowFirst : LowRAM (sp - (96#64))
  lowSecond : LowRAM (sp - (96#64) + (8#64))

theorem execute_bitwise_run (op : Op) (s : State) (left right : BitVec 64)
    (hl : s.regs.get? Register.x10 = some left)
    (hr : s.regs.get? Register.x11 = some right) :
    (execute_RTYPE (.Regidx 11) (.Regidx 10) (.Regidx 10) (sailOp op)).run s =
      .ok RETIRE_SUCCESS
        (setRegister s Register.x10 (Oak.RiscVBitwiseFunction.eval64 op left right)) := by
  cases op with
  | and => exact execute_and_run s left right hl hr
  | or => exact execute_or_run s left right hl hr
  | xor => exact execute_xor_run s left right hl hr

theorem frame_instructions_run (op : Op) (s : State)
    (sp saved1 saved2 left right ra next : BitVec 64)
    (regions : List PMA_Region) (first second : PMA_Region)
    (hc : MemoryConfig s regions) (hcfg : ConfigOK s)
    (ha : FrameAccess regions sp first second)
    (hsp : s.regs.get? Register.x2 = some sp)
    (h1 : s.regs.get? Register.x9 = some saved1)
    (h2 : s.regs.get? Register.x18 = some saved2)
    (hl : s.regs.get? Register.x10 = some left)
    (hr : s.regs.get? Register.x11 = some right)
    (hra : s.regs.get? Register.x1 = some ra)
    (hn : s.regs.get? Register.nextPC = some next) (halign : ReturnAligned ra) :
    (runFrameInstructions (framedInstructions (sailOp op))).run s =
      .ok RETIRE_SUCCESS (finalFrameState s (sp - (96#64)) saved1 saved2
        (Oak.RiscVBitwiseFunction.eval64 op left right) (Sail.BitVec.update ra 0 0#1)) := by
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
  have e1 := execute_sp_add_run s sp 0xfa0 hsp
  rw [halloc] at e1
  have e2 := execute_save_x9_run s1 base saved1 0 regions first cm1 sp1
    (by simpa [s1, setRegister, Std.ExtDHashMap.get?_insert] using h1)
    (by simpa only [hzero, _root_.BitVec.add_zero, base] using ha.first)
    (by simpa only [hzero, _root_.BitVec.add_zero, base] using ha.lowFirst)
  simp only [hzero, _root_.BitVec.add_zero] at e2
  have e3 := execute_save_x18_run s2 base saved2 8 regions second cm2 sp2
    (by simpa [s2, s1, setRegister, Std.ExtDHashMap.get?_insert] using h2)
    (by simpa only [height, base] using ha.second) (by simpa only [height, base] using ha.lowSecond)
  simp only [height] at e3
  have e4 := execute_copy_right_run s3 right
    (by simpa [s3, s2, s1, setRegister, Std.ExtDHashMap.get?_insert] using hr)
  have e5 := execute_bitwise_run op s4 left right
    (by simpa [s4, s3, s2, s1, setRegister, Std.ExtDHashMap.get?_insert] using hl)
    (by simpa [s4, s3, s2, s1, setRegister, Std.ExtDHashMap.get?_insert] using hr)
  have e6 := execute_restore_x9_run s5 base saved1 0 regions first cm5 sp5
    (by simpa only [hzero, _root_.BitVec.add_zero, base] using ha.first)
    (by simpa only [hzero, _root_.BitVec.add_zero, base] using ha.lowFirst)
    (by simpa only [hzero, _root_.BitVec.add_zero, s5, s4, s3, s2, setRegister, frameSavedMemory] using
      (frameSavedMemory_first_byte s1 base saved1 saved2))
  have e7 := execute_restore_x18_run s6 base saved2 8 regions second cm6 sp6
    (by simpa only [height, base] using ha.second) (by simpa only [height, base] using ha.lowSecond)
    (by simpa only [height, s6, s5, s4, s3, s2, setRegister, frameSavedMemory] using (frameSavedMemory_second_byte s1 base saved1 saved2))
  have e8 := execute_sp_add_run s7 base 96 sp7
  rw [hrelease] at e8
  have e9 := execute_ret_run s8 ra next
    (by simpa [s8,s7,s6,s5,s4,s3,s2,s1, ConfigOK, setRegister,
      Std.ExtDHashMap.get?_insert] using hcfg)
    (by simpa [s8,s7,s6,s5,s4,s3,s2,s1,setRegister,Std.ExtDHashMap.get?_insert] using hra)
    (by simpa [s8,s7,s6,s5,s4,s3,s2,s1,setRegister,Std.ExtDHashMap.get?_insert] using hn) halign
  simp only [framedInstructions, runFrameInstructions, executeFrameInstruction, Int.reduceToNat]
  simp only [RETIRE_SUCCESS] at e1 e2 e3 e4 e5 e6 e7 e8 e9 ⊢
  rw [bind_run_ok _ _ e1, bind_run_ok _ _ e2, bind_run_ok _ _ e3,
    bind_run_ok _ _ e4, bind_run_ok _ _ e5, bind_run_ok _ _ e6,
    bind_run_ok _ _ e7, bind_run_ok _ _ e8, bind_run_ok _ _ e9]
  change EStateM.Result.ok RETIRE_SUCCESS
    (stagedFrameState s base sp saved1 saved2 right result (Sail.BitVec.update ra 0 0#1)) = _
  rw [stagedFrameState_eq_finalFrameState s base sp saved1 saved2 right result _ hsp h1 h2]
  rfl


/-- Every supplied byte is decoded by the pinned Sail decoder before all nine
unchanged instruction bodies execute in order. -/
theorem exact_frame_execution (op : Op) (s : State) (left right : BitVec 32)
    (sp saved1 saved2 ra next : BitVec 64)
    (regions : List PMA_Region) (first second : PMA_Region)
    (hc : MemoryConfig s regions) (hcfg : ConfigOK s)
    (ha : FrameAccess regions sp first second)
    (hsp : s.regs.get? Register.x2 = some sp)
    (h1 : s.regs.get? Register.x9 = some saved1)
    (h2 : s.regs.get? Register.x18 = some saved2)
    (hl : s.regs.get? Register.x10 = some (Oak.RiscV.widen 32 false left))
    (hr : s.regs.get? Register.x11 = some (Oak.RiscV.widen 32 false right))
    (hra : s.regs.get? Register.x1 = some ra)
    (hn : s.regs.get? Register.nextPC = some next) (halign : ReturnAligned ra) :
    (suppliedFrame (Oak.RiscVFramedBitwise.functionBytes op)).run s =
      .ok RETIRE_SUCCESS (finalFrameState s (sp - (96#64)) saved1 saved2
        (Oak.RiscV.widen 32 false (eval op left right)) (Sail.BitVec.update ra 0 0#1)) := by
  have hd : (decodeWords (framedWords (Oak.RiscVBitwiseFunction.bodyWord op))).run s =
      .ok (framedInstructions (sailOp op)) s := by
    cases op with
    | and => exact framed_decode s hcfg _ _ decode_and
    | or => exact framed_decode s hcfg _ _ decode_or
    | xor => exact framed_decode s hcfg _ _ decode_xor
  unfold suppliedFrame
  rw [OakSailComposition.unpack_framed]
  rw [bind_run_ok _ _ hd]
  have run := frame_instructions_run op s sp saved1 saved2 _ _ ra next regions first second
    hc hcfg ha hsp h1 h2 hl hr hra hn halign
  rw [Oak.RiscVBitwiseFunction.eval64_widen] at run
  exact run

/-- Reuse the independently checked source grammar and complete compiler-body
identity. Acceptance is about the full36-byte wrapper, not an execution premise. -/
abbrev acceptsFrame := OakSailComposition.acceptsProjection

theorem accepted_source_frame {source : List UInt8} {claim : Oak.BitwiseSource.Decl}
    {complete : List (BitVec 8)} (accepted : acceptsFrame source claim complete = true)
    (left right : BitVec 32) (s : State)
    (sp saved1 saved2 ra next : BitVec 64)
    (regions : List PMA_Region) (first second : PMA_Region)
    (hc : MemoryConfig s regions) (hcfg : ConfigOK s)
    (ha : FrameAccess regions sp first second)
    (hsp : s.regs.get? Register.x2 = some sp)
    (h1 : s.regs.get? Register.x9 = some saved1)
    (h2 : s.regs.get? Register.x18 = some saved2)
    (hl : s.regs.get? Register.x10 = some (Oak.RiscV.widen 32 false left))
    (hr : s.regs.get? Register.x11 = some (Oak.RiscV.widen 32 false right))
    (hra : s.regs.get? Register.x1 = some ra)
    (hn : s.regs.get? Register.nextPC = some next) (halign : ReturnAligned ra) :
    Oak.BitwiseSource.Means source claim left right (eval claim.op left right) ∧
    (suppliedFrame complete).run s =
      .ok RETIRE_SUCCESS (finalFrameState s (sp - (96#64)) saved1 saved2
        (Oak.RiscV.widen 32 false (eval claim.op left right)) (Sail.BitVec.update ra 0 0#1)) := by
  have h : Oak.BitwiseSource.parse source = some claim ∧
      Oak.RiscVFramedBitwise.accepts .rv64 .lp64d [32,32] 32 claim.op complete = true := by
    simpa [acceptsFrame, OakSailComposition.acceptsProjection] using accepted
  have grammar := Oak.BitwiseSource.parse_sound h.1
  refine ⟨⟨grammar, Oak.BitwiseSource.grammar_evaluation grammar left right⟩, ?_⟩
  have bytes := ((Oak.RiscVFramedBitwise.accepts_iff _ _ _ _ _ _).mp h.2).2.2.2.2
  rw [bytes]
  exact exact_frame_execution claim.op s left right sp saved1 saved2 ra next regions first second
    hc hcfg ha hsp h1 h2 hl hr hra hn halign

theorem accepted_typed_frame {source : List UInt8} {claim : Oak.BitwiseSource.Decl}
    {complete : List (BitVec 8)} (accepted : acceptsFrame source claim complete = true)
    (left right : BitVec 32) (fuel : Nat) (s : State)
    (sp saved1 saved2 ra next : BitVec 64)
    (regions : List PMA_Region) (first second : PMA_Region)
    (hc : MemoryConfig s regions) (hcfg : ConfigOK s)
    (ha : FrameAccess regions sp first second)
    (hsp : s.regs.get? Register.x2 = some sp)
    (h1 : s.regs.get? Register.x9 = some saved1)
    (h2 : s.regs.get? Register.x18 = some saved2)
    (hl : s.regs.get? Register.x10 = some (Oak.RiscV.widen 32 false left))
    (hr : s.regs.get? Register.x11 = some (Oak.RiscV.widen 32 false right))
    (hra : s.regs.get? Register.x1 = some ra)
    (hn : s.regs.get? Register.nextPC = some next) (halign : ReturnAligned ra) :
    Oak.BitwiseSource.Grammar source claim ∧
    Oak.LoweringRefinement.evalX (Oak.BitwiseSourceLowering.toExpr claim)
      (Oak.BitwiseSourceLowering.inputs left right) (fun _ => 0) fuel =
        some (eval claim.op left right) ∧
    (suppliedFrame complete).run s =
      .ok RETIRE_SUCCESS (finalFrameState s (sp - (96#64)) saved1 saved2
        (Oak.RiscV.widen 32 false (eval claim.op left right)) (Sail.BitVec.update ra 0 0#1)) := by
  have run := accepted_source_frame accepted left right s sp saved1 saved2 ra next regions
    first second hc hcfg ha hsp h1 h2 hl hr hra hn halign
  have typed := (Oak.BitwiseSourceLowering.means_iff_existing source claim left right
    (eval claim.op left right) fuel).mp run.1
  exact ⟨typed.1, typed.2, run.2⟩

theorem result_u32 (s : State) (base saved1 saved2 target : BitVec 64) (value : BitVec 32) :
    ((finalFrameState s base saved1 saved2 (Oak.RiscV.widen 32 false value) target).regs.get?
      Register.x10).map (fun word => word.truncate 32) = some value := by
  rw [finalFrameState_result]
  simp only [Option.map_some, Oak.RiscV.widen_truncate_u32]

/-- Natural byte offsets fit within the reserved, nonwrapping96-byte frame. -/
theorem saved_slots_bounds (sp : BitVec 64) (h : 96 ≤ sp.toNat) :
    (sp - (96#64)).toNat = sp.toNat - 96 ∧
    (sp - (96#64) + (8#64)).toNat = sp.toNat - 96 + 8 ∧
    (sp - (96#64) + (8#64)).toNat + 8 ≤ sp.toNat := by
  have hlo : (sp - (96#64)).toNat = sp.toNat - 96 :=
    _root_.BitVec.toNat_sub_of_le (show (96#64) ≤ sp from h)
  have hs := sp.isLt
  have hadd : (sp - (96#64) + (8#64)).toNat = (sp - (96#64)).toNat + 8 := by
    apply _root_.BitVec.toNat_add_of_lt
    simp only [hlo]
    change sp.toNat - 96 + 8 < 2^64
    omega
  refine ⟨hlo, ?_, ?_⟩
  · exact hadd.trans (congrArg (fun n : Nat => n + 8) hlo)
  · rw [hadd, hlo]
    omega

example (s : State) : (suppliedFrame []).run s = .error Sail.Error.Unreachable s := by rfl
example (s : State) :
    (suppliedFrame ((Oak.RiscVFramedBitwise.functionBytes .and).take 35)).run s =
      .error Sail.Error.Unreachable s := by rfl
example : acceptsFrame (Oak.BitwiseSource.render (Oak.BitwiseSource.fixture .and))
    (Oak.BitwiseSource.fixture .and)
    ((Oak.RiscVFramedBitwise.functionBytes .and).set 4 0x13) = false := by decide +kernel
example (regions : List PMA_Region) (first second : PMA_Region) :
    ¬ FrameAccess regions (95#64) first second := by
  intro h
  have hb := h.nonwrapping
  change 96 ≤ 95 at hb
  omega
example (regions : List PMA_Region) (first second : PMA_Region) :
    ¬ FrameAccess regions (97#64) first second := by
  intro h
  have hb := h.aligned
  change 1 = 0 at hb
  contradiction
example (regions : List PMA_Region) (addr : BitVec 64) (region : PMA_Region)
    (h : region.attributes.writable = false) : ¬ RAMRegion regions addr region := by
  intro hr
  have hw := hr.2.2.1
  rw [h] at hw
  contradiction

/-- A concrete nonempty permission/alignment witness; platform reachability
is a separate obligation, not inferred from this configuration example. -/
def witnessRegion : PMA_Region :=
  { base := 0x10000, size := 0x1000,
    attributes := { (default : PMA) with readable := true, writable := true },
    include_in_device_tree := false }

example : FrameAccess [witnessRegion] (0x10100#64) witnessRegion witnessRegion := by
  constructor
  · decide +kernel
  · decide +kernel
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · unfold LowRAM; decide +kernel
  · unfold LowRAM; decide +kernel

end OakSailFramedComposition
