import ReturnScalar
import Oak.BitwiseFunction
import Oak.AArch64BitwiseFunction
import Std.Data.ExtDHashMap.Lemmas

/-! Execution of the actual Sail-generated, source-extracted scalar fragment.
Cut callees are arbitrary actions, never silently successful implementations.
This is a register/state projection, not complete architectural execution. -/
namespace Oak.SailBridge.ExtendedScalar
open ReturnExecution ReturnExecution.ScalarFunctions
open Sail PreSail

abbrev State := PreSail.SequentialState ReturnExecution.RegisterType Sail.trivialChoiceSource
abbrev Bank := Vector (BitVec 64) 31

def put (s : State) (r : ReturnExecution.Register) (v : ReturnExecution.RegisterType r) : State :=
  { s with regs := s.regs.insert r v }

/-- Selected scalar result, stated independently from the generated body. -/
def result (op : ReturnExecution.LogicalOp) (a b : BitVec 32) : BitVec 32 :=
  match op with
  | .LogicalOp_AND => a &&& b
  | .LogicalOp_ORR => a ||| b
  | .LogicalOp_EOR => a ^^^ b

private theorem undefined_bits_eq (width : Nat) :
    (PreSail.undefined_bitvector width : SailM (BitVec width)) = pure (0 : BitVec width) := by
  funext state
  have hc : state.choiceState = () := Subsingleton.elim (α := Unit) _ _
  change EStateM.Result.ok (0 : BitVec width) { state with choiceState := () } = .ok _ state
  rw [← hc]

private theorem append_zero32 (x : BitVec 32) :
    0#32 ++ x = x.zeroExtend 64 := by bv_decide

def externalOp : Oak.BitwiseFunction.Op → LogicalOp
  | .and => .LogicalOp_AND | .or => .LogicalOp_ORR | .xor => .LogicalOp_EOR

theorem result_eq_common (op : Oak.BitwiseFunction.Op) (a b : BitVec 32) :
    result (externalOp op) a b = Oak.BitwiseFunction.eval op a b := by
  cases op <;> rfl

/-- Original LSL's zero arm never invokes the arbitrary LSL_C callback. -/
theorem lsl_zero (boundaries : ScalarBoundaries) (state : State) (x : BitVec 32) :
    (LSL boundaries x 0).run state = .ok x state := by
  simp [LSL, PreSail.assert, undefined_bits_eq,
    EStateM.run, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure,
    MonadStateOf.get, MonadStateOf.set, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- All 2^64 input pairs, in the generated register state; exactly one bank
write, no flag write, and no nonzero-shift boundary call. -/
theorem logical_body_run (boundaries : ScalarBoundaries) (state : State) (bank : Bank)
    (initialized : state.regs.get? ReturnExecution.Register._R = some bank)
    (op : ReturnExecution.LogicalOp) :
    (integer_logical_shiftedreg boundaries 0 32 false 1 0 op false 0 .ShiftType_LSL).run state =
      .ok () (put state ._R (bank.set! 0
        ((result op (bank[0].extractLsb' 0 32) (bank[1].extractLsb' 0 32)).zeroExtend 64))) := by
  cases op <;>
    simp [integer_logical_shiftedreg, ShiftReg, LSL, aget_X, aset_X, ZeroExtend__0,
      result, put, initialized, PreSail.assert, undefined_bits_eq, Sail.BitVec.length, Sail.BitVec.slice, Zeros,
      vectorUpdate, readReg, writeReg, modify, modifyGet, append_zero32, EStateM.run, Bind.bind, Pure.pure,
      EStateM.bind, EStateM.pure, MonadState.get, getThe, MonadStateOf.get,
      MonadStateOf.set, MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.get]

private theorem undefined_bool_eq :
    (PreSail.undefined_bool () : SailM Bool) = pure false := by
  funext state
  have hc : state.choiceState = () := Subsingleton.elim (α := Unit) _ _
  change EStateM.Result.ok false { state with choiceState := () } = .ok _ state
  rw [← hc]

private theorem undefined_logical_eq :
    undefined_LogicalOp () = (pure .LogicalOp_AND : SailM LogicalOp) := by
  funext state
  have hc : state.choiceState = () := Subsingleton.elim (α := Unit) _ _
  change EStateM.Result.ok LogicalOp.LogicalOp_AND { state with choiceState := () } = .ok _ state
  rw [← hc]

private theorem undefined_branch_eq :
    undefined_BranchType () = (pure .BranchType_DIRCALL : SailM BranchType) := by
  funext state
  have hc : state.choiceState = () := Subsingleton.elim (α := Unit) _ _
  change EStateM.Result.ok BranchType.BranchType_DIRCALL { state with choiceState := () } = .ok _ state
  rw [← hc]

/-- Sufficient supported query profile for the unchanged eager Lean export.
BTI is absent and execution is AArch64. Both feature queries must be initialized,
read-only and successful, including UsingAArch32 even with BTI=false. Relating
these cut queries to a full model's configuration registers is still external. -/
structure QuietControl (b : ScalarBoundaries) (s : State) : Prop where
  bti : (b.HaveBTIExt ()).run s = .ok false s
  aarch64 : (b.UsingAArch32 ()).run s = .ok false s

/-- BranchTargetCheck is not called in this supported profile. -/
theorem postdecode_quiet (b : ScalarBoundaries) (s : State) (h : QuietControl b s) :
    (__PostDecode b ()).run s = .ok () s := by
  rcases h with ⟨hb, ha⟩
  simp only [__PostDecode, EStateM.run, Bind.bind, EStateM.bind] at hb ha ⊢
  rw [hb]
  dsimp only
  rw [ha]
  rfl

def opc : LogicalOp → BitVec 2
  | .LogicalOp_AND => 0 | .LogicalOp_ORR => 1 | .LogicalOp_EOR => 2

/-- The original decoder's exact32-bit, noninverted, nonflag-setting,
zero-shift selected fields retain PostDecode rather than replacing it. -/
theorem logical_decode_factorization (b : ScalarBoundaries) (op : LogicalOp) :
    integer_logical_shiftedreg_decode b 0#5 0#5 0#6 1#5 0#1 0#2 (opc op) 0#1 =
      (do
        writeReg ReturnExecution.Register.__unconditional true
        __PostDecode b ()
        integer_logical_shiftedreg b 0 32 false 1 0 op false 0 .ShiftType_LSL) := by
  cases op <;> simp [integer_logical_shiftedreg_decode, opc, UInt, DecodeShift,
    undefined_bool_eq, undefined_logical_eq, Sail.BitVec.access, Sail.BitVec.join1] <;> rfl

/-- RET reads the incoming X30, records BTypeNext=00, then invokes the arbitrary
BranchTo callback with the actual return branch kind. It does not equate that
callback with a PC assignment or assume that it succeeds. -/
theorem ret_body_factorization (b : ScalarBoundaries) (state : State) (bank : Bank)
    (initialized : state.regs.get? ReturnExecution.Register._R = some bank) :
    (branch_unconditional_register b .BranchType_RET 0 30 false false true).run state =
      (b.BranchTo bank[30] .BranchType_RET).run (put state .BTypeNext 0#2) := by
  simp [branch_unconditional_register, aget_X, initialized, readReg, writeReg,
    put, Sail.BitVec.slice, EStateM.run, Bind.bind, Pure.pure,
    EStateM.bind, EStateM.pure, MonadState.get, getThe, MonadStateOf.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.get]
  rfl

/-- Literal behavior of the unchanged exporter. The non-PAC decoder still
performs HavePACExt because nested Boolean actions are eagerly lifted.
This is not a claim that the original Sail short-circuit path queried PAC. -/
theorem ret_decode_factorization (b : ScalarBoundaries) :
    branch_unconditional_register_decode b 0#5 30#5 0#1 0#1 31#5 2#2 0#1 =
      (do
        writeReg ReturnExecution.Register.__unconditional true
        let _ ← b.HavePACExt ()
        __PostDecode b ()
        branch_unconditional_register b .BranchType_RET 0 30 false false true) := by
  simp [branch_unconditional_register_decode, undefined_branch_eq, UInt]
  rfl

private theorem write_then {α : Type} (s : State) (r : ReturnExecution.Register)
    (v : ReturnExecution.RegisterType r) (next : SailM α) :
    (do writeReg r v; next).run s = next.run (put s r v) := rfl

/-- Successful field-decoder execution after explicit read-only AArch64,
no-BTI callback obligations. No full model configuration is invented. -/
theorem logical_fields_run (b : ScalarBoundaries) (state : State) (bank : Bank)
    (initialized : state.regs.get? ReturnExecution.Register._R = some bank)
    (op : LogicalOp)
    (control : QuietControl b (put state .__unconditional true)) :
    (integer_logical_shiftedreg_decode b 0#5 0#5 0#6 1#5 0#1 0#2 (opc op) 0#1).run state =
      .ok () (put (put state .__unconditional true) ._R (bank.set! 0
        ((result op (bank[0].extractLsb' 0 32) (bank[1].extractLsb' 0 32)).zeroExtend 64))) := by
  rw [logical_decode_factorization, write_then]
  have hp := postdecode_quiet b _ control
  have hi : (put state .__unconditional true).regs.get? ReturnExecution.Register._R = some bank := by
    simpa [put, Std.ExtDHashMap.get?_insert] using initialized
  have hb := logical_body_run b (put state .__unconditional true) bank hi op
  simp only [EStateM.run, Bind.bind, EStateM.bind] at hp hb ⊢
  rw [hp]
  exact hb

/-- Full RET field-decoder projection, including __unconditional and BTypeNext.
The feature query's value is irrelevant on this non-PAC route, but its success
and state-purity are required by the unchanged eager export. BranchTo may fail
or change any state component; its result remains exactly in the conclusion. -/
theorem ret_fields_run (b : ScalarBoundaries) (state : State) (bank : Bank)
    (initialized : state.regs.get? ReturnExecution.Register._R = some bank)
    (pacSupported : Bool)
    (pacQuery : (b.HavePACExt ()).run (put state .__unconditional true) =
      .ok pacSupported (put state .__unconditional true))
    (control : QuietControl b (put state .__unconditional true)) :
    (branch_unconditional_register_decode b 0#5 30#5 0#1 0#1 31#5 2#2 0#1).run state =
      (b.BranchTo bank[30] .BranchType_RET).run
        (put (put state .__unconditional true) .BTypeNext 0#2) := by
  rw [ret_decode_factorization, write_then]
  have hp := postdecode_quiet b _ control
  have hi : (put state .__unconditional true).regs.get? ReturnExecution.Register._R = some bank := by
    simpa [put, Std.ExtDHashMap.get?_insert] using initialized
  have hb := ret_body_factorization b (put state .__unconditional true) bank hi
  simp only [EStateM.run, Bind.bind, EStateM.bind] at pacQuery hp hb ⊢
  rw [pacQuery]
  dsimp only
  rw [hp]
  exact hb

def logicalWord : LogicalOp → BitVec 32
  | .LogicalOp_AND => 0x0a010000#32
  | .LogicalOp_ORR => 0x2a010000#32
  | .LogicalOp_EOR => 0x4a010000#32

def clauseNumber : LogicalOp → Int
  | .LogicalOp_AND => 1845 | .LogicalOp_ORR => 1858 | .LogicalOp_EOR => 1788

/-- These are the four copied original clauses plus a rejecting fallback,
not Arm's complete first-match decoder. SEE is initialized explicitly; source
clause-selection correctness against every omitted clause remains separate. -/
def decodeSelected := ReturnExecution.ScalarFunctions.decode64

/-! Closed field facts are kernel checked independently of state execution. -/
@[simp] private theorem and_field_30_24 : Sail.BitVec.extractLsb 0x0a010000#32 30 24 = 10#7 := by decide +kernel
@[simp] private theorem and_field_21_21 : Sail.BitVec.extractLsb 0x0a010000#32 21 21 = 0#1 := by decide +kernel
@[simp] private theorem and_field_4_0 : Sail.BitVec.extractLsb 0x0a010000#32 4 0 = 0#5 := by decide +kernel
@[simp] private theorem and_field_9_5 : Sail.BitVec.extractLsb 0x0a010000#32 9 5 = 0#5 := by decide +kernel
@[simp] private theorem and_field_15_10 : Sail.BitVec.extractLsb 0x0a010000#32 15 10 = 0#6 := by decide +kernel
@[simp] private theorem and_field_20_16 : Sail.BitVec.extractLsb 0x0a010000#32 20 16 = 1#5 := by decide +kernel
@[simp] private theorem and_field_23_22 : Sail.BitVec.extractLsb 0x0a010000#32 23 22 = 0#2 := by decide +kernel
@[simp] private theorem and_field_30_29 : Sail.BitVec.extractLsb 0x0a010000#32 30 29 = 0#2 := by decide +kernel
@[simp] private theorem and_field_31_10 : Sail.BitVec.extractLsb 0x0a010000#32 31 10 = 163904#22 := by decide +kernel
@[simp] private theorem and_field_22_21 : Sail.BitVec.extractLsb 0x0a010000#32 22 21 = 0#2 := by decide +kernel
@[simp] private theorem and_bit_21 : Sail.BitVec.join1 [Sail.BitVec.access 0x0a010000#32 21] = 0#1 := by decide +kernel
@[simp] private theorem and_bit_31 : Sail.BitVec.join1 [Sail.BitVec.access 0x0a010000#32 31] = 0#1 := by decide +kernel
@[simp] private theorem and_bit_10 : Sail.BitVec.join1 [Sail.BitVec.access 0x0a010000#32 10] = 0#1 := by decide +kernel
@[simp] private theorem and_bit_11 : Sail.BitVec.join1 [Sail.BitVec.access 0x0a010000#32 11] = 0#1 := by decide +kernel
@[simp] private theorem and_bit_24 : Sail.BitVec.join1 [Sail.BitVec.access 0x0a010000#32 24] = 0#1 := by decide +kernel
@[simp] private theorem or_field_30_24 : Sail.BitVec.extractLsb 0x2a010000#32 30 24 = 42#7 := by decide +kernel
@[simp] private theorem or_field_21_21 : Sail.BitVec.extractLsb 0x2a010000#32 21 21 = 0#1 := by decide +kernel
@[simp] private theorem or_field_4_0 : Sail.BitVec.extractLsb 0x2a010000#32 4 0 = 0#5 := by decide +kernel
@[simp] private theorem or_field_9_5 : Sail.BitVec.extractLsb 0x2a010000#32 9 5 = 0#5 := by decide +kernel
@[simp] private theorem or_field_15_10 : Sail.BitVec.extractLsb 0x2a010000#32 15 10 = 0#6 := by decide +kernel
@[simp] private theorem or_field_20_16 : Sail.BitVec.extractLsb 0x2a010000#32 20 16 = 1#5 := by decide +kernel
@[simp] private theorem or_field_23_22 : Sail.BitVec.extractLsb 0x2a010000#32 23 22 = 0#2 := by decide +kernel
@[simp] private theorem or_field_30_29 : Sail.BitVec.extractLsb 0x2a010000#32 30 29 = 1#2 := by decide +kernel
@[simp] private theorem or_field_31_10 : Sail.BitVec.extractLsb 0x2a010000#32 31 10 = 688192#22 := by decide +kernel
@[simp] private theorem or_field_22_21 : Sail.BitVec.extractLsb 0x2a010000#32 22 21 = 0#2 := by decide +kernel
@[simp] private theorem or_bit_21 : Sail.BitVec.join1 [Sail.BitVec.access 0x2a010000#32 21] = 0#1 := by decide +kernel
@[simp] private theorem or_bit_31 : Sail.BitVec.join1 [Sail.BitVec.access 0x2a010000#32 31] = 0#1 := by decide +kernel
@[simp] private theorem or_bit_10 : Sail.BitVec.join1 [Sail.BitVec.access 0x2a010000#32 10] = 0#1 := by decide +kernel
@[simp] private theorem or_bit_11 : Sail.BitVec.join1 [Sail.BitVec.access 0x2a010000#32 11] = 0#1 := by decide +kernel
@[simp] private theorem or_bit_24 : Sail.BitVec.join1 [Sail.BitVec.access 0x2a010000#32 24] = 0#1 := by decide +kernel
@[simp] private theorem xor_field_30_24 : Sail.BitVec.extractLsb 0x4a010000#32 30 24 = 74#7 := by decide +kernel
@[simp] private theorem xor_field_21_21 : Sail.BitVec.extractLsb 0x4a010000#32 21 21 = 0#1 := by decide +kernel
@[simp] private theorem xor_field_4_0 : Sail.BitVec.extractLsb 0x4a010000#32 4 0 = 0#5 := by decide +kernel
@[simp] private theorem xor_field_9_5 : Sail.BitVec.extractLsb 0x4a010000#32 9 5 = 0#5 := by decide +kernel
@[simp] private theorem xor_field_15_10 : Sail.BitVec.extractLsb 0x4a010000#32 15 10 = 0#6 := by decide +kernel
@[simp] private theorem xor_field_20_16 : Sail.BitVec.extractLsb 0x4a010000#32 20 16 = 1#5 := by decide +kernel
@[simp] private theorem xor_field_23_22 : Sail.BitVec.extractLsb 0x4a010000#32 23 22 = 0#2 := by decide +kernel
@[simp] private theorem xor_field_30_29 : Sail.BitVec.extractLsb 0x4a010000#32 30 29 = 2#2 := by decide +kernel
@[simp] private theorem xor_field_31_10 : Sail.BitVec.extractLsb 0x4a010000#32 31 10 = 1212480#22 := by decide +kernel
@[simp] private theorem xor_field_22_21 : Sail.BitVec.extractLsb 0x4a010000#32 22 21 = 0#2 := by decide +kernel
@[simp] private theorem xor_bit_21 : Sail.BitVec.join1 [Sail.BitVec.access 0x4a010000#32 21] = 0#1 := by decide +kernel
@[simp] private theorem xor_bit_31 : Sail.BitVec.join1 [Sail.BitVec.access 0x4a010000#32 31] = 0#1 := by decide +kernel
@[simp] private theorem xor_bit_10 : Sail.BitVec.join1 [Sail.BitVec.access 0x4a010000#32 10] = 0#1 := by decide +kernel
@[simp] private theorem xor_bit_11 : Sail.BitVec.join1 [Sail.BitVec.access 0x4a010000#32 11] = 0#1 := by decide +kernel
@[simp] private theorem xor_bit_24 : Sail.BitVec.join1 [Sail.BitVec.access 0x4a010000#32 24] = 0#1 := by decide +kernel
@[simp] private theorem ret_field_30_24 : Sail.BitVec.extractLsb 0xd65f03c0#32 30 24 = 86#7 := by decide +kernel
@[simp] private theorem ret_field_21_21 : Sail.BitVec.extractLsb 0xd65f03c0#32 21 21 = 0#1 := by decide +kernel
@[simp] private theorem ret_field_4_0 : Sail.BitVec.extractLsb 0xd65f03c0#32 4 0 = 0#5 := by decide +kernel
@[simp] private theorem ret_field_9_5 : Sail.BitVec.extractLsb 0xd65f03c0#32 9 5 = 30#5 := by decide +kernel
@[simp] private theorem ret_field_15_10 : Sail.BitVec.extractLsb 0xd65f03c0#32 15 10 = 0#6 := by decide +kernel
@[simp] private theorem ret_field_20_16 : Sail.BitVec.extractLsb 0xd65f03c0#32 20 16 = 31#5 := by decide +kernel
@[simp] private theorem ret_field_23_22 : Sail.BitVec.extractLsb 0xd65f03c0#32 23 22 = 1#2 := by decide +kernel
@[simp] private theorem ret_field_30_29 : Sail.BitVec.extractLsb 0xd65f03c0#32 30 29 = 2#2 := by decide +kernel
@[simp] private theorem ret_field_31_10 : Sail.BitVec.extractLsb 0xd65f03c0#32 31 10 = 3512256#22 := by decide +kernel
@[simp] private theorem ret_field_22_21 : Sail.BitVec.extractLsb 0xd65f03c0#32 22 21 = 2#2 := by decide +kernel
@[simp] private theorem ret_bit_21 : Sail.BitVec.join1 [Sail.BitVec.access 0xd65f03c0#32 21] = 0#1 := by decide +kernel
@[simp] private theorem ret_bit_31 : Sail.BitVec.join1 [Sail.BitVec.access 0xd65f03c0#32 31] = 1#1 := by decide +kernel
@[simp] private theorem ret_bit_10 : Sail.BitVec.join1 [Sail.BitVec.access 0xd65f03c0#32 10] = 0#1 := by decide +kernel
@[simp] private theorem ret_bit_11 : Sail.BitVec.join1 [Sail.BitVec.access 0xd65f03c0#32 11] = 0#1 := by decide +kernel
@[simp] private theorem ret_bit_24 : Sail.BitVec.join1 [Sail.BitVec.access 0xd65f03c0#32 24] = 0#1 := by decide +kernel

theorem selected_logical_dispatch (b : ScalarBoundaries) (state : State) (op : LogicalOp)
    (ready : state.regs.get? ReturnExecution.Register.SEE = some (-1)) :
    (decodeSelected b (logicalWord op)).run state =
      (integer_logical_shiftedreg_decode b 0#5 0#5 0#6 1#5 0#1 0#2 (opc op) 0#1).run
        (put state .SEE (clauseNumber op)) := by
  cases op <;>
    simp [decodeSelected, decode64, logicalWord, clauseNumber, opc,
      readReg, writeReg, put, ready, EStateM.run, Bind.bind, Pure.pure,
      EStateM.bind, EStateM.pure, MonadState.get, getThe, MonadStateOf.get,
      modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.get] <;> rfl

theorem selected_ret_dispatch (b : ScalarBoundaries) (state : State)
    (ready : state.regs.get? ReturnExecution.Register.SEE = some (-1)) :
    (decodeSelected b 0xd65f03c0#32).run state =
      (branch_unconditional_register_decode b 0#5 30#5 0#1 0#1 31#5 2#2 0#1).run
        (put state .SEE 1522) := by
  simp [decodeSelected, decode64, readReg, writeReg, put, ready, EStateM.run,
    Bind.bind, Pure.pure, EStateM.bind, EStateM.pure, MonadState.get, getThe,
    MonadStateOf.get, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    EStateM.get]

def logicalControlState (op : LogicalOp) (s : State) : State :=
  put (put (put s .SEE (-1)) .SEE (clauseNumber op)) .__unconditional true

def updatedBank (op : LogicalOp) (bank : Bank) : Bank :=
  bank.set! 0 ((result op (bank[0].extractLsb' 0 32)
    (bank[1].extractLsb' 0 32)).zeroExtend 64)

def afterLogical (op : LogicalOp) (s : State) (bank : Bank) : State :=
  put (logicalControlState op s) ._R (updatedBank op bank)

def retControlState (s : State) : State :=
  put (put (put s .SEE (-1)) .SEE 1522) .__unconditional true

def dispatch (b : ScalarBoundaries) (word : BitVec 32) : SailM Unit := do
  writeReg ReturnExecution.Register.SEE (-1)
  decodeSelected b word

/-- Explicit adapter supplying decoder SEE initialization. This is not a
fetch-loop theorem and does not manufacture loaded or executable memory. -/
theorem dispatch_logical (b : ScalarBoundaries) (s : State) (bank : Bank) (op : LogicalOp)
    (initialized : s.regs.get? ReturnExecution.Register._R = some bank)
    (control : QuietControl b (logicalControlState op s)) :
    (dispatch b (logicalWord op)).run s = .ok () (afterLogical op s bank) := by
  unfold dispatch
  rw [write_then, selected_logical_dispatch b _ op (by simp [put, Std.ExtDHashMap.get?_insert])]
  exact logical_fields_run b _ bank
    (by simpa [put, Std.ExtDHashMap.get?_insert] using initialized) op control

theorem dispatch_ret (b : ScalarBoundaries) (s : State) (bank : Bank)
    (initialized : s.regs.get? ReturnExecution.Register._R = some bank)
    (pacSupported : Bool)
    (pacQuery : (b.HavePACExt ()).run (retControlState s) = .ok pacSupported (retControlState s))
    (control : QuietControl b (retControlState s)) :
    (dispatch b 0xd65f03c0#32).run s =
      (b.BranchTo bank[30] .BranchType_RET).run (put (retControlState s) .BTypeNext 0#2) := by
  unfold dispatch
  rw [write_then, selected_ret_dispatch b _ (by simp [put, Std.ExtDHashMap.get?_insert])]
  exact ret_fields_run b _ bank
    (by simpa [put, Std.ExtDHashMap.get?_insert] using initialized)
    pacSupported pacQuery control

/-- Decode two complete little-endian words with no trailing bytes. Unsupported
lengths fail rather than being padded; the generated decoder is the selected
four-clause projection, not the omitted full Arm instruction set. -/
def executeBytes (b : ScalarBoundaries) (bytes : List UInt8) : SailM Unit :=
  match Oak.AArch64BitwiseFunction.takeWord bytes with
  | some (first, rest) =>
    match Oak.AArch64BitwiseFunction.takeWord rest with
    | some (second, []) => do dispatch b first; dispatch b second
    | _ => sailThrow (.Error_Undefined ())
  | _ => sailThrow (.Error_Undefined ())

private theorem exact_byte_shape (b : ScalarBoundaries) (op : Oak.BitwiseFunction.Op) :
    executeBytes b (Oak.AArch64BitwiseFunction.functionBytes op) =
      (do dispatch b (logicalWord (externalOp op)); dispatch b 0xd65f03c0#32) := by
  cases op <;> rfl

/-- Exact bytes, actual exported scalar register execution and RET state/event
boundary. BranchTo's complete result (including errors and final state) is
preserved, not equated to a no-fault PC update. This theorem supplies the
computed argument state to that still-external architectural boundary. -/
theorem function_bytes_to_return_request
    (b : ScalarBoundaries) (s : State) (bank : Bank) (op : Oak.BitwiseFunction.Op)
    (initialized : s.regs.get? ReturnExecution.Register._R = some bank)
    (logicalControl : QuietControl b (logicalControlState (externalOp op) s))
    (retControl : QuietControl b (retControlState (afterLogical (externalOp op) s bank)))
    (pacSupported : Bool)
    (pacQuery : (b.HavePACExt ()).run (retControlState (afterLogical (externalOp op) s bank)) =
      .ok pacSupported (retControlState (afterLogical (externalOp op) s bank))) :
    (executeBytes b (Oak.AArch64BitwiseFunction.functionBytes op)).run s =
      (b.BranchTo bank[30] .BranchType_RET).run
        (put (retControlState (afterLogical (externalOp op) s bank)) .BTypeNext 0#2) := by
  rw [exact_byte_shape]
  have first := dispatch_logical b s bank (externalOp op) initialized logicalControl
  have second := dispatch_ret b (afterLogical (externalOp op) s bank)
    (updatedBank (externalOp op) bank)
    (by simp [afterLogical, put, Std.ExtDHashMap.get?_insert])
    pacSupported pacQuery retControl
  have returnValue : (updatedBank (externalOp op) bank)[30] = bank[30] := by
    simp [updatedBank, Vector.getElem_set!]
  rw [returnValue] at second
  simp only [EStateM.run, Bind.bind, EStateM.bind] at first second ⊢
  rw [first]
  exact second

def requestState (op : Oak.BitwiseFunction.Op) (s : State) (bank : Bank) : State :=
  put (retControlState (afterLogical (externalOp op) s bank)) .BTypeNext 0#2

theorem request_register_bank (op : Oak.BitwiseFunction.Op) (s : State) (bank : Bank) :
    (requestState op s bank).regs.get? ReturnExecution.Register._R =
      some (updatedBank (externalOp op) bank) := by
  simp [requestState, retControlState, afterLogical, put, Std.ExtDHashMap.get?_insert]

theorem request_result_u32 (op : Oak.BitwiseFunction.Op) (bank : Bank) :
    (updatedBank (externalOp op) bank)[0] =
      (Oak.BitwiseFunction.eval op (bank[0].extractLsb' 0 32)
        (bank[1].extractLsb' 0 32)).zeroExtend 64 := by
  simp [updatedBank, result_eq_common]

theorem request_frames_pstate_and_memory (op : Oak.BitwiseFunction.Op) (s : State) (bank : Bank) :
    (requestState op s bank).regs.get? ReturnExecution.Register.PSTATE =
      s.regs.get? ReturnExecution.Register.PSTATE ∧
    (requestState op s bank).mem = s.mem ∧
    (requestState op s bank).tags = s.tags := by
  simp [requestState, retControlState, afterLogical, logicalControlState, put,
    Std.ExtDHashMap.get?_insert]

theorem request_records_return_kind (op : Oak.BitwiseFunction.Op) (s : State) (bank : Bank) :
    (requestState op s bank).regs.get? ReturnExecution.Register.BTypeNext = some 0#2 := by
  simp [requestState, put, Std.ExtDHashMap.get?_insert]

/-- External architectural return obligation. Alignment is explicit, but is
not sufficient: a real instantiation must establish BranchTo success under
its translation, address-tag/control-protection and execution configuration,
and relate its full architectural state to this generated fragment state.
There is no default implementation of this proposition. -/
structure ReturnBoundary (b : ScalarBoundaries) (target : BitVec 64) (before after : State) : Prop where
  aligned : target.toNat % 4 = 0
  executes : (b.BranchTo target .BranchType_RET).run before = .ok () after
  bankFrame : after.regs.get? ReturnExecution.Register._R = before.regs.get? ReturnExecution.Register._R

/-- Conditional successful external-fragment execution, not equality of two
faults. The only remaining dynamic return premise is named and exposes both
alignment and full callback execution/frame obligations. -/
theorem successful_function_under_return_boundary
    (b : ScalarBoundaries) (s final : State) (bank : Bank) (op : Oak.BitwiseFunction.Op)
    (initialized : s.regs.get? ReturnExecution.Register._R = some bank)
    (logicalControl : QuietControl b (logicalControlState (externalOp op) s))
    (retControl : QuietControl b (retControlState (afterLogical (externalOp op) s bank)))
    (pacSupported : Bool)
    (pacQuery : (b.HavePACExt ()).run (retControlState (afterLogical (externalOp op) s bank)) =
      .ok pacSupported (retControlState (afterLogical (externalOp op) s bank)))
    (returned : ReturnBoundary b bank[30] (requestState op s bank) final) :
    (executeBytes b (Oak.AArch64BitwiseFunction.functionBytes op)).run s = .ok () final ∧
    final.regs.get? ReturnExecution.Register._R = some (updatedBank (externalOp op) bank) := by
  constructor
  · rw [function_bytes_to_return_request b s bank op initialized logicalControl
      retControl pacSupported pacQuery]
    exact returned.executes
  · rw [returned.bankFrame]
    exact request_register_bank op s bank

/-- Regression for the unchanged eager export: BTI=false cannot hide a failed
UsingAArch32 query, nor discard the failure's post-state. -/
theorem postdecode_eager_failure (b : ScalarBoundaries) (s after : State)
    (e : Error ReturnExecution.exception)
    (hb : (b.HaveBTIExt ()).run s = .ok false s)
    (ha : (b.UsingAArch32 ()).run s = .error e after) :
    (__PostDecode b ()).run s = .error e after := by
  simp only [__PostDecode, EStateM.run, Bind.bind, EStateM.bind] at hb ha ⊢
  rw [hb]
  dsimp only
  rw [ha]

/-- Non-PAC does not suppress the raw export's eager feature-query failure. -/
theorem ret_eager_pac_failure (b : ScalarBoundaries) (s after : State)
    (e : Error ReturnExecution.exception)
    (failed : (b.HavePACExt ()).run (put s .__unconditional true) = .error e after) :
    (branch_unconditional_register_decode b 0#5 30#5 0#1 0#1 31#5 2#2 0#1).run s =
      .error e after := by
  rw [ret_decode_factorization, write_then]
  simp only [EStateM.run, Bind.bind, EStateM.bind] at failed ⊢
  rw [failed]

example (b : ScalarBoundaries) (s : State) :
    (executeBytes b [0,0,1,10,192,3,95]).run s = .error (.User (.Error_Undefined ())) s := by rfl

end Oak.SailBridge.ExtendedScalar
