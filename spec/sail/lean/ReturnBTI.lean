import ReturnComposition
namespace Oak.SailBridge.ReturnBTI
open ReturnExecution ReturnExecution.Functions Sail PreSail
open Oak.SailBridge
set_option linter.unusedSimpArgs false
abbrev State := ReturnConfig.State
abbrev put := Return.put

private theorem undefined_bits_eq (width : Nat) :
 (PreSail.undefined_bitvector width : SailM (BitVec width)) = pure (0 : BitVec width) := by
 funext state
 have hc : state.choiceState = () := Subsingleton.elim (α := Unit) _ _
 change EStateM.Result.ok (0 : BitVec width) {state with choiceState := ()} = .ok _ state
 rw [← hc]

/-- Initialized control reads, with BTYPE=00. The page may be guarded or unguarded;
EDSCR selects ordinary running state rather than bypassing the check by halting. -/
structure Ready (s : State) (ps : ProcState) (guarded compatible : Bool) where
 pstate : s.regs.get? Register.PSTATE = some ps
 btype : ps.BTYPE = 0
 page : s.regs.get? Register.InGuardedPage = some guarded
 compatible : s.regs.get? Register.BTypeCompatible = some compatible
 edscr : s.regs.get? Register.EDSCR = some 1#32

def withControl (s : State) (ps : ProcState) (guarded compatible : Bool) : State :=
 put (put (put (put s .PSTATE {ps with BTYPE := 0}) .InGuardedPage guarded)
  .BTypeCompatible compatible) .EDSCR 1#32

theorem withControl_ready (s : State) (ps : ProcState) (guarded compatible : Bool) :
 Ready (withControl s ps guarded compatible) {ps with BTYPE := 0} guarded compatible := by
 constructor <;> simp [withControl,put,Return.put,Std.ExtDHashMap.get?_insert]

theorem halted_running (s : State) (h : s.regs.get? Register.EDSCR = some 1#32) :
 (Halted ()).run s = .ok false s := by
 simp [Halted,readReg,h,EStateM.run,Bind.bind,Pure.pure,EStateM.bind,EStateM.pure,
 MonadStateOf.get,MonadState.get,EStateM.get,getThe,Sail.BitVec.slice]

theorem current_instruction (s : State) (word : BitVec 32)
 (h : s.regs.get? Register.__currentInstr = some word) :
 (ThisInstr ()).run s = .ok word s := by
 simp [ThisInstr,readReg,h,EStateM.run,Bind.bind,Pure.pure,EStateM.bind,EStateM.pure,
 MonadStateOf.get,MonadState.get,EStateM.get,getThe,Sail.BitVec.slice]

def branchWord (word : BitVec 32) : Bool :=
 word.extractLsb' 25 7 == 0b1101011#7 && word.extractLsb' 16 5 == 31#5 &&
 word.extractLsb' 21 4 != 5#4

def btiWord (word : BitVec 32) : Bool :=
 word.extractLsb' 22 10 == 0b1101010100#10 && word.extractLsb' 12 10 == 0b0000110010#10 &&
 word.extractLsb' 0 5 == 31#5 && word.extractLsb' 8 4 == 4#4 && word.extractLsb' 5 1 == 0#1

theorem logical_recognizer_values (op : Oak.BitwiseFunction.Op) :
 branchWord (ExtendedScalar.logicalWord (ExtendedScalar.externalOp op)) = false ∧
 btiWord (ExtendedScalar.logicalWord (ExtendedScalar.externalOp op)) = false := by
 cases op <;> decide +kernel

theorem ret_recognizer_values : branchWord 0xd65f03c0#32 = true ∧
 btiWord 0xd65f03c0#32 = false := by decide +kernel

theorem logical_branch_run (s : State) (v : ReturnConfig.Values)
 (cfg : ReturnConfig.Initialized s v) (enabled : v.v85 = true)
 (op : Oak.BitwiseFunction.Op)
 (instr : s.regs.get? Register.__currentInstr = some (ExtendedScalar.logicalWord (ExtendedScalar.externalOp op))) :
 (AArch64_ExecutingBROrBLROrRetInstr ()).run s = .ok false s := by
 have feature : HaveBTIExt () s = .ok true s := by
  simpa [EStateM.run,enabled] using ReturnConfig.haveBTI_run s v cfg
 cases op <;>
 simp [AArch64_ExecutingBROrBLROrRetInstr,feature,ThisInstr,undefined_bits_eq,readReg,instr,ExtendedScalar.logicalWord,ExtendedScalar.externalOp,
  EStateM.run,Bind.bind,Pure.pure,EStateM.bind,EStateM.pure,
  MonadStateOf.get,MonadState.get,EStateM.get,getThe,Sail.BitVec.slice]

theorem logical_bti_run (s : State) (v : ReturnConfig.Values)
 (cfg : ReturnConfig.Initialized s v) (enabled : v.v85 = true)
 (op : Oak.BitwiseFunction.Op)
 (instr : s.regs.get? Register.__currentInstr = some (ExtendedScalar.logicalWord (ExtendedScalar.externalOp op))) :
 (AArch64_ExecutingBTIInstr ()).run s = .ok false s := by
 have feature : HaveBTIExt () s = .ok true s := by
  simpa [EStateM.run,enabled] using ReturnConfig.haveBTI_run s v cfg
 cases op <;>
 simp [AArch64_ExecutingBTIInstr,feature,ThisInstr,undefined_bits_eq,readReg,instr,ExtendedScalar.logicalWord,ExtendedScalar.externalOp,
  EStateM.run,Bind.bind,Pure.pure,EStateM.bind,EStateM.pure,
  MonadStateOf.get,MonadState.get,EStateM.get,getThe,Sail.BitVec.slice]

theorem ret_branch_run (s : State) (v : ReturnConfig.Values)
 (cfg : ReturnConfig.Initialized s v) (enabled : v.v85 = true)

 (instr : s.regs.get? Register.__currentInstr = some (0xd65f03c0#32)) :
 (AArch64_ExecutingBROrBLROrRetInstr ()).run s = .ok true s := by
 have feature : HaveBTIExt () s = .ok true s := by
  simpa [EStateM.run,enabled] using ReturnConfig.haveBTI_run s v cfg

 simp [AArch64_ExecutingBROrBLROrRetInstr,feature,ThisInstr,undefined_bits_eq,readReg,instr,
  EStateM.run,Bind.bind,Pure.pure,EStateM.bind,EStateM.pure,
  MonadStateOf.get,MonadState.get,EStateM.get,getThe,Sail.BitVec.slice]

theorem ret_bti_run (s : State) (v : ReturnConfig.Values)
 (cfg : ReturnConfig.Initialized s v) (enabled : v.v85 = true)

 (instr : s.regs.get? Register.__currentInstr = some (0xd65f03c0#32)) :
 (AArch64_ExecutingBTIInstr ()).run s = .ok false s := by
 have feature : HaveBTIExt () s = .ok true s := by
  simpa [EStateM.run,enabled] using ReturnConfig.haveBTI_run s v cfg

 simp [AArch64_ExecutingBTIInstr,feature,ThisInstr,undefined_bits_eq,readReg,instr,
  EStateM.run,Bind.bind,Pure.pure,EStateM.bind,EStateM.pure,
  MonadStateOf.get,MonadState.get,EStateM.get,getThe,Sail.BitVec.slice]

/-- The exception callback is universally quantified and not invoked. All eager
control reads still occur, including compatibility and debug state. -/
theorem check_clear (b : Boundaries) (s : State) (v : ReturnConfig.Values)
 (cfg : ReturnConfig.Initialized s v) (enabled : v.v85 = true)
 (ps : ProcState) (mv : ReturnMode.Values) (mode : ReturnMode.Ready s ps mv)
 (guarded compatible : Bool) (ready : Ready s ps guarded compatible) :
 (BranchTargetCheck b ()).run s =
 (do
  let branch ← AArch64_ExecutingBROrBLROrRetInstr ()
  let bti ← AArch64_ExecutingBTIInstr ()
  if !(branch || bti) then writeReg Register.BTypeNext 0#2 else pure ()).run s := by
 have feature : HaveBTIExt () s = .ok true s := by
  simpa [EStateM.run,enabled] using ReturnConfig.haveBTI_run s v cfg
 have modeQuery : UsingAArch32 () s = .ok false s := ReturnMode.using_run s ps mv mode
 have debug : Halted () s = .ok false s := halted_running s ready.edscr
 simp [BranchTargetCheck,feature,modeQuery,debug,readReg,ready.pstate,ready.btype,
  ready.page,ready.compatible,PreSail.assert,EStateM.run,Bind.bind,Pure.pure,
  EStateM.bind,EStateM.pure,MonadStateOf.get,MonadState.get,EStateM.get,getThe,Sail.BitVec.slice]

theorem logical_check_run (b : Boundaries) (s : State) (v : ReturnConfig.Values)
 (cfg : ReturnConfig.Initialized s v) (enabled : v.v85 = true)
 (ps : ProcState) (mv : ReturnMode.Values) (mode : ReturnMode.Ready s ps mv)
 (guarded compatible : Bool) (ready : Ready s ps guarded compatible)
 (op : Oak.BitwiseFunction.Op)
 (instr : s.regs.get? Register.__currentInstr = some (ExtendedScalar.logicalWord (ExtendedScalar.externalOp op))) :
 (BranchTargetCheck b ()).run s = .ok () (put s .BTypeNext 0#2) := by
 rw [check_clear b s v cfg enabled ps mv mode guarded compatible ready]
 have hb := logical_branch_run s v cfg enabled op instr
 have ht := logical_bti_run s v cfg enabled op instr
 simp only [EStateM.run,Bind.bind,EStateM.bind] at hb ht ⊢
 rw [hb]
 dsimp only
 rw [ht]
 rfl

theorem ret_check_run (b : Boundaries) (s : State) (v : ReturnConfig.Values)
 (cfg : ReturnConfig.Initialized s v) (enabled : v.v85 = true)
 (ps : ProcState) (mv : ReturnMode.Values) (mode : ReturnMode.Ready s ps mv)
 (guarded compatible : Bool) (ready : Ready s ps guarded compatible)
 (instr : s.regs.get? Register.__currentInstr = some 0xd65f03c0#32) :
 (BranchTargetCheck b ()).run s = .ok () s := by
 rw [check_clear b s v cfg enabled ps mv mode guarded compatible ready]
 have hb := ret_branch_run s v cfg enabled instr
 have ht := ret_bti_run s v cfg enabled instr
 simp only [EStateM.run,Bind.bind,EStateM.bind] at hb ht ⊢
 rw [hb]
 dsimp only
 rw [ht]
 rfl

/-- The concrete enabled profile; no success equation for a callback occurs here. -/
structure Context (s : State) (ps : ProcState) (v : ReturnConfig.Values)
 (mv : ReturnMode.Values) (guarded compatible : Bool) : Prop where
 versions : ReturnConfig.Initialized s v
 mode : ReturnMode.Ready s ps mv
 control : Ready s ps guarded compatible
 enabled : v.v85 = true

def InstructionWrite : Register → Prop
 | .SEE | .__unconditional | ._R | .BTypeNext | .__currentInstr | ._PC | .__PC_changed => True
 | _ => False

theorem context_put (s : State) (ps : ProcState) (v : ReturnConfig.Values)
 (mv : ReturnMode.Values) (guarded compatible : Bool)
 (h : Context s ps v mv guarded compatible)
 (r : Register) (allowed : InstructionWrite r) (value : RegisterType r) :
 Context (put s r value) ps v mv guarded compatible := by
 rcases h with ⟨⟨v1,v2,v3,v4,v5⟩,⟨⟨m0,m1,m2,m3⟩,mh,mp,mn⟩,⟨cp,cb,cg,cc,cd⟩,ve⟩
 cases r <;> simp_all only [InstructionWrite]
 all_goals refine ⟨⟨?_,?_,?_,?_,?_⟩,⟨⟨?_,?_,?_,?_⟩,?_,?_,mn⟩,⟨?_,cb,?_,?_,?_⟩,ve⟩
 all_goals simp_all [put,Return.put,Std.ExtDHashMap.get?_insert]

def install (scalar : ScalarBoundaries) (returns : Boundaries) : ScalarBoundaries :=
 ConcreteReturn.install {scalar with BranchTargetCheck := BranchTargetCheck returns} returns

theorem postdecode_run (scalar : ScalarBoundaries) (returns : Boundaries)
 (s : State) (ps : ProcState) (v : ReturnConfig.Values) (mv : ReturnMode.Values)
 (guarded compatible : Bool) (h : Context s ps v mv guarded compatible) :
 (ReturnExecution.ScalarFunctions.__PostDecode (install scalar returns) ()).run s =
 (BranchTargetCheck returns ()).run s :=
 ConcreteReturn.postdecode_enabled_boundary _ returns s v h.versions h.enabled ps mv h.mode

/-- The harness loads the current word explicitly, then supplies the existing
SEE initializer and selected-clause dispatch. Fetch and full decode64 remain open. -/
def dispatch (scalar : ScalarBoundaries) (returns : Boundaries) (word : BitVec 32) : SailM Unit := do
 writeReg Register.__currentInstr word
 ExtendedScalar.dispatch (install scalar returns) word

def logicalControl (op : Oak.BitwiseFunction.Op) (s : State) : State :=
 ExtendedScalar.logicalControlState (ExtendedScalar.externalOp op)
  (put s .__currentInstr (ExtendedScalar.logicalWord (ExtendedScalar.externalOp op)))

def logicalFinal (op : Oak.BitwiseFunction.Op) (s : State) (bank : ExtendedScalar.Bank) : State :=
 put (put (logicalControl op s) .BTypeNext 0#2) ._R (ExtendedScalar.updatedBank (ExtendedScalar.externalOp op) bank)

theorem context_logical_control (s : State) (ps : ProcState) (v : ReturnConfig.Values)
 (mv : ReturnMode.Values) (guarded compatible : Bool) (h : Context s ps v mv guarded compatible)
 (op : Oak.BitwiseFunction.Op) : Context (logicalControl op s) ps v mv guarded compatible := by
 unfold logicalControl ExtendedScalar.logicalControlState
 apply context_put _ _ _ _ _ _ _ .__unconditional trivial
 apply context_put _ _ _ _ _ _ _ .SEE trivial
 apply context_put _ _ _ _ _ _ _ .SEE trivial
 exact context_put _ _ _ _ _ _ h .__currentInstr trivial _

theorem context_logical_final (s : State) (ps : ProcState) (v : ReturnConfig.Values)
 (mv : ReturnMode.Values) (guarded compatible : Bool) (h : Context s ps v mv guarded compatible)
 (op : Oak.BitwiseFunction.Op) (bank : ExtendedScalar.Bank) :
 Context (logicalFinal op s bank) ps v mv guarded compatible := by
 unfold logicalFinal
 apply context_put _ _ _ _ _ _ _ ._R trivial
 apply context_put _ _ _ _ _ _ _ .BTypeNext trivial
 exact context_logical_control s ps v mv guarded compatible h op

private theorem write_then {α : Type} (s : State) (r : Register)
 (value : RegisterType r) (next : SailM α) :
 (do writeReg r value; next).run s = next.run (put s r value) := rfl

theorem dispatch_logical (scalar : ScalarBoundaries) (returns : Boundaries)
 (s : State) (ps : ProcState) (v : ReturnConfig.Values) (mv : ReturnMode.Values)
 (guarded compatible : Bool) (h : Context s ps v mv guarded compatible)
 (bank : ExtendedScalar.Bank) (initialized : s.regs.get? Register._R = some bank)
 (op : Oak.BitwiseFunction.Op) :
 (dispatch scalar returns (ExtendedScalar.logicalWord (ExtendedScalar.externalOp op))).run s =
 .ok () (logicalFinal op s bank) := by
 unfold dispatch ExtendedScalar.dispatch
 rw [write_then,write_then,ExtendedScalar.selected_logical_dispatch _ _ (ExtendedScalar.externalOp op)
  (by simp [put,Return.put,ExtendedScalar.put,Std.ExtDHashMap.get?_insert])]
 rw [ExtendedScalar.logical_decode_factorization,write_then]
 change (do
  ReturnExecution.ScalarFunctions.__PostDecode (install scalar returns) ()
  ReturnExecution.ScalarFunctions.integer_logical_shiftedreg (install scalar returns) 0 32 false 1 0
   (ExtendedScalar.externalOp op) false 0 .ShiftType_LSL).run (logicalControl op s) = _
 have hc := context_logical_control s ps v mv guarded compatible h op
 have hp : (ReturnExecution.ScalarFunctions.__PostDecode (install scalar returns) ()).run
   (logicalControl op s) = .ok () (put (logicalControl op s) .BTypeNext 0#2) := by
  rw [postdecode_run scalar returns _ ps v mv guarded compatible hc]
  exact logical_check_run returns _ v hc.versions hc.enabled ps mv hc.mode guarded compatible hc.control op
   (by simp [logicalControl,ExtendedScalar.logicalControlState,put,Return.put,ExtendedScalar.put,Std.ExtDHashMap.get?_insert])
 have hb := ExtendedScalar.logical_body_run (install scalar returns)
  (put (logicalControl op s) .BTypeNext 0#2) bank
  (by simpa [logicalControl,ExtendedScalar.logicalControlState,put,Return.put,ExtendedScalar.put,Std.ExtDHashMap.get?_insert] using initialized)
  (ExtendedScalar.externalOp op)
 simp only [EStateM.run,Bind.bind,EStateM.bind] at hp hb ⊢
 rw [hp]
 exact hb

def retControl (s : State) : State := ExtendedScalar.retControlState (put s .__currentInstr 0xd65f03c0#32)

theorem context_ret_control (s : State) (ps : ProcState) (v : ReturnConfig.Values)
 (mv : ReturnMode.Values) (guarded compatible : Bool) (h : Context s ps v mv guarded compatible) :
 Context (retControl s) ps v mv guarded compatible := by
 unfold retControl ExtendedScalar.retControlState
 apply context_put _ _ _ _ _ _ _ .__unconditional trivial
 apply context_put _ _ _ _ _ _ _ .SEE trivial
 apply context_put _ _ _ _ _ _ _ .SEE trivial
 exact context_put _ _ _ _ _ _ h .__currentInstr trivial _

theorem dispatch_ret (scalar : ScalarBoundaries) (returns : Boundaries)
 (s : State) (ps : ProcState) (v : ReturnConfig.Values) (mv : ReturnMode.Values)
 (guarded compatible : Bool) (h : Context s ps v mv guarded compatible)
 (bank : ExtendedScalar.Bank) (initialized : s.regs.get? Register._R = some bank) :
 (dispatch scalar returns 0xd65f03c0#32).run s =
 (BranchTo returns bank[30] .BranchType_RET).run (put (retControl s) .BTypeNext 0#2) := by
 unfold dispatch ExtendedScalar.dispatch
 rw [write_then,write_then,ExtendedScalar.selected_ret_dispatch _ _
  (by simp [put,Return.put,ExtendedScalar.put,Std.ExtDHashMap.get?_insert])]
 rw [ExtendedScalar.ret_decode_factorization,write_then]
 change (do
  let _ ← (install scalar returns).HavePACExt ()
  ReturnExecution.ScalarFunctions.__PostDecode (install scalar returns) ()
  ReturnExecution.ScalarFunctions.branch_unconditional_register (install scalar returns)
   .BranchType_RET 0 30 false false true).run (retControl s) = _
 have hc := context_ret_control s ps v mv guarded compatible h
 have hp : (ReturnExecution.ScalarFunctions.__PostDecode (install scalar returns) ()).run
   (retControl s) = .ok () (retControl s) := by
  rw [postdecode_run scalar returns _ ps v mv guarded compatible hc]
  exact ret_check_run returns _ v hc.versions hc.enabled ps mv hc.mode guarded compatible hc.control
   (by simp [retControl,ExtendedScalar.retControlState,put,Return.put,ExtendedScalar.put,Std.ExtDHashMap.get?_insert])
 have pac : ((install scalar returns).HavePACExt ()).run (retControl s) = .ok v.v83 (retControl s) :=
  ReturnConfig.havePAC_run _ v hc.versions
 have hb := ExtendedScalar.ret_body_factorization (install scalar returns) (retControl s) bank
  (by simpa [retControl,ExtendedScalar.retControlState,put,Return.put,ExtendedScalar.put,Std.ExtDHashMap.get?_insert] using initialized)
 simp only [EStateM.run,Bind.bind,EStateM.bind] at pac hp hb ⊢
 rw [pac]
 dsimp only
 rw [hp]
 exact hb

end Oak.SailBridge.ReturnBTI
