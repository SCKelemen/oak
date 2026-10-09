import ReturnBTIExecution
namespace Oak.SailBridge.ReturnBTIControls
open ReturnExecution ReturnExecution.Functions Sail PreSail
open Oak.SailBridge ReturnBTI
set_option linter.unusedSimpArgs false
abbrev State := ReturnConfig.State

def initialized (s : State) (ps : ProcState) (guarded compatible : Bool) : State :=
 withControl (ReturnMode.withValues (ReturnConfig.withValues s {}) ps {})
  {ps with nRW := 0} guarded compatible

theorem initialized_context (s : State) (ps : ProcState) (guarded compatible : Bool) :
 Context (initialized s ps guarded compatible) {ps with nRW := 0, BTYPE := 0} {} {} guarded compatible := by
 refine ⟨⟨?_,?_,?_,?_,?_⟩,⟨⟨?_,?_,?_,?_⟩,?_,?_,rfl⟩,⟨?_,rfl,?_,?_,?_⟩,rfl⟩
 all_goals simp [initialized,withControl,ReturnMode.withValues,ReturnConfig.withValues,
  put,Return.put,Std.ExtDHashMap.get?_insert]

/-- Both page classes admit the enabled profile; neither requires debug halt. -/
theorem both_page_profiles (s : State) (ps : ProcState) :
 Context (initialized s ps false false) {ps with nRW := 0, BTYPE := 0} {} {} false false ∧
 Context (initialized s ps true false) {ps with nRW := 0, BTYPE := 0} {} {} true false :=
 ⟨initialized_context s ps false false, initialized_context s ps true false⟩

def afterCheck : SailM Unit := do
 let branch ← AArch64_ExecutingBROrBLROrRetInstr ()
 let bti ← AArch64_ExecutingBTIInstr ()
 if !(branch || bti) then writeReg Register.BTypeNext 0#2 else pure ()

/-- Outside BTYPE=00, retain the actual exception callback and every subsequent
read/write. A successful state-changing callback is not treated as a no-op. -/
theorem exception_path (b : Boundaries) (s : State) (v : ReturnConfig.Values)
 (cfg : ReturnConfig.Initialized s v) (enabled : v.v85 = true)
 (ps : ProcState) (mv : ReturnMode.Values) (mode : ReturnMode.Ready s ps mv)
 (pstate : s.regs.get? Register.PSTATE = some ps) (btype : ps.BTYPE ≠ 0#2)
 (page : s.regs.get? Register.InGuardedPage = some true)
 (compatible : s.regs.get? Register.BTypeCompatible = some false)
 (debug : s.regs.get? Register.EDSCR = some 1#32)
 (pc : BitVec 64) (pcRead : s.regs.get? Register._PC = some pc) :
 (BranchTargetCheck b ()).run s =
 (do b.AArch64_BranchTargetException (pc.extractLsb' 0 52); afterCheck).run s := by
 have feature : HaveBTIExt () s = .ok true s := by
  simpa [EStateM.run,enabled] using ReturnConfig.haveBTI_run s v cfg
 have modeQuery : UsingAArch32 () s = .ok false s := ReturnMode.using_run s ps mv mode
 have halted : Halted () s = .ok false s := halted_running s debug
 simp [BranchTargetCheck,afterCheck,feature,modeQuery,halted,readReg,pstate,btype,page,
  compatible,ThisInstrAddr,pcRead,Sail.BitVec.slice,PreSail.assert,EStateM.run,Bind.bind,
  Pure.pure,EStateM.bind,EStateM.pure,MonadStateOf.get,MonadState.get,EStateM.get,getThe]

/-- The complete exception result is bound, so failure preserves its exact state. -/
theorem exception_failure (b : Boundaries) (s after : State) (pc : BitVec 64)
 (err : Sail.Error ReturnExecution.exception)
 (failure : (b.AArch64_BranchTargetException (pc.extractLsb' 0 52)).run s = .error err after) :
 (do b.AArch64_BranchTargetException (pc.extractLsb' 0 52); afterCheck).run s = .error err after := by
 simp only [EStateM.run,Bind.bind,EStateM.bind] at failure ⊢
 rw [failure]

theorem exception_success_state (b : Boundaries) (s after : State) (pc : BitVec 64)
 (success : (b.AArch64_BranchTargetException (pc.extractLsb' 0 52)).run s = .ok () after) :
 (do b.AArch64_BranchTargetException (pc.extractLsb' 0 52); afterCheck).run s = afterCheck.run after := by
 simp only [EStateM.run,Bind.bind,EStateM.bind] at success ⊢
 rw [success]

theorem missing_guarded_page (b : Boundaries) (s : State) (v : ReturnConfig.Values)
 (cfg : ReturnConfig.Initialized s v) (enabled : v.v85 = true)
 (ps : ProcState) (mv : ReturnMode.Values) (mode : ReturnMode.Ready s ps mv)
 (missing : s.regs.get? Register.InGuardedPage = none) :
 (BranchTargetCheck b ()).run s = .error .Unreachable s := by
 have feature : HaveBTIExt () s = .ok true s := by
  simpa [EStateM.run,enabled] using ReturnConfig.haveBTI_run s v cfg
 have modeQuery : UsingAArch32 () s = .ok false s := ReturnMode.using_run s ps mv mode
 simp [BranchTargetCheck,feature,modeQuery,readReg,mode.pstate,missing,Halted,
  PreSail.assert,EStateM.run,Bind.bind,Pure.pure,EStateM.bind,EStateM.pure,
  MonadStateOf.get,MonadState.get,EStateM.get,getThe,throw,throwThe,MonadExceptOf.throw,EStateM.throw]

theorem missing_compatibility (b : Boundaries) (s : State) (v : ReturnConfig.Values)
 (cfg : ReturnConfig.Initialized s v) (enabled : v.v85 = true)
 (ps : ProcState) (mv : ReturnMode.Values) (mode : ReturnMode.Ready s ps mv)
 (guarded : Bool) (page : s.regs.get? Register.InGuardedPage = some guarded)
 (missing : s.regs.get? Register.BTypeCompatible = none) :
 (BranchTargetCheck b ()).run s = .error .Unreachable s := by
 have feature : HaveBTIExt () s = .ok true s := by
  simpa [EStateM.run,enabled] using ReturnConfig.haveBTI_run s v cfg
 have modeQuery : UsingAArch32 () s = .ok false s := ReturnMode.using_run s ps mv mode
 simp [BranchTargetCheck,feature,modeQuery,readReg,mode.pstate,missing,Halted,page,
  PreSail.assert,EStateM.run,Bind.bind,Pure.pure,EStateM.bind,EStateM.pure,
  MonadStateOf.get,MonadState.get,EStateM.get,getThe,throw,throwThe,MonadExceptOf.throw,EStateM.throw]

theorem missing_debug (b : Boundaries) (s : State) (v : ReturnConfig.Values)
 (cfg : ReturnConfig.Initialized s v) (enabled : v.v85 = true)
 (ps : ProcState) (mv : ReturnMode.Values) (mode : ReturnMode.Ready s ps mv)
 (guarded compatible : Bool) (page : s.regs.get? Register.InGuardedPage = some guarded)
 (compat : s.regs.get? Register.BTypeCompatible = some compatible)
 (missing : s.regs.get? Register.EDSCR = none) :
 (BranchTargetCheck b ()).run s = .error .Unreachable s := by
 have feature : HaveBTIExt () s = .ok true s := by
  simpa [EStateM.run,enabled] using ReturnConfig.haveBTI_run s v cfg
 have modeQuery : UsingAArch32 () s = .ok false s := ReturnMode.using_run s ps mv mode
 simp [BranchTargetCheck,feature,modeQuery,readReg,mode.pstate,missing,Halted,page,compat,
  PreSail.assert,EStateM.run,Bind.bind,Pure.pure,EStateM.bind,EStateM.pure,
  MonadStateOf.get,MonadState.get,EStateM.get,getThe,throw,throwThe,MonadExceptOf.throw,EStateM.throw]

theorem missing_current_instruction (b : Boundaries) (s : State)
 (ps : ProcState) (v : ReturnConfig.Values) (mv : ReturnMode.Values)
 (guarded compatible : Bool) (h : Context s ps v mv guarded compatible)
 (missing : s.regs.get? Register.__currentInstr = none) :
 (BranchTargetCheck b ()).run s = .error .Unreachable s := by
 rw [check_clear b s v h.versions h.enabled ps mv h.mode guarded compatible h.control]
 have feature : HaveBTIExt () s = .ok true s := by
  simpa [EStateM.run,h.enabled] using ReturnConfig.haveBTI_run s v h.versions
 simp [AArch64_ExecutingBROrBLROrRetInstr,feature,ThisInstr,readReg,missing,
  EStateM.run,Bind.bind,Pure.pure,EStateM.bind,EStateM.pure,
  MonadStateOf.get,MonadState.get,EStateM.get,getThe,throw,throwThe,MonadExceptOf.throw,EStateM.throw]

def initial (s : State) (ps : ProcState) (bank : ExtendedScalar.Bank) (guarded : Bool) : State :=
 initialized (put (put (ReturnELMode.withValues s) .TCR_EL1 0#64) ._R bank) {ps with EL := 1} guarded false

/-- A constructive full enabled profile for every operand bank and both page
classes. This is initialization by the harness, not a reset-reachability claim. -/
theorem initial_admits (s : State) (ps : ProcState) (bank : ExtendedScalar.Bank) (guarded : Bool) :
 Context (initial s ps bank guarded) {ps with EL := 1, nRW := 0, BTYPE := 0} {} {} guarded false ∧
 Nonempty (ReturnELMode.Ready (initial s ps bank guarded)) ∧
 (initial s ps bank guarded).regs.get? Register._R = some bank ∧
 (initial s ps bank guarded).regs.get? Register.TCR_EL1 = some 0#64 := by
 refine ⟨initialized_context _ _ _ _, ?_, ?_, ?_⟩
 · refine ⟨⟨⟨?_,?_,?_,?_⟩,?_,1024,?_,by decide,2147483648,?_,by decide⟩⟩
   all_goals simp [initial,initialized,withControl,ReturnMode.withValues,ReturnConfig.withValues,
    ReturnELMode.withValues,put,Return.put,Std.ExtDHashMap.get?_insert]
 all_goals simp [initial,initialized,withControl,ReturnMode.withValues,ReturnConfig.withValues,
  ReturnELMode.withValues,put,Return.put,Std.ExtDHashMap.get?_insert]

theorem hostile_exception_unreachable (b : Boundaries) (s after : State)
 (ps : ProcState) (v : ReturnConfig.Values) (mv : ReturnMode.Values)
 (guarded compatible : Bool) (h : Context s ps v mv guarded compatible)
 (op : Oak.BitwiseFunction.Op)
 (instr : s.regs.get? Register.__currentInstr = some (ExtendedScalar.logicalWord (ExtendedScalar.externalOp op)))
 (err : Sail.Error ReturnExecution.exception) :
 (BranchTargetCheck {b with AArch64_BranchTargetException := fun _ _ => .error err after} ()).run s =
 .ok () (put s .BTypeNext 0#2) :=
 logical_check_run _ s v h.versions h.enabled ps mv h.mode guarded compatible h.control op instr

theorem guarded_exception_failure (b : Boundaries) (s after : State) (v : ReturnConfig.Values)
 (cfg : ReturnConfig.Initialized s v) (enabled : v.v85 = true)
 (ps : ProcState) (mv : ReturnMode.Values) (mode : ReturnMode.Ready s ps mv)
 (pstate : s.regs.get? Register.PSTATE = some ps) (btype : ps.BTYPE ≠ 0#2)
 (page : s.regs.get? Register.InGuardedPage = some true)
 (compatible : s.regs.get? Register.BTypeCompatible = some false)
 (debug : s.regs.get? Register.EDSCR = some 1#32)
 (pc : BitVec 64) (pcRead : s.regs.get? Register._PC = some pc)
 (err : Sail.Error ReturnExecution.exception)
 (failure : (b.AArch64_BranchTargetException (pc.extractLsb' 0 52)).run s = .error err after) :
 (BranchTargetCheck b ()).run s = .error err after := by
 rw [exception_path b s v cfg enabled ps mv mode pstate btype page compatible debug pc pcRead]
 exact exception_failure b s after pc err failure

theorem guarded_exception_success_state (b : Boundaries) (s after : State) (v : ReturnConfig.Values)
 (cfg : ReturnConfig.Initialized s v) (enabled : v.v85 = true)
 (ps : ProcState) (mv : ReturnMode.Values) (mode : ReturnMode.Ready s ps mv)
 (pstate : s.regs.get? Register.PSTATE = some ps) (btype : ps.BTYPE ≠ 0#2)
 (page : s.regs.get? Register.InGuardedPage = some true)
 (compatible : s.regs.get? Register.BTypeCompatible = some false)
 (debug : s.regs.get? Register.EDSCR = some 1#32)
 (pc : BitVec 64) (pcRead : s.regs.get? Register._PC = some pc)
 (success : (b.AArch64_BranchTargetException (pc.extractLsb' 0 52)).run s = .ok () after) :
 (BranchTargetCheck b ()).run s = afterCheck.run after := by
 rw [exception_path b s v cfg enabled ps mv mode pstate btype page compatible debug pc pcRead]
 exact exception_success_state b s after pc success

theorem missing_version (b : Boundaries) (s : State)
 (missing : s.regs.get? Register.__v81_implemented = none) :
 (BranchTargetCheck b ()).run s = .error .Unreachable s := by
 have feature : HaveBTIExt () s = .error .Unreachable s := by
  simp [HaveBTIExt,HasArchVersion,readReg,missing,EStateM.run,Bind.bind,Pure.pure,
   EStateM.bind,EStateM.pure,MonadStateOf.get,MonadState.get,EStateM.get,getThe,
   throw,throwThe,MonadExceptOf.throw,EStateM.throw]
 simp [BranchTargetCheck,feature,EStateM.run,Bind.bind,EStateM.bind]

theorem missing_pstate (b : Boundaries) (s : State) (v : ReturnConfig.Values)
 (cfg : ReturnConfig.Initialized s v) (enabled : v.v85 = true)
 (missing : s.regs.get? Register.PSTATE = none) :
 (BranchTargetCheck b ()).run s = .error .Unreachable s := by
 have feature : HaveBTIExt () s = .ok true s := by
  simpa [EStateM.run,enabled] using ReturnConfig.haveBTI_run s v cfg
 have modeQuery : UsingAArch32 () s = .error .Unreachable s := ReturnMode.missing_pstate s missing
 simp [BranchTargetCheck,feature,modeQuery,EStateM.run,Bind.bind,EStateM.bind]

private theorem write_then {α : Type} (s : State) (r : Register)
 (value : RegisterType r) (next : SailM α) :
 (do writeReg r value; next).run s = next.run (put s r value) := rfl

/-- A failing first feature read retains current-word, SEE and unconditional
writes already performed by this exact dispatch. No register bank is read. -/
theorem logical_dispatch_missing_version (scalar : ScalarBoundaries) (returns : Boundaries)
 (s : State) (op : Oak.BitwiseFunction.Op)
 (missing : s.regs.get? Register.__v81_implemented = none) :
 (dispatch scalar returns (ExtendedScalar.logicalWord (ExtendedScalar.externalOp op))).run s =
 .error .Unreachable (logicalControl op s) := by
 unfold dispatch ExtendedScalar.dispatch
 rw [write_then,write_then,ExtendedScalar.selected_logical_dispatch _ _ (ExtendedScalar.externalOp op)
  (by simp [put,Return.put,ExtendedScalar.put,Std.ExtDHashMap.get?_insert])]
 rw [ExtendedScalar.logical_decode_factorization,write_then]
 change (do
  ReturnExecution.ScalarFunctions.__PostDecode (install scalar returns) ()
  ReturnExecution.ScalarFunctions.integer_logical_shiftedreg (install scalar returns) 0 32 false 1 0
   (ExtendedScalar.externalOp op) false 0 .ShiftType_LSL).run (logicalControl op s) = _
 simp [ReturnExecution.ScalarFunctions.__PostDecode,install,ConcreteReturn.install,
  HaveBTIExt,HasArchVersion,readReg,logicalControl,ExtendedScalar.logicalControlState,
  put,Return.put,ExtendedScalar.put,Std.ExtDHashMap.get?_insert,missing,
  EStateM.run,Bind.bind,Pure.pure,EStateM.bind,EStateM.pure,
  MonadStateOf.get,MonadState.get,EStateM.get,getThe,throw,throwThe,MonadExceptOf.throw,EStateM.throw]

end Oak.SailBridge.ReturnBTIControls
