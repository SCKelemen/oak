import ReturnExecutionBridge
import ReturnScalarBridge
namespace Oak.SailBridge.ConcreteReturn
open ReturnExecution Sail PreSail
abbrev State := Oak.SailBridge.Return.State

def install (scalar : ScalarBoundaries) (returns : Boundaries) : ScalarBoundaries :=
 {scalar with
  UsingAArch32 := ReturnExecution.Functions.UsingAArch32
  HavePACExt := ReturnExecution.Functions.HavePACExt
  BranchTo := fun target kind => ReturnExecution.Functions.BranchTo returns target kind}

def finalState (op : Oak.BitwiseFunction.Op) (s : State) (bank : Oak.SailBridge.ExtendedScalar.Bank) : State :=
 Oak.SailBridge.Return.put (Oak.SailBridge.Return.put (Oak.SailBridge.ExtendedScalar.requestState op s bank) ._PC bank[30]) .__PC_changed true

private theorem quiet (scalar : ScalarBoundaries) (returns : Boundaries)
 (bti : scalar.HaveBTIExt () = pure false) (s : State)
 (ps : ProcState) (mv : ReturnMode.Values) (h : ReturnMode.Ready s ps mv) :
 Oak.SailBridge.ExtendedScalar.QuietControl (install scalar returns) s := by
 constructor
 · simp [install, bti, EStateM.run, Pure.pure, EStateM.pure]
 · exact ReturnMode.using_run s ps mv h

/-- These actual instruction updates touch no architectural-version register. -/
theorem versions_after_ret_control (op : Oak.BitwiseFunction.Op) (s : State)
 (bank : Oak.SailBridge.ExtendedScalar.Bank) (v : ReturnConfig.Values)
 (h : ReturnConfig.Initialized s v) :
 ReturnConfig.Initialized (Oak.SailBridge.ExtendedScalar.retControlState
  (Oak.SailBridge.ExtendedScalar.afterLogical (Oak.SailBridge.ExtendedScalar.externalOp op) s bank)) v := by
 rcases h with ⟨h1,h2,h3,h4,h5⟩
 constructor <;> simp_all [Oak.SailBridge.ExtendedScalar.retControlState,
 Oak.SailBridge.ExtendedScalar.afterLogical, Oak.SailBridge.ExtendedScalar.logicalControlState,
 Oak.SailBridge.ExtendedScalar.put, Std.ExtDHashMap.get?_insert]

theorem versions_after_request (op : Oak.BitwiseFunction.Op) (s : State)
 (bank : Oak.SailBridge.ExtendedScalar.Bank) (v : ReturnConfig.Values)
 (h : ReturnConfig.Initialized s v) :
 ReturnConfig.Initialized (Oak.SailBridge.ExtendedScalar.requestState op s bank) v := by
 rcases h with ⟨h1,h2,h3,h4,h5⟩
 constructor <;> simp_all [Oak.SailBridge.ExtendedScalar.requestState,
 Oak.SailBridge.ExtendedScalar.retControlState, Oak.SailBridge.ExtendedScalar.afterLogical,
 Oak.SailBridge.ExtendedScalar.logicalControlState, Oak.SailBridge.ExtendedScalar.put,
 Std.ExtDHashMap.get?_insert]

theorem versions_after_return (op : Oak.BitwiseFunction.Op) (s : State)
 (bank : Oak.SailBridge.ExtendedScalar.Bank) (v : ReturnConfig.Values)
 (h : ReturnConfig.Initialized s v) :
 ReturnConfig.Initialized (finalState op s bank) v := by
 rcases versions_after_request op s bank v h with ⟨h1,h2,h3,h4,h5⟩
 constructor <;> simp_all [finalState, Oak.SailBridge.Return.put, Std.ExtDHashMap.get?_insert]

theorem mode_after_logical_control (op : Oak.BitwiseFunction.Op) (s : State)
 (bank : Oak.SailBridge.ExtendedScalar.Bank) (ps : ProcState) (v : ReturnMode.Values)
 (h : ReturnMode.Ready s ps v) : ReturnMode.Ready (Oak.SailBridge.ExtendedScalar.logicalControlState (Oak.SailBridge.ExtendedScalar.externalOp op) s) ps v := by
 rcases h with ⟨⟨h0,h1,h2,h3⟩,hh,hp,hn⟩
 constructor
 · constructor <;> simp_all [finalState, Oak.SailBridge.Return.put,
     Oak.SailBridge.ExtendedScalar.requestState, Oak.SailBridge.ExtendedScalar.retControlState,
     Oak.SailBridge.ExtendedScalar.afterLogical, Oak.SailBridge.ExtendedScalar.logicalControlState,
     Oak.SailBridge.ExtendedScalar.put, Std.ExtDHashMap.get?_insert]
 all_goals simp_all [finalState, Oak.SailBridge.Return.put,
     Oak.SailBridge.ExtendedScalar.requestState, Oak.SailBridge.ExtendedScalar.retControlState,
     Oak.SailBridge.ExtendedScalar.afterLogical, Oak.SailBridge.ExtendedScalar.logicalControlState,
     Oak.SailBridge.ExtendedScalar.put, Std.ExtDHashMap.get?_insert]

theorem mode_after_ret_control (op : Oak.BitwiseFunction.Op) (s : State)
 (bank : Oak.SailBridge.ExtendedScalar.Bank) (ps : ProcState) (v : ReturnMode.Values)
 (h : ReturnMode.Ready s ps v) : ReturnMode.Ready (Oak.SailBridge.ExtendedScalar.retControlState (Oak.SailBridge.ExtendedScalar.afterLogical (Oak.SailBridge.ExtendedScalar.externalOp op) s bank)) ps v := by
 rcases h with ⟨⟨h0,h1,h2,h3⟩,hh,hp,hn⟩
 constructor
 · constructor <;> simp_all [finalState, Oak.SailBridge.Return.put,
     Oak.SailBridge.ExtendedScalar.requestState, Oak.SailBridge.ExtendedScalar.retControlState,
     Oak.SailBridge.ExtendedScalar.afterLogical, Oak.SailBridge.ExtendedScalar.logicalControlState,
     Oak.SailBridge.ExtendedScalar.put, Std.ExtDHashMap.get?_insert]
 all_goals simp_all [finalState, Oak.SailBridge.Return.put,
     Oak.SailBridge.ExtendedScalar.requestState, Oak.SailBridge.ExtendedScalar.retControlState,
     Oak.SailBridge.ExtendedScalar.afterLogical, Oak.SailBridge.ExtendedScalar.logicalControlState,
     Oak.SailBridge.ExtendedScalar.put, Std.ExtDHashMap.get?_insert]

theorem mode_after_request (op : Oak.BitwiseFunction.Op) (s : State)
 (bank : Oak.SailBridge.ExtendedScalar.Bank) (ps : ProcState) (v : ReturnMode.Values)
 (h : ReturnMode.Ready s ps v) : ReturnMode.Ready (Oak.SailBridge.ExtendedScalar.requestState op s bank) ps v := by
 rcases h with ⟨⟨h0,h1,h2,h3⟩,hh,hp,hn⟩
 constructor
 · constructor <;> simp_all [finalState, Oak.SailBridge.Return.put,
     Oak.SailBridge.ExtendedScalar.requestState, Oak.SailBridge.ExtendedScalar.retControlState,
     Oak.SailBridge.ExtendedScalar.afterLogical, Oak.SailBridge.ExtendedScalar.logicalControlState,
     Oak.SailBridge.ExtendedScalar.put, Std.ExtDHashMap.get?_insert]
 all_goals simp_all [finalState, Oak.SailBridge.Return.put,
     Oak.SailBridge.ExtendedScalar.requestState, Oak.SailBridge.ExtendedScalar.retControlState,
     Oak.SailBridge.ExtendedScalar.afterLogical, Oak.SailBridge.ExtendedScalar.logicalControlState,
     Oak.SailBridge.ExtendedScalar.put, Std.ExtDHashMap.get?_insert]

theorem mode_after_return (op : Oak.BitwiseFunction.Op) (s : State)
 (bank : Oak.SailBridge.ExtendedScalar.Bank) (ps : ProcState) (v : ReturnMode.Values)
 (h : ReturnMode.Ready s ps v) : ReturnMode.Ready (finalState op s bank) ps v := by
 rcases h with ⟨⟨h0,h1,h2,h3⟩,hh,hp,hn⟩
 constructor
 · constructor <;> simp_all [finalState, Oak.SailBridge.Return.put,
     Oak.SailBridge.ExtendedScalar.requestState, Oak.SailBridge.ExtendedScalar.retControlState,
     Oak.SailBridge.ExtendedScalar.afterLogical, Oak.SailBridge.ExtendedScalar.logicalControlState,
     Oak.SailBridge.ExtendedScalar.put, Std.ExtDHashMap.get?_insert]
 all_goals simp_all [finalState, Oak.SailBridge.Return.put,
     Oak.SailBridge.ExtendedScalar.requestState, Oak.SailBridge.ExtendedScalar.retControlState,
     Oak.SailBridge.ExtendedScalar.afterLogical, Oak.SailBridge.ExtendedScalar.logicalControlState,
     Oak.SailBridge.ExtendedScalar.put, Std.ExtDHashMap.get?_insert]

def elMode_after_request (op : Oak.BitwiseFunction.Op) (s : State)
 (bank : Oak.SailBridge.ExtendedScalar.Bank) (h : ReturnELMode.Ready s) :
 ReturnELMode.Ready (Oak.SailBridge.ExtendedScalar.requestState op s bank) := by
 rcases h with ⟨⟨c0,c1,c2,c3⟩,hi,sv,sr,srw,hv,hr,hrw⟩
 refine ⟨?_,?_,sv,?_,srw,hv,?_,hrw⟩
 · constructor <;> simp_all [finalState, Oak.SailBridge.Return.put,
     Oak.SailBridge.ExtendedScalar.requestState, Oak.SailBridge.ExtendedScalar.retControlState,
     Oak.SailBridge.ExtendedScalar.afterLogical, Oak.SailBridge.ExtendedScalar.logicalControlState,
     Oak.SailBridge.ExtendedScalar.put, Std.ExtDHashMap.get?_insert]
 all_goals simp_all [finalState, Oak.SailBridge.Return.put,
     Oak.SailBridge.ExtendedScalar.requestState, Oak.SailBridge.ExtendedScalar.retControlState,
     Oak.SailBridge.ExtendedScalar.afterLogical, Oak.SailBridge.ExtendedScalar.logicalControlState,
     Oak.SailBridge.ExtendedScalar.put, Std.ExtDHashMap.get?_insert]

def elMode_after_return (op : Oak.BitwiseFunction.Op) (s : State)
 (bank : Oak.SailBridge.ExtendedScalar.Bank) (h : ReturnELMode.Ready s) :
 ReturnELMode.Ready (finalState op s bank) := by
 rcases h with ⟨⟨c0,c1,c2,c3⟩,hi,sv,sr,srw,hv,hr,hrw⟩
 refine ⟨?_,?_,sv,?_,srw,hv,?_,hrw⟩
 · constructor <;> simp_all [finalState, Oak.SailBridge.Return.put,
     Oak.SailBridge.ExtendedScalar.requestState, Oak.SailBridge.ExtendedScalar.retControlState,
     Oak.SailBridge.ExtendedScalar.afterLogical, Oak.SailBridge.ExtendedScalar.logicalControlState,
     Oak.SailBridge.ExtendedScalar.put, Std.ExtDHashMap.get?_insert]
 all_goals simp_all [finalState, Oak.SailBridge.Return.put,
     Oak.SailBridge.ExtendedScalar.requestState, Oak.SailBridge.ExtendedScalar.retControlState,
     Oak.SailBridge.ExtendedScalar.afterLogical, Oak.SailBridge.ExtendedScalar.logicalControlState,
     Oak.SailBridge.ExtendedScalar.put, Std.ExtDHashMap.get?_insert]

theorem elMode_final_ready (op : Oak.BitwiseFunction.Op) (s : State)
 (bank : Oak.SailBridge.ExtendedScalar.Bank) (h : ReturnELMode.Ready s) :
 Nonempty (ReturnELMode.Ready (finalState op s bank)) := ⟨elMode_after_return op s bank h⟩

theorem exact_bytes_return (scalar : ScalarBoundaries) (returns : Boundaries)
 (bti : scalar.HaveBTIExt () = pure false)
 (s : State) (bank : Oak.SailBridge.ExtendedScalar.Bank) (op : Oak.BitwiseFunction.Op)
 (versions : ReturnConfig.Values) (config : ReturnConfig.Initialized s versions)
 (elMode : ReturnELMode.Ready s)
 (initialized : s.regs.get? ReturnExecution.Register._R = some bank)
 (ps : ProcState) (modeValues : ReturnMode.Values) (mode : ReturnMode.Ready s ps modeValues)
 (pstate : s.regs.get? ReturnExecution.Register.PSTATE = some ps)
 (el : ps.EL = ReturnExecution.Functions.EL1)
 (tcr : s.regs.get? ReturnExecution.Register.TCR_EL1 = some (0 : BitVec 64)) :
 (Oak.SailBridge.ExtendedScalar.executeBytes (install scalar returns) (Oak.AArch64BitwiseFunction.functionBytes op)).run s =
 .ok () (finalState op s bank) := by
 rw [Oak.SailBridge.ExtendedScalar.function_bytes_to_return_request (install scalar returns) s bank op initialized
  (quiet scalar returns bti _ ps modeValues (mode_after_logical_control op s bank ps modeValues mode))
  (quiet scalar returns bti _ ps modeValues (mode_after_ret_control op s bank ps modeValues mode)) versions.v83
  (ReturnConfig.havePAC_run _ versions (versions_after_ret_control op s bank versions config))]
 change (ReturnExecution.Functions.BranchTo returns bank[30] .BranchType_RET).run
  (Oak.SailBridge.ExtendedScalar.requestState op s bank) = _
 exact Oak.SailBridge.Return.branchTo64_el1_no_tags returns (Oak.SailBridge.ExtendedScalar.requestState op s bank) versions (versions_after_request op s bank versions config) (elMode_after_request op s bank elMode) ps modeValues (mode_after_request op s bank ps modeValues mode)
  (by simpa [Oak.SailBridge.ExtendedScalar.requestState, Oak.SailBridge.ExtendedScalar.retControlState, Oak.SailBridge.ExtendedScalar.afterLogical, Oak.SailBridge.ExtendedScalar.logicalControlState, Oak.SailBridge.ExtendedScalar.put, Std.ExtDHashMap.get?_insert] using pstate) el
  (by simpa [Oak.SailBridge.ExtendedScalar.requestState, Oak.SailBridge.ExtendedScalar.retControlState, Oak.SailBridge.ExtendedScalar.afterLogical, Oak.SailBridge.ExtendedScalar.logicalControlState, Oak.SailBridge.ExtendedScalar.put, Std.ExtDHashMap.get?_insert] using tcr) bank[30] .BranchType_RET

/-- The real RET decoder keeps its preceding control write when the eager
configuration read fails; installing the concrete query does not hide faults. -/
theorem ret_missing_version (scalar : ScalarBoundaries) (returns : Boundaries)
 (s : State) (missing : s.regs.get? Register.__v81_implemented = none) :
 (ReturnExecution.ScalarFunctions.branch_unconditional_register_decode
   (install scalar returns) 0#5 30#5 0#1 0#1 31#5 2#2 0#1).run s =
 .error .Unreachable (Oak.SailBridge.ExtendedScalar.put s .__unconditional true) := by
 apply Oak.SailBridge.ExtendedScalar.ret_eager_pac_failure
 exact ReturnConfig.missing_v81 _ (by
  simpa [Oak.SailBridge.ExtendedScalar.put, Std.ExtDHashMap.get?_insert] using missing)

/-- BTI=false does not erase the exported PostDecode's eager concrete mode read. -/
theorem postdecode_missing_pstate (scalar : ScalarBoundaries) (returns : Boundaries)
 (s : State) (bti : (scalar.HaveBTIExt ()).run s = .ok false s)
 (missing : s.regs.get? Register.PSTATE = none) :
 (ReturnExecution.ScalarFunctions.__PostDecode (install scalar returns) ()).run s =
 .error .Unreachable s := by
 exact Oak.SailBridge.ExtendedScalar.postdecode_eager_failure _ s s .Unreachable bti
  (ReturnMode.missing_pstate s missing)

theorem final_observations (op : Oak.BitwiseFunction.Op) (s : State) (bank : Oak.SailBridge.ExtendedScalar.Bank) :
 (finalState op s bank).regs.get? ReturnExecution.Register._PC = some bank[30] ∧
 (finalState op s bank).regs.get? ReturnExecution.Register.__PC_changed = some true ∧
 (finalState op s bank).regs.get? ReturnExecution.Register._R = some (Oak.SailBridge.ExtendedScalar.updatedBank (Oak.SailBridge.ExtendedScalar.externalOp op) bank) ∧
 (finalState op s bank).mem = s.mem ∧ (finalState op s bank).tags = s.tags := by
 simp [finalState, Oak.SailBridge.Return.put, Oak.SailBridge.ExtendedScalar.requestState, Oak.SailBridge.ExtendedScalar.retControlState, Oak.SailBridge.ExtendedScalar.afterLogical,
 Oak.SailBridge.ExtendedScalar.logicalControlState, Oak.SailBridge.ExtendedScalar.put, Std.ExtDHashMap.get?_insert]

/-- Alignment is an ABI/future-fetch premise, not a hidden BranchTo check. -/
theorem aligned_return_observation (op : Oak.BitwiseFunction.Op) (s : State)
 (bank : Oak.SailBridge.ExtendedScalar.Bank) (aligned : bank[30].toNat % 4 = 0) :
 ∃ pc : BitVec 64, (finalState op s bank).regs.get? ReturnExecution.Register._PC = some pc ∧
 pc.toNat % 4 = 0 := ⟨bank[30], (final_observations op s bank).1, aligned⟩

#print axioms exact_bytes_return
#print axioms final_observations
end Oak.SailBridge.ConcreteReturn
