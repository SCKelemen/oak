import ReturnExecutionBridge
import ReturnScalarBridge
namespace Oak.SailBridge.ConcreteReturn
open ReturnExecution Sail PreSail
abbrev State := Oak.SailBridge.Return.State

def install (scalar : ScalarBoundaries) (returns : Boundaries) : ScalarBoundaries :=
 {scalar with
  UsingAArch32 := returns.UsingAArch32
  HavePACExt := returns.HavePACExt
  BranchTo := fun target kind => ReturnExecution.Functions.BranchTo returns target kind}

def finalState (op : Oak.BitwiseFunction.Op) (s : State) (bank : Oak.SailBridge.ExtendedScalar.Bank) : State :=
 Oak.SailBridge.Return.put (Oak.SailBridge.Return.put (Oak.SailBridge.ExtendedScalar.requestState op s bank) ._PC bank[30]) .__PC_changed true

private theorem quiet (scalar : ScalarBoundaries) (returns : Boundaries)
 (q : Oak.SailBridge.Return.QueryProfile returns) (bti : scalar.HaveBTIExt () = pure false) (s : State) :
 Oak.SailBridge.ExtendedScalar.QuietControl (install scalar returns) s := by
 constructor <;> simp [install, bti, q.usingA32, EStateM.run, Pure.pure, EStateM.pure]

theorem exact_bytes_return (scalar : ScalarBoundaries) (returns : Boundaries)
 (q : Oak.SailBridge.Return.QueryProfile returns) (bti : scalar.HaveBTIExt () = pure false)
 (s : State) (bank : Oak.SailBridge.ExtendedScalar.Bank) (op : Oak.BitwiseFunction.Op)
 (initialized : s.regs.get? ReturnExecution.Register._R = some bank)
 (ps : ProcState) (pstate : s.regs.get? ReturnExecution.Register.PSTATE = some ps)
 (el : ps.EL = ReturnExecution.Functions.EL1)
 (tcr : s.regs.get? ReturnExecution.Register.TCR_EL1 = some (0 : BitVec 64)) :
 (Oak.SailBridge.ExtendedScalar.executeBytes (install scalar returns) (Oak.AArch64BitwiseFunction.functionBytes op)).run s =
 .ok () (finalState op s bank) := by
 rw [Oak.SailBridge.ExtendedScalar.function_bytes_to_return_request (install scalar returns) s bank op initialized
  (quiet scalar returns q bti _) (quiet scalar returns q bti _) false
  (by simp [install, q.pac, EStateM.run, Pure.pure, EStateM.pure])]
 change (ReturnExecution.Functions.BranchTo returns bank[30] .BranchType_RET).run
  (Oak.SailBridge.ExtendedScalar.requestState op s bank) = _
 exact Oak.SailBridge.Return.branchTo64_el1_no_tags returns q (Oak.SailBridge.ExtendedScalar.requestState op s bank) ps
  (by simpa [Oak.SailBridge.ExtendedScalar.requestState, Oak.SailBridge.ExtendedScalar.retControlState, Oak.SailBridge.ExtendedScalar.afterLogical, Oak.SailBridge.ExtendedScalar.logicalControlState, Oak.SailBridge.ExtendedScalar.put, Std.ExtDHashMap.get?_insert] using pstate) el
  (by simpa [Oak.SailBridge.ExtendedScalar.requestState, Oak.SailBridge.ExtendedScalar.retControlState, Oak.SailBridge.ExtendedScalar.afterLogical, Oak.SailBridge.ExtendedScalar.logicalControlState, Oak.SailBridge.ExtendedScalar.put, Std.ExtDHashMap.get?_insert] using tcr) bank[30] .BranchType_RET

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
