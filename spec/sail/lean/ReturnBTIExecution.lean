import ReturnBTI
import ReturnSimulation
namespace Oak.SailBridge.ReturnBTIExecution
open ReturnExecution Sail PreSail
open Oak.SailBridge ReturnBTI
set_option linter.unusedSimpArgs false
abbrev State := ReturnConfig.State

/-- Two prefetched complete words with no trailing bytes. Each dispatch installs
that same word in __currentInstr before calling the unchanged scalar export. -/
def executeBytes (scalar : ScalarBoundaries) (returns : Boundaries) (bytes : List UInt8) : SailM Unit :=
 match Oak.AArch64BitwiseFunction.takeWord bytes with
 | some (first, rest) =>
   match Oak.AArch64BitwiseFunction.takeWord rest with
   | some (second, []) => do dispatch scalar returns first; dispatch scalar returns second
   | _ => sailThrow (.Error_Undefined ())
 | _ => sailThrow (.Error_Undefined ())

theorem exact_byte_shape (scalar : ScalarBoundaries) (returns : Boundaries) (op : Oak.BitwiseFunction.Op) :
 executeBytes scalar returns (Oak.AArch64BitwiseFunction.functionBytes op) =
 (do dispatch scalar returns (ExtendedScalar.logicalWord (ExtendedScalar.externalOp op))
     dispatch scalar returns 0xd65f03c0#32) := by cases op <;> rfl

def requestState (op : Oak.BitwiseFunction.Op) (s : State) (bank : ExtendedScalar.Bank) : State :=
 put (retControl (logicalFinal op s bank)) .BTypeNext 0#2

def finalState (op : Oak.BitwiseFunction.Op) (s : State) (bank : ExtendedScalar.Bank) : State :=
 put (put (requestState op s bank) ._PC bank[30]) .__PC_changed true

theorem bytes_to_request (scalar : ScalarBoundaries) (returns : Boundaries)
 (s : State) (ps : ProcState) (v : ReturnConfig.Values) (mv : ReturnMode.Values)
 (guarded compatible : Bool) (h : Context s ps v mv guarded compatible)
 (bank : ExtendedScalar.Bank) (initialized : s.regs.get? Register._R = some bank)
 (op : Oak.BitwiseFunction.Op) :
 (executeBytes scalar returns (Oak.AArch64BitwiseFunction.functionBytes op)).run s =
 (ReturnExecution.Functions.BranchTo returns bank[30] .BranchType_RET).run (requestState op s bank) := by
 rw [exact_byte_shape]
 have first := dispatch_logical scalar returns s ps v mv guarded compatible h bank initialized op
 have second := dispatch_ret scalar returns (logicalFinal op s bank) ps v mv guarded compatible
  (context_logical_final s ps v mv guarded compatible h op bank)
  (ExtendedScalar.updatedBank (ExtendedScalar.externalOp op) bank)
  (by simp [logicalFinal,put,Return.put,Std.ExtDHashMap.get?_insert])
 have returnValue : (ExtendedScalar.updatedBank (ExtendedScalar.externalOp op) bank)[30] = bank[30] := by
  simp [ExtendedScalar.updatedBank,Vector.getElem_set!]
 rw [returnValue] at second
 simp only [EStateM.run,Bind.bind,EStateM.bind] at first second ⊢
 rw [first]
 exact second

theorem context_request (s : State) (ps : ProcState) (v : ReturnConfig.Values)
 (mv : ReturnMode.Values) (guarded compatible : Bool) (h : Context s ps v mv guarded compatible)
 (op : Oak.BitwiseFunction.Op) (bank : ExtendedScalar.Bank) :
 Context (requestState op s bank) ps v mv guarded compatible :=
 context_put _ _ _ _ _ _ (context_ret_control _ _ _ _ _ _
  (context_logical_final s ps v mv guarded compatible h op bank)) .BTypeNext trivial _

def el_mode_put (s : State) (h : ReturnELMode.Ready s) (r : Register)
 (allowed : InstructionWrite r) (value : RegisterType r) : ReturnELMode.Ready (put s r value) := by
 rcases h with ⟨⟨c0,c1,c2,c3⟩,hi,sv,sr,srw,hv,hr,hrw⟩
 cases r <;> simp_all only [InstructionWrite]
 all_goals refine ⟨⟨?_,?_,?_,?_⟩,?_,sv,?_,srw,hv,?_,hrw⟩
 all_goals simp_all [put,Return.put,Std.ExtDHashMap.get?_insert]

def el_mode_request (s : State) (h : ReturnELMode.Ready s)
 (op : Oak.BitwiseFunction.Op) (bank : ExtendedScalar.Bank) : ReturnELMode.Ready (requestState op s bank) := by
 unfold requestState retControl logicalFinal logicalControl ExtendedScalar.logicalControlState ExtendedScalar.retControlState
 apply el_mode_put _ _ .BTypeNext trivial
 apply el_mode_put _ _ .__unconditional trivial
 apply el_mode_put _ _ .SEE trivial
 apply el_mode_put _ _ .SEE trivial
 apply el_mode_put _ _ .__currentInstr trivial
 apply el_mode_put _ _ ._R trivial
 apply el_mode_put _ _ .BTypeNext trivial
 apply el_mode_put _ _ .__unconditional trivial
 apply el_mode_put _ _ .SEE trivial
 apply el_mode_put _ _ .SEE trivial
 exact el_mode_put _ h .__currentInstr trivial _

/-- BTI is concretely enabled. No assumption on exception-handler success,
read-only behavior, or returned state is required. -/
theorem exact_bytes_return (scalar : ScalarBoundaries) (returns : Boundaries)
 (s : State) (ps : ProcState) (v : ReturnConfig.Values) (mv : ReturnMode.Values)
 (guarded compatible : Bool) (h : Context s ps v mv guarded compatible)
 (elMode : ReturnELMode.Ready s) (el : ps.EL = ReturnExecution.Functions.EL1)
 (tcr : s.regs.get? Register.TCR_EL1 = some 0#64)
 (bank : ExtendedScalar.Bank) (initialized : s.regs.get? Register._R = some bank)
 (op : Oak.BitwiseFunction.Op) :
 (executeBytes scalar returns (Oak.AArch64BitwiseFunction.functionBytes op)).run s =
 .ok () (finalState op s bank) := by
 rw [bytes_to_request scalar returns s ps v mv guarded compatible h bank initialized op]
 have hc := context_request s ps v mv guarded compatible h op bank
 exact Return.branchTo64_el1_no_tags returns _ v hc.versions (el_mode_request s elMode op bank)
  ps mv hc.mode hc.control.pstate el
  (by simpa [requestState,retControl,logicalFinal,logicalControl,ExtendedScalar.logicalControlState,
   ExtendedScalar.retControlState,put,Return.put,ExtendedScalar.put,Std.ExtDHashMap.get?_insert] using tcr)
  bank[30] .BranchType_RET
/-- All old scalar registers and every non-register state component agree with
the established observation; the extra current-instruction register records RET. -/
theorem final_state_frame (op : Oak.BitwiseFunction.Op) (s : State) (bank : ExtendedScalar.Bank) :
 finalState op s bank = put (ConcreteReturn.finalState op s bank) .__currentInstr 0xd65f03c0#32 := by
 unfold finalState requestState retControl logicalFinal logicalControl
 unfold ConcreteReturn.finalState ExtendedScalar.requestState ExtendedScalar.retControlState
 unfold ExtendedScalar.afterLogical ExtendedScalar.logicalControlState
 simp only [put,Return.put,ExtendedScalar.put]
 congr 1
 apply Std.ExtDHashMap.ext_get?
 intro r
 cases r <;> simp [Std.ExtDHashMap.get?_insert]

theorem project_current_instruction (s : State) (word : BitVec 32) :
 StateProjection.project (put s .__currentInstr word) = StateProjection.project s := by
 simp [StateProjection.project,put,Return.put,Std.ExtDHashMap.get?_insert]

theorem projected_final (op : Oak.BitwiseFunction.Op) (s : State) (bank : ExtendedScalar.Bank) :
 StateProjection.project (finalState op s bank) = StateProjection.project (ConcreteReturn.finalState op s bank) := by
 rw [final_state_frame,project_current_instruction]

theorem original_scalar_observation (base : ScalarExecution.Boundaries) (s : State)
 (bank : ExtendedScalar.Bank) (op : Oak.BitwiseFunction.Op)
 (initialized : s.regs.get? Register._R = some bank) :
 (Scalar.executeBytes (StateProjection.observedReturn base)
  (Oak.AArch64BitwiseFunction.functionBytes op)).run (StateProjection.project s) =
 .ok () (StateProjection.project (finalState op s bank)) := by
 rw [projected_final]
 exact StateProjection.exact_bytes_projected base s bank op initialized

theorem final_observations (op : Oak.BitwiseFunction.Op) (s : State) (bank : ExtendedScalar.Bank) :
 (finalState op s bank).regs.get? Register.__currentInstr = some 0xd65f03c0#32 ∧
 (finalState op s bank).regs.get? Register.BTypeNext = some 0#2 ∧
 (finalState op s bank).regs.get? Register._PC = some bank[30] ∧
 (finalState op s bank).regs.get? Register._R = some (ExtendedScalar.updatedBank (ExtendedScalar.externalOp op) bank) ∧
 (finalState op s bank).regs.get? Register.PSTATE = s.regs.get? Register.PSTATE ∧
 (finalState op s bank).mem = s.mem ∧ (finalState op s bank).tags = s.tags := by
 simp [finalState,requestState,retControl,logicalFinal,logicalControl,ExtendedScalar.retControlState,
  ExtendedScalar.logicalControlState,put,Return.put,ExtendedScalar.put,Std.ExtDHashMap.get?_insert]
end Oak.SailBridge.ReturnBTIExecution
