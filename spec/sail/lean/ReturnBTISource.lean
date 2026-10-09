import ReturnBTIExecution
import Oak.BitwiseSourceLowering

/-!
Original canonical source bytes and the complete eight-byte native body are
checked together, then connected to the existing typed source interpreter and
the actual generated BTI-enabled logical/RET execution. The initialized context
and prefetched selected-decoder harness remain explicit. This is neither a
whole-language parser/compiler theorem nor a full decoder, fetch, reset, OS,
exporter-correctness or hardware-equivalence claim. No verified verdict changes.
-/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Oak.SailBridge.ReturnBTISource
open ReturnExecution Sail PreSail
open Oak.BitwiseFunction
open Oak.BitwiseSource (Bytes Decl Grammar Means)
abbrev State := ReturnConfig.State
abbrev Bank := ExtendedScalar.Bank

/-- Bind the original source, name/parameters/operator, target/ABI, and entire
function extent. The source grammar already fixes both inputs and output to u32. -/
def accepts (source : Bytes) (claim : Decl) (target : Target)
 (abi : Oak.AArch64BitwiseFunction.ABI) (body : Bytes) : Bool :=
 decide (Oak.BitwiseSource.parse source = some claim) &&
 Oak.AArch64BitwiseFunction.accepts target abi [32,32] 32 claim.op body

theorem accepted_identity {source body : Bytes} {claim : Decl} {target : Target}
 {abi : Oak.AArch64BitwiseFunction.ABI}
 (accepted : accepts source claim target abi body = true) :
 Grammar source claim ∧ target = .arm64 ∧ abi = .aapcs64U32 ∧
 body = Oak.AArch64BitwiseFunction.functionBytes claim.op := by
 have both := Bool.and_eq_true_iff.mp accepted
 have parsed : Oak.BitwiseSource.parse source = some claim := by simpa using both.1
 have bodyIdentity : target = .arm64 ∧ abi = .aapcs64U32 ∧
  ([32,32] : List Nat) = [32,32] ∧ (32 : Nat) = 32 ∧
  body = Oak.AArch64BitwiseFunction.functionBytes claim.op := by
  simpa [Oak.AArch64BitwiseFunction.accepts] using both.2
 exact ⟨Oak.BitwiseSource.parse_sound parsed, bodyIdentity.1,
  bodyIdentity.2.1, bodyIdentity.2.2.2.2⟩

/-- Any changed source refuses the old claim, including semantically equivalent
renaming or reordered operands. This binds identity rather than source hashes. -/
theorem refuses_source_replay (source body : Bytes) (claim : Decl) (target : Target)
 (abi : Oak.AArch64BitwiseFunction.ABI) (changed : source ≠ Oak.BitwiseSource.render claim) :
 accepts source claim target abi body = false := by
 have refused : Oak.BitwiseSource.parse source ≠ some claim :=
  fun h => changed (Oak.BitwiseSource.parse_exact h)
 simp [accepts, refused]

theorem refuses_body_replay (source body : Bytes) (claim : Decl) (target : Target)
 (abi : Oak.AArch64BitwiseFunction.ABI)
 (changed : body ≠ Oak.AArch64BitwiseFunction.functionBytes claim.op) :
 accepts source claim target abi body = false := by
 simp [accepts, Oak.AArch64BitwiseFunction.rejects_changed_bytes target abi [32,32] 32 claim.op body changed]

/-- Only these register cells can change; all other cells, including absence,
are framed. Whole PSTATE preservation includes every flag and mode field. -/
def Written : Register → Prop
 | ._R | .__currentInstr | .__unconditional | .SEE | .BTypeNext | ._PC | .__PC_changed => True
 | _ => False

theorem final_register_frame (op : Op) (s : State) (bank : Bank)
 (r : Register) (untouched : ¬ Written r) :
 (ReturnBTIExecution.finalState op s bank).regs.get? r = s.regs.get? r := by
 cases r <;>
 simp_all [Written,ReturnBTIExecution.finalState,ReturnBTIExecution.requestState,
  ReturnBTI.retControl,ReturnBTI.logicalFinal,ReturnBTI.logicalControl,
  ExtendedScalar.logicalControlState,ExtendedScalar.retControlState,
  ReturnBTI.put,Return.put,ExtendedScalar.put,Std.ExtDHashMap.get?_insert]

/-- The result bank is exactly the typed source result zero-extended into X0;
all incoming upper halves are unrestricted. -/
theorem result_bank (op : Op) (bank : Bank) (left right : BitVec 32)
 (hleft : bank[0].extractLsb' 0 32 = left) (hright : bank[1].extractLsb' 0 32 = right) :
 ExtendedScalar.updatedBank (ExtendedScalar.externalOp op) bank =
 bank.set! 0 ((eval op left right).zeroExtend 64) := by
 simp [ExtendedScalar.updatedBank,ExtendedScalar.result_eq_common,hleft,hright]

/-- A successful run plus exact return/result and every non-register field.
No field assumes successful execution; accepted_source_execution constructs it. -/
structure Outcome (source body : Bytes) (claim : Decl)
 (scalar : ScalarBoundaries) (returns : Boundaries) (s : State) (bank : Bank)
 (left right : BitVec 32) (fuel : Nat) : Prop where
 grammar : Grammar source claim
 meaning : Means source claim left right (eval claim.op left right)
 typed : Oak.LoweringRefinement.evalX (Oak.BitwiseSourceLowering.toExpr claim)
  (Oak.BitwiseSourceLowering.inputs left right) (fun _ => 0) fuel = some (eval claim.op left right)
 execution : (ReturnBTIExecution.executeBytes scalar returns body).run s =
  .ok () (ReturnBTIExecution.finalState claim.op s bank)
 bankResult : (ReturnBTIExecution.finalState claim.op s bank).regs.get? Register._R =
  some (bank.set! 0 ((eval claim.op left right).zeroExtend 64))
 others : ∀ (i : Fin 31), i ≠ 0 →
  (bank.set! 0 ((eval claim.op left right).zeroExtend 64))[i] = bank[i]
 pc : (ReturnBTIExecution.finalState claim.op s bank).regs.get? Register._PC = some bank[30]
 changed : (ReturnBTIExecution.finalState claim.op s bank).regs.get? Register.__PC_changed = some true
 current : (ReturnBTIExecution.finalState claim.op s bank).regs.get? Register.__currentInstr = some 0xd65f03c0#32
 btype : (ReturnBTIExecution.finalState claim.op s bank).regs.get? Register.BTypeNext = some 0#2
 pstate : (ReturnBTIExecution.finalState claim.op s bank).regs.get? Register.PSTATE = s.regs.get? Register.PSTATE
 registers : ∀ r, ¬ Written r →
  (ReturnBTIExecution.finalState claim.op s bank).regs.get? r = s.regs.get? r
 memory : (ReturnBTIExecution.finalState claim.op s bank).mem = s.mem
 tags : (ReturnBTIExecution.finalState claim.op s bank).tags = s.tags
 choice : (ReturnBTIExecution.finalState claim.op s bank).choiceState = s.choiceState
 cycles : (ReturnBTIExecution.finalState claim.op s bank).cycleCount = s.cycleCount
 output : (ReturnBTIExecution.finalState claim.op s bank).sailOutput = s.sailOutput

/-- Universal original-source-to-generated-execution theorem. The complete
admitted body really succeeds; success or callback purity is never a premise. -/
theorem accepted_source_execution {source body : Bytes} {claim : Decl} {target : Target}
 {abi : Oak.AArch64BitwiseFunction.ABI}
 (accepted : accepts source claim target abi body = true)
 (scalar : ScalarBoundaries) (returns : Boundaries)
 (s : State) (ps : ProcState) (v : ReturnConfig.Values) (mv : ReturnMode.Values)
 (guarded compatible : Bool) (context : ReturnBTI.Context s ps v mv guarded compatible)
 (elMode : ReturnELMode.Ready s) (el : ps.EL = ReturnExecution.Functions.EL1)
 (tcr : s.regs.get? Register.TCR_EL1 = some 0#64)
 (bank : Bank) (initialized : s.regs.get? Register._R = some bank)
 (left right : BitVec 32) (hleft : bank[0].extractLsb' 0 32 = left)
 (hright : bank[1].extractLsb' 0 32 = right) (fuel : Nat) :
 Outcome source body claim scalar returns s bank left right fuel := by
 have identity := accepted_identity accepted
 have obs := ReturnBTIExecution.final_observations claim.op s bank
 refine ⟨identity.1, ⟨identity.1, Oak.BitwiseSource.grammar_evaluation identity.1 left right⟩,
  Oak.BitwiseSourceLowering.lowering_success claim left right fuel, ?_, ?_, ?_,
  obs.2.2.1, ?_, obs.1, obs.2.1, obs.2.2.2.2.1,
  final_register_frame claim.op s bank, obs.2.2.2.2.2.1, obs.2.2.2.2.2.2, rfl, rfl, rfl⟩
 · rw [identity.2.2.2]
   exact ReturnBTIExecution.exact_bytes_return scalar returns s ps v mv guarded compatible context
    elMode el tcr bank initialized claim.op
 · rw [obs.2.2.2.1, result_bank claim.op bank left right hleft hright]
 · intro i nonzero
   have nz : i.val ≠ 0 := fun h => nonzero (Fin.ext h)
   simp [Vector.getElem_set!, Ne.symm nz]
 · simp [ReturnBTIExecution.finalState,Return.put,Std.ExtDHashMap.get?_insert]

end Oak.SailBridge.ReturnBTISource
