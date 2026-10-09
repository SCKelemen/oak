import ReturnStateProjection
namespace Oak.SailBridge.StateProjection
open Sail PreSail

/-- Observation of return in the old register universe: it has no PC fields.
The concrete extended return execution is justified separately below. -/
def observedReturn (base : ScalarExecution.Boundaries) : ScalarExecution.Boundaries :=
 {base with
  HaveBTIExt := fun _ => pure false
  UsingAArch32 := fun _ => pure false
  HavePACExt := fun _ => pure false
  BranchTo := fun _ _ => pure ()}

private theorem observed_quiet (base : ScalarExecution.Boundaries) (s : Scalar.State) :
 Scalar.QuietControl (observedReturn base) s := ⟨rfl, rfl⟩

theorem original_observation (base : ScalarExecution.Boundaries) (old : Scalar.State)
 (bank : Scalar.Bank) (op : Oak.BitwiseFunction.Op)
 (initialized : old.regs.get? ScalarExecution.Register._R = some bank) :
 (Scalar.executeBytes (observedReturn base) (Oak.AArch64BitwiseFunction.functionBytes op)).run old =
 .ok () (Scalar.requestState op old bank) := by
 rw [Scalar.function_bytes_to_return_request (observedReturn base) old bank op initialized
  (observed_quiet base _) (observed_quiet base _) false (by rfl)]
 rfl

/-- Successful exact-byte simulation preserves all six original registers
(including every ProcState field) and every non-register state component.
The extended model additionally records the concrete generated return PC. -/
theorem exact_bytes_simulation (oldBase : ScalarExecution.Boundaries)
 (scalar : ReturnExecution.ScalarBoundaries) (returns : ReturnExecution.Boundaries)

 (old : Scalar.State) (extended : Return.State) (related : Related old extended)
 (versions : ReturnConfig.Values) (config : ReturnConfig.Initialized extended versions)
 (disabled : versions.v85 = false)
 (elMode : ReturnELMode.Ready extended)
 (bank : Scalar.Bank) (op : Oak.BitwiseFunction.Op)
 (initialized : extended.regs.get? ReturnExecution.Register._R = some bank)
 (ps : ReturnExecution.ProcState)
 (modeValues : ReturnMode.Values) (mode : ReturnMode.Ready extended ps modeValues)
 (pstate : extended.regs.get? ReturnExecution.Register.PSTATE = some ps)
 (el : ps.EL = ReturnExecution.Functions.EL1)
 (tcr : extended.regs.get? ReturnExecution.Register.TCR_EL1 = some (0 : BitVec 64)) :
 (Scalar.executeBytes (observedReturn oldBase) (Oak.AArch64BitwiseFunction.functionBytes op)).run old =
   .ok () (Scalar.requestState op old bank) ∧
 (ExtendedScalar.executeBytes (ConcreteReturn.install scalar returns)
   (Oak.AArch64BitwiseFunction.functionBytes op)).run extended =
   .ok () (ConcreteReturn.finalState op extended bank) ∧
 Related (Scalar.requestState op old bank) (ConcreteReturn.finalState op extended bank) := by
 refine ⟨original_observation oldBase old bank op (related.bank.trans initialized), ?_, ?_⟩
 · exact ConcreteReturn.exact_bytes_return scalar returns extended bank op versions config disabled elMode initialized ps modeValues mode pstate el tcr
 · exact final_related old extended related op bank

/-- The original official scalar observation commutes with total projection.
No relation-existence premise is needed. -/
theorem exact_bytes_projected (base : ScalarExecution.Boundaries) (s : Return.State)
 (bank : Scalar.Bank) (op : Oak.BitwiseFunction.Op)
 (initialized : s.regs.get? ReturnExecution.Register._R = some bank) :
 (Scalar.executeBytes (observedReturn base) (Oak.AArch64BitwiseFunction.functionBytes op)).run (project s) =
 .ok () (project (ConcreteReturn.finalState op s bank)) := by
 rw [project_final]
 exact original_observation base (project s) bank op ((project_related s).bank.trans initialized)

#print axioms exact_bytes_projected
#print axioms original_observation
#print axioms exact_bytes_simulation
end Oak.SailBridge.StateProjection
