import Oak.OptIRStatefulCopyGenerated

/-!
# Bounded actual-record translation validator

Full-field equality binds an accepted candidate to the freshly exported CFG.
The additional instruction/control equations freeze the semantic projection
used by the arbitrary-state refinement proof. They are inspected from actual
records, not supplied by a proof callback or inferred from an input hash.

The named positive theorem must be rechecked against every fresh export. A
changed export cannot obtain acceptance merely by comparing equal to itself.
These nine equations are not by themselves a total-copy correctness theorem;
the separate complete `OptIRStatefulCopy` refinement remains mandatory.
-/
namespace Oak.OptIRStatefulCopy

open Oak.OptIRExecution

-- Exact source contexts may be long; inspect the complete records without
-- falling back to truncated identity or a source hash.
set_option maxRecDepth 10000

def blockAt (candidate : Program) (function block : Nat) : Option Block := do
  let cfg ← candidate[function]?
  cfg.blocks[block]?

def opAt (candidate : Program) (function block operation : Nat) : Option Operation := do
  let block ← blockAt candidate function block
  block.operations[operation]?

def checkInstructionEquations (candidate : Program) : Bool :=
  decide ((opAt candidate 0 5 2).map (·.attributes) = some [⟨"value", "1"⟩]) &&
  decide ((blockAt candidate 0 0).map
    (fun b => (b.terminator.trueEdge.target, b.terminator.falseEdge.target)) = some (1, 2)) &&
  decide ((opAt candidate 0 4 0).map (·.code) = some "compare.less") &&
  decide ((blockAt candidate 0 5).map (fun b => b.operations.map (·.code)) =
    some ["memory.byte-load", "memory.byte-store", "const.integer", "integer.add"]) &&
  decide ((blockAt candidate 0 5).map (fun b => b.terminator.trueEdge.arguments) = some [15]) &&
  decide ((opAt candidate 0 6 0).map (·.operands) = some [3]) &&
  decide ((opAt candidate 1 0 1).map (·.attributes) = some [⟨"callee", "bytes__copy_uinto"⟩]) &&
  decide ((opAt candidate 1 1 1).map (·.operands) = some [6, 3]) &&
  decide ((opAt candidate 0 1 0).map (·.attributes) =
    some [⟨"variant", "bytes__CopyError.DestinationTooSmall"⟩])

/-- Full-field exact snapshot acceptance plus fixed semantic record equations.
Fresh export/Go correspondence is a separately tested trust boundary. -/
def checkProjection (candidate : Program) : Bool :=
  decide (candidate = Generated.program) && checkInstructionEquations candidate

/-- Required positive check on the actual fresh export. Every semantic mutation
control recompiles this exact theorem, not a parallel anonymous example. -/
theorem generated_projection_accepted : checkProjection Generated.program = true := by
  decide

theorem check_projection_sound (candidate : Program) :
    checkProjection candidate = true ↔ candidate = Generated.program := by
  constructor
  · intro accepted
    have parts : decide (candidate = Generated.program) = true ∧
        checkInstructionEquations candidate = true := by
      simpa only [checkProjection, Bool.and_eq_true_iff] using accepted
    exact of_decide_eq_true parts.1
  · intro exactSnapshot
    subst candidate
    exact generated_projection_accepted

end Oak.OptIRStatefulCopy
