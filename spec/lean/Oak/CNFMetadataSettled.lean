import Oak.CNFReplayHeader
import Oak.CNFWordSettled

/-!
# Metadata-gated settled word equality

Even constant-only equalities must pass the complete replay header check.
The returned ordered parameters are exactly those used to project the words
and interpret their named inputs; validity is checked, not assumed separately.
Allocation and replay of the complete disequality remain mandatory.

This composes the supplied-model checks. It does not establish arbitrary Go
graph/table projection, signed-field admission, or bind recording coverage to
the same semantic snapshot. Nonconstant roots still need a certificate, and
refusal does not prove inequality. Source/ISA and compiler verdict authority
remain outside this theorem; no new compiler consumer is introduced.
-/

set_option autoImplicit false

namespace Oak.CNFMetadataSettled

open Oak.CNFWordInput Oak.CNFWordProjection

def check (header : Oak.CNFReplayHeader.Snapshot)
    (allocation : Oak.CNFDenseAllocation.Snapshot) (maxInt : Nat)
    (left right : WordTerm) : Option (List Parameter) :=
  match Oak.CNFReplayHeader.check header with
  | none => none
  | some parameters =>
      if Oak.CNFWordSettled.checkEqual allocation parameters maxInt left right then
        some parameters
      else none

theorem check_spec {header : Oak.CNFReplayHeader.Snapshot}
    {allocation : Oak.CNFDenseAllocation.Snapshot} {maxInt : Nat}
    {left right : WordTerm} {parameters : List Parameter}
    (accepted : check header allocation maxInt left right = some parameters) :
    Oak.CNFReplayHeader.check header = some parameters ∧
      Oak.CNFWordSettled.checkEqual allocation parameters maxInt left right = true := by
  unfold check at accepted
  cases headerChecked : Oak.CNFReplayHeader.check header with
  | none => simp [headerChecked] at accepted
  | some checked =>
      simp only [headerChecked] at accepted
      split at accepted
      next settled =>
        cases Option.some.inj accepted
        exact ⟨rfl, settled⟩
      next => contradiction

/-- Complete metadata validity, exact ordered names, and word equality follow
from a single acceptance, for every typed input. No coverage or input-binding
premise is supplied by the caller. -/
theorem check_sound {header : Oak.CNFReplayHeader.Snapshot}
    {allocation : Oak.CNFDenseAllocation.Snapshot} {maxInt : Nat}
    {left right : WordTerm} {parameters : List Parameter}
    (accepted : check header allocation maxInt left right = some parameters)
    (inputs : Inputs) :
    parametersValid parameters = true ∧ parameters.map Parameter.name = header.params ∧
      left.width = right.width ∧ (left.eval inputs).toNat = (right.eval inputs).toNat := by
  obtain ⟨headerChecked, settled⟩ := check_spec accepted
  exact ⟨Oak.CNFReplayHeader.check_parameters_valid headerChecked,
    Oak.CNFReplayHeader.check_names headerChecked,
    Oak.CNFWordSettled.checkEqual_sound settled inputs⟩

end Oak.CNFMetadataSettled
