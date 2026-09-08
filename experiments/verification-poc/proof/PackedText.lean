import ProofPacking
import RUPText

set_option autoImplicit false
namespace OakVerification.PackedText

def check (cnf proof : String) : Except String Bool :=
  match Text.parseDIMACS cnf with
  | .error message => .error message
  | .ok formula =>
    match Text.parseLRAT proof with
    | .error message => .error message
    | .ok instructions => .ok (ProofPacking.check formula.variables formula.clauses instructions)

-- Soundness is about the formula returned by the executable text parser.
-- No assertion of external grammar correctness or Oak equivalence is hidden here.
theorem check_sound (cnf proof : String) (accepted : check cnf proof = .ok true) :
    ∃ formula instructions,
      Text.parseDIMACS cnf = .ok formula ∧ Text.parseLRAT proof = .ok instructions ∧
      Unsatisfiable (initialDatabase formula.clauses) := by
  cases formulaResult : Text.parseDIMACS cnf with
  | error message => simp [check, formulaResult] at accepted
  | ok formula =>
    cases proofResult : Text.parseLRAT proof with
    | error message => simp [check, formulaResult, proofResult] at accepted
    | ok instructions =>
      exact ⟨formula, instructions, rfl, rfl,
        ProofPacking.check_sound formula.variables formula.clauses instructions
          (by simpa [check, formulaResult, proofResult] using accepted)⟩

#print axioms check
#print axioms check_sound
end OakVerification.PackedText
