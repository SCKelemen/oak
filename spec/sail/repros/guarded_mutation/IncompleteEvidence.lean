import Out
open Sail PreSail
abbrev State := PreSail.SequentialState RegisterType Sail.trivialChoiceSource
/-- The original incomplete-match reproducer is retained alongside the total one. -/
theorem exported_incomplete_result (s : State) :
    (Out.Functions.repro false 1).run s = .ok 63 s := by rfl
#print axioms exported_incomplete_result
#eval match (Out.Functions.repro false 1).run ⟨default, (), default, default, default, default⟩ with
  | .ok value _ => value
  | .error _ _ => -1
