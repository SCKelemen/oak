import Oak.LRATLifecyclePlan

/-! All allocation outcomes of the source-audited, normally returning LRAT
resource protocol. A successful replay means every ownership transition was
legal; the final observation means each allocated block was freed exactly once
and each failed allocation stayed absent. No result pattern is assumed. -/
set_option autoImplicit false
namespace Oak.LRATLifecycle

private def outcomes (a b c d e f : Bool) : Results
  | .starts => a
  | .lengths => b
  | .alive => c
  | .store => d
  | .assign => e
  | .trail => f

private theorem all_outcomes (a b c d e f : Bool) :
    (run (outcomes a b c d e f) (fun _ => .vacant)
      (schedule true true (outcomes a b c d e f))).map observe =
        some (released (outcomes a b c d e f)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

theorem production_schedule_releases (results : Results) :
    (run results (fun _ => .vacant) (schedule true true results)).map observe = some (released results) := by
  have same : results = outcomes (results .starts) (results .lengths) (results .alive)
      (results .store) (results .assign) (results .trail) := by
    funext slot
    cases slot <;> rfl
  exact same ▸ all_outcomes _ _ _ _ _ _

/-- Output-capacity and preflight refusal perform no resource operation. -/
theorem refused_schedule_empty (outFits admitted : Bool) (results : Results)
    (refused : outFits = false ∨ admitted = false) : schedule outFits admitted results = [] := by
  rcases refused with h | h <;> simp [schedule, h]

/-- The checker is reached only after all six allocations succeed. -/
theorem checker_requires_all (outFits admitted : Bool) (results : Results)
    (reached : Action.check ∈ schedule outFits admitted results) : allPresent results = true := by
  by_cases all : allPresent results = true
  · exact all
  · simp [schedule, all, allocations, cleanup] at reached

-- Negative protocol controls: null ownership, duplicate free and free while
-- owned are rejected by the semantics, rather than silently erased.
example : step (fun _ => false) (fun _ => .absent) (.own .starts) = none := rfl
example : step (fun _ => true) (fun _ => .freed) (.free .starts) = none := rfl
example : step (fun _ => true) (fun _ => .owned) (.free .starts) = none := rfl
example : step (fun _ => true) (fun _ => .raw) .check = none := rfl

-- Whole-schedule negative controls fail even though their allocation set is
-- identical: ordering and exactly-once cleanup are semantically significant.
example : (run (fun _ => true) (fun _ => .vacant)
    (allocations ++ ownedCall ++ cleanup ++ [.free .starts])) = none := by decide
example : (run (fun _ => false) (fun _ => .vacant)
    (allocations ++ ownedCall ++ cleanup)) = none := by decide
example : (run (fun _ => true) (fun _ => .vacant)
    (allocations ++ ownedCall ++ cleanup.tail)).map observe ≠ some (released (fun _ => true)) := by decide

end Oak.LRATLifecycle
