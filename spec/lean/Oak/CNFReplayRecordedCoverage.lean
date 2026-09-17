import Oak.CNFReplayRecording

/-!
# Checked recording sequences to exact native replay coverage

Execute the supplied recording events from empty, tie the final scalar counts
to the supplied producer tables, and apply the existing numeric finish check.
Acceptance supplies the admitted-state invariant needed for exact coverage;
callers no longer assume `Reachable` separately for this composed model check.

This does not synthesize a recording trace from an actual Go execution or prove
faithful pointer/key projection, unchanged producer contents, or root semantics.
The snapshot is fixed throughout the model run. Failure returns no accepted
result; it does not assert rollback of earlier successful writes in Go.
-/

set_option autoImplicit false

namespace Oak.CNFReplayRecordedCoverage

open Oak.CNFReplayCoverage Oak.CNFReplayRecording

def check (snapshot : Snapshot) (events : List Event) (start current : Shape) :
    Option State :=
  match run snapshot events with
  | none => none
  | some state =>
      if current.termMemo = snapshot.terms.length ∧
          current.inputs = snapshot.inputs.length ∧
          current.gateMemo = snapshot.gates.length ∧
          finish state.terms.length state.inputs.length state.gates.length start current = true then
        some state
      else none

theorem check_spec {snapshot : Snapshot} {events : List Event}
    {start current : Shape} {state : State}
    (accepted : check snapshot events start current = some state) :
    run snapshot events = some state ∧
      current.termMemo = snapshot.terms.length ∧
      current.inputs = snapshot.inputs.length ∧
      current.gateMemo = snapshot.gates.length ∧
      finish state.terms.length state.inputs.length state.gates.length start current = true := by
  unfold check at accepted
  cases recorded : run snapshot events with
  | none => simp [recorded] at accepted
  | some result =>
      simp only [recorded] at accepted
      split at accepted
      · rename_i checks
        have same : result = state := Option.some.inj accepted
        subst state
        exact ⟨rfl, checks⟩
      · contradiction

/-- Exact key domains and term-root lookups follow from the executable run
and completion check, rather than an assumed admitted-recording relation.
The shape result is scalar equality only, not producer content integrity. -/
theorem check_exact {snapshot : Snapshot} {events : List Event}
    {start current : Shape} {state : State}
    (accepted : check snapshot events start current = some state) :
    Exact (producer snapshot) state ∧ current = start := by
  obtain ⟨recorded, terms, inputs, gates, completed⟩ := check_spec accepted
  exact finish_exact (run_reachable recorded) completed
    (by simpa [producer] using terms)
    (by simpa [producer] using inputs)
    (by simpa [producer] using gates)

private def exampleSnapshot : Snapshot :=
  ⟨[⟨0, [2]⟩, ⟨1, [4]⟩, ⟨2, [6]⟩], [(0, 1), (1, 2)], [(0, 3)], 3, 1024⟩

private def exampleShape : Shape := ⟨3, 3, 2, 1, 1, 3, 2, 0, false⟩

private def exampleEvents : List Event :=
  [.input 0, .term 0 [2], .input 1, .term 1 [4], .gate 0, .term 2 [6],
    .input 0, .term 0 [2], .gate 0]

-- Repeated writes do not inflate the completed domains.
example : (check exampleSnapshot exampleEvents exampleShape exampleShape).isSome = true := by decide

example : (check exampleSnapshot [.input 0, .term 0 [2]]
    exampleShape exampleShape).isSome = false := by decide

example : (check exampleSnapshot [.input 0, .term 0 [3]]
    exampleShape exampleShape).isSome = false := by decide

example : (check exampleSnapshot [.gate 1]
    exampleShape exampleShape).isSome = false := by decide

end Oak.CNFReplayRecordedCoverage
