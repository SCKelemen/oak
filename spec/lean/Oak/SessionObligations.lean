import Oak.Loops
import Oak.Discipline
import Oak.Regions

/-! Obligations of an Oak REPL session, stated by `:lean`. Each theorem is one
recorded assumption the compiler could not discharge; proving it here discharges
it. Generated — edit the proofs, regenerate the statements. -/

namespace Oak.Session

/-- OAK-D0103: the loop in `loop` at repl.oak:3 has no statically evident bound. -/
-- variables: 0 ↦ `running`, 1 ↦ `i`
def loop_loop_1 : Oak.Loops.Loop :=
  { guard := (.var 0),
    body := [{ var := 1, ty := (.u 32), value := (.bin .add (.var 1) (.lit 1)) },
            { var := 0, ty := .b, value := (.bin .lt (.wrap (.u 32) (.bin .add (.var 1) (.lit 1))) (.lit 10)) }] }

theorem loop_loop_1_terminates : ∀ env, Oak.Loops.Terminates loop_loop_1 env := by
  -- Discharge: exact Oak.Loops.ranking_terminates loop_loop_1 (fun env => <rank>) (by intro env h; <decrease>)
  sorry

/-- OAK-D0103: the loop in `countdown` at repl.oak:8 has no statically evident bound. -/
-- variables: 0 ↦ `k`
def loop_countdown_2 : Oak.Loops.Loop :=
  { guard := (.bin .gt (.var 0) (.lit 0)),
    body := [{ var := 0, ty := (.u 32), value := (.cond (.bin .gt (.var 0) (.lit 5)) (.bin .sub (.var 0) (.lit 2)) (.bin .sub (.var 0) (.lit 1))) }] }

theorem loop_countdown_2_terminates : ∀ env, Oak.Loops.Terminates loop_countdown_2 env := by
  -- Discharge: exact Oak.Loops.ranking_terminates loop_countdown_2 (fun env => <rank>) (by intro env h; <decrease>)
  sorry

/-- OAK-D0102: tail recursion through `ping`, `pong` relies on tail-call elimination.
Functions: 0 ↦ `ping`, 1 ↦ `pong`. Every internal call is a tail call, so the constant rank
certificate the compiler computed satisfies Oak.Discipline.Ranked. -/
theorem cycle_1_ranked : ∃ rank : Nat → Nat, Oak.Discipline.Ranked [] [(0, 1), (1, 0)] rank :=
  ⟨fun _ => 0, by simp [Oak.Discipline.Ranked]⟩

/-- OAK-B0110 at repl.oak:19: unsafe assumption: writable span "b" is assumed disjoint from existing writable access to "buf" -/
-- The regions overlap: the admitted assumption is false.
theorem unsafe_1_overlaps : ¬ Oak.Regions.Disjoint ⟨0, 16⟩ ⟨0, 16⟩ := by decide

end Oak.Session
