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
    body := [{ var := 1, ty := (.u 32), value := (.wrap (.u 32) (.bin .add (.var 1) (.lit 1))) },
            { var := 0, ty := .b, value := (.bin .lt (.wrap (.u 32) (.wrap (.u 32) (.bin .add (.var 1) (.lit 1)))) (.lit 10)) }],
    writes := [] }

theorem loop_loop_1_terminates : ∀ (F : Oak.Loops.Funs) (s : Oak.Loops.State), Oak.Loops.Terminates F loop_loop_1 s := by
  -- Discharge: intro F; exact Oak.Loops.ranking_terminates F loop_loop_1 (fun s => <rank>) (by intro s h; <decrease>)
  sorry

/-- OAK-D0103: the loop in `countdown` at repl.oak:8 has no statically evident bound. -/
-- variables: 0 ↦ `k`
def loop_countdown_2 : Oak.Loops.Loop :=
  { guard := (.bin .gt (.var 0) (.lit 0)),
    body := [{ var := 0, ty := (.u 32), value := (.cond (.bin .gt (.var 0) (.lit 5)) (.wrap (.u 32) (.bin .sub (.var 0) (.lit 2))) (.wrap (.u 32) (.bin .sub (.var 0) (.lit 1)))) }],
    writes := [] }

theorem loop_countdown_2_terminates : ∀ (F : Oak.Loops.Funs) (s : Oak.Loops.State), Oak.Loops.Terminates F loop_countdown_2 s := by
  -- Discharge: intro F; exact Oak.Loops.ranking_terminates F loop_countdown_2 (fun s => <rank>) (by intro s h; <decrease>)
  sorry

/-- OAK-D0103: the loop in `fill` at repl.oak:18 has no statically evident bound. -/
-- variables: 0 ↦ `i`, 1 ↦ `n`
-- arrays: 0 ↦ `buf`
-- uninterpreted functions (constrain F with hypotheses): 0 ↦ `mystery`
def loop_fill_3 : Oak.Loops.Loop :=
  { guard := (.bin .ne (.var 0) (.var 1)),
    body := [{ var := 0, ty := (.u 32), value := (.wrap (.u 32) (.bin .add (.wrap (.u 32) (.bin .add (.var 0) (.wrap (.u 32) (.cond (.bin .eq (.lit 0) (.wrap (.u 32) (.bin .rem (.var 0) (.lit 8)))) (.wrap (.u 8) (.wrap (.u 8) (.wrap (.u 32) (.wrap (.u 32) (.bin .add (.var 0) (.lit 1)))))) (.index 0 (.lit 0)))))) (.call 0 [(.lit 1)]))) }],
    writes := [{ arr := 0, ty := (.u 8), index := (.wrap (.u 32) (.bin .rem (.var 0) (.lit 8))), value := (.wrap (.u 8) (.wrap (.u 32) (.wrap (.u 32) (.bin .add (.var 0) (.lit 1))))) }] }

theorem loop_fill_3_terminates : ∀ (F : Oak.Loops.Funs) (s : Oak.Loops.State), Oak.Loops.Terminates F loop_fill_3 s := by
  -- Discharge: intro F; exact Oak.Loops.ranking_terminates F loop_fill_3 (fun s => <rank>) (by intro s h; <decrease>)
  sorry

/-- OAK-D0103: the loop in `walk` at repl.oak:31 has no statically evident bound. -/
-- variables: 0 ↦ `p.on`, 1 ↦ `p.v`, 2 ↦ `q.p.v`, 3 ↦ `n`
-- arrays: 0 ↦ `cs.v`
def loop_walk_4 : Oak.Loops.Loop :=
  { guard := (.var 0),
    body := [{ var := 1, ty := (.u 32), value := (.wrap (.u 32) (.bin .add (.wrap (.u 32) (.var 1)) (.lit 1))) },
            { var := 2, ty := (.u 32), value := (.wrap (.u 32) (.wrap (.u 32) (.bin .add (.wrap (.u 32) (.var 1)) (.lit 1)))) },
            { var := 0, ty := .b, value := (.bin .lt (.cond (.bin .eq (.lit 0) (.lit 0)) (.wrap (.u 32) (.wrap (.u 32) (.bin .add (.index 0 (.lit 0)) (.wrap (.u 32) (.wrap (.u 32) (.wrap (.u 32) (.bin .add (.wrap (.u 32) (.var 1)) (.lit 1)))))))) (.index 0 (.lit 0))) (.var 3)) }],
    writes := [{ arr := 0, ty := (.u 32), index := (.lit 0), value := (.wrap (.u 32) (.bin .add (.index 0 (.lit 0)) (.wrap (.u 32) (.wrap (.u 32) (.wrap (.u 32) (.bin .add (.wrap (.u 32) (.var 1)) (.lit 1))))))) }] }

theorem loop_walk_4_terminates : ∀ (F : Oak.Loops.Funs) (s : Oak.Loops.State), Oak.Loops.Terminates F loop_walk_4 s := by
  -- Discharge: intro F; exact Oak.Loops.ranking_terminates F loop_walk_4 (fun s => <rank>) (by intro s h; <decrease>)
  sorry

/-- OAK-D0102: tail recursion through `ping`, `pong` relies on tail-call elimination.
Functions: 0 ↦ `ping`, 1 ↦ `pong`. Every internal call is a tail call, so the constant rank
certificate the compiler computed satisfies Oak.Discipline.Ranked. -/
theorem cycle_1_ranked : ∃ rank : Nat → Nat, Oak.Discipline.Ranked [] [(0, 1), (1, 0)] rank :=
  ⟨fun _ => 0, by simp [Oak.Discipline.Ranked]⟩

/-- OAK-B0110 at repl.oak:46: unsafe assumption: writable span "b" is assumed disjoint from existing writable access to "shared" -/
-- The regions overlap: the admitted assumption is false.
theorem unsafe_1_overlaps : ¬ Oak.Regions.Disjoint ⟨0, 16⟩ ⟨0, 16⟩ := by decide

end Oak.Session
