import Oak.SessionObligations

/-!
# Discharging a session's obligations

`Oak.SessionObligations` is what the REPL's `:lean` emitted for the example
session in `repl/lean_test.go`: two loop-termination statements left as
`sorry`, a tail cycle already discharged by the compiler's rank certificate,
and a refuted span-disjointness assumption. This file is the programmer's
half of the exchange — the proofs of the two loop statements by ranking
functions (`Oak.Loops.ranking_terminates`), showing the emitted statements
are the real obligations and are provable as stated.
-/

namespace Oak.Session

open Oak.Loops

theorem two_pow_32 : (2 : Int) ^ 32 = 4294967296 := by decide

/-- `countdown`: `k` strictly decreases while positive. A value outside the
32-bit range wraps on the first step and is then smaller, so `k.toNat` ranks
every environment. -/
theorem loop_countdown_2_terminates_proved : ∀ env, Terminates loop_countdown_2 env := by
  refine ranking_terminates loop_countdown_2 (fun env => (env 0).toNat) ?_
  intro env h
  have hpos : 0 < env 0 := by
    simp only [loop_countdown_2, Loop.holds, Expr.eval, Op.apply, ofBool] at h
    by_cases hc : 0 < env 0
    · exact hc
    · simp [hc] at h
  simp [loop_countdown_2, Loop.step, Expr.eval, Op.apply, Ty.wrap, ofBool, two_pow_32]
  by_cases h5 : 5 < env 0 <;> simp [h5] <;> omega

/-- `loop`: while `running` holds, `i` advances toward 10 and `running`
becomes `i + 1 < 10` on the wrapped value. Rank by distance to 10 while `i`
is in range; from any other `i` the wrapped successor is either in range or
clears the flag, so one step reaches a smaller rank. -/
theorem loop_loop_1_terminates_proved : ∀ env, Terminates loop_loop_1 env := by
  refine ranking_terminates loop_loop_1
    (fun env => if env 0 = 0 then 0
      else if 0 ≤ env 1 ∧ env 1 < 10 then (10 - env 1).toNat + 1 else 12) ?_
  intro env h
  have hr : env 0 ≠ 0 := by simpa [loop_loop_1, Loop.holds, Expr.eval] using h
  have hm0 : 0 ≤ (env 1 + 1) % 4294967296 := Int.emod_nonneg _ (by decide)
  have hm1 : (env 1 + 1) % 4294967296 < 4294967296 := Int.emod_lt_of_pos _ (by decide)
  simp [loop_loop_1, Loop.step, Expr.eval, Op.apply, Ty.wrap, ofBool, two_pow_32, hr]
  by_cases hj : (env 1 + 1) % 4294967296 < 10
  · have hj' : ¬ 10 ≤ (env 1 + 1) % 4294967296 := by omega
    by_cases hi : 0 ≤ env 1 ∧ env 1 < 10 <;> simp [hj, hj', hi, hm0] <;> omega
  · have hj' : 10 ≤ (env 1 + 1) % 4294967296 := by omega
    by_cases hi : 0 ≤ env 1 ∧ env 1 < 10 <;> simp [hj, hj', hi, hm0] <;> omega

end Oak.Session
