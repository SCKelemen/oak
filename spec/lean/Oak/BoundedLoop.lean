namespace Oak.BoundedLoop

/-! # Bounded loops

Model for `docs/spec/85-discipline.md` section 3 (Power of Ten rule 2): a
loop is statically bounded when its guard compares a counter against a fixed
bound and every iteration advances the counter by at least one. `Trace`
records a run of such a loop: the guard must hold to take a step, and each
step advances the counter by `k ≥ 1`. The theorem gives the static iteration
bound the compiler's shape recognizer relies on: no run exceeds `n - i`
iterations, so in particular no infinite run exists. -/

/-- `Trace i n k m`: a run of `m` guarded iterations of a loop with counter
    starting at `i`, exclusive bound `n`, and per-iteration advance `k`. -/
inductive Trace (n k : Nat) : Nat → Nat → Prop
  | done {i : Nat} (h : ¬ i < n) : Trace n k i 0
  | step {i m : Nat} (hguard : i < n) (hk : 1 ≤ k)
      (rest : Trace n k (i + k) m) : Trace n k i (m + 1)

/-- **Static iteration bound**: a guarded advancing counter admits at most
    `n - i` iterations. -/
theorem trace_bounded {n k i m : Nat} (t : Trace n k i m) : m ≤ n - i := by
  induction t with
  | done _ => exact Nat.zero_le _
  | step hguard hk _ ih => omega

/-- Consequently the loop terminates: no run is longer than the bound
    itself, whatever the advance. -/
theorem no_run_exceeds_bound {n k i m : Nat} (t : Trace n k i m) : m ≤ n := by
  have := trace_bounded t
  omega

end Oak.BoundedLoop
