/-!
# Resumable work and cancellation

Abstract scheduling laws: partitioning a deterministic transition sequence
preserves its state; an invariant preserved by each transition survives
any quantum; cancellation carries no result. These do not refine the Oak
mutable stack or replay tape. Compiled differential tests cover that bridge.
-/
namespace Oak.SolverScheduling

inductive Run (σ α : Type) where
  | pending : σ → Run σ α
  | finished : α → Run σ α
  | cancelled : Run σ α
  deriving DecidableEq

def advance (step : σ → Run σ α) : Run σ α → Run σ α
  | .pending s => step s
  | .finished a => .finished a
  | .cancelled => .cancelled

def run (step : σ → Run σ α) : Nat → Run σ α → Run σ α
  | 0, s => s
  | n + 1, s => run step n (advance step s)

theorem split_quantum (step : σ → Run σ α) (a b : Nat) (s : Run σ α) :
    run step (a + b) s = run step b (run step a s) := by
  induction a generalizing s with
  | zero => simp [run]
  | succ a ih => simpa [Nat.succ_add, run] using ih (advance step s)

theorem preserves (step : σ → Run σ α) (invariant : Run σ α → Prop)
    (each : ∀ s, invariant s → invariant (advance step s))
    (n : Nat) (s : Run σ α) (initial : invariant s) :
    invariant (run step n s) := by
  induction n generalizing s with
  | zero => exact initial
  | succ n ih => exact ih _ (each _ initial)

theorem cancelled_stable (step : σ → Run σ α) (n : Nat) :
    run step n .cancelled = .cancelled := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [run, advance] using ih

theorem cancelled_has_no_result (step : σ → Run σ α) (n : Nat) (a : α) :
    run step n .cancelled ≠ .finished a := by
  rw [cancelled_stable]
  intro impossible
  cases impossible

theorem finished_stable (step : σ → Run σ α) (n : Nat) (a : α) :
    run step n (.finished a) = .finished a := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [run, advance] using ih

end Oak.SolverScheduling
