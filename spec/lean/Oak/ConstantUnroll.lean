/-!
# Verified constant-trip unrolling

`nativegen/unroll_constant.go` (docs/spec/94-assembler.md §9 "Constant-trip
loops") rewrites a loop whose trip count is a literal,

    i: u32 = 0
    while i < u32(N) { body(i); i = i + u32(1) }

into `N` copies of the body, the `k`th with `i` replaced by the literal
`k`, followed by `i = u32(N)`. The verifier proves the assembly against the
rewritten body; this file is the rewrite's own correctness: from any state,
the loop that steps `i` from zero while it is below `N` computes what the
unrolled sequence computes. Nothing is assumed of the body beyond being a
function of the trip's index and the state — it may not write `i`, which
the matcher checks.
-/

namespace Oak.ConstantUnroll

/-- The loop from index `i` with a trip budget: while `i < n` the body
    runs at `i` and the loop continues at `i + 1`. -/
def loopFrom {σ : Type} (f : Nat → σ → σ) (n : Nat) : Nat → Nat → σ → σ
  | 0, _, s => s
  | fuel + 1, i, s => if i < n then loopFrom f n fuel (i + 1) (f i s) else s

/-- The loop as written: from zero, with the budget it spends. -/
def loop {σ : Type} (f : Nat → σ → σ) (n : Nat) (s : σ) : σ :=
  loopFrom f n n 0 s

/-- The unrolled sequence: the body at `0`, then at `1`, …, then at `n - 1`. -/
def unrolled {σ : Type} (f : Nat → σ → σ) (n : Nat) (s : σ) : σ :=
  (List.range n).foldl (fun s k => f k s) s

theorem loopFrom_eq {σ : Type} (f : Nat → σ → σ) (n : Nat) :
    ∀ (fuel i : Nat) (s : σ), i + fuel = n →
      loopFrom f n fuel i s = (List.range' i fuel).foldl (fun s k => f k s) s := by
  intro fuel
  induction fuel with
  | zero => intro i s _; rfl
  | succ fuel ih =>
    intro i s h
    have lt : i < n := by omega
    simp only [loopFrom, lt, if_true, List.range'_succ, List.foldl_cons]
    exact ih (i + 1) (f i s) (by omega)

/-- **The rewrite is the loop**: the loop from zero equals the unrolled
    sequence, whatever the body does to the state. -/
theorem loop_eq_unrolled {σ : Type} (f : Nat → σ → σ) (n : Nat) (s : σ) :
    loop f n s = unrolled f n s := by
  unfold loop unrolled
  rw [loopFrom_eq f n n 0 s (by omega), List.range_eq_range']

end Oak.ConstantUnroll
