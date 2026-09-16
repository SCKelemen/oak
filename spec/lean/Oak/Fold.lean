/-!
# Verified fold vectorization

`nativegen/vector_fold.go` (docs/spec/94-assembler.md §9 "Fold
vectorization") rewrites a reduction whose element expression is lane-wise
over spans of one length — the dot product `total = total + a[i] * b[i]` —
before lowering,

    while i < len(a) { acc = acc + f(a[i], b[i], …); i = i + 1 }

into a main loop that computes `f` over each block of `L` elements as one
vector (`simd.load`, the lane-wise operations) and then folds the vector's
lanes into the accumulator one at a time, in element order, under the
slack guard `len(a) >= L && i <= len(a) - L`, and the remainder loop as
written. The verifier proves the assembly against the rewritten body;
this file is the rewrite's own correctness: over the list of the span's
elements, the blocked fold equals the sequential fold. Nothing is assumed
of `f` beyond being a function of one element position (each simd
operation is lane-wise by its specification, docs/spec/93-simd.md §1) and
nothing of the accumulation `g` at all — the lanes reach the accumulator
in the order the elements did, so a floating-point accumulator rounds in
the same order and the rewrite reassociates nothing. That is why a float
reduction vectorizes here where `Oak.Reduction`'s strided accumulators,
which need associativity, take integers only.
-/

namespace Oak.Fold

/-- The sequential loop: the accumulator folded with each element's value. -/
def sequential {α β γ : Type} (f : α → γ) (g : β → γ → β) (acc : β) (l : List α) : β :=
  l.foldl (fun a e => g a (f e)) acc

/-- The rewritten loops with a trip budget: while at least `L` elements
    remain (and `L` is positive), one block of `L` is computed as a vector
    and its lanes folded in order, and the loop continues past it;
    otherwise the remainder is folded one element at a time. The budget is
    the loop's trip bound; `blocked` below spends the list's length, which
    every run stays within. -/
def blockedFuel {α β γ : Type} (L : Nat) (f : α → γ) (g : β → γ → β) : Nat → β → List α → β
  | 0, acc, l => l.foldl (fun a e => g a (f e)) acc
  | n + 1, acc, l =>
    if L ≤ l.length ∧ 0 < L then
      blockedFuel L f g n (((l.take L).map f).foldl g acc) (l.drop L)
    else l.foldl (fun a e => g a (f e)) acc

/-- The rewritten loops over the elements. -/
def blocked {α β γ : Type} (L : Nat) (f : α → γ) (g : β → γ → β) (acc : β) (l : List α) : β :=
  blockedFuel L f g l.length acc l

/-- One block: the vector's lanes folded in order into the accumulator is
    the fold of the block's elements. -/
theorem block_eq {α β γ : Type} (L : Nat) (f : α → γ) (g : β → γ → β) (acc : β) (l : List α) :
    ((l.take L).map f).foldl g acc = (l.take L).foldl (fun a e => g a (f e)) acc := by
  rw [List.foldl_map]

theorem blockedFuel_eq {α β γ : Type} (L : Nat) (f : α → γ) (g : β → γ → β) :
    ∀ (n : Nat) (acc : β) (l : List α),
      blockedFuel L f g n acc l = l.foldl (fun a e => g a (f e)) acc := by
  intro n
  induction n with
  | zero => intro acc l; rfl
  | succ n ih =>
    intro acc l
    simp only [blockedFuel]
    split
    · rw [ih, block_eq, ← List.foldl_append, List.take_append_drop]
    · rfl

/-- **The rewrite is the loop**: the blocked fold equals the sequential
    fold from the same accumulator — the value the vector main loop and
    the scalar remainder leave in the accumulator is the value the scalar
    loop leaves, whatever `f` and `g` are. -/
theorem blocked_eq {α β γ : Type} (L : Nat) (f : α → γ) (g : β → γ → β) (acc : β) (l : List α) :
    blocked L f g acc l = sequential f g acc l :=
  blockedFuel_eq L f g l.length acc l

end Oak.Fold
