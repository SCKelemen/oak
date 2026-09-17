/-!
# Verified lane-wise accumulators

`nativegen/vector_lanes.go` (docs/spec/94-assembler.md §9 "Lane-wise
accumulators") rewrites a loop whose body updates `L` independent
accumulators, one per element of each block of `L`,

    while len(a) >= L && i <= len(a) - L {
      acc[0] = acc[0] + f(a[i]); …; acc[L-1] = acc[L-1] + f(a[i + L-1])
      i = i + L
    }

into the same loop over vector accumulators: each block loaded as vectors,
`f` applied lane-wise, and each lane added to its own accumulator — the
accumulators loaded from `acc` before the loop and stored back after it.
The verifier proves the assembly against the rewritten body; this file is
the rewrite's own correctness: over the list of blocks, the vector fold
equals the `L` scalar folds, lane by lane. Nothing is assumed of `f` or of
the accumulation `g`: lane `k` of the vector form meets exactly the values
`acc[k]` met, in the same order, so a floating-point accumulator rounds as
before. What the rewrite uses is that the `L` statements of a block
touch `L` different lanes, so their order is immaterial and one lane-wise
step does all of them (docs/spec/93-simd.md §1: each simd operation is
lane-wise by its specification).
-/

namespace Oak.Lanes

/-- One block's `L` elements and the `L` accumulators, as functions of the
    lane. -/
abbrev Lanes (L : Nat) (α : Type) := Fin L → α

/-- The scalar statements of one block, in lane order: lane `k` takes
    `g (acc k) (f (blk k))`, the other lanes stand. -/
def scalarStep {L : Nat} {α β γ : Type} (f : α → γ) (g : β → γ → β)
    (blk : Lanes L α) (acc : Lanes L β) : Lanes L β :=
  fun k => g (acc k) (f (blk k))

/-- The vector statement of one block: `f` lane-wise, then the lane-wise
    accumulation. -/
def vectorStep {L : Nat} {α β γ : Type} (f : α → γ) (g : β → γ → β)
    (blk : Lanes L α) (acc : Lanes L β) : Lanes L β :=
  fun k => g (acc k) ((fun j => f (blk j)) k)

/-- One statement of the scalar block updates one lane and leaves the rest. -/
def laneStatement {L : Nat} {α β γ : Type} (f : α → γ) (g : β → γ → β)
    (blk : Lanes L α) (k : Fin L) (acc : Lanes L β) : Lanes L β :=
  fun j => if j = k then g (acc j) (f (blk j)) else acc j

/-- The `L` statements in lane order, as the scalar loop body runs them. -/
def statements {L : Nat} {α β γ : Type} (f : α → γ) (g : β → γ → β)
    (blk : Lanes L α) (acc : Lanes L β) : Lanes L β :=
  (List.finRange L).foldl (fun acc k => laneStatement f g blk k acc) acc

/-- A statement at lane `k` does not read what an earlier statement wrote:
    after any prefix of the statements, lane `j` holds either its start or
    its own update, never another lane's. -/
theorem statements_lane {L : Nat} {α β γ : Type} (f : α → γ) (g : β → γ → β)
    (blk : Lanes L α) (acc : Lanes L β) (ks : List (Fin L)) (h : ks.Nodup) (j : Fin L) :
    (ks.foldl (fun acc k => laneStatement f g blk k acc) acc) j
      = if j ∈ ks then g (acc j) (f (blk j)) else acc j := by
  induction ks generalizing acc with
  | nil => simp
  | cons k ks ih =>
    rw [List.nodup_cons] at h
    obtain ⟨hk, hks⟩ := h
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih _ hks]
    by_cases hj : j = k
    · subst hj
      simp [laneStatement, hk]
    · simp [laneStatement, hj]

/-- **The statements are the lane-wise step**: running the `L` scalar
    statements in order equals one vector step. -/
theorem statements_eq_vectorStep {L : Nat} {α β γ : Type} (f : α → γ) (g : β → γ → β)
    (blk : Lanes L α) (acc : Lanes L β) :
    statements f g blk acc = vectorStep f g blk acc := by
  funext j
  unfold statements vectorStep
  rw [statements_lane f g blk acc (List.finRange L) (List.nodup_finRange L)]
  simp [List.mem_finRange]

/-- Over the blocks of the main loop, the scalar loop and the vector loop
    compute the same accumulators. -/
theorem blocks_eq {L : Nat} {α β γ : Type} (f : α → γ) (g : β → γ → β)
    (blocks : List (Lanes L α)) (acc : Lanes L β) :
    blocks.foldl (fun acc blk => statements f g blk acc) acc
      = blocks.foldl (fun acc blk => vectorStep f g blk acc) acc := by
  induction blocks generalizing acc with
  | nil => rfl
  | cons blk rest ih =>
    simp only [List.foldl_cons]
    rw [statements_eq_vectorStep, ih]

end Oak.Lanes
