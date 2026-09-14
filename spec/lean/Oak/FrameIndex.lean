/-!
# Frame loads at a data-dependent index

Model for docs/spec/94-assembler.md §8 (frame loads at a data-dependent
index). Under the checker's guard `cmp wI, #K; b.hs trap` a load from an
owned frame array of `K` elements at index `wI` reads the elements merged
under the index: from the last element down, `if idx = k then v k else …`,
the last element the default. The Oak side merges an array element under a
symbolic index by the same fold, so on every index below the bound both
read element `idx` (`chain_select`), and on an index at or past the bound
— the path the guard's trap removes — both read the last element
(`chain_beyond`), so no mismatch is invented there.
-/

namespace Oak.FrameIndex

variable {β : Type}

/-- The merge of elements `0 … k-1` under `idx`, with `v last` as the
    default when none matches: `chain v idx last k`. -/
def chain (v : Nat → β) (idx last : Nat) : Nat → β
  | 0 => v last
  | k + 1 => if idx = k then v k else chain v idx last k

/-- Below the count, the chain selects the element. -/
theorem chain_select_lt (v : Nat → β) (idx last k : Nat) (h : idx < k) :
    chain v idx last k = v idx := by
  induction k with
  | zero => omega
  | succ k ih =>
    unfold chain
    by_cases hk : idx = k
    · simp [hk]
    · have : idx < k := by omega
      simp [hk, ih this]

/-- At or past the count, the chain is the default. -/
theorem chain_default (v : Nat → β) (idx last k : Nat) (h : k ≤ idx) :
    chain v idx last k = v last := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold chain
    have hk : idx ≠ k := by omega
    simp [hk, ih (by omega)]

/-- **The merged read**: the verifier's fold over `K` elements is
    `chain v idx (K-1) (K-1)` — elements `0 … K-2` tested, the last the
    default — and on every guarded index `idx < K` it is element `idx`. -/
theorem chain_select (v : Nat → β) (idx K : Nat) (hK : 0 < K) (h : idx < K) :
    chain v idx (K - 1) (K - 1) = v idx := by
  by_cases hl : idx = K - 1
  · subst hl
    exact chain_default v _ _ _ (Nat.le_refl _)
  · exact chain_select_lt v idx (K - 1) (K - 1) (by omega)

/-- **Beyond the bound**: an index at or past `K` reads the last element
    — on both sides, the machine's path there having trapped. -/
theorem chain_beyond (v : Nat → β) (idx K : Nat) (hK : 0 < K) (h : K ≤ idx) :
    chain v idx (K - 1) (K - 1) = v (K - 1) :=
  chain_default v idx (K - 1) (K - 1) (by omega)

end Oak.FrameIndex
