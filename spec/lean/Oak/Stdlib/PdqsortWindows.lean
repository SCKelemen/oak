import Oak.Stdlib.PdqsortLaws

set_option linter.unusedSimpArgs false

/-!
# Oak.Stdlib.PdqsortWindows — window permutations, write-backs, and fuel monotonicity

The first of three files proving that the extracted pdqsort sorts (the
permutation law is `Oak.Stdlib.PdqsortLaws`; the helper postconditions are
`Oak.Stdlib.PdqsortHelpers`; the main-loop invariant and the theorems are
`Oak.Stdlib.PdqsortSorted`). The argument is the classical one for an
iterative quicksort, stated over the extraction's explicit range stack:

* `WinPerm a b xs ys` says a helper rewrote the window `[a, b)` of `xs`
  into `ys` without touching anything outside it, and every value now in the
  window came from the window. Every in-place helper (the pattern breaker,
  the partial insertion sort, both partitions) and every window write-back
  (insertion sort, heap sort, reversal of `items[a:b]`) satisfies it.
* The two partitions get their postconditions: `sort_partition_u32` leaves
  everything left of `mid` at most the pivot, the pivot at `mid`, and
  everything right of `mid` at least the pivot; `sort_partition_equal_u32`
  leaves `[a, i')` at most the pivot and `[i', b)` above it. The partial
  insertion sort, when it reports the range sorted, has sorted it.
* `Ord items stack depth cur` is the ordering invariant of the main loop:
  two positions are in order unless they lie in the **same pending range**
  (the current range `cur`, or one of the `depth` ranges on the stack), and
  `Disj` says the pending ranges are pairwise disjoint. Finishing a range
  (insertion sort, heap sort, a successful partial insertion) removes it from
  the pending set; a partition replaces the current range by its two sides
  with the pivot between them final; the equal-elements partition finalizes
  the prefix of equal elements. When the loop stops, no range is pending,
  and `Ord` says the whole array is sorted.

Fuel: the extracted insertion and heap sorts have existence-style laws in
`Oak.Stdlib.SortLaws` (enough fuel ⇒ a sorted permutation). Here the sub-calls
run with whatever fuel the main loop has left, so those laws are bridged by
fuel monotonicity: a call that returns at some fuel returns the same value at
every larger fuel.
-/

namespace Oak.Stdlib.SortU32

/-! ## Window permutations -/

/-- `ys` is `xs` with only the window `[a, b)` rewritten, and every value now
in the window was in the window before. -/
def WinPerm (a b : Nat) (xs ys : Array UInt32) : Prop :=
  ys.size = xs.size ∧
  (∀ x, x < xs.size → (x < a ∨ b ≤ x) → ys.getD x 0 = xs.getD x 0) ∧
  (∀ i, a ≤ i → i < b → i < xs.size → ∃ k, a ≤ k ∧ k < b ∧ k < xs.size ∧ ys.getD i 0 = xs.getD k 0)

theorem WinPerm.refl (a b : Nat) (xs : Array UInt32) : WinPerm a b xs xs :=
  ⟨rfl, fun _ _ _ => rfl, fun i hai hib hi => ⟨i, hai, hib, hi, rfl⟩⟩

theorem WinPerm.trans {a b : Nat} {xs ys zs : Array UInt32} (h1 : WinPerm a b xs ys) (h2 : WinPerm a b ys zs) :
    WinPerm a b xs zs := by
  obtain ⟨hs1, hout1, hin1⟩ := h1
  obtain ⟨hs2, hout2, hin2⟩ := h2
  refine ⟨by rw [hs2, hs1], ?_, ?_⟩
  · intro x hx hout
    rw [hout2 x (by rw [hs1]; exact hx) hout, hout1 x hx hout]
  · intro i hai hib hi
    obtain ⟨k, hak, hkb, hk, hk'⟩ := hin2 i hai hib (by rw [hs1]; exact hi)
    obtain ⟨m, ham, hmb, hm, hm'⟩ := hin1 k hak hkb (by rw [← hs1]; exact hk)
    exact ⟨m, ham, hmb, hm, by rw [hk', hm']⟩

/-- A window permutation over a larger window. -/
theorem WinPerm.widen {a b : Nat} {xs ys : Array UInt32} (h : WinPerm a b xs ys) (a' b' : Nat)
    (ha : a' ≤ a) (hb : b ≤ b') : WinPerm a' b' xs ys := by
  obtain ⟨hs, hout, hin⟩ := h
  refine ⟨hs, fun x hx hx' => hout x hx (by omega), ?_⟩
  intro i hai hib hi
  by_cases hin' : a ≤ i ∧ i < b
  · obtain ⟨k, hak, hkb, hk, hk'⟩ := hin i hin'.1 hin'.2 hi
    exact ⟨k, by omega, by omega, hk, hk'⟩
  · exact ⟨i, hai, hib, hi, hout i hi (by omega)⟩

/-- The two stores of a swap at in-bounds positions `i`, `j` inside the window. -/
theorem two_stores_win (xs : Array UInt32) (a b i j : Nat) (hi : i < xs.size) (hj : j < xs.size)
    (hai : a ≤ i) (hib : i < b) (haj : a ≤ j) (hjb : j < b) :
    WinPerm a b xs ((xs.setIfInBounds i (xs.getD j 0)).setIfInBounds j (xs.getD i 0)) := by
  rw [two_stores_eq_swap xs i j hi hj]
  refine ⟨by simp, ?_, ?_⟩
  · intro x hx hout
    rw [swap_getD' xs i j hi hj x, if_neg (by omega), if_neg (by omega)]
  · intro k hak hkb hk
    rw [swap_getD' xs i j hi hj k]
    by_cases hkj : k = j
    · rw [if_pos hkj]; exact ⟨i, hai, hib, hi, rfl⟩
    · rw [if_neg hkj]
      by_cases hki : k = i
      · rw [if_pos hki]; exact ⟨j, haj, hjb, hj, rfl⟩
      · rw [if_neg hki]; exact ⟨k, hak, hkb, hk, rfl⟩

/-- Reads after the two stores of a swap. -/
theorem two_stores_getD (xs : Array UInt32) (i j : Nat) (hi : i < xs.size) (hj : j < xs.size) (k : Nat) :
    ((xs.setIfInBounds i (xs.getD j 0)).setIfInBounds j (xs.getD i 0)).getD k 0
      = if k = j then xs.getD i 0 else if k = i then xs.getD j 0 else xs.getD k 0 := by
  rw [two_stores_eq_swap xs i j hi hj]; exact swap_getD' xs i j hi hj k

/-- `sort_swap_u32` on in-bounds indices inside the window: the window
permutation and the read equations. -/
theorem swap_win (xs : Array UInt32) (a b : Nat) (i j : UInt32) (fuel : Nat) (ys : Array UInt32)
    (h : sort_swap_u32 xs i j fuel = some ((), ys)) (hi : i.toNat < xs.size) (hj : j.toNat < xs.size)
    (hai : a ≤ i.toNat) (hib : i.toNat < b) (haj : a ≤ j.toNat) (hjb : j.toNat < b) :
    WinPerm a b xs ys ∧
    (∀ k, ys.getD k 0 = if k = j.toNat then xs.getD i.toNat 0 else if k = i.toNat then xs.getD j.toNat 0 else xs.getD k 0) := by
  unfold sort_swap_u32 at h
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq, true_and] at h
  subst h
  exact ⟨two_stores_win xs a b i.toNat j.toNat hi hj hai hib haj hjb, two_stores_getD xs i.toNat j.toNat hi hj⟩

theorem swap_getD_eq (xs : Array UInt32) (i j : UInt32) (fuel : Nat) (ys : Array UInt32)
    (h : sort_swap_u32 xs i j fuel = some ((), ys)) (hi : i.toNat < xs.size) (hj : j.toNat < xs.size) (k : Nat) :
    ys.getD k 0 = if k = j.toNat then xs.getD i.toNat 0 else if k = i.toNat then xs.getD j.toNat 0 else xs.getD k 0 := by
  unfold sort_swap_u32 at h
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq, true_and] at h
  subst h
  exact two_stores_getD xs i.toNat j.toNat hi hj k

/-! ## Window write-backs

`items.extract 0 lo ++ short ++ items.extract (lo + short.size) items.size`
with `short` a permutation of `items.extract lo hi`, `lo ≤ hi ≤ items.size`. -/

theorem extract_getD (xs : Array UInt32) (lo hi k : Nat) (hk : k < min hi xs.size - lo) :
    (xs.extract lo hi).getD k 0 = xs.getD (lo + k) 0 := by
  have hk' : k < (xs.extract lo hi).size := by rw [Array.size_extract]; exact hk
  rw [getD_eq_getElem _ _ hk', Array.getElem_extract, getD_eq_getElem _ _ (by omega)]

theorem writeback_size (items short : Array UInt32) (lo hi : Nat) (hlo : lo ≤ hi) (hhi : hi ≤ items.size)
    (hs : short.size = hi - lo) :
    ((items.extract 0 lo ++ short) ++ items.extract (lo + short.size) items.size).size = items.size := by
  simp only [Array.size_append, Array.size_extract]
  omega

theorem writeback_getD_left (items short : Array UInt32) (lo hi x : Nat) (hlo : lo ≤ hi) (hhi : hi ≤ items.size)
    (hs : short.size = hi - lo) (hx : x < lo) :
    ((items.extract 0 lo ++ short) ++ items.extract (lo + short.size) items.size).getD x 0 = items.getD x 0 := by
  have hsz := writeback_size items short lo hi hlo hhi hs
  have hx' : x < ((items.extract 0 lo ++ short) ++ items.extract (lo + short.size) items.size).size := by omega
  rw [getD_eq_getElem _ _ hx', Array.getElem_append_left (by simp only [Array.size_append, Array.size_extract]; omega),
    Array.getElem_append_left (by simp only [Array.size_extract]; omega), Array.getElem_extract,
    getD_eq_getElem _ _ (by omega)]
  simp

theorem writeback_getD_mid (items short : Array UInt32) (lo hi x : Nat) (hlo : lo ≤ hi) (hhi : hi ≤ items.size)
    (hs : short.size = hi - lo) (hx1 : lo ≤ x) (hx2 : x < hi) :
    ((items.extract 0 lo ++ short) ++ items.extract (lo + short.size) items.size).getD x 0 = short.getD (x - lo) 0 := by
  have hsz := writeback_size items short lo hi hlo hhi hs
  have hx' : x < ((items.extract 0 lo ++ short) ++ items.extract (lo + short.size) items.size).size := by omega
  have hlen0 : (items.extract 0 lo).size = lo := by rw [Array.size_extract]; omega
  rw [getD_eq_getElem _ _ hx', Array.getElem_append_left (by simp only [Array.size_append]; omega),
    Array.getElem_append_right (by omega), getD_eq_getElem short (x - lo) (by omega)]
  simp only [hlen0]

theorem writeback_getD_right (items short : Array UInt32) (lo hi x : Nat) (hlo : lo ≤ hi) (hhi : hi ≤ items.size)
    (hs : short.size = hi - lo) (hx1 : hi ≤ x) (hx2 : x < items.size) :
    ((items.extract 0 lo ++ short) ++ items.extract (lo + short.size) items.size).getD x 0 = items.getD x 0 := by
  have hsz := writeback_size items short lo hi hlo hhi hs
  have hx' : x < ((items.extract 0 lo ++ short) ++ items.extract (lo + short.size) items.size).size := by omega
  have hlen0 : (items.extract 0 lo ++ short).size = hi := by simp only [Array.size_append, Array.size_extract]; omega
  rw [getD_eq_getElem _ _ hx', Array.getElem_append_right (by omega), Array.getElem_extract,
    getD_eq_getElem _ _ hx2]
  simp only [hlen0]
  congr 1
  omega

/-- A permutation of the window's extract holds only values of the window. -/
theorem perm_extract_values (items short : Array UInt32) (lo hi : Nat) (_hlo : lo ≤ hi) (hhi : hi ≤ items.size)
    (h : short.Perm (items.extract lo hi)) (m : Nat) (hm : m < short.size) :
    ∃ k, lo ≤ k ∧ k < hi ∧ short.getD m 0 = items.getD k 0 := by
  have hmem : short.getD m 0 ∈ items.extract lo hi := by
    rw [← Array.Perm.mem_iff h, getD_eq_getElem _ _ hm]
    exact Array.getElem_mem hm
  obtain ⟨i, hidx, hidx'⟩ := Array.mem_iff_getElem.mp hmem
  have hi2 : i < min hi items.size - lo := by rw [Array.size_extract] at hidx; exact hidx
  refine ⟨lo + i, by omega, by omega, ?_⟩
  rw [← hidx', Array.getElem_extract, getD_eq_getElem _ _ (by omega)]

/-- Writing a permutation of the window back is a window permutation of `items`. -/
theorem writeback_win (items short : Array UInt32) (lo hi : Nat) (hlo : lo ≤ hi) (hhi : hi ≤ items.size)
    (h : short.Perm (items.extract lo hi)) :
    WinPerm lo hi items ((items.extract 0 lo ++ short) ++ items.extract (lo + short.size) items.size) := by
  have hs : short.size = hi - lo := by rw [h.size_eq, Array.size_extract]; omega
  refine ⟨writeback_size items short lo hi hlo hhi hs, ?_, ?_⟩
  · intro x hx hout
    rcases hout with hlt | hge
    · exact writeback_getD_left items short lo hi x hlo hhi hs hlt
    · exact writeback_getD_right items short lo hi x hlo hhi hs hge hx
  · intro i hli hih hisz
    rw [writeback_getD_mid items short lo hi i hlo hhi hs hli hih]
    obtain ⟨k, hk1, hk2, hk3⟩ := perm_extract_values items short lo hi hlo hhi h (i - lo) (by omega)
    exact ⟨k, hk1, hk2, by omega, hk3⟩

/-! ## Fuel monotonicity for the insertion and heap sorts -/

theorem insertion_loop2_mono (fuel : Nat) : ∀ (xs : Array UInt32) (j : UInt32) (r : Array UInt32 × UInt32),
    sort_insertion_u32.loop2 xs j fuel = some r → sort_insertion_u32.loop2 xs j (fuel + 1) = some r := by
  induction fuel with
  | zero => intro xs j r h; simp [sort_insertion_u32.loop2] at h
  | succ fuel ih =>
    intro xs j r h
    unfold sort_insertion_u32.loop2 at h ⊢
    split at h
    · rename_i hc
      rw [if_pos hc]
      simp only [] at h ⊢
      exact ih _ _ _ h
    · rename_i hc
      rw [if_neg hc]
      exact h

theorem insertion_loop1_mono (fuel : Nat) : ∀ (xs : Array UInt32) (i : UInt32) (r : Array UInt32 × UInt32),
    sort_insertion_u32.loop1 xs i fuel = some r → sort_insertion_u32.loop1 xs i (fuel + 1) = some r := by
  induction fuel with
  | zero => intro xs i r h; simp [sort_insertion_u32.loop1] at h
  | succ fuel ih =>
    intro xs i r h
    unfold sort_insertion_u32.loop1 at h ⊢
    split at h
    · rename_i hc
      rw [if_pos hc]
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨st, h2, h1⟩ := h
      exact ⟨st, insertion_loop2_mono fuel _ _ _ h2, ih _ _ _ h1⟩
    · rename_i hc
      rw [if_neg hc]
      exact h

theorem insertion_mono (xs : Array UInt32) (fuel : Nat) (r : Unit × Array UInt32)
    (h : sort_insertion_u32 xs fuel = some r) : sort_insertion_u32 xs (fuel + 1) = some r := by
  unfold sort_insertion_u32 at h ⊢
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨st, h2, h1⟩ := h
  exact ⟨st, insertion_loop1_mono fuel _ _ _ h2, h1⟩

theorem insertion_mono_add (xs : Array UInt32) (fuel : Nat) (r : Unit × Array UInt32)
    (h : sort_insertion_u32 xs fuel = some r) : ∀ k, sort_insertion_u32 xs (fuel + k) = some r := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih => exact insertion_mono xs _ r ih

theorem insertion_mono_le (xs : Array UInt32) (fuel fuel' : Nat) (hle : fuel ≤ fuel') (r : Unit × Array UInt32)
    (h : sort_insertion_u32 xs fuel = some r) : sort_insertion_u32 xs fuel' = some r := by
  have := insertion_mono_add xs fuel r h (fuel' - fuel)
  rwa [Nat.add_sub_cancel' hle] at this

theorem sift_loop_mono (fuel : Nat) : ∀ (xs : Array UInt32) (end_ root : UInt32) (more : Bool)
    (r : Array UInt32 × UInt32 × Bool),
    sort_sift_down_u32.loop1 xs end_ root more fuel = some r →
    sort_sift_down_u32.loop1 xs end_ root more (fuel + 1) = some r := by
  induction fuel with
  | zero => intro xs end_ root more r h; simp [sort_sift_down_u32.loop1] at h
  | succ fuel ih =>
    intro xs end_ root more r h
    unfold sort_sift_down_u32.loop1 at h ⊢
    split at h
    · rename_i hc
      rw [if_pos hc]
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨st, h2, h1⟩ := h
      exact ⟨st, h2, ih _ _ _ _ _ h1⟩
    · rename_i hc
      rw [if_neg hc]
      exact h

theorem sift_down_mono (xs : Array UInt32) (start end_ : UInt32) (fuel : Nat) (r : Unit × Array UInt32)
    (h : sort_sift_down_u32 xs start end_ fuel = some r) : sort_sift_down_u32 xs start end_ (fuel + 1) = some r := by
  unfold sort_sift_down_u32 at h ⊢
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨st, h2, h1⟩ := h
  exact ⟨st, sift_loop_mono fuel _ _ _ _ _ h2, h1⟩

theorem heap_loop1_mono (fuel : Nat) : ∀ (xs : Array UInt32) (n start : UInt32) (r : Array UInt32 × UInt32),
    sort_heap_u32.loop1 xs n start fuel = some r → sort_heap_u32.loop1 xs n start (fuel + 1) = some r := by
  induction fuel with
  | zero => intro xs n start r h; simp [sort_heap_u32.loop1] at h
  | succ fuel ih =>
    intro xs n start r h
    unfold sort_heap_u32.loop1 at h ⊢
    split at h
    · rename_i hc
      rw [if_pos hc]
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨st, h2, h1⟩ := h
      exact ⟨st, sift_down_mono _ _ _ fuel _ h2, ih _ _ _ _ h1⟩
    · rename_i hc
      rw [if_neg hc]
      exact h

theorem heap_loop2_mono (fuel : Nat) : ∀ (xs : Array UInt32) (end_ : UInt32) (r : Array UInt32 × UInt32),
    sort_heap_u32.loop2 xs end_ fuel = some r → sort_heap_u32.loop2 xs end_ (fuel + 1) = some r := by
  induction fuel with
  | zero => intro xs end_ r h; simp [sort_heap_u32.loop2] at h
  | succ fuel ih =>
    intro xs end_ r h
    unfold sort_heap_u32.loop2 at h ⊢
    split at h
    · rename_i hc
      rw [if_pos hc]
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨st, h2, h1⟩ := h
      exact ⟨st, sift_down_mono _ _ _ fuel _ h2, ih _ _ _ h1⟩
    · rename_i hc
      rw [if_neg hc]
      exact h

theorem heap_mono (xs : Array UInt32) (fuel : Nat) (r : Unit × Array UInt32)
    (h : sort_heap_u32 xs fuel = some r) : sort_heap_u32 xs (fuel + 1) = some r := by
  unfold sort_heap_u32 at h ⊢
  simp only [Option.pure_def, Option.bind_eq_bind] at h ⊢
  split at h
  · rename_i hc
    rw [if_pos hc]
    simp only [Option.bind_eq_some_iff] at h ⊢
    obtain ⟨items, ⟨st1, h1, st2, h2, h3⟩, h4⟩ := h
    exact ⟨items, ⟨st1, heap_loop1_mono fuel _ _ _ _ h1, st2, heap_loop2_mono fuel _ _ _ h2, h3⟩, h4⟩
  · rename_i hc
    rw [if_neg hc]
    exact h

theorem heap_mono_add (xs : Array UInt32) (fuel : Nat) (r : Unit × Array UInt32)
    (h : sort_heap_u32 xs fuel = some r) : ∀ k, sort_heap_u32 xs (fuel + k) = some r := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih => exact heap_mono xs _ r ih

theorem heap_mono_le (xs : Array UInt32) (fuel fuel' : Nat) (hle : fuel ≤ fuel') (r : Unit × Array UInt32)
    (h : sort_heap_u32 xs fuel = some r) : sort_heap_u32 xs fuel' = some r := by
  have := heap_mono_add xs fuel r h (fuel' - fuel)
  rwa [Nat.add_sub_cancel' hle] at this

/-- Whenever the extracted insertion sort returns, its output is sorted. -/
theorem insertion_sorted_partial (xs : Array UInt32) (fuel : Nat) (ys : Array UInt32)
    (h : sort_insertion_u32 xs fuel = some ((), ys)) (hsmall : xs.size < 2 ^ 32) : SortedPrefix ys ys.size := by
  have h' := insertion_mono_le xs fuel (fuel + 2 * xs.size + 1) (by omega) _ h
  obtain ⟨out, heq, _, _, hsorted⟩ := sort_insertion_spec xs hsmall (fuel + 2 * xs.size + 1) (by omega)
  rw [heq] at h'
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at h'
  subst h'
  exact hsorted

/-- Whenever the extracted heap sort returns, its output is sorted. -/
theorem heap_sorted_partial (xs : Array UInt32) (fuel : Nat) (ys : Array UInt32)
    (h : sort_heap_u32 xs fuel = some ((), ys)) (hsmall : xs.size < 2 ^ 31) : SortedPrefix ys ys.size := by
  have h' := heap_mono_le xs fuel (fuel + 3 * xs.size + 4) (by omega) _ h
  obtain ⟨out, heq, _, _, hsorted⟩ := sort_heap_spec xs hsmall (fuel + 3 * xs.size + 4) (by omega)
  rw [heq] at h'
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at h'
  subst h'
  exact hsorted

/-! ## Sorted windows -/

/-- Positions `[lo, hi)` are in non-decreasing order. -/
def SortedRange (xs : Array UInt32) (lo hi : Nat) : Prop :=
  ∀ x y, lo ≤ x → x < y → y < hi → (xs.getD x 0).toNat ≤ (xs.getD y 0).toNat

theorem SortedRange.mono {xs : Array UInt32} {lo hi lo' hi' : Nat} (h : SortedRange xs lo hi) (hlo : lo ≤ lo') (hhi : hi' ≤ hi) :
    SortedRange xs lo' hi' := fun x y hx hxy hy => h x y (by omega) hxy (by omega)

/-- A sorted array written back over the window `[lo, hi)` sorts the window. -/
theorem writeback_sorted (items short : Array UInt32) (lo hi : Nat) (hlo : lo ≤ hi) (hhi : hi ≤ items.size)
    (hs : short.size = hi - lo) (hsorted : SortedPrefix short short.size) :
    SortedRange ((items.extract 0 lo ++ short) ++ items.extract (lo + short.size) items.size) lo hi := by
  intro x y hx hxy hy
  rw [writeback_getD_mid items short lo hi x hlo hhi hs hx (by omega),
    writeback_getD_mid items short lo hi y hlo hhi hs (by omega) hy]
  exact hsorted (x - lo) (y - lo) (by omega) (by omega)

end Oak.Stdlib.SortU32
