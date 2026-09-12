import Oak.Stdlib.PdqsortHelpers

set_option linter.unusedSimpArgs false

/-!
# Oak.Stdlib.PdqsortSorted — the extracted pdqsort sorts

The last of three files. `sort_span_budget_u32.loop1` keeps a current range
`[a, b)` and a stack of pending ranges. The invariant is that every pair of
positions that does not share a pending range is already in order (`Ord`),
and that the pending ranges are pairwise disjoint (`Disj`). Every helper is a
window permutation of the current range and so keeps `Ord`; finishing a
window (insertion, heap, or a successful partial insertion) removes the
current range; a partition splits it into two pending ranges around a pivot
that is already final; the equal-elements partition shrinks it. When the
stack is empty and the current range is done, `Ord` says the whole array is
sorted.

Together with `sort_span_perm` this gives full functional correctness of the
extracted `sort_u32_span`: whenever it returns, the result is a sorted
permutation of the input.
-/

namespace Oak.Stdlib.SortU32

/-! ## Pending ranges -/

/-- Lower bound of the pending range stored at stack level `k`. -/
def Rlo (stack : Array UInt32) (k : Nat) : Nat := (stack.getD (3 * k) 0).toNat

/-- Upper bound (exclusive) of the pending range stored at stack level `k`. -/
def Rhi (stack : Array UInt32) (k : Nat) : Nat := (stack.getD (3 * k + 1) 0).toNat

/-- Positions `i` and `j` share a pending range: the current one `[lo, hi)` or
a stacked one below `depth`. -/
def Same (stack : Array UInt32) (depth lo hi i j : Nat) : Prop :=
  (lo ≤ i ∧ i < hi ∧ lo ≤ j ∧ j < hi) ∨
  (∃ k, k < depth ∧ Rlo stack k ≤ i ∧ i < Rhi stack k ∧ Rlo stack k ≤ j ∧ j < Rhi stack k)

/-- Every pair of positions that does not share a pending range is in order. -/
def Ord (items stack : Array UInt32) (depth lo hi : Nat) : Prop :=
  ∀ i j, i < j → j < items.size → ¬ Same stack depth lo hi i j →
    (items.getD i 0).toNat ≤ (items.getD j 0).toNat

/-- The pending ranges are pairwise disjoint. -/
def Disj (stack : Array UInt32) (depth lo hi : Nat) : Prop :=
  (∀ k, k < depth → hi ≤ Rlo stack k ∨ Rhi stack k ≤ lo) ∧
  (∀ k l, k < l → l < depth → Rhi stack k ≤ Rlo stack l ∨ Rhi stack l ≤ Rlo stack k)

/-- With no pending range at all, `Ord` is sortedness. -/
theorem sorted_of_ord0 (items stack : Array UInt32) (hord : Ord items stack 0 0 0) :
    SortedPrefix items items.size := by
  intro i j hij hj
  apply hord i j hij hj
  intro hsm
  rcases hsm with hsm | ⟨k, hk, -⟩
  · omega
  · exact absurd hk (Nat.not_lt_zero k)

/-! ## Preservation -/

/-- A window permutation of the current range keeps `Ord`. -/
theorem ord_win (items ys stack : Array UInt32) (depth a b : Nat)
    (hord : Ord items stack depth a b) (hdisj : Disj stack depth a b) (hw : WinPerm a b items ys)
    (hb : b ≤ items.size) : Ord ys stack depth a b := by
  obtain ⟨hsize, hout, hin⟩ := hw
  intro i j hij hj hns
  rw [hsize] at hj
  have hfree : ∀ x, a ≤ x → x < b → ∀ k, k < depth → ¬ (Rlo stack k ≤ x ∧ x < Rhi stack k) := by
    intro x hx1 hx2 k hk hxk
    rcases hdisj.1 k hk with h | h <;> omega
  by_cases hi : a ≤ i ∧ i < b
  · by_cases hj' : a ≤ j ∧ j < b
    · exact absurd (Or.inl ⟨hi.1, hi.2, hj'.1, hj'.2⟩) hns
    · have hjb : b ≤ j := by omega
      obtain ⟨k, hk1, hk2, hk3, hk4⟩ := hin i hi.1 hi.2 (by omega)
      rw [hk4, hout j hj (Or.inr hjb)]
      apply hord k j (by omega) hj
      intro hs
      rcases hs with hs | ⟨m, hm, hm1, hm2, hm3, hm4⟩
      · omega
      · exact hfree k hk1 hk2 m hm ⟨hm1, hm2⟩
  · by_cases hj' : a ≤ j ∧ j < b
    · have hia : i < a := by omega
      obtain ⟨k, hk1, hk2, hk3, hk4⟩ := hin j hj'.1 hj'.2 (by omega)
      rw [hk4, hout i (by omega) (Or.inl hia)]
      apply hord i k (by omega) (by omega)
      intro hs
      rcases hs with hs | ⟨m, hm, hm1, hm2, hm3, hm4⟩
      · omega
      · exact hfree k hk1 hk2 m hm ⟨hm3, hm4⟩
    · rw [hout i (by omega) (by omega), hout j hj (by omega)]
      exact hord i j hij hj hns

/-- Once the current range is sorted it can be dropped. -/
theorem ord_finish (items stack : Array UInt32) (depth a b : Nat)
    (hord : Ord items stack depth a b) (hs : SortedRange items a b) : Ord items stack depth 0 0 := by
  intro i j hij hj hns
  by_cases hin : a ≤ i ∧ j < b
  · exact hs i j hin.1 hij hin.2
  · apply hord i j hij hj
    intro hsm
    rcases hsm with hsm | hsm
    · omega
    · exact hns (Or.inr hsm)

theorem disj_none {stack : Array UInt32} {depth a b : Nat} (hdisj : Disj stack depth a b) :
    Disj stack depth 0 0 :=
  ⟨fun _ _ => Or.inl (Nat.zero_le _), hdisj.2⟩

/-- Popping the top of the stack makes it the current range. -/
theorem ord_pop (items stack : Array UInt32) (d : Nat) (hord : Ord items stack (d + 1) 0 0) :
    Ord items stack d (Rlo stack d) (Rhi stack d) := by
  intro i j hij hj hns
  apply hord i j hij hj
  intro hsm
  rcases hsm with hsm | ⟨k, hk, hk1, hk2, hk3, hk4⟩
  · omega
  · by_cases hkd : k = d
    · rw [hkd] at hk1 hk2 hk3 hk4
      exact hns (Or.inl ⟨hk1, hk2, hk3, hk4⟩)
    · exact hns (Or.inr ⟨k, by omega, hk1, hk2, hk3, hk4⟩)

theorem disj_pop (stack : Array UInt32) (d : Nat) (hdisj : Disj stack (d + 1) 0 0) :
    Disj stack d (Rlo stack d) (Rhi stack d) := by
  refine ⟨?_, fun k l hkl hl => hdisj.2 k l hkl (by omega)⟩
  intro k hk
  rcases hdisj.2 k d hk (Nat.lt_succ_self _) with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- The equal-elements partition shrinks the current range to `[i', b)`:
everything before `i'` is at most the pivot value `v` and, being at least
`v` as well, is already in order. -/
theorem ord_shrink (items stack : Array UInt32) (depth a b i' v : Nat)
    (hord : Ord items stack depth a b) (_hi1 : a ≤ i') (_hi2 : i' ≤ b)
    (hlow : ∀ x, a ≤ x → x < b → v ≤ (items.getD x 0).toNat)
    (hle : ∀ x, a ≤ x → x < i' → (items.getD x 0).toNat ≤ v)
    (hgt : ∀ y, i' ≤ y → y < b → v < (items.getD y 0).toNat) : Ord items stack depth i' b := by
  intro i j hij hj hns
  by_cases hin : a ≤ i ∧ j < b
  · by_cases hii : i < i'
    · by_cases hjj : j < i'
      · exact Nat.le_trans (hle i hin.1 hii) (hlow j (by omega) hin.2)
      · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (hle i hin.1 hii) (hgt j (by omega) hin.2))
    · exact absurd (Or.inl ⟨by omega, by omega, by omega, hin.2⟩) hns
  · apply hord i j hij hj
    intro hsm
    rcases hsm with hsm | hsm
    · omega
    · exact hns (Or.inr hsm)

theorem disj_shrink (stack : Array UInt32) (depth a b i' : Nat) (hdisj : Disj stack depth a b) (ha : a ≤ i') :
    Disj stack depth i' b := by
  refine ⟨?_, hdisj.2⟩
  intro k hk
  rcases hdisj.1 k hk with h | h
  · exact Or.inl h
  · exact Or.inr (by omega)

/-- The equal-elements partition step of the main loop, from the state before
the partition: the element just before the range is at least the pivot value,
so every element of the range is, and the low side is all equal to it. -/
theorem ord_equal_step (items ys stack : Array UInt32) (depth a b i' p : Nat)
    (hord : Ord items stack depth a b) (hdisj : Disj stack depth a b) (hw : WinPerm a b items ys)
    (hb : b ≤ items.size) (ha : 0 < a)
    (hge : (items.getD p 0).toNat ≤ (items.getD (a - 1) 0).toNat)
    (hi1 : a ≤ i') (hi2 : i' ≤ b)
    (hle : ∀ x, a ≤ x → x < i' → (ys.getD x 0).toNat ≤ (items.getD p 0).toNat)
    (hgt : ∀ y, i' ≤ y → y < b → (items.getD p 0).toNat < (ys.getD y 0).toNat) :
    Ord ys stack depth i' b := by
  have hord' := ord_win items ys stack depth a b hord hdisj hw hb
  have hlow : ∀ x, a ≤ x → x < b → (items.getD p 0).toNat ≤ (ys.getD x 0).toNat := by
    intro x hx1 hx2
    obtain ⟨k, hk1, hk2, hk3, hk4⟩ := hw.2.2 x hx1 hx2 (by omega)
    rw [hk4]
    refine Nat.le_trans hge (hord (a - 1) k (by omega) (by omega) ?_)
    intro hsm
    rcases hsm with hsm | ⟨m, hm, hm1, hm2, hm3, hm4⟩
    · omega
    · rcases hdisj.1 m hm with h | h <;> omega
  exact ord_shrink ys stack depth a b i' (items.getD p 0).toNat hord' hi1 hi2 hlow hle hgt

/-- A partition of the current range `[a, b)` around a final pivot at `mid`:
one side becomes the new current range `[clo, chi)`, the other is pushed as
`[plo, phi)` at level `depth`. -/
theorem ord_split (ys stack stack' : Array UInt32) (depth a mid b clo chi plo phi : Nat)
    (hord : Ord ys stack depth a b) (_hmid1 : a ≤ mid) (_hmid2 : mid < b)
    (hL : ∀ x, a ≤ x → x < mid → (ys.getD x 0).toNat ≤ (ys.getD mid 0).toNat)
    (hR : ∀ y, mid < y → y < b → (ys.getD mid 0).toNat ≤ (ys.getD y 0).toNat)
    (hkeep : ∀ k, k < depth → Rlo stack' k = Rlo stack k ∧ Rhi stack' k = Rhi stack k)
    (hplo : Rlo stack' depth = plo) (hphi : Rhi stack' depth = phi)
    (hsides : (clo = a ∧ chi = mid ∧ plo = mid + 1 ∧ phi = b) ∨ (clo = mid + 1 ∧ chi = b ∧ plo = a ∧ phi = mid)) :
    Ord ys stack' (depth + 1) clo chi := by
  intro i j hij hj hns
  have hnew : ∀ x y, (a ≤ x ∧ x < mid ∧ a ≤ y ∧ y < mid) ∨ (mid < x ∧ x < b ∧ mid < y ∧ y < b) →
      Same stack' (depth + 1) clo chi x y := by
    intro x y hxy
    rcases hsides with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · rcases hxy with h | h
      · exact Or.inl ⟨by omega, by omega, by omega, by omega⟩
      · exact Or.inr ⟨depth, Nat.lt_succ_self _, by rw [hplo]; omega, by rw [hphi]; omega,
          by rw [hplo]; omega, by rw [hphi]; omega⟩
    · rcases hxy with h | h
      · exact Or.inr ⟨depth, Nat.lt_succ_self _, by rw [hplo]; omega, by rw [hphi]; omega,
          by rw [hplo]; omega, by rw [hphi]; omega⟩
      · exact Or.inl ⟨by omega, by omega, by omega, by omega⟩
  by_cases hin : a ≤ i ∧ j < b
  · by_cases hjm : j < mid
    · exact absurd (hnew i j (Or.inl ⟨hin.1, by omega, by omega, hjm⟩)) hns
    · by_cases him : mid < i
      · exact absurd (hnew i j (Or.inr ⟨him, by omega, by omega, hin.2⟩)) hns
      · have h1 : (ys.getD i 0).toNat ≤ (ys.getD mid 0).toNat := by
          by_cases hi : i = mid
          · rw [hi]; exact Nat.le_refl _
          · exact hL i hin.1 (by omega)
        have h2 : (ys.getD mid 0).toNat ≤ (ys.getD j 0).toNat := by
          by_cases hj' : j = mid
          · rw [hj']; exact Nat.le_refl _
          · exact hR j (by omega) hin.2
        exact Nat.le_trans h1 h2
  · apply hord i j hij hj
    intro hsm
    rcases hsm with hsm | ⟨k, hk, hk1, hk2, hk3, hk4⟩
    · omega
    · obtain ⟨hlo, hhi⟩ := hkeep k hk
      exact hns (Or.inr ⟨k, by omega, by rw [hlo]; exact hk1, by rw [hhi]; exact hk2,
        by rw [hlo]; exact hk3, by rw [hhi]; exact hk4⟩)

theorem disj_split (stack stack' : Array UInt32) (depth a mid b clo chi plo phi : Nat)
    (hdisj : Disj stack depth a b) (hmid1 : a ≤ mid) (hmid2 : mid < b)
    (hkeep : ∀ k, k < depth → Rlo stack' k = Rlo stack k ∧ Rhi stack' k = Rhi stack k)
    (hplo : Rlo stack' depth = plo) (hphi : Rhi stack' depth = phi)
    (hsides : (clo = a ∧ chi = mid ∧ plo = mid + 1 ∧ phi = b) ∨ (clo = mid + 1 ∧ chi = b ∧ plo = a ∧ phi = mid)) :
    Disj stack' (depth + 1) clo chi := by
  have hbounds : a ≤ clo ∧ chi ≤ b ∧ a ≤ plo ∧ phi ≤ b ∧ (chi ≤ plo ∨ phi ≤ clo) := by
    rcases hsides with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ <;> omega
  obtain ⟨hc1, hc2, hp1, hp2, hcp⟩ := hbounds
  refine ⟨?_, ?_⟩
  · intro k hk
    by_cases hkd : k = depth
    · rw [hkd, hplo, hphi]; exact hcp
    · obtain ⟨hlo, hhi⟩ := hkeep k (by omega)
      rw [hlo, hhi]
      rcases hdisj.1 k (by omega) with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
  · intro k l hkl hl
    by_cases hld : l = depth
    · obtain ⟨hlo, hhi⟩ := hkeep k (by omega)
      rw [hld, hlo, hhi, hplo, hphi]
      rcases hdisj.1 k (by omega) with h | h
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
    · obtain ⟨hlo, hhi⟩ := hkeep k (by omega)
      obtain ⟨hlo', hhi'⟩ := hkeep l (by omega)
      rw [hlo, hhi, hlo', hhi']
      exact hdisj.2 k l hkl (by omega)

/-- Writing a range at stack level `depth` leaves the lower levels alone. -/
theorem push_slots (stack : Array UInt32) (depth : Nat) (pa pb : UInt32) (hs : stack.size = 144) (hd : depth ≤ 27) :
    ∀ pk : UInt32,
    (∀ k, k < depth →
      Rlo (((stack.setIfInBounds (3 * depth) pa).setIfInBounds (3 * depth + 1) pb).setIfInBounds (3 * depth + 2) pk) k =
        Rlo stack k ∧
      Rhi (((stack.setIfInBounds (3 * depth) pa).setIfInBounds (3 * depth + 1) pb).setIfInBounds (3 * depth + 2) pk) k =
        Rhi stack k) ∧
    Rlo (((stack.setIfInBounds (3 * depth) pa).setIfInBounds (3 * depth + 1) pb).setIfInBounds (3 * depth + 2) pk) depth =
      pa.toNat ∧
    Rhi (((stack.setIfInBounds (3 * depth) pa).setIfInBounds (3 * depth + 1) pb).setIfInBounds (3 * depth + 2) pk) depth =
      pb.toNat := by
  intro pk
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    have h1 : 3 * depth + 2 ≠ 3 * k := by omega
    have h2 : 3 * depth + 1 ≠ 3 * k := by omega
    have h3 : 3 * depth ≠ 3 * k := by omega
    have h4 : 3 * depth + 2 ≠ 3 * k + 1 := by omega
    have h5 : 3 * depth + 1 ≠ 3 * k + 1 := by omega
    have h6 : 3 * depth ≠ 3 * k + 1 := by omega
    unfold Rlo Rhi
    rw [getD_setIfInBounds_ne _ _ _ _ h1, getD_setIfInBounds_ne _ _ _ _ h2, getD_setIfInBounds_ne _ _ _ _ h3,
      getD_setIfInBounds_ne _ _ _ _ h4, getD_setIfInBounds_ne _ _ _ _ h5, getD_setIfInBounds_ne _ _ _ _ h6]
    exact ⟨rfl, rfl⟩
  · have h1 : 3 * depth + 2 ≠ 3 * depth := by omega
    have h2 : 3 * depth + 1 ≠ 3 * depth := by omega
    unfold Rlo
    rw [getD_setIfInBounds_ne _ _ _ _ h1, getD_setIfInBounds_ne _ _ _ _ h2,
      getD_setIfInBounds_self _ _ _ (by rw [hs]; omega)]
  · have h1 : 3 * depth + 2 ≠ 3 * depth + 1 := by omega
    unfold Rhi
    rw [getD_setIfInBounds_ne _ _ _ _ h1,
      getD_setIfInBounds_self _ _ _ (by rw [Array.size_setIfInBounds, hs]; omega)]

/-! ## The main loop -/

set_option maxHeartbeats 8000000 in
/-- `sort_span_budget_u32.loop1` keeps `Ord` and `Disj` while working and
returns a sorted array. The bounds hypotheses are those of `span_loop_perm`. -/
theorem span_loop_sorted (fuel : Nat) : ∀ (items stack : Array UInt32) (depth a b limit : UInt32)
    (balanced partitioned working : Bool) (ys stack' : Array UInt32) (d' a' b' l' : UInt32) (bl' pt' w' : Bool),
    sort_span_budget_u32.loop1 items stack depth a b limit balanced partitioned working fuel =
      some (ys, stack', d', a', b', l', bl', pt', w') →
    items.size < 2 ^ 31 → stack.size = 144 → depth.toNat ≤ 28 →
    a.toNat ≤ b.toNat → b.toNat ≤ items.size → (b.toNat - a.toNat) * 2 ^ depth.toNat ≤ items.size →
    StackInv stack depth.toNat items.size →
    (working = true → Ord items stack depth.toNat a.toNat b.toNat ∧ Disj stack depth.toNat a.toNat b.toNat) →
    (working = false → SortedPrefix items items.size) →
    SortedPrefix ys ys.size := by
  induction fuel with
  | zero =>
    intro items stack depth a b limit balanced partitioned working ys stack' d' a' b' l' bl' pt' w' h
    simp [sort_span_budget_u32.loop1] at h
  | succ fuel ih =>
    intro items stack depth a b limit balanced partitioned working ys stack' d' a' b' l' bl' pt' w' h hsmall hs hd hab hb hlen hinv hw1 hw0
    unfold sort_span_budget_u32.loop1 at h
    cases working with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hw0 rfl
    | true =>
      obtain ⟨hord, hdisj⟩ := hw1 rfl
      simp only [↓reduceIte, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨items2, stack2, depth2, a2, b2, limit2, bal2, part2, done2⟩, hbody,
        ⟨depth3, a3, b3, limit3, bal3, part3, w3⟩, hpop, hrec⟩ := h
      simp only at hpop hrec
      have hlenNat : (b - a).toNat = b.toNat - a.toNat := toNat_sub_of_le' b a hab
      -- Step 1: the body keeps the invariant on (items2, stack2, depth2, a2, b2).
      have hbody' : items2.size = items.size ∧ stack2.size = 144 ∧ depth2.toNat ≤ 28 ∧ a2.toNat ≤ b2.toNat ∧
          b2.toNat ≤ items.size ∧ (b2.toNat - a2.toNat) * 2 ^ depth2.toNat ≤ items.size ∧
          StackInv stack2 depth2.toNat items.size ∧
          (done2 = true → Ord items2 stack2 depth2.toNat 0 0 ∧ Disj stack2 depth2.toNat 0 0) ∧
          (done2 = false → Ord items2 stack2 depth2.toNat a2.toNat b2.toNat ∧ Disj stack2 depth2.toNat a2.toNat b2.toNat) := by
        split at hbody
        · -- insertion sort of the window
          simp only [Option.bind_eq_some_iff] at hbody
          obtain ⟨items', ⟨⟨u, short'⟩, hins, hwb⟩, hbody⟩ := hbody
          simp only [Option.some.injEq, Prod.mk.injEq] at hwb hbody
          obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hbody
          have hshort := insertion_perm _ fuel short' hins (by rw [Array.size_extract]; omega)
          have hssz : short'.size = b.toNat - a.toNat := by rw [hshort.size_eq, Array.size_extract]; omega
          have hsorted := insertion_sorted_partial _ fuel short' hins (by rw [Array.size_extract]; omega)
          refine ⟨?_, hs, hd, hab, hb, hlen, hinv, fun _ => ?_, fun hf => Bool.noConfusion hf⟩
          · rw [← hwb]; exact writeback_size items short' a.toNat b.toNat hab hb hssz
          · rw [← hwb]
            exact ⟨ord_finish _ _ _ _ _
              (ord_win _ _ _ _ _ _ hord hdisj (writeback_win items short' a.toNat b.toNat hab hb hshort) hb)
              (writeback_sorted items short' a.toNat b.toNat hab hb hssz hsorted), disj_none hdisj⟩
        · split at hbody
          · -- heap sort of the window
            simp only [Option.bind_eq_some_iff] at hbody
            obtain ⟨⟨items4, stack4, depth4, a4, b4, limit4, bal4, part4, done4⟩,
              ⟨items', ⟨⟨u, short'⟩, hheap, hwb⟩, hmid⟩, hfin⟩ := hbody
            simp only [Option.some.injEq, Prod.mk.injEq] at hwb hmid hfin
            obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hmid
            obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hfin
            have hshort := heap_perm _ fuel short' hheap (by rw [Array.size_extract]; omega)
            have hssz : short'.size = b.toNat - a.toNat := by rw [hshort.size_eq, Array.size_extract]; omega
            have hsorted := heap_sorted_partial _ fuel short' hheap (by rw [Array.size_extract]; omega)
            refine ⟨?_, hs, hd, hab, hb, hlen, hinv, fun _ => ?_, fun hf => Bool.noConfusion hf⟩
            · rw [← hwb]; exact writeback_size items short' a.toNat b.toNat hab hb hssz
            · rw [← hwb]
              exact ⟨ord_finish _ _ _ _ _
                (ord_win _ _ _ _ _ _ hord hdisj (writeback_win items short' a.toNat b.toNat hab hb hshort) hb)
                (writeback_sorted items short' a.toNat b.toNat hab hb hssz hsorted), disj_none hdisj⟩
          · -- a partition round
            rename_i hgt12 hlim
            have h13 : 13 ≤ b.toNat - a.toNat := by
              have h0 : ¬ (b - a ≤ 12) := of_decide_eq_false (Bool.eq_false_iff.mpr hgt12)
              have h1 : ¬ ((b - a).toNat ≤ (12 : UInt32).toNat) := fun hl => h0 (UInt32.le_iff_toNat_le.mpr hl)
              rw [hlenNat] at h1
              simp at h1
              omega
            simp only [Option.bind_eq_some_iff] at hbody
            obtain ⟨⟨items4, stack4, depth4, a4, b4, limit4, bal4, part4, done4⟩,
              ⟨⟨items5, limit5⟩, hbreak, ⟨chosen, items6⟩, hchoose, ⟨items7, pivot7, hint7⟩, hrev,
                ⟨items8, done8, handled8⟩, hpi, ⟨items9, a9, handled9⟩, hpe,
                ⟨items10, stack10, depth10, a10, b10, bal10, part10⟩, hpt, hlast⟩, hfin⟩ := hbody
            simp only at hchoose
            simp only at hrev
            simp only at hpi
            simp only at hpe
            simp only at hpt
            simp only [Option.some.injEq, Prod.mk.injEq] at hlast hfin
            obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hlast
            obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hfin
            -- (a) pattern breaking
            have hw5 : WinPerm a.toNat b.toNat items items5 := by
              split at hbreak
              · simp only [Option.bind_eq_some_iff] at hbreak
                obtain ⟨⟨u, items5'⟩, hbp, hbreak⟩ := hbreak
                simp only [Option.some.injEq, Prod.mk.injEq] at hbreak
                obtain ⟨rfl, rfl⟩ := hbreak
                exact break_patterns_win items a b fuel items5' hbp hsmall hab hb
              · simp only [Option.some.injEq, Prod.mk.injEq] at hbreak
                obtain ⟨rfl, rfl⟩ := hbreak
                exact WinPerm.refl _ _ _
            have hsize5 : items5.size = items.size := hw5.1
            have hord5 := ord_win _ _ _ _ _ _ hord hdisj hw5 hb
            -- (b) pivot selection
            obtain ⟨hitems6, hpiv_a, hpiv_b⟩ :=
              choose_pivot_spec items5 a b fuel chosen items6 hchoose (by omega) (UInt32.toNat_lt b)
            subst items6
            -- (c) optional reversal of a descending window
            have hp7 : WinPerm a.toNat b.toNat items5 items7 ∧ a.toNat ≤ pivot7.toNat ∧ pivot7.toNat < b.toNat := by
              split at hrev
              · simp only [Option.bind_eq_some_iff] at hrev
                obtain ⟨items7', ⟨⟨u, short'⟩, hrv, hwb⟩, hrev⟩ := hrev
                simp only [Option.some.injEq, Prod.mk.injEq] at hwb hrev
                obtain ⟨rfl, rfl, rfl⟩ := hrev
                have hshort := reverse_perm _ fuel short' hrv (by rw [Array.size_extract]; omega)
                have hb1 : (b - 1).toNat = b.toNat - 1 := uint32_toNat_sub_one b (by omega)
                have hpa : (chosen.index - a).toNat = chosen.index.toNat - a.toNat := toNat_sub_of_le' _ _ hpiv_a
                have hmirror : ((b - 1) - (chosen.index - a)).toNat = b.toNat - 1 - (chosen.index.toNat - a.toNat) := by
                  rw [toNat_sub_of_le' _ _ (by rw [hb1, hpa]; omega), hb1, hpa]
                refine ⟨?_, by rw [hmirror]; omega, by rw [hmirror]; omega⟩
                rw [← hwb]
                exact writeback_win items5 short' a.toNat b.toNat hab (by rw [hsize5]; exact hb) hshort
              · simp only [Option.some.injEq, Prod.mk.injEq] at hrev
                obtain ⟨rfl, rfl, rfl⟩ := hrev
                exact ⟨WinPerm.refl _ _ _, hpiv_a, hpiv_b⟩
            obtain ⟨hw7, hpiv7_a, hpiv7_b⟩ := hp7
            have hsize7 : items7.size = items.size := by rw [hw7.1, hsize5]
            have hord7 := ord_win _ _ _ _ _ _ hord5 hdisj hw7 (by rw [hsize5]; exact hb)
            -- (d) partial insertion sort
            have hp8 : WinPerm a.toNat b.toNat items7 items8 ∧ handled8 = done8 ∧
                (done8 = true → SortedRange items8 a.toNat b.toNat) := by
              split at hpi
              · simp only [Option.bind_eq_some_iff] at hpi
                obtain ⟨⟨r, items8'⟩, hpins, ⟨d1, h1⟩, hdh, hpi⟩ := hpi
                simp only [Option.some.injEq, Prod.mk.injEq] at hpi
                obtain ⟨rfl, rfl, rfl⟩ := hpi
                obtain ⟨hw8, hsr8⟩ := partial_insertion_spec items7 a b fuel r items8' hpins (by omega) (by omega)
                  (by rw [hsize7]; exact hb)
                split at hdh
                · rename_i hr
                  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hdh
                  obtain ⟨rfl, rfl⟩ := hdh
                  exact ⟨hw8, rfl, fun _ => hsr8 hr⟩
                · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hdh
                  obtain ⟨rfl, rfl⟩ := hdh
                  exact ⟨hw8, rfl, fun hf => Bool.noConfusion hf⟩
              · simp only [Option.some.injEq, Prod.mk.injEq] at hpi
                obtain ⟨rfl, rfl, rfl⟩ := hpi
                exact ⟨WinPerm.refl _ _ _, rfl, fun hf => Bool.noConfusion hf⟩
            obtain ⟨hw8, hh8d, hsr8⟩ := hp8
            have hsize8 : items8.size = items.size := by rw [hw8.1, hsize7]
            have hord8 := ord_win _ _ _ _ _ _ hord7 hdisj hw8 (by rw [hsize7]; exact hb)
            -- (e) the equal-elements partition
            have hp9 : items9.size = items.size ∧ a.toNat ≤ a9.toNat ∧ a9.toNat ≤ b.toNat ∧
                (handled9 = false → a9 = a ∧ items9 = items8 ∧ handled8 = false) ∧
                (handled9 = true → (handled8 = true ∧ items9 = items8 ∧ a9 = a) ∨
                  (handled8 = false ∧ Ord items9 stack depth.toNat a9.toNat b.toNat ∧
                    Disj stack depth.toNat a9.toNat b.toNat)) := by
              split at hpe
              · rename_i hc
                simp only [Option.bind_eq_some_iff] at hpe
                obtain ⟨⟨i', items9'⟩, hpeq, hpe⟩ := hpe
                simp only [Option.some.injEq, Prod.mk.injEq] at hpe
                obtain ⟨rfl, rfl, rfl⟩ := hpe
                have hcond := (Bool.and_eq_true _ _).mp hc
                have hcond1 := (Bool.and_eq_true _ _).mp hcond.1
                have hh8 : handled8 = false := by
                  have := hcond1.1
                  rwa [Bool.not_eq_true'] at this
                have hapos : 0 < a.toNat := by
                  have := lt_toNat (of_decide_eq_true hcond1.2 : (0 : UInt32) < a)
                  simpa using this
                have hge : (items8.getD pivot7.toNat 0).toNat ≤ (items8.getD (a - 1).toNat 0).toNat := by
                  have h2 := hcond.2
                  rw [Bool.not_eq_true'] at h2
                  exact not_lt_toNat (of_decide_eq_false h2)
                rw [uint32_toNat_sub_one a hapos] at hge
                obtain ⟨hw9, h1, h2, hle, hgt⟩ := partition_equal_post items8 a b pivot7 fuel i' items9' hpeq
                  (by rw [hsize8]; omega) (by omega) (by rw [hsize8]; exact hb) hpiv7_a hpiv7_b
                refine ⟨by rw [hw9.1, hsize8], by omega, h2, fun hf => Bool.noConfusion hf,
                  fun _ => Or.inr ⟨hh8, ?_, disj_shrink _ _ _ _ _ hdisj (by omega)⟩⟩
                exact ord_equal_step _ _ _ _ _ _ _ _ hord8 hdisj hw9 (by rw [hsize8]; exact hb) hapos hge (by omega) h2 hle hgt
              · simp only [Option.some.injEq, Prod.mk.injEq] at hpe
                obtain ⟨rfl, rfl, rfl⟩ := hpe
                exact ⟨hsize8, Nat.le_refl _, hab, fun h => ⟨rfl, rfl, h⟩, fun h => Or.inl ⟨h, rfl, rfl⟩⟩
            obtain ⟨hsize9, ha9a, ha9b, hh9f, hh9t⟩ := hp9
            -- the range has at least 13 elements, so the depth is at most 27 before a push
            have hd27 : depth.toNat ≤ 27 := by
              apply Nat.le_of_not_lt
              intro hlt
              have h28 : 2 ^ 28 ≤ 2 ^ depth.toNat := Nat.pow_le_pow_right (by decide) hlt
              have h13' : 13 * 2 ^ depth.toNat ≤ (b.toNat - a.toNat) * 2 ^ depth.toNat := Nat.mul_le_mul_right _ h13
              omega
            -- (f) the partition and the push of the larger side
            have hp10 : items10.size = items.size ∧ stack10.size = 144 ∧ depth10.toNat ≤ 28 ∧ a10.toNat ≤ b10.toNat ∧
                b10.toNat ≤ items.size ∧ (b10.toNat - a10.toNat) * 2 ^ depth10.toNat ≤ items.size ∧
                StackInv stack10 depth10.toNat items.size ∧
                (done8 = true → Ord items10 stack10 depth10.toNat 0 0 ∧ Disj stack10 depth10.toNat 0 0) ∧
                (done8 = false → Ord items10 stack10 depth10.toNat a10.toNat b10.toNat ∧
                  Disj stack10 depth10.toNat a10.toNat b10.toNat) := by
              split at hpt
              · rename_i hnh
                rw [Bool.not_eq_true'] at hnh
                obtain ⟨ha9, hi9, hh8⟩ := hh9f hnh
                subst a9
                subst items9
                have hd8 : done8 = false := by rw [← hh8d]; exact hh8
                subst hd8
                simp only [Option.bind_eq_some_iff] at hpt
                obtain ⟨⟨sp, items10'⟩, hpart, ⟨na, nb, nbal, pa, pb⟩, hsides, hpt⟩ := hpt
                simp only [Option.some.injEq, Prod.mk.injEq] at hpt
                obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hpt
                obtain ⟨hw10, hmid_a, hmid_b, hle10, hmidv, hge10⟩ :=
                  partition_post items8 a b pivot7 fuel sp items10' hpart (by rw [hsize8]; omega) (by omega)
                    (by rw [hsize8]; exact hb) hpiv7_a hpiv7_b
                have hord10 := ord_win _ _ _ _ _ _ hord8 hdisj hw10 (by rw [hsize8]; exact hb)
                have hL : ∀ x, a.toNat ≤ x → x < sp.mid.toNat →
                    (items10'.getD x 0).toNat ≤ (items10'.getD sp.mid.toNat 0).toNat := by
                  intro x hx1 hx2; rw [hmidv]; exact hle10 x hx1 hx2
                have hR : ∀ y, sp.mid.toNat < y → y < b.toNat →
                    (items10'.getD sp.mid.toNat 0).toNat ≤ (items10'.getD y 0).toNat := by
                  intro y hy1 hy2; rw [hmidv]; exact hge10 y hy1 hy2
                obtain ⟨hi0, hi1, hi2⟩ := stack_index_toNat depth hd
                have hd1 : (depth + 1).toNat = depth.toNat + 1 := by
                  rw [toNat_add_of_lt _ _ (by rw [toNat_one']; omega), toNat_one']
                have hmidNat : (sp.mid - a).toNat = sp.mid.toNat - a.toNat := toNat_sub_of_le' _ _ hmid_a
                have hbmidNat : (b - sp.mid).toNat = b.toNat - sp.mid.toNat := toNat_sub_of_le' _ _ (by omega)
                have hmid1 : (sp.mid + 1).toNat = sp.mid.toNat + 1 := by
                  rw [toNat_add_of_lt _ _ (by rw [toNat_one']; omega), toNat_one']
                have hstack_size : ∀ pa pb pk : UInt32,
                    (((stack.setIfInBounds (depth * 3).toNat pa).setIfInBounds (depth * 3 + 1).toNat pb).setIfInBounds
                      (depth * 3 + 2).toNat pk).size = 144 := by
                  intro pa pb pk
                  simp only [Array.size_setIfInBounds, hs]
                have hpush : ∀ pa pb pk : UInt32, pa.toNat ≤ pb.toNat → pb.toNat ≤ items.size →
                    (pb.toNat - pa.toNat) * 2 ^ depth.toNat ≤ items.size →
                    StackInv (((stack.setIfInBounds (depth * 3).toNat pa).setIfInBounds (depth * 3 + 1).toNat pb).setIfInBounds
                      (depth * 3 + 2).toNat pk) (depth.toNat + 1) items.size := by
                  intro pa pb pk h1 h2 h3
                  rw [hi0, hi1, hi2]
                  exact StackInv.push stack depth.toNat items.size pa pb pk hs hd27 hinv h1 h2 h3
                have hdouble : 2 ^ (depth.toNat + 1) = 2 * 2 ^ depth.toNat := Nat.pow_succ'
                have hsize10 : items10'.size = items.size := by rw [hw10.1, hsize8]
                split at hsides
                · -- the left side is smaller: continue with [a, mid), push [mid + 1, b)
                  rename_i hlt
                  have hlt' : sp.mid.toNat - a.toNat < b.toNat - sp.mid.toNat := by
                    have := UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true hlt)
                    rw [hmidNat, hbmidNat] at this
                    exact this
                  simp only [Option.some.injEq, Prod.mk.injEq] at hsides
                  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hsides
                  refine ⟨hsize10, hstack_size _ _ _, by rw [hd1]; omega, hmid_a, by omega, ?_, ?_,
                    fun hf => Bool.noConfusion hf, fun _ => ?_⟩
                  · rw [hd1, hdouble, ← Nat.mul_assoc]
                    exact Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) hlen
                  · rw [hd1]
                    refine hpush _ _ _ (by rw [hmid1]; omega) hb ?_
                    rw [hmid1]
                    exact Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) hlen
                  · rw [hi0, hi1, hi2, hd1]
                    have hps := push_slots stack depth.toNat (sp.mid + 1) b hs hd27
                    exact ⟨ord_split _ stack _ depth.toNat a.toNat sp.mid.toNat b.toNat a.toNat sp.mid.toNat
                        (sp.mid.toNat + 1) b.toNat hord10 hmid_a hmid_b hL hR (hps _).1
                        (by rw [(hps _).2.1, hmid1]) (hps _).2.2 (Or.inl ⟨rfl, rfl, rfl, rfl⟩),
                      disj_split stack _ depth.toNat a.toNat sp.mid.toNat b.toNat a.toNat sp.mid.toNat
                        (sp.mid.toNat + 1) b.toNat hdisj hmid_a hmid_b (hps _).1
                        (by rw [(hps _).2.1, hmid1]) (hps _).2.2 (Or.inl ⟨rfl, rfl, rfl, rfl⟩)⟩
                · -- the right side is not larger: continue with [mid + 1, b), push [a, mid)
                  rename_i hge
                  have hge' : ¬ (sp.mid.toNat - a.toNat < b.toNat - sp.mid.toNat) := by
                    intro hl
                    apply hge
                    apply decide_eq_true
                    apply UInt32.lt_iff_toNat_lt.mpr
                    rw [hmidNat, hbmidNat]
                    exact hl
                  simp only [Option.some.injEq, Prod.mk.injEq] at hsides
                  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hsides
                  refine ⟨hsize10, hstack_size _ _ _, by rw [hd1]; omega, by rw [hmid1]; omega, hb, ?_, ?_,
                    fun hf => Bool.noConfusion hf, fun _ => ?_⟩
                  · rw [hd1, hdouble, hmid1, ← Nat.mul_assoc]
                    exact Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) hlen
                  · rw [hd1]
                    exact hpush _ _ _ hmid_a (by omega) (Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) hlen)
                  · rw [hi0, hi1, hi2, hd1, hmid1]
                    have hps := push_slots stack depth.toNat a sp.mid hs hd27
                    exact ⟨ord_split _ stack _ depth.toNat a.toNat sp.mid.toNat b.toNat (sp.mid.toNat + 1) b.toNat
                        a.toNat sp.mid.toNat hord10 hmid_a hmid_b hL hR (hps _).1 (hps _).2.1 (hps _).2.2
                        (Or.inr ⟨rfl, rfl, rfl, rfl⟩),
                      disj_split stack _ depth.toNat a.toNat sp.mid.toNat b.toNat (sp.mid.toNat + 1) b.toNat
                        a.toNat sp.mid.toNat hdisj hmid_a hmid_b (hps _).1 (hps _).2.1 (hps _).2.2
                        (Or.inr ⟨rfl, rfl, rfl, rfl⟩)⟩
              · -- no partition: either the range is done or the equal-elements partition handled it
                rename_i hnh
                have hh9 : handled9 = true := by
                  revert hnh
                  cases handled9 <;> simp
                simp only [Option.some.injEq, Prod.mk.injEq] at hpt
                obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hpt
                refine ⟨hsize9, hs, hd, ha9b, hb, Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) hlen, hinv, ?_, ?_⟩
                · intro hd8
                  rcases hh9t hh9 with ⟨-, hi9, ha9⟩ | ⟨hh8f, -, -⟩
                  · subst items9
                    subst a9
                    exact ⟨ord_finish _ _ _ _ _ hord8 (hsr8 hd8), disj_none hdisj⟩
                  · rw [← hh8d] at hd8
                    rw [hd8] at hh8f
                    cases hh8f
                · intro hd8
                  rcases hh9t hh9 with ⟨hh8t, -, -⟩ | ⟨-, hord9, hdisj9⟩
                  · rw [← hh8d] at hd8
                    rw [hd8] at hh8t
                    cases hh8t
                  · exact ⟨hord9, hdisj9⟩
            exact hp10
      obtain ⟨hsize2, hs2, hd2, hab2, hb2, hlen2, hinv2, hdone2, hndone2⟩ := hbody'
      -- Step 2: the pop keeps the invariant on (depth3, a3, b3).
      have hpop' : depth3.toNat ≤ 28 ∧ a3.toNat ≤ b3.toNat ∧ b3.toNat ≤ items.size ∧
          (b3.toNat - a3.toNat) * 2 ^ depth3.toNat ≤ items.size ∧ StackInv stack2 depth3.toNat items.size ∧
          (w3 = true → Ord items2 stack2 depth3.toNat a3.toNat b3.toNat ∧ Disj stack2 depth3.toNat a3.toNat b3.toNat) ∧
          (w3 = false → SortedPrefix items2 items2.size) := by
        split at hpop
        · rename_i hdone
          split at hpop
          · rename_i hz
            have hz' : depth2 = 0 := beq_iff_eq.mp hz
            subst hz'
            simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hpop
            obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hpop
            obtain ⟨hord2, -⟩ := hdone2 hdone
            have h0 : (0 : UInt32).toNat = 0 := rfl
            rw [h0] at hord2
            exact ⟨hd2, hab2, hb2, hlen2, hinv2, fun hf => Bool.noConfusion hf, fun _ => sorted_of_ord0 _ _ hord2⟩
          · rename_i hne
            have h0 : depth2 ≠ 0 := fun heq => hne (beq_iff_eq.mpr heq)
            have hpos : 0 < depth2.toNat := by
              apply Nat.pos_of_ne_zero
              intro hz
              exact h0 (UInt32.toNat_inj.mp hz)
            simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hpop
            obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hpop
            have hd1 : (depth2 - 1).toNat = depth2.toNat - 1 := uint32_toNat_sub_one depth2 hpos
            obtain ⟨hi0, hi1, -⟩ := stack_index_toNat (depth2 - 1) (by rw [hd1]; omega)
            obtain ⟨hk1, hk2, hk3⟩ := hinv2 (depth2.toNat - 1) (by omega)
            obtain ⟨hord2, hdisj2⟩ := hdone2 hdone
            have hd2' : depth2.toNat = (depth2.toNat - 1) + 1 := by omega
            rw [hd2'] at hord2 hdisj2
            rw [hi0, hi1, hd1]
            exact ⟨by omega, hk1, hk2, hk3, hinv2.mono _ (by omega),
              fun _ => ⟨ord_pop _ _ _ hord2, disj_pop _ _ hdisj2⟩, fun hf => Bool.noConfusion hf⟩
        · rename_i hnd
          have hnd' : done2 = false := Bool.eq_false_iff.mpr hnd
          simp only [Option.some.injEq, Prod.mk.injEq] at hpop
          obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hpop
          exact ⟨hd2, hab2, hb2, hlen2, hinv2, fun _ => hndone2 hnd', fun hf => Bool.noConfusion hf⟩
      obtain ⟨hd3, hab3, hb3, hlen3, hinv3, hw3t, hw3f⟩ := hpop'
      exact ih items2 stack2 depth3 a3 b3 limit3 bal3 part3 w3 ys stack' d' a' b' l' bl' pt' w' hrec
        (by rw [hsize2]; exact hsmall) hs2 hd3 hab3 (by rw [hsize2]; exact hb3) (by rw [hsize2]; exact hlen3)
        (by rw [hsize2]; exact hinv3) hw3t hw3f

/-! ## Sortedness of the whole sort -/

/-- `sort_span_budget_u32` returns a sorted array whenever it returns. -/
theorem sort_span_budget_sorted (xs : Array UInt32) (limit : UInt32) (fuel : Nat) (ys : Array UInt32)
    (h : sort_span_budget_u32 xs limit fuel = some ((), ys)) (hsmall : xs.size < 2 ^ 31) :
    SortedPrefix ys ys.size := by
  have hn : (xs.size.toUInt32).toNat = xs.size := by
    rw [Nat.toUInt32, UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  unfold sort_span_budget_u32 at h
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨items', hbranch, hfin⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hfin
  subst hfin
  split at hbranch
  · simp only [Option.bind_eq_some_iff] at hbranch
    obtain ⟨⟨u, zs⟩, hins, hz⟩ := hbranch
    simp only [Option.some.injEq] at hz
    subst hz
    exact insertion_sorted_partial xs fuel zs hins (by omega)
  · simp only [Option.bind_eq_some_iff] at hbranch
    obtain ⟨⟨zs, stack', d', a', b', l', bl', pt', w'⟩, hloop, hz⟩ := hbranch
    simp only [Option.some.injEq] at hz
    subst hz
    have h0 : (0 : UInt32).toNat = 0 := rfl
    refine span_loop_sorted fuel xs (Array.replicate 144 0) 0 0 (xs.size.toUInt32) limit true true true
      zs stack' d' a' b' l' bl' pt' w' hloop hsmall (by simp) (by decide) (by rw [hn]; exact Nat.zero_le _)
      (Nat.le_of_eq hn) (by rw [hn]; simp) (fun k hk => absurd hk (Nat.not_lt_zero k)) (fun _ => ⟨?_, ?_⟩)
      (fun hf => Bool.noConfusion hf)
    · rw [h0, hn]
      intro i j hij hj hns
      exact absurd (Or.inl ⟨Nat.zero_le _, by omega, Nat.zero_le _, hj⟩) hns
    · exact ⟨fun k hk => absurd hk (Nat.not_lt_zero k), fun k l _ hl => absurd hl (Nat.not_lt_zero l)⟩

/-- `sort_span_u32` (pdqsort with the default depth budget) returns a sorted array. -/
theorem sort_span_sorted (xs : Array UInt32) (fuel : Nat) (ys : Array UInt32)
    (h : sort_span_u32 xs fuel = some ((), ys)) (hsmall : xs.size < 2 ^ 31) : SortedPrefix ys ys.size := by
  unfold sort_span_u32 at h
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨bits, -, ⟨u, zs⟩, hbudget, hz⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hz
  subst hz
  exact sort_span_budget_sorted xs bits fuel zs hbudget hsmall

/-- The public entry point `sort_u32_span` returns a sorted array. -/
theorem sort_u32_span_sorted (xs : Array UInt32) (fuel : Nat) (ys : Array UInt32)
    (h : sort_u32_span xs fuel = some ((), ys)) (hsmall : xs.size < 2 ^ 31) : SortedPrefix ys ys.size := by
  unfold sort_u32_span at h
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨u, zs⟩, hspan, hz⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hz
  subst hz
  exact sort_span_sorted xs fuel zs hspan hsmall

/-- Full functional correctness of the extracted pdqsort: whenever
`sort_u32_span` returns, the result is a sorted permutation of the input. -/
theorem sort_u32_span_correct (xs : Array UInt32) (fuel : Nat) (ys : Array UInt32)
    (h : sort_u32_span xs fuel = some ((), ys)) (hsmall : xs.size < 2 ^ 31) :
    ys.Perm xs ∧ SortedPrefix ys ys.size :=
  ⟨sort_u32_span_perm xs fuel ys h hsmall, sort_u32_span_sorted xs fuel ys h hsmall⟩

end Oak.Stdlib.SortU32
