import Oak.Stdlib.SortLaws

set_option linter.unusedSimpArgs false

/-!
# Oak.Stdlib.PdqsortLaws — the pattern-defeating quicksort on the extraction

`sort_span_u32` (and `sort_span_budget_u32`) is the iterative pdqsort of
`stdlib/sort.oak` extracted to Lean. This file proves the **permutation law**
universally: whenever the extracted sort returns, its output is a permutation
of its input.

The proof is in partial-correctness style — `f xs fuel = some out → out.Perm
xs` — so no fuel bound is needed. Every helper of the sort performs its writes
as swaps of two indices; a swap of two in-bounds indices is a permutation
(`two_stores_eq_swap`, `Array.swap_perm`), while the extraction *drops* an
out-of-range store, so the whole argument is an in-bounds argument: every
index a helper touches lies in the range `[a, b)` it was given, every range
the main loop works on satisfies `a ≤ b ≤ items.size`, and every range on the
explicit stack does too (`StackInv`, carried through the main loop by fuel
induction in `span_loop_perm`; a range at depth `k` has at most `n / 2^k`
elements because the loop continues with the smaller side, so the depth stays
below 29 and no stack index wraps or leaves the 144 slots).

Sortedness on the pattern-defeating path is not stated here; it remains
decided on adversarial inputs in `Oak.Stdlib.SortLaws`.
-/

namespace Oak.Stdlib.SortU32

/-! ## Swaps -/

/-- A swap of two in-bounds positions written as two guarded stores is a
permutation and keeps the size. -/
theorem two_stores_perm (xs : Array UInt32) (i j : Nat) (hi : i < xs.size) (hj : j < xs.size) :
    ((xs.setIfInBounds i (xs.getD j 0)).setIfInBounds j (xs.getD i 0)).Perm xs := by
  rw [two_stores_eq_swap xs i j hi hj]
  exact Array.swap_perm hi hj

theorem two_stores_size (xs : Array UInt32) (i j : Nat) (v w : UInt32) :
    ((xs.setIfInBounds i v).setIfInBounds j w).size = xs.size := by
  simp

/-- `sort_swap_u32` always returns; on in-bounds indices it returns a permutation. -/
theorem swap_perm (xs : Array UInt32) (i j : UInt32) (fuel : Nat) (ys : Array UInt32)
    (h : sort_swap_u32 xs i j fuel = some ((), ys)) (hi : i.toNat < xs.size) (hj : j.toNat < xs.size) :
    ys.Perm xs := by
  unfold sort_swap_u32 at h
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq, true_and] at h
  subst h
  exact two_stores_perm xs i.toNat j.toNat hi hj

theorem swap_size (xs : Array UInt32) (i j : UInt32) (fuel : Nat) (ys : Array UInt32)
    (h : sort_swap_u32 xs i j fuel = some ((), ys)) : ys.size = xs.size := by
  unfold sort_swap_u32 at h
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq, true_and] at h
  subst h
  simp

/-! ## Insertion sort, partially -/

theorem insertion_loop2_perm (fuel : Nat) : ∀ (xs : Array UInt32) (j : UInt32) (ys : Array UInt32) (j' : UInt32),
    sort_insertion_u32.loop2 xs j fuel = some (ys, j') → j.toNat < xs.size → ys.Perm xs := by
  induction fuel with
  | zero => intro xs j ys j' h; simp [sort_insertion_u32.loop2] at h
  | succ fuel ih =>
    intro xs j ys j' h hj
    unfold sort_insertion_u32.loop2 at h
    by_cases hc : (decide (j > (0 : UInt32)) && decide (xs.getD j.toNat 0 < xs.getD (j - 1).toNat 0)) = true
    · rw [if_pos hc] at h
      have hpos : 0 < j.toNat := by
        have := (Bool.and_eq_true _ _).mp hc
        have h0 := of_decide_eq_true this.1
        exact UInt32.lt_iff_toNat_lt.mp h0
      have hj1 : (j - 1).toNat = j.toNat - 1 := uint32_toNat_sub_one j hpos
      have hperm := ih _ _ _ _ h (by rw [two_stores_size, hj1]; omega)
      refine hperm.trans ?_
      rw [hj1]
      exact two_stores_perm xs j.toNat (j.toNat - 1) hj (by omega)
    · rw [if_neg hc] at h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      rw [h.1]

theorem insertion_loop1_perm (fuel : Nat) : ∀ (xs : Array UInt32) (i : UInt32) (ys : Array UInt32) (i' : UInt32),
    sort_insertion_u32.loop1 xs i fuel = some (ys, i') → xs.size < 2 ^ 32 → ys.Perm xs := by
  induction fuel with
  | zero => intro xs i ys i' h; simp [sort_insertion_u32.loop1] at h
  | succ fuel ih =>
    intro xs i ys i' h hsmall
    unfold sort_insertion_u32.loop1 at h
    by_cases hc : decide (i < xs.size.toUInt32) = true
    · rw [if_pos hc] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨xs2, j2⟩, h2, h1⟩ := h
      have hn : (xs.size.toUInt32).toNat = xs.size := by
        show (UInt32.ofNat _).toNat = _
        rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt hsmall
      have hi : i.toNat < xs.size := by
        have := UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true hc); rwa [hn] at this
      have hp2 := insertion_loop2_perm fuel xs i xs2 j2 h2 hi
      have hp1 := ih xs2 (i + 1) ys i' h1 (by rw [hp2.size_eq]; exact hsmall)
      exact hp1.trans hp2
    · rw [if_neg hc] at h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      rw [h.1]

/-- Whenever the extracted insertion sort returns, it returns a permutation. -/
theorem insertion_perm (xs : Array UInt32) (fuel : Nat) (ys : Array UInt32)
    (h : sort_insertion_u32 xs fuel = some ((), ys)) (hsmall : xs.size < 2 ^ 32) : ys.Perm xs := by
  unfold sort_insertion_u32 at h
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨xs2, i2⟩, h2, h1⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at h1
  subst h1
  exact insertion_loop1_perm fuel xs 1 xs2 i2 h2 hsmall

/-! ## Heap sort, partially

The sift loop keeps `root < end_ ≤ size` while it runs, so the swap of the
root with its larger child is in bounds; sizes stay below `2^31` so that the
child index `2 * root + 1` does not wrap. -/

theorem sift_loop_perm (fuel : Nat) : ∀ (xs : Array UInt32) (end_ root : UInt32) (more : Bool)
    (ys : Array UInt32) (root' : UInt32) (more' : Bool),
    sort_sift_down_u32.loop1 xs end_ root more fuel = some (ys, root', more') →
    xs.size < 2 ^ 31 → end_.toNat ≤ xs.size → (more = true → root.toNat < end_.toNat) → ys.Perm xs := by
  induction fuel with
  | zero => intro xs end_ root more ys root' more' h; simp [sort_sift_down_u32.loop1] at h
  | succ fuel ih =>
    intro xs end_ root more ys root' more' h hsmall hend hroot
    unfold sort_sift_down_u32.loop1 at h
    cases more with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      rw [h.1]
    | true =>
      have hr := hroot rfl
      simp only [↓reduceIte, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨xs2, root2, more2⟩, h2, h1⟩ := h
      have hchild : ((root * 2) + 1).toNat = 2 * root.toNat + 1 := by
        rw [UInt32.toNat_add, UInt32.toNat_mul]
        have : root.toNat * 2 % 2 ^ 32 = root.toNat * 2 := Nat.mod_eq_of_lt (by omega)
        rw [show (2 : UInt32).toNat = 2 from rfl, show (1 : UInt32).toNat = 1 from rfl, this]
        have h2 := Nat.mod_eq_of_lt (show root.toNat * 2 + 1 < 2 ^ 32 by omega)
        omega
      by_cases hc : decide ((root * 2) + 1 ≥ end_) = true
      · rw [if_pos hc] at h2
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl, rfl⟩ := h2
        exact ih xs end_ root false ys root' more' h1 hsmall hend (fun h => by cases h)
      · rw [if_neg hc] at h2
        have hlt : 2 * root.toNat + 1 < end_.toNat := by
          have hnot : ¬ (end_ ≤ (root * 2) + 1) := of_decide_eq_false (Bool.eq_false_iff.mpr hc)
          have hnot' : ¬ (end_.toNat ≤ ((root * 2) + 1).toNat) := fun hle => hnot (UInt32.le_iff_toNat_le.mpr hle)
          rw [hchild] at hnot'
          omega
        have hright : ((root * 2) + 1 + 1).toNat = 2 * root.toNat + 2 := by
          rw [UInt32.toNat_add, hchild, show (1 : UInt32).toNat = 1 from rfl]
          exact Nat.mod_eq_of_lt (by omega)
        simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h2
        obtain ⟨⟨xs3, root3, more3⟩, h3, h2'⟩ := h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h2'
        obtain ⟨rfl, rfl, rfl⟩ := h2'
        -- the larger child is below `end_`
        have hlargest : (if (decide ((root * 2) + 1 + 1 < end_) &&
            decide (xs.getD ((root * 2) + 1).toNat 0 < xs.getD ((root * 2) + 1 + 1).toNat 0)) then
            (root * 2) + 1 + 1 else (root * 2) + 1).toNat < end_.toNat := by
          split
          · rename_i hsplit
            have := UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true ((Bool.and_eq_true _ _).mp hsplit).1)
            exact this
          · rw [hchild]; exact hlt
        generalize hL : (if (decide ((root * 2) + 1 + 1 < end_) &&
            decide (xs.getD ((root * 2) + 1).toNat 0 < xs.getD ((root * 2) + 1 + 1).toNat 0)) then
            (root * 2) + 1 + 1 else (root * 2) + 1) = largest at h3 hlargest
        by_cases hs : decide (xs.getD root.toNat 0 < xs.getD largest.toNat 0) = true
        · rw [if_pos hs] at h3
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h3
          obtain ⟨rfl, rfl, rfl⟩ := h3
          have hperm := two_stores_perm xs root.toNat largest.toNat (by omega) (by omega)
          have := ih _ end_ largest true ys root' more' h1 (by rw [hperm.size_eq]; exact hsmall)
            (by rw [hperm.size_eq]; exact hend) (fun _ => hlargest)
          exact this.trans hperm
        · rw [if_neg hs] at h3
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h3
          obtain ⟨rfl, rfl, rfl⟩ := h3
          exact ih xs end_ root false ys root' more' h1 hsmall hend (fun h => by cases h)

theorem sift_down_perm (xs : Array UInt32) (start end_ : UInt32) (fuel : Nat) (ys : Array UInt32)
    (h : sort_sift_down_u32 xs start end_ fuel = some ((), ys)) (hsmall : xs.size < 2 ^ 31)
    (hend : end_.toNat ≤ xs.size) (hstart : start.toNat < end_.toNat) : ys.Perm xs := by
  unfold sort_sift_down_u32 at h
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨xs2, r2, m2⟩, h2, h1⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at h1
  subst h1
  exact sift_loop_perm fuel xs end_ start true xs2 r2 m2 h2 hsmall hend (fun _ => hstart)

theorem heap_loop1_perm (fuel : Nat) : ∀ (xs : Array UInt32) (n start : UInt32) (ys : Array UInt32) (s' : UInt32),
    sort_heap_u32.loop1 xs n start fuel = some (ys, s') → xs.size < 2 ^ 31 → n.toNat ≤ xs.size →
    start.toNat ≤ n.toNat → ys.Perm xs := by
  induction fuel with
  | zero => intro xs n start ys s' h; simp [sort_heap_u32.loop1] at h
  | succ fuel ih =>
    intro xs n start ys s' h hsmall hn hstart
    unfold sort_heap_u32.loop1 at h
    by_cases hc : decide (start > (0 : UInt32)) = true
    · rw [if_pos hc] at h
      have hpos : 0 < start.toNat := UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true hc)
      have hs1 : (start - 1).toNat = start.toNat - 1 := uint32_toNat_sub_one start hpos
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨u, xs2⟩, h2, h1⟩ := h
      have hp2 := sift_down_perm xs (start - 1) n fuel xs2 h2 hsmall hn (by rw [hs1]; omega)
      have hp1 := ih xs2 n (start - 1) ys s' h1 (by rw [hp2.size_eq]; exact hsmall)
        (by rw [hp2.size_eq]; exact hn) (by rw [hs1]; omega)
      exact hp1.trans hp2
    · rw [if_neg hc] at h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      rw [h.1]

theorem heap_loop2_perm (fuel : Nat) : ∀ (xs : Array UInt32) (end_ : UInt32) (ys : Array UInt32) (e' : UInt32),
    sort_heap_u32.loop2 xs end_ fuel = some (ys, e') → xs.size < 2 ^ 31 → end_.toNat ≤ xs.size → ys.Perm xs := by
  induction fuel with
  | zero => intro xs end_ ys e' h; simp [sort_heap_u32.loop2] at h
  | succ fuel ih =>
    intro xs end_ ys e' h hsmall hend
    unfold sort_heap_u32.loop2 at h
    by_cases hc : decide (end_ > (1 : UInt32)) = true
    · rw [if_pos hc] at h
      have hgt : 1 < end_.toNat := UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true hc)
      have he1 : (end_ - 1).toNat = end_.toNat - 1 := uint32_toNat_sub_one end_ (by omega)
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨u, xs3⟩, h3, h1⟩ := h
      have hswap := two_stores_perm xs 0 (end_ - 1).toNat (by omega) (by rw [he1]; omega)
      have hp3 := sift_down_perm _ 0 (end_ - 1) fuel xs3 h3 (by rw [hswap.size_eq]; exact hsmall)
        (by rw [hswap.size_eq, he1]; omega) (by rw [he1]; show 0 < _; omega)
      have hp1 := ih xs3 (end_ - 1) ys e' h1 (by rw [hp3.size_eq, hswap.size_eq]; exact hsmall)
        (by rw [hp3.size_eq, hswap.size_eq, he1]; omega)
      exact hp1.trans (hp3.trans hswap)
    · rw [if_neg hc] at h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      rw [h.1]

/-- Whenever the extracted heap sort returns, it returns a permutation. -/
theorem heap_perm (xs : Array UInt32) (fuel : Nat) (ys : Array UInt32)
    (h : sort_heap_u32 xs fuel = some ((), ys)) (hsmall : xs.size < 2 ^ 31) : ys.Perm xs := by
  unfold sort_heap_u32 at h
  have hn : (xs.size.toUInt32).toNat = xs.size := by
    show (UInt32.ofNat _).toNat = _
    rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  simp only [Option.pure_def, Option.bind_eq_bind] at h
  split at h
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨items, ⟨⟨xs2, s2⟩, h2, ⟨xs3, e3⟩, h3, h4⟩, h1⟩ := h
    simp only [Option.some.injEq, Prod.mk.injEq, true_and] at h1 h4
    subst h1 h4
    have hhalf : (xs.size.toUInt32 / 2).toNat ≤ xs.size := by
      rw [UInt32.toNat_div, hn]; exact Nat.div_le_self _ _
    have hp2 := heap_loop1_perm fuel xs _ _ xs2 s2 h2 hsmall (Nat.le_of_eq hn) (by rw [hn]; exact hhalf)
    have hp3 := heap_loop2_perm fuel xs2 _ xs3 e3 h3 (by rw [hp2.size_eq]; exact hsmall)
      (by rw [hp2.size_eq]; exact Nat.le_of_eq hn)
    exact hp3.trans hp2
  · simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq, true_and] at h
    rw [h]

/-! ## Reversal, partially -/

theorem reverse_loop_perm (fuel : Nat) : ∀ (xs : Array UInt32) (n i : UInt32) (ys : Array UInt32) (i' : UInt32),
    sort_reverse_u32.loop1 xs n i fuel = some (ys, i') → n.toNat ≤ xs.size → ys.Perm xs := by
  induction fuel with
  | zero => intro xs n i ys i' h; simp [sort_reverse_u32.loop1] at h
  | succ fuel ih =>
    intro xs n i ys i' h hn
    unfold sort_reverse_u32.loop1 at h
    by_cases hc : (decide (n > (1 : UInt32)) && decide (i < n / 2)) = true
    · rw [if_pos hc] at h
      have hc' := (Bool.and_eq_true _ _).mp hc
      have hn1 : 1 < n.toNat := UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true hc'.1)
      have hi : i.toNat < n.toNat / 2 := by
        have := UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true hc'.2)
        rwa [UInt32.toNat_div, show (2 : UInt32).toNat = 2 from rfl] at this
      have hmirror : ((n - 1) - i).toNat = n.toNat - 1 - i.toNat := by
        rw [UInt32.toNat_sub_of_le, uint32_toNat_sub_one n (by omega)]
        rw [UInt32.le_iff_toNat_le, uint32_toNat_sub_one n (by omega)]; omega
      have hperm := two_stores_perm xs i.toNat ((n - 1) - i).toNat (by omega) (by rw [hmirror]; omega)
      have := ih _ n (i + 1) ys i' h (by rw [hperm.size_eq]; exact hn)
      exact this.trans hperm
    · rw [if_neg hc] at h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      rw [h.1]

/-- Whenever the extracted reversal returns, it returns a permutation. -/
theorem reverse_perm (xs : Array UInt32) (fuel : Nat) (ys : Array UInt32)
    (h : sort_reverse_u32 xs fuel = some ((), ys)) (hsmall : xs.size < 2 ^ 32) : ys.Perm xs := by
  unfold sort_reverse_u32 at h
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨xs2, i2⟩, h2, h1⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at h1
  subst h1
  have hn : (xs.size.toUInt32).toNat = xs.size := by
    show (UInt32.ofNat _).toNat = _
    rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt hsmall
  exact reverse_loop_perm fuel xs _ 0 xs2 i2 h2 (Nat.le_of_eq hn)

/-! ## Arithmetic helpers -/

theorem toNat_add_of_lt (x y : UInt32) (h : x.toNat + y.toNat < 2 ^ 32) : (x + y).toNat = x.toNat + y.toNat := by
  rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt h

theorem toNat_sub_of_le' (x y : UInt32) (h : y.toNat ≤ x.toNat) : (x - y).toNat = x.toNat - y.toNat :=
  UInt32.toNat_sub_of_le x y (UInt32.le_iff_toNat_le.mpr h)

theorem toNat_two : (2 : UInt32).toNat = 2 := rfl
theorem toNat_one' : (1 : UInt32).toNat = 1 := rfl

/-! ## The bit length

`sort_bit_length n` returns `bits` with `n < 2 ^ bits` and, for `n ≠ 0`,
`2 ^ (bits - 1) ≤ n`; the pattern breaker relies on it to keep its random
offsets below twice the range length. -/

theorem bit_length_loop_spec (fuel : Nat) : ∀ (bits rest : UInt32) (b' r' : UInt32),
    sort_bit_length.loop1 bits rest fuel = some (b', r') → bits.toNat ≤ 32 → rest.toNat < 2 ^ (32 - bits.toNat) →
    bits.toNat ≤ b'.toNat ∧ b'.toNat ≤ 32 ∧ rest.toNat < 2 ^ (b'.toNat - bits.toNat) ∧
      (rest.toNat ≠ 0 → 2 ^ (b'.toNat - bits.toNat - 1) ≤ rest.toNat) ∧
      (rest.toNat = 0 → b'.toNat = bits.toNat) := by
  induction fuel with
  | zero => intro bits rest b' r' h; simp [sort_bit_length.loop1] at h
  | succ fuel ih =>
    intro bits rest b' r' h hb32 hrest
    unfold sort_bit_length.loop1 at h
    by_cases hc : decide (rest > (0 : UInt32)) = true
    · rw [if_pos hc] at h
      have hpos : 0 < rest.toNat := UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true hc)
      have hbits : bits.toNat < 32 := by
        apply Nat.lt_of_not_le
        intro hge
        have h0 : 32 - bits.toNat = 0 := by omega
        have h1 : (2 : Nat) ^ (32 - bits.toNat) = 1 := by rw [h0]
        omega
      have hb1 : (bits + 1).toNat = bits.toNat + 1 := toNat_add_of_lt bits 1 (by rw [toNat_one']; omega)
      have hhalf : (rest >>> 1).toNat = rest.toNat / 2 := by
        rw [UInt32.toNat_shiftRight, toNat_one', Nat.shiftRight_eq_div_pow]
      have hsplit : 2 ^ (32 - bits.toNat) = 2 * 2 ^ (32 - (bits.toNat + 1)) := by
        rw [← Nat.pow_succ']; congr 1; omega
      have hrest' : (rest >>> 1).toNat < 2 ^ (32 - (bits.toNat + 1)) := by
        rw [hhalf]; omega
      obtain ⟨h1, h2, h3, h4, h5⟩ := ih (bits + 1) (rest >>> 1) b' r' h (by rw [hb1]; omega) (by rw [hb1]; exact hrest')
      rw [hb1] at h1 h3 h4 h5
      rw [hhalf] at h3 h4 h5
      have hk : 2 ^ (b'.toNat - bits.toNat) = 2 * 2 ^ (b'.toNat - (bits.toNat + 1)) := by
        rw [← Nat.pow_succ']; congr 1; omega
      refine ⟨by omega, h2, by omega, ?_, fun h0 => by omega⟩
      intro _
      by_cases hz : rest.toNat / 2 = 0
      · have h5' := h5 hz
        have hk1 : b'.toNat - bits.toNat - 1 = 0 := by omega
        rw [hk1, Nat.pow_zero]; omega
      · have h4' := h4 hz
        have hne : b'.toNat - (bits.toNat + 1) ≠ 0 := by
          intro h0
          rw [h0, Nat.pow_zero] at h3
          omega
        have hk1 : 2 ^ (b'.toNat - bits.toNat - 1) = 2 * 2 ^ (b'.toNat - (bits.toNat + 1) - 1) := by
          rw [← Nat.pow_succ']; congr 1; omega
        omega
    · rw [if_neg hc] at h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hz : rest.toNat = 0 := by
        have h0 : ¬ ((0 : UInt32) < rest) := of_decide_eq_false (Bool.eq_false_iff.mpr hc)
        have h1 : ¬ ((0 : UInt32).toNat < rest.toNat) := fun hl => h0 (UInt32.lt_iff_toNat_lt.mpr hl)
        simp at h1; omega
      refine ⟨Nat.le_refl _, hb32, ?_, fun h0 => absurd hz h0, fun _ => rfl⟩
      rw [Nat.sub_self, Nat.pow_zero]; omega

theorem bit_length_spec (n : UInt32) (fuel : Nat) (bits : UInt32) (h : sort_bit_length n fuel = some bits) :
    bits.toNat ≤ 32 ∧ n.toNat < 2 ^ bits.toNat ∧ (n.toNat ≠ 0 → 2 ^ (bits.toNat - 1) ≤ n.toNat) := by
  unfold sort_bit_length at h
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨b', r'⟩, h', h1⟩ := h
  simp only [Option.some.injEq] at h1
  subst h1
  obtain ⟨_, h2, h3, h4, _⟩ := bit_length_loop_spec fuel 0 n b' r' h' (by simp) (by simp; exact UInt32.toNat_lt n)
  simp at h3 h4
  exact ⟨h2, h3, h4⟩

/-! ## Pattern breaking

Three swaps inside `[a, b)`: the middle positions `middle - 1 + step` and the
random positions `a + other` with `other < length`. -/

theorem break_loop_perm (fuel : Nat) : ∀ (xs : Array UInt32) (a length mask : UInt32) (random : UInt64)
    (middle step : UInt32) (ys : Array UInt32) (r' : UInt64) (s' : UInt32),
    sort_break_patterns_u32.loop1 xs a length mask random middle step fuel = some (ys, r', s') →
    xs.size < 2 ^ 32 → a.toNat + length.toNat ≤ xs.size → mask.toNat + 1 ≤ 2 * length.toNat →
    a.toNat + 3 ≤ middle.toNat → middle.toNat + 2 ≤ a.toNat + length.toNat →
    ys.Perm xs := by
  induction fuel with
  | zero => intro xs a length mask random middle step ys r' s' h; simp [sort_break_patterns_u32.loop1] at h
  | succ fuel ih =>
    intro xs a length mask random middle step ys r' s' h hsmall hab hmask hmid1 hmid2
    unfold sort_break_patterns_u32.loop1 at h
    by_cases hc : decide (step < (3 : UInt32)) = true
    · rw [if_pos hc] at h
      have hstep : step.toNat < 3 := by
        have := UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true hc); simpa using this
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨other, hother, ⟨u, xs2⟩, hswap, h1⟩ := h
      -- the random offset stays below the length
      have hother_lt : other.toNat < length.toNat := by
        have hraw : ((((random ^^^ (random <<< 13)) ^^^ ((random ^^^ (random <<< 13)) >>> 7)) ^^^
            (((random ^^^ (random <<< 13)) ^^^ ((random ^^^ (random <<< 13)) >>> 7)) <<< 17)).toUInt32 &&& mask).toNat
            ≤ mask.toNat := by
          rw [UInt32.toNat_and]; exact Nat.and_le_right
        generalize hr : ((((random ^^^ (random <<< 13)) ^^^ ((random ^^^ (random <<< 13)) >>> 7)) ^^^
            (((random ^^^ (random <<< 13)) ^^^ ((random ^^^ (random <<< 13)) >>> 7)) <<< 17)).toUInt32 &&& mask) = raw at hother hraw
        split at hother
        · rename_i hge
          simp only [Option.pure_def, Option.some.injEq] at hother
          subst hother
          have hge' : length.toNat ≤ raw.toNat := UInt32.le_iff_toNat_le.mp (of_decide_eq_true hge)
          rw [toNat_sub_of_le' raw length hge']
          omega
        · rename_i hlt
          simp only [Option.pure_def, Option.some.injEq] at hother
          subst hother
          have h0 : ¬ (length ≤ raw) := of_decide_eq_false (Bool.eq_false_iff.mpr hlt)
          have h1 : ¬ (length.toNat ≤ raw.toNat) := fun hl => h0 (UInt32.le_iff_toNat_le.mpr hl)
          omega
      have hi : ((middle - 1) + step).toNat = middle.toNat - 1 + step.toNat := by
        rw [toNat_add_of_lt _ _ (by rw [toNat_sub_of_le' middle 1 (by rw [toNat_one']; omega), toNat_one']; omega),
          toNat_sub_of_le' middle 1 (by rw [toNat_one']; omega), toNat_one']
      have hj : (a + other).toNat = a.toNat + other.toNat := toNat_add_of_lt a other (by omega)
      have hperm := swap_perm xs _ _ fuel xs2 hswap (by rw [hi]; omega) (by rw [hj]; omega)
      have := ih xs2 a length mask _ middle (step + 1) ys r' s' h1 (by rw [hperm.size_eq]; exact hsmall)
        (by rw [hperm.size_eq]; exact hab) hmask hmid1 hmid2
      exact this.trans hperm
    · rw [if_neg hc] at h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      rw [h.1]

/-- Whenever the pattern breaker returns on a range `[a, b)` of the array, it
returns a permutation. -/
theorem break_patterns_perm (xs : Array UInt32) (a b : UInt32) (fuel : Nat) (ys : Array UInt32)
    (h : sort_break_patterns_u32 xs a b fuel = some ((), ys)) (hsmall : xs.size < 2 ^ 31)
    (hab : a.toNat ≤ b.toNat) (hb : b.toNat ≤ xs.size) : ys.Perm xs := by
  unfold sort_break_patterns_u32 at h
  have hlen : (b - a).toNat = b.toNat - a.toNat := toNat_sub_of_le' b a hab
  simp only [Option.pure_def, Option.bind_eq_bind] at h
  split at h
  · rename_i hge
    have hge8 : 8 ≤ b.toNat - a.toNat := by
      have := UInt32.le_iff_toNat_le.mp (of_decide_eq_true hge); rwa [hlen] at this
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨items, ⟨bits, hbits, ⟨xs2, r2, s2⟩, hloop, h2⟩, h1⟩ := h
    simp only [Option.some.injEq, Prod.mk.injEq, true_and] at h1 h2
    subst h1 h2
    obtain ⟨hb32, hlt, hlow⟩ := bit_length_spec (b - a) fuel bits hbits
    rw [hlen] at hlt hlow
    have hbits31 : bits.toNat ≤ 31 := by
      apply Nat.le_of_not_lt
      intro hgt
      have h32 : bits.toNat = 32 := by omega
      have := hlow (by omega)
      rw [h32] at this
      have : 2 ^ 31 ≤ b.toNat - a.toNat := this
      omega
    have hmask : (if decide (bits ≥ (32 : UInt32)) = true then (4294967295 : UInt32)
        else ((1 : UInt32) <<< bits) - 1).toNat + 1 ≤ 2 * (b.toNat - a.toNat) := by
      have hnot : decide (bits ≥ (32 : UInt32)) = false := by
        apply decide_eq_false
        intro hge32
        have := UInt32.le_iff_toNat_le.mp hge32
        simp at this; omega
      rw [hnot]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hshift : ((1 : UInt32) <<< bits).toNat = 2 ^ bits.toNat := by
        rw [UInt32.toNat_shiftLeft, toNat_one', Nat.shiftLeft_eq, Nat.one_mul,
          Nat.mod_eq_of_lt (by omega : bits.toNat < 32)]
        exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))
      have hmask_val : ((1 : UInt32) <<< bits - 1).toNat = 2 ^ bits.toNat - 1 := by
        rw [toNat_sub_of_le' _ 1 (by rw [hshift, toNat_one']; exact Nat.one_le_two_pow), hshift, toNat_one']
      have hlow' := hlow (by omega)
      have hbpos : 1 ≤ bits.toNat := by
        apply Nat.one_le_iff_ne_zero.mpr
        intro h0
        rw [h0, Nat.pow_zero] at hlt
        omega
      have h2 : 2 ^ bits.toNat = 2 * 2 ^ (bits.toNat - 1) := by
        rw [← Nat.pow_succ']; congr 1; omega
      rw [hmask_val, Nat.sub_add_cancel (Nat.two_pow_pos _), h2]
      exact Nat.mul_le_mul_left 2 hlow'
    have hquarter : ((b - a) / 4).toNat = (b.toNat - a.toNat) / 4 := by
      rw [UInt32.toNat_div, hlen]; rfl
    have hq2 : (((b - a) / 4) * 2).toNat = (b.toNat - a.toNat) / 4 * 2 := by
      rw [UInt32.toNat_mul, hquarter, toNat_two]; exact Nat.mod_eq_of_lt (by omega)
    have hmid : ((a + (((b - a) / 4) * 2)) - 1).toNat = a.toNat + (b.toNat - a.toNat) / 4 * 2 - 1 := by
      rw [toNat_sub_of_le' _ 1 (by rw [toNat_add_of_lt _ _ (by rw [hq2]; omega), hq2, toNat_one']; omega),
        toNat_add_of_lt _ _ (by rw [hq2]; omega), hq2, toNat_one']
    exact break_loop_perm fuel xs a (b - a) _ _ _ 0 xs2 r2 s2 hloop (by omega) (by rw [hlen]; omega)
      (by rw [hlen]; exact hmask) (by rw [hmid]; omega) (by rw [hmid, hlen]; omega)
  · simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq, true_and] at h
    rw [h]

/-! ## Pivot selection: read-only, and inside the range -/

theorem median3_spec (xs : Array UInt32) (a b c swaps : UInt32) (fuel : Nat) (m : SortMedian) (ys : Array UInt32)
    (h : sort_median3_u32 xs a b c swaps fuel = some (m, ys)) :
    ys = xs ∧ (m.index = a ∨ m.index = b ∨ m.index = c) := by
  unfold sort_median3_u32 at h
  simp only [Option.pure_def, Option.bind_eq_bind] at h
  split at h <;> simp only [Option.bind_some] at h <;> split at h <;> simp only [Option.bind_some] at h <;>
    split at h <;>
    (simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp)

/-- The chosen pivot lies in `[a, b)` whenever the range is non-empty, and the
selection does not write. -/
theorem choose_pivot_spec (xs : Array UInt32) (a b : UInt32) (fuel : Nat) (p : SortPivot) (ys : Array UInt32)
    (h : sort_choose_pivot_u32 xs a b fuel = some (p, ys)) (hab : a.toNat < b.toNat) (hb : b.toNat < 2 ^ 32) :
    ys = xs ∧ a.toNat ≤ p.index.toNat ∧ p.index.toNat < b.toNat := by
  unfold sort_choose_pivot_u32 at h
  have hlen : (b - a).toNat = b.toNat - a.toNat := toNat_sub_of_le' b a (by omega)
  have hq : ((b - a) / 4).toNat = (b.toNat - a.toNat) / 4 := by rw [UInt32.toNat_div, hlen]; rfl
  have hi : (a + (b - a) / 4).toNat = a.toNat + (b.toNat - a.toNat) / 4 := by
    rw [toNat_add_of_lt _ _ (by rw [hq]; omega), hq]
  have hq2 : (((b - a) / 4) * 2).toNat = (b.toNat - a.toNat) / 4 * 2 := by
    rw [UInt32.toNat_mul, hq, toNat_two]; exact Nat.mod_eq_of_lt (by omega)
  have hj : (a + ((b - a) / 4) * 2).toNat = a.toNat + (b.toNat - a.toNat) / 4 * 2 := by
    rw [toNat_add_of_lt _ _ (by rw [hq2]; omega), hq2]
  have hq3 : (((b - a) / 4) * 3).toNat = (b.toNat - a.toNat) / 4 * 3 := by
    rw [UInt32.toNat_mul, hq, show (3 : UInt32).toNat = 3 from rfl]; exact Nat.mod_eq_of_lt (by omega)
  have hk : (a + ((b - a) / 4) * 3).toNat = a.toNat + (b.toNat - a.toNat) / 4 * 3 := by
    rw [toNat_add_of_lt _ _ (by rw [hq3]; omega), hq3]
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨xs1, i1, j1, k1, s1⟩, h1, h'⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  show xs1 = xs ∧ a.toNat ≤ j1.toNat ∧ j1.toNat < b.toNat
  split at h1
  · rename_i hge8
    have h8 : 8 ≤ b.toNat - a.toNat := by
      have := UInt32.le_iff_toNat_le.mp (of_decide_eq_true hge8); rwa [hlen] at this
    simp only [Option.bind_eq_some_iff] at h1
    obtain ⟨⟨xs0, i0, j0, k0, s0⟩, h0, h1⟩ := h1
    simp only [Option.bind_eq_some_iff] at h1
    obtain ⟨⟨m4, xs4⟩, h4, h1⟩ := h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h1
    obtain ⟨hxs4, hm4⟩ := median3_spec xs0 i0 j0 k0 s0 fuel m4 xs4 h4
    have hcand : xs0 = xs ∧ a.toNat ≤ i0.toNat ∧ i0.toNat < b.toNat ∧ a.toNat ≤ j0.toNat ∧ j0.toNat < b.toNat ∧
        a.toNat ≤ k0.toNat ∧ k0.toNat < b.toNat := by
      split at h0
      · rename_i hge50
        have h50 : 50 ≤ b.toNat - a.toNat := by
          have := UInt32.le_iff_toNat_le.mp (of_decide_eq_true hge50); rwa [hlen] at this
        simp only [Option.bind_eq_some_iff] at h0
        obtain ⟨⟨mi, xsi⟩, hmi, ⟨mj, xsj⟩, hmj, ⟨mk, xsk⟩, hmk, h0⟩ := h0
        simp only [Option.some.injEq, Prod.mk.injEq] at h0
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h0
        obtain ⟨hxsi, hmi'⟩ := median3_spec _ _ _ _ _ fuel mi xsi hmi
        obtain ⟨hxsj, hmj'⟩ := median3_spec _ _ _ _ _ fuel mj xsj hmj
        obtain ⟨hxsk, hmk'⟩ := median3_spec _ _ _ _ _ fuel mk xsk hmk
        have hi1 : (a + (b - a) / 4 - 1).toNat = a.toNat + (b.toNat - a.toNat) / 4 - 1 := by
          rw [toNat_sub_of_le' _ 1 (by rw [hi, toNat_one']; omega), hi, toNat_one']
        have hi2 : (a + (b - a) / 4 + 1).toNat = a.toNat + (b.toNat - a.toNat) / 4 + 1 := by
          rw [toNat_add_of_lt _ _ (by rw [hi, toNat_one']; omega), hi, toNat_one']
        have hj1 : (a + ((b - a) / 4) * 2 - 1).toNat = a.toNat + (b.toNat - a.toNat) / 4 * 2 - 1 := by
          rw [toNat_sub_of_le' _ 1 (by rw [hj, toNat_one']; omega), hj, toNat_one']
        have hj2 : (a + ((b - a) / 4) * 2 + 1).toNat = a.toNat + (b.toNat - a.toNat) / 4 * 2 + 1 := by
          rw [toNat_add_of_lt _ _ (by rw [hj, toNat_one']; omega), hj, toNat_one']
        have hk1 : (a + ((b - a) / 4) * 3 - 1).toNat = a.toNat + (b.toNat - a.toNat) / 4 * 3 - 1 := by
          rw [toNat_sub_of_le' _ 1 (by rw [hk, toNat_one']; omega), hk, toNat_one']
        have hk2 : (a + ((b - a) / 4) * 3 + 1).toNat = a.toNat + (b.toNat - a.toNat) / 4 * 3 + 1 := by
          rw [toNat_add_of_lt _ _ (by rw [hk, toNat_one']; omega), hk, toNat_one']
        refine ⟨by rw [hxsk, hxsj, hxsi], ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rcases hmi' with h | h | h <;> rw [h] <;> omega
        · rcases hmi' with h | h | h <;> rw [h] <;> omega
        · rcases hmj' with h | h | h <;> rw [h] <;> omega
        · rcases hmj' with h | h | h <;> rw [h] <;> omega
        · rcases hmk' with h | h | h <;> rw [h] <;> omega
        · rcases hmk' with h | h | h <;> rw [h] <;> omega
      · simp only [Option.some.injEq, Prod.mk.injEq] at h0
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h0
        refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hi, hj, hk] <;> omega
    obtain ⟨hxs0, hi1, hi2, hj1, hj2, hk1, hk2⟩ := hcand
    refine ⟨by rw [hxs4, hxs0], ?_, ?_⟩
    · rcases hm4 with h | h | h <;> rw [h] <;> omega
    · rcases hm4 with h | h | h <;> rw [h] <;> omega
  · simp only [Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h1
    refine ⟨rfl, ?_, ?_⟩
    · rw [hj]; omega
    · rw [hj]; omega

/-! ## Partial insertion sort

Every swap is `(i, i - 1)` with `a < i < b`, either at the first disorder or
while shifting an element left or right from it. -/

theorem pi_loop2_bounds (fuel : Nat) : ∀ (xs : Array UInt32) (b i i' : UInt32),
    sort_partial_insertion_u32.loop2 xs b i fuel = some i' → i.toNat ≤ b.toNat →
    i.toNat ≤ i'.toNat ∧ i'.toNat ≤ b.toNat := by
  induction fuel with
  | zero => intro xs b i i' h; simp [sort_partial_insertion_u32.loop2] at h
  | succ fuel ih =>
    intro xs b i i' h hi
    unfold sort_partial_insertion_u32.loop2 at h
    split at h
    · rename_i hc
      have hlt : i.toNat < b.toNat := UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true ((Bool.and_eq_true _ _).mp hc).1)
      have hi1 : (i + 1).toNat = i.toNat + 1 := toNat_add_of_lt i 1 (by rw [toNat_one']; have := UInt32.toNat_lt b; omega)
      obtain ⟨h1, h2⟩ := ih xs b (i + 1) i' h (by rw [hi1]; omega)
      rw [hi1] at h1
      exact ⟨by omega, h2⟩
    · simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      exact ⟨Nat.le_refl _, hi⟩

theorem pi_loop3_perm (fuel : Nat) : ∀ (xs : Array UInt32) (a left : UInt32) (sh : Bool) (ys : Array UInt32)
    (l' : UInt32) (s' : Bool),
    sort_partial_insertion_u32.loop3 xs a left sh fuel = some (ys, l', s') → left.toNat < xs.size → ys.Perm xs := by
  induction fuel with
  | zero => intro xs a left sh ys l' s' h; simp [sort_partial_insertion_u32.loop3] at h
  | succ fuel ih =>
    intro xs a left sh ys l' s' h hleft
    unfold sort_partial_insertion_u32.loop3 at h
    split at h
    · rename_i hc
      have hgt : a.toNat < left.toNat := UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true ((Bool.and_eq_true _ _).mp hc).2)
      have hl1 : (left - 1).toNat = left.toNat - 1 := uint32_toNat_sub_one left (by omega)
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨xs2, l2, s2⟩, h2, h1⟩ := h
      split at h2
      · simp only [Option.bind_eq_some_iff] at h2
        obtain ⟨⟨u, xs3⟩, hswap, h2⟩ := h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl, rfl⟩ := h2
        have hperm := swap_perm xs left (left - 1) fuel xs3 hswap hleft (by rw [hl1]; omega)
        have := ih xs3 a (left - 1) sh ys l' s' h1 (by rw [hperm.size_eq, hl1]; omega)
        exact this.trans hperm
      · simp only [Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl, rfl⟩ := h2
        exact ih xs a left false ys l' s' h1 hleft
    · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      rw [h.1]

theorem pi_loop4_perm (fuel : Nat) : ∀ (xs : Array UInt32) (b right : UInt32) (mv : Bool) (ys : Array UInt32)
    (r' : UInt32) (m' : Bool),
    sort_partial_insertion_u32.loop4 xs b right mv fuel = some (ys, r', m') → b.toNat ≤ xs.size →
    1 ≤ right.toNat → ys.Perm xs := by
  induction fuel with
  | zero => intro xs b right mv ys r' m' h; simp [sort_partial_insertion_u32.loop4] at h
  | succ fuel ih =>
    intro xs b right mv ys r' m' h hb hright
    unfold sort_partial_insertion_u32.loop4 at h
    split at h
    · rename_i hc
      have hlt : right.toNat < b.toNat := UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true ((Bool.and_eq_true _ _).mp hc).2)
      have hr1 : (right - 1).toNat = right.toNat - 1 := uint32_toNat_sub_one right (by omega)
      have hr2 : (right + 1).toNat = right.toNat + 1 := toNat_add_of_lt right 1 (by rw [toNat_one']; have := UInt32.toNat_lt b; omega)
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨xs2, r2, m2⟩, h2, h1⟩ := h
      split at h2
      · simp only [Option.bind_eq_some_iff] at h2
        obtain ⟨⟨u, xs3⟩, hswap, h2⟩ := h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl, rfl⟩ := h2
        have hperm := swap_perm xs right (right - 1) fuel xs3 hswap (by omega) (by rw [hr1]; omega)
        have := ih xs3 b (right + 1) mv ys r' m' h1 (by rw [hperm.size_eq]; exact hb) (by rw [hr2]; omega)
        exact this.trans hperm
      · simp only [Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl, rfl⟩ := h2
        exact ih xs b right false ys r' m' h1 hb hright
    · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      rw [h.1]

theorem pi_loop1_perm (fuel : Nat) : ∀ (xs : Array UInt32) (a b i steps : UInt32) (sorted trying : Bool)
    (ys : Array UInt32) (i' st' : UInt32) (so' tr' : Bool),
    sort_partial_insertion_u32.loop1 xs a b i steps sorted trying fuel = some (ys, i', st', so', tr') →
    xs.size < 2 ^ 32 → a.toNat < b.toNat → b.toNat ≤ xs.size → a.toNat + 1 ≤ i.toNat → i.toNat ≤ b.toNat →
    ys.Perm xs := by
  induction fuel with
  | zero => intro xs a b i steps sorted trying ys i' st' so' tr' h; simp [sort_partial_insertion_u32.loop1] at h
  | succ fuel ih =>
    intro xs a b i steps sorted trying ys i' st' so' tr' h hsmall hab hb hai hib
    unfold sort_partial_insertion_u32.loop1 at h
    split at h
    · simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨i2, hi2, ⟨xs2, st2, so2, tr2⟩, hbody, hrec⟩ := h
      obtain ⟨hi2a, hi2b⟩ := pi_loop2_bounds fuel xs b i i2 hi2 hib
      -- the body: either done, or give up, or one fix-up round
      have hbody' : xs2.Perm xs := by
        split at hbody
        · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hbody
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hbody
          exact Array.Perm.refl _
        · rename_i hne
          have hne' : i2 ≠ b := by
            intro heq; subst heq; simp at hne
          have hlt : i2.toNat < b.toNat := by
            have : i2.toNat ≠ b.toNat := fun heq => hne' (UInt32.toNat.inj heq)
            omega
          simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at hbody
          obtain ⟨⟨xs3, st3, tr3⟩, hfix, hbody⟩ := hbody
          simp only [Option.some.injEq, Prod.mk.injEq] at hbody
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hbody
          split at hfix
          · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hfix
            obtain ⟨rfl, rfl, rfl⟩ := hfix
            exact Array.Perm.refl _
          · simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at hfix
            obtain ⟨⟨u, xs4⟩, hswap, xs5, hleft, xs6, hright, hfix⟩ := hfix
            simp only [Option.some.injEq, Prod.mk.injEq] at hfix
            obtain ⟨rfl, rfl, rfl⟩ := hfix
            have hi21 : (i2 - 1).toNat = i2.toNat - 1 := uint32_toNat_sub_one i2 (by omega)
            have hp4 := swap_perm xs i2 (i2 - 1) fuel xs4 hswap (by omega) (by rw [hi21]; omega)
            have hp5 : xs5.Perm xs4 := by
              split at hleft
              · simp only [Option.bind_eq_some_iff] at hleft
                obtain ⟨⟨xs5', l', s'⟩, h3, hleft⟩ := hleft
                simp only [Option.some.injEq] at hleft
                subst hleft
                exact pi_loop3_perm fuel xs4 a (i2 - 1) true xs5' l' s' h3 (by rw [hp4.size_eq, hi21]; omega)
              · simp only [Option.pure_def, Option.some.injEq] at hleft
                subst hleft
                exact Array.Perm.refl _
            have hp6 : xs6.Perm xs5 := by
              split at hright
              · simp only [Option.bind_eq_some_iff] at hright
                obtain ⟨⟨xs6', r', m'⟩, h4, hright⟩ := hright
                simp only [Option.some.injEq] at hright
                subst hright
                have hi2p : (i2 + 1).toNat = i2.toNat + 1 := toNat_add_of_lt i2 1 (by rw [toNat_one']; omega)
                exact pi_loop4_perm fuel xs5 b (i2 + 1) true xs6' r' m' h4 (by rw [hp5.size_eq, hp4.size_eq]; exact hb)
                  (by rw [hi2p]; omega)
              · simp only [Option.pure_def, Option.some.injEq] at hright
                subst hright
                exact Array.Perm.refl _
            exact hp6.trans (hp5.trans hp4)
      have := ih xs2 a b i2 st2 so2 tr2 ys i' st' so' tr' hrec (by rw [hbody'.size_eq]; exact hsmall) hab
        (by rw [hbody'.size_eq]; exact hb) (by omega) hi2b
      exact this.trans hbody'
    · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      rw [h.1]

/-- Whenever the partial insertion sort returns on a non-empty range `[a, b)`
of the array, it returns a permutation. -/
theorem partial_insertion_perm (xs : Array UInt32) (a b : UInt32) (fuel : Nat) (r : Bool) (ys : Array UInt32)
    (h : sort_partial_insertion_u32 xs a b fuel = some (r, ys)) (hsmall : xs.size < 2 ^ 32)
    (hab : a.toNat < b.toNat) (hb : b.toNat ≤ xs.size) : ys.Perm xs := by
  unfold sort_partial_insertion_u32 at h
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨xs2, i2, st2, so2, tr2⟩, h2, h1⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  have ha1 : (a + 1).toNat = a.toNat + 1 := toNat_add_of_lt a 1 (by rw [toNat_one']; have := UInt32.toNat_lt b; omega)
  exact pi_loop1_perm fuel xs a b (a + 1) 0 false true xs2 i2 st2 so2 tr2 h2 hsmall hab hb (Nat.le_of_eq ha1.symm)
    (by rw [ha1]; omega)

/-! ## The two partitions

Both scans keep `a + 1 ≤ i ≤ b` and `a ≤ j < b`: `i` only moves up while
`i ≤ j`, `j` only moves down while `i ≤ j`, so the swap of `i` and `j`
happens inside `[a + 1, b)` and the final swap of `j` with `a` inside
`[a, b)`. -/

theorem pe_loop2_bounds (fuel : Nat) : ∀ (xs : Array UInt32) (a i j i' : UInt32),
    sort_partition_equal_u32.loop2 xs a i j fuel = some i' → ∀ (bnd : Nat), bnd < 2 ^ 32 → i.toNat ≤ bnd → j.toNat + 1 ≤ bnd →
    i.toNat ≤ i'.toNat ∧ i'.toNat ≤ bnd := by
  induction fuel with
  | zero => intro xs a i j i' h; simp [sort_partition_equal_u32.loop2] at h
  | succ fuel ih =>
    intro xs a i j i' h bnd hbnd hi hj
    unfold sort_partition_equal_u32.loop2 at h
    split at h
    · rename_i hc
      have hle : i.toNat ≤ j.toNat := UInt32.le_iff_toNat_le.mp (of_decide_eq_true ((Bool.and_eq_true _ _).mp hc).1)
      have hi1 : (i + 1).toNat = i.toNat + 1 := toNat_add_of_lt i 1 (by rw [toNat_one']; omega)
      obtain ⟨h1, h2⟩ := ih xs a (i + 1) j i' h bnd hbnd (by rw [hi1]; omega) hj
      rw [hi1] at h1
      exact ⟨by omega, h2⟩
    · simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      exact ⟨Nat.le_refl _, hi⟩

theorem pe_loop3_bounds (fuel : Nat) : ∀ (xs : Array UInt32) (a i j j' : UInt32),
    sort_partition_equal_u32.loop3 xs a i j fuel = some j' → a.toNat + 1 ≤ i.toNat → a.toNat ≤ j.toNat →
    j'.toNat ≤ j.toNat ∧ a.toNat ≤ j'.toNat := by
  induction fuel with
  | zero => intro xs a i j j' h; simp [sort_partition_equal_u32.loop3] at h
  | succ fuel ih =>
    intro xs a i j j' h hi hj
    unfold sort_partition_equal_u32.loop3 at h
    split at h
    · rename_i hc
      have hle : i.toNat ≤ j.toNat := UInt32.le_iff_toNat_le.mp (of_decide_eq_true ((Bool.and_eq_true _ _).mp hc).1)
      have hj1 : (j - 1).toNat = j.toNat - 1 := uint32_toNat_sub_one j (by omega)
      obtain ⟨h1, h2⟩ := ih xs a i (j - 1) j' h hi (by rw [hj1]; omega)
      rw [hj1] at h1
      exact ⟨by omega, h2⟩
    · simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      exact ⟨Nat.le_refl _, hj⟩

theorem pe_loop1_spec (fuel : Nat) : ∀ (xs : Array UInt32) (a i j : UInt32) (sc : Bool) (ys : Array UInt32)
    (i' j' : UInt32) (s' : Bool),
    sort_partition_equal_u32.loop1 xs a i j sc fuel = some (ys, i', j', s') →
    ∀ (b : Nat), b < 2 ^ 32 → b ≤ xs.size → a.toNat + 1 ≤ i.toNat → i.toNat ≤ b → a.toNat ≤ j.toNat → j.toNat + 1 ≤ b →
    ys.Perm xs ∧ a.toNat + 1 ≤ i'.toNat ∧ i'.toNat ≤ b := by
  induction fuel with
  | zero => intro xs a i j sc ys i' j' s' h; simp [sort_partition_equal_u32.loop1] at h
  | succ fuel ih =>
    intro xs a i j sc ys i' j' s' h b hb32 hb hai hib haj hjb
    unfold sort_partition_equal_u32.loop1 at h
    cases sc with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨Array.Perm.refl _, hai, hib⟩
    | true =>
      simp only [↓reduceIte, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨i2, hi2, j2, hj2, ⟨xs3, i3, j3, s3⟩, hbody, hrec⟩ := h
      obtain ⟨hi2a, hi2b⟩ := pe_loop2_bounds fuel xs a i j i2 hi2 b hb32 hib hjb
      obtain ⟨hj2a, hj2b⟩ := pe_loop3_bounds fuel xs a i2 j j2 hj2 (by omega) haj
      split at hbody
      · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hbody
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hbody
        exact ih xs a i2 j2 false ys i' j' s' hrec b hb32 hb (by omega) hi2b hj2b (by omega)
      · rename_i hle
        have hle' : i2.toNat ≤ j2.toNat := by
          have h0 : ¬ (j2 < i2) := of_decide_eq_false (Bool.eq_false_iff.mpr hle)
          have h1 : ¬ (j2.toNat < i2.toNat) := fun hl => h0 (UInt32.lt_iff_toNat_lt.mpr hl)
          omega
        simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at hbody
        obtain ⟨⟨u, xs4⟩, hswap, hbody⟩ := hbody
        simp only [Option.some.injEq, Prod.mk.injEq] at hbody
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hbody
        have hperm := swap_perm xs i2 j2 fuel xs4 hswap (by omega) (by omega)
        have hi21 : (i2 + 1).toNat = i2.toNat + 1 := toNat_add_of_lt i2 1 (by rw [toNat_one']; omega)
        have hj21 : (j2 - 1).toNat = j2.toNat - 1 := uint32_toNat_sub_one j2 (by omega)
        obtain ⟨hp, h1, h2⟩ := ih xs4 a (i2 + 1) (j2 - 1) true ys i' j' s' hrec b hb32 (by rw [hperm.size_eq]; exact hb)
          (by rw [hi21]; omega) (by rw [hi21]; omega) (by rw [hj21]; omega) (by rw [hj21]; omega)
        exact ⟨hp.trans hperm, h1, h2⟩

/-- Whenever the equal-elements partition returns on a non-empty range `[a, b)`
with the pivot inside it, it returns a permutation and a split index in
`[a + 1, b]`. -/
theorem partition_equal_spec (xs : Array UInt32) (a b pivot : UInt32) (fuel : Nat) (i' : UInt32) (ys : Array UInt32)
    (h : sort_partition_equal_u32 xs a b pivot fuel = some (i', ys))
    (hab : a.toNat < b.toNat) (hb : b.toNat ≤ xs.size) (_hpa : a.toNat ≤ pivot.toNat) (hpb : pivot.toNat < b.toNat) :
    ys.Perm xs ∧ a.toNat + 1 ≤ i'.toNat ∧ i'.toNat ≤ b.toNat := by
  unfold sort_partition_equal_u32 at h
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨u, xs2⟩, hswap, ⟨xs3, i3, j3, s3⟩, hloop, h1⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  have hperm := swap_perm xs a pivot fuel xs2 hswap (by omega) (by omega)
  have ha1 : (a + 1).toNat = a.toNat + 1 := toNat_add_of_lt a 1 (by rw [toNat_one']; have := UInt32.toNat_lt b; omega)
  have hb1 : (b - 1).toNat = b.toNat - 1 := uint32_toNat_sub_one b (by omega)
  obtain ⟨hp, h1, h2⟩ := pe_loop1_spec fuel xs2 a (a + 1) (b - 1) true xs3 i3 j3 s3 hloop b.toNat (UInt32.toNat_lt b)
    (by rw [hperm.size_eq]; exact hb) (Nat.le_of_eq ha1.symm) (by rw [ha1]; omega) (by rw [hb1]; omega) (by rw [hb1]; omega)
  exact ⟨hp.trans hperm, h1, h2⟩

theorem pt_loop1_bounds (fuel : Nat) : ∀ (xs : Array UInt32) (a i j i' : UInt32),
    sort_partition_u32.loop1 xs a i j fuel = some i' → ∀ (bnd : Nat), bnd < 2 ^ 32 → i.toNat ≤ bnd → j.toNat + 1 ≤ bnd →
    i.toNat ≤ i'.toNat ∧ i'.toNat ≤ bnd := by
  induction fuel with
  | zero => intro xs a i j i' h; simp [sort_partition_u32.loop1] at h
  | succ fuel ih =>
    intro xs a i j i' h bnd hbnd hi hj
    unfold sort_partition_u32.loop1 at h
    split at h
    · rename_i hc
      have hle : i.toNat ≤ j.toNat := UInt32.le_iff_toNat_le.mp (of_decide_eq_true ((Bool.and_eq_true _ _).mp hc).1)
      have hi1 : (i + 1).toNat = i.toNat + 1 := toNat_add_of_lt i 1 (by rw [toNat_one']; omega)
      obtain ⟨h1, h2⟩ := ih xs a (i + 1) j i' h bnd hbnd (by rw [hi1]; omega) hj
      rw [hi1] at h1
      exact ⟨by omega, h2⟩
    · simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      exact ⟨Nat.le_refl _, hi⟩

theorem pt_loop4_bounds (fuel : Nat) : ∀ (xs : Array UInt32) (a i j i' : UInt32),
    sort_partition_u32.loop4 xs a i j fuel = some i' → ∀ (bnd : Nat), bnd < 2 ^ 32 → i.toNat ≤ bnd → j.toNat + 1 ≤ bnd →
    i.toNat ≤ i'.toNat ∧ i'.toNat ≤ bnd := by
  induction fuel with
  | zero => intro xs a i j i' h; simp [sort_partition_u32.loop4] at h
  | succ fuel ih =>
    intro xs a i j i' h bnd hbnd hi hj
    unfold sort_partition_u32.loop4 at h
    split at h
    · rename_i hc
      have hle : i.toNat ≤ j.toNat := UInt32.le_iff_toNat_le.mp (of_decide_eq_true ((Bool.and_eq_true _ _).mp hc).1)
      have hi1 : (i + 1).toNat = i.toNat + 1 := toNat_add_of_lt i 1 (by rw [toNat_one']; omega)
      obtain ⟨h1, h2⟩ := ih xs a (i + 1) j i' h bnd hbnd (by rw [hi1]; omega) hj
      rw [hi1] at h1
      exact ⟨by omega, h2⟩
    · simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      exact ⟨Nat.le_refl _, hi⟩

theorem pt_loop2_bounds (fuel : Nat) : ∀ (xs : Array UInt32) (a i j j' : UInt32),
    sort_partition_u32.loop2 xs a i j fuel = some j' → a.toNat + 1 ≤ i.toNat → a.toNat ≤ j.toNat →
    j'.toNat ≤ j.toNat ∧ a.toNat ≤ j'.toNat := by
  induction fuel with
  | zero => intro xs a i j j' h; simp [sort_partition_u32.loop2] at h
  | succ fuel ih =>
    intro xs a i j j' h hi hj
    unfold sort_partition_u32.loop2 at h
    split at h
    · rename_i hc
      have hle : i.toNat ≤ j.toNat := UInt32.le_iff_toNat_le.mp (of_decide_eq_true ((Bool.and_eq_true _ _).mp hc).1)
      have hj1 : (j - 1).toNat = j.toNat - 1 := uint32_toNat_sub_one j (by omega)
      obtain ⟨h1, h2⟩ := ih xs a i (j - 1) j' h hi (by rw [hj1]; omega)
      rw [hj1] at h1
      exact ⟨by omega, h2⟩
    · simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      exact ⟨Nat.le_refl _, hj⟩

theorem pt_loop5_bounds (fuel : Nat) : ∀ (xs : Array UInt32) (a i j j' : UInt32),
    sort_partition_u32.loop5 xs a i j fuel = some j' → a.toNat + 1 ≤ i.toNat → a.toNat ≤ j.toNat →
    j'.toNat ≤ j.toNat ∧ a.toNat ≤ j'.toNat := by
  induction fuel with
  | zero => intro xs a i j j' h; simp [sort_partition_u32.loop5] at h
  | succ fuel ih =>
    intro xs a i j j' h hi hj
    unfold sort_partition_u32.loop5 at h
    split at h
    · rename_i hc
      have hle : i.toNat ≤ j.toNat := UInt32.le_iff_toNat_le.mp (of_decide_eq_true ((Bool.and_eq_true _ _).mp hc).1)
      have hj1 : (j - 1).toNat = j.toNat - 1 := uint32_toNat_sub_one j (by omega)
      obtain ⟨h1, h2⟩ := ih xs a i (j - 1) j' h hi (by rw [hj1]; omega)
      rw [hj1] at h1
      exact ⟨by omega, h2⟩
    · simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      exact ⟨Nat.le_refl _, hj⟩

theorem pt_loop3_spec (fuel : Nat) : ∀ (xs : Array UInt32) (a i j : UInt32) (sc : Bool) (ys : Array UInt32)
    (i' j' : UInt32) (s' : Bool),
    sort_partition_u32.loop3 xs a i j sc fuel = some (ys, i', j', s') →
    ∀ (b : Nat), b < 2 ^ 32 → b ≤ xs.size → a.toNat + 1 ≤ i.toNat → i.toNat ≤ b → a.toNat ≤ j.toNat → j.toNat + 1 ≤ b →
    ys.Perm xs ∧ a.toNat ≤ j'.toNat ∧ j'.toNat + 1 ≤ b := by
  induction fuel with
  | zero => intro xs a i j sc ys i' j' s' h; simp [sort_partition_u32.loop3] at h
  | succ fuel ih =>
    intro xs a i j sc ys i' j' s' h b hb32 hb hai hib haj hjb
    unfold sort_partition_u32.loop3 at h
    cases sc with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨Array.Perm.refl _, haj, hjb⟩
    | true =>
      simp only [↓reduceIte, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨i2, hi2, j2, hj2, ⟨xs3, i3, j3, s3⟩, hbody, hrec⟩ := h
      obtain ⟨hi2a, hi2b⟩ := pt_loop4_bounds fuel xs a i j i2 hi2 b hb32 hib hjb
      obtain ⟨hj2a, hj2b⟩ := pt_loop5_bounds fuel xs a i2 j j2 hj2 (by omega) haj
      split at hbody
      · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hbody
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hbody
        exact ih xs a i2 j2 false ys i' j' s' hrec b hb32 hb (by omega) hi2b hj2b (by omega)
      · rename_i hle
        have hle' : i2.toNat ≤ j2.toNat := by
          have h0 : ¬ (j2 < i2) := of_decide_eq_false (Bool.eq_false_iff.mpr hle)
          have h1 : ¬ (j2.toNat < i2.toNat) := fun hl => h0 (UInt32.lt_iff_toNat_lt.mpr hl)
          omega
        simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at hbody
        obtain ⟨⟨u, xs4⟩, hswap, hbody⟩ := hbody
        simp only [Option.some.injEq, Prod.mk.injEq] at hbody
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hbody
        have hperm := swap_perm xs i2 j2 fuel xs4 hswap (by omega) (by omega)
        have hi21 : (i2 + 1).toNat = i2.toNat + 1 := toNat_add_of_lt i2 1 (by rw [toNat_one']; omega)
        have hj21 : (j2 - 1).toNat = j2.toNat - 1 := uint32_toNat_sub_one j2 (by omega)
        obtain ⟨hp, h1, h2⟩ := ih xs4 a (i2 + 1) (j2 - 1) true ys i' j' s' hrec b hb32 (by rw [hperm.size_eq]; exact hb)
          (by rw [hi21]; omega) (by rw [hi21]; omega) (by rw [hj21]; omega) (by rw [hj21]; omega)
        exact ⟨hp.trans hperm, h1, h2⟩

/-- Whenever the partition returns on a non-empty range `[a, b)` with the
pivot inside it, it returns a permutation and a split point in `[a, b)`. -/
theorem partition_spec (xs : Array UInt32) (a b pivot : UInt32) (fuel : Nat) (split : SortSplit) (ys : Array UInt32)
    (h : sort_partition_u32 xs a b pivot fuel = some (split, ys))
    (hab : a.toNat < b.toNat) (hb : b.toNat ≤ xs.size) (_hpa : a.toNat ≤ pivot.toNat) (hpb : pivot.toNat < b.toNat) :
    ys.Perm xs ∧ a.toNat ≤ split.mid.toNat ∧ split.mid.toNat + 1 ≤ b.toNat := by
  unfold sort_partition_u32 at h
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨u, xs2⟩, hswap, i1, hi1, j1, hj1, ⟨r2, xs5, i5, j5⟩, hbody, h1⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  have hperm := swap_perm xs a pivot fuel xs2 hswap (by omega) (by omega)
  have ha1 : (a + 1).toNat = a.toNat + 1 := toNat_add_of_lt a 1 (by rw [toNat_one']; have := UInt32.toNat_lt b; omega)
  have hb1 : (b - 1).toNat = b.toNat - 1 := uint32_toNat_sub_one b (by omega)
  obtain ⟨hi1a, hi1b⟩ := pt_loop1_bounds fuel xs2 a (a + 1) (b - 1) i1 hi1 b.toNat (UInt32.toNat_lt b) (by rw [ha1]; omega) (by rw [hb1]; omega)
  obtain ⟨hj1a, hj1b⟩ := pt_loop2_bounds fuel xs2 a i1 (b - 1) j1 hj1 (by rw [ha1] at hi1a; omega) (by rw [hb1]; omega)
  rw [hb1] at hj1a
  split at hbody
  · simp only [Option.bind_eq_some_iff] at hbody
    obtain ⟨⟨u3, xs3⟩, hswap3, hbody⟩ := hbody
    simp only [Option.some.injEq, Prod.mk.injEq] at hbody
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hbody
    have hp3 := swap_perm xs2 j1 a fuel xs3 hswap3 (by rw [hperm.size_eq]; omega) (by rw [hperm.size_eq]; omega)
    exact ⟨hp3.trans hperm, hj1b, by show j1.toNat + 1 ≤ b.toNat; omega⟩
  · rename_i hle
    have hle' : i1.toNat ≤ j1.toNat := by
      have h0 : ¬ (j1 < i1) := of_decide_eq_false (Bool.eq_false_iff.mpr hle)
      have h1 : ¬ (j1.toNat < i1.toNat) := fun hl => h0 (UInt32.lt_iff_toNat_lt.mpr hl)
      omega
    simp only [Option.bind_eq_some_iff] at hbody
    obtain ⟨⟨u4, xs4⟩, hswap4, ⟨xs6, i6, j6, s6⟩, hloop, ⟨u7, xs7⟩, hswap7, hbody⟩ := hbody
    simp only [Option.some.injEq, Prod.mk.injEq] at hbody
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hbody
    have hp4 := swap_perm xs2 i1 j1 fuel xs4 hswap4 (by rw [hperm.size_eq]; omega) (by rw [hperm.size_eq]; omega)
    have hi11 : (i1 + 1).toNat = i1.toNat + 1 := toNat_add_of_lt i1 1 (by rw [toNat_one']; have := UInt32.toNat_lt b; omega)
    have hj11 : (j1 - 1).toNat = j1.toNat - 1 := uint32_toNat_sub_one j1 (by rw [ha1] at hi1a; omega)
    obtain ⟨hp6, hj6a, hj6b⟩ := pt_loop3_spec fuel xs4 a (i1 + 1) (j1 - 1) true xs6 i6 j6 s6 hloop b.toNat (UInt32.toNat_lt b)
      (by rw [hp4.size_eq, hperm.size_eq]; exact hb) (by rw [hi11, ha1] at *; omega) (by rw [hi11]; omega)
      (by rw [hj11, ha1] at *; omega) (by rw [hj11]; omega)
    have hp7 := swap_perm xs6 j6 a fuel xs7 hswap7 (by rw [hp6.size_eq, hp4.size_eq, hperm.size_eq]; omega)
      (by rw [hp6.size_eq, hp4.size_eq, hperm.size_eq]; omega)
    exact ⟨hp7.trans (hp6.trans (hp4.trans hperm)), hj6a, hj6b⟩

/-! ## The range stack

Entry `k` of the stack occupies slots `3k`, `3k + 1`, `3k + 2`: a range
`[a_k, b_k)` and the packed budget and flags. The invariant carried through
the main loop says every pushed range is inside the array and, because the
loop always continues with the smaller side of a split and pushes the larger,
a range at depth `k` has length at most `n / 2^k`; pushes happen only for
ranges of thirteen or more elements, so the depth never exceeds 28 for arrays
below `2^31` elements and no stack index wraps or leaves the 144 slots. -/

def StackInv (stack : Array UInt32) (depth n : Nat) : Prop :=
  ∀ k, k < depth →
    (stack.getD (3 * k) 0).toNat ≤ (stack.getD (3 * k + 1) 0).toNat ∧
    (stack.getD (3 * k + 1) 0).toNat ≤ n ∧
    ((stack.getD (3 * k + 1) 0).toNat - (stack.getD (3 * k) 0).toNat) * 2 ^ k ≤ n

theorem getD_setIfInBounds_ne (xs : Array UInt32) (i j : Nat) (v : UInt32) (h : i ≠ j) :
    (xs.setIfInBounds i v).getD j 0 = xs.getD j 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, if_neg h]

theorem getD_setIfInBounds_self (xs : Array UInt32) (i : Nat) (v : UInt32) (hi : i < xs.size) :
    (xs.setIfInBounds i v).getD i 0 = v := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, if_pos rfl, if_pos hi, Option.getD_some]

theorem StackInv.mono {stack : Array UInt32} {depth n : Nat} (h : StackInv stack depth n) (d : Nat) (hd : d ≤ depth) :
    StackInv stack d n := fun k hk => h k (by omega)

/-- Pushing a valid range at the current depth keeps the invariant one level deeper. -/
theorem StackInv.push (stack : Array UInt32) (depth n : Nat) (pa pb pk : UInt32) (hs : stack.size = 144)
    (hd : depth ≤ 27) (hinv : StackInv stack depth n) (hab : pa.toNat ≤ pb.toNat) (hb : pb.toNat ≤ n)
    (hlen : (pb.toNat - pa.toNat) * 2 ^ depth ≤ n) :
    StackInv (((stack.setIfInBounds (3 * depth) pa).setIfInBounds (3 * depth + 1) pb).setIfInBounds (3 * depth + 2) pk)
      (depth + 1) n := by
  intro k hk
  by_cases hkd : k = depth
  · subst hkd
    rw [getD_setIfInBounds_ne _ _ _ _ (by omega), getD_setIfInBounds_ne _ _ _ _ (by omega),
      getD_setIfInBounds_self _ _ _ (by simp [hs]; omega),
      getD_setIfInBounds_ne _ _ _ _ (by omega), getD_setIfInBounds_self _ _ _ (by simp [hs]; omega)]
    exact ⟨hab, hb, hlen⟩
  · have hk' : k < depth := by omega
    rw [getD_setIfInBounds_ne _ _ _ _ (by omega), getD_setIfInBounds_ne _ _ _ _ (by omega),
      getD_setIfInBounds_ne _ _ _ _ (by omega), getD_setIfInBounds_ne _ _ _ _ (by omega),
      getD_setIfInBounds_ne _ _ _ _ (by omega), getD_setIfInBounds_ne _ _ _ _ (by omega)]
    exact hinv k hk'

theorem stack_index_toNat (depth : UInt32) (hd : depth.toNat ≤ 28) :
    (depth * 3).toNat = 3 * depth.toNat ∧ (depth * 3 + 1).toNat = 3 * depth.toNat + 1 ∧
    (depth * 3 + 2).toNat = 3 * depth.toNat + 2 := by
  have h0 : (depth * 3).toNat = 3 * depth.toNat := by
    rw [UInt32.toNat_mul, show (3 : UInt32).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega)]; omega
  refine ⟨h0, ?_, ?_⟩
  · rw [toNat_add_of_lt _ _ (by rw [h0, toNat_one']; omega), h0, toNat_one']
  · rw [toNat_add_of_lt _ _ (by rw [h0, toNat_two]; omega), h0, toNat_two]

/-- A permutation of the window `items[a:b]` written back is a permutation of `items`, and keeps its size. -/
theorem window_writeback (items short : Array UInt32) (lo hi : Nat) (h : short.Perm (items.extract lo hi)) :
    ((items.extract 0 lo ++ short) ++ items.extract (lo + short.size) items.size).Perm items :=
  writeback_perm items short lo hi h

/-! ## The main loop -/

set_option maxHeartbeats 4000000 in
theorem span_loop_perm (fuel : Nat) : ∀ (items stack : Array UInt32) (depth a b limit : UInt32)
    (balanced partitioned working : Bool) (ys stack' : Array UInt32) (d' a' b' l' : UInt32) (bl' pt' w' : Bool),
    sort_span_budget_u32.loop1 items stack depth a b limit balanced partitioned working fuel =
      some (ys, stack', d', a', b', l', bl', pt', w') →
    items.size < 2 ^ 31 → stack.size = 144 → depth.toNat ≤ 28 →
    a.toNat ≤ b.toNat → b.toNat ≤ items.size → (b.toNat - a.toNat) * 2 ^ depth.toNat ≤ items.size →
    StackInv stack depth.toNat items.size → ys.Perm items := by
  induction fuel with
  | zero =>
    intro items stack depth a b limit balanced partitioned working ys stack' d' a' b' l' bl' pt' w' h
    simp [sort_span_budget_u32.loop1] at h
  | succ fuel ih =>
    intro items stack depth a b limit balanced partitioned working ys stack' d' a' b' l' bl' pt' w' h hsmall hs hd hab hb hlen hinv
    unfold sort_span_budget_u32.loop1 at h
    cases working with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact Array.Perm.refl _
    | true =>
      simp only [↓reduceIte, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨items2, stack2, depth2, a2, b2, limit2, bal2, part2, done2⟩, hbody,
        ⟨depth3, a3, b3, limit3, bal3, part3, w3⟩, hpop, hrec⟩ := h
      simp only at hpop hrec
      have hlenNat : (b - a).toNat = b.toNat - a.toNat := toNat_sub_of_le' b a hab
      -- Step 1: the body keeps the invariant on (items2, stack2, depth2, a2, b2).
      have hbody' : items2.Perm items ∧ stack2.size = 144 ∧ depth2.toNat ≤ 28 ∧ a2.toNat ≤ b2.toNat ∧
          b2.toNat ≤ items.size ∧ (b2.toNat - a2.toNat) * 2 ^ depth2.toNat ≤ items.size ∧
          StackInv stack2 depth2.toNat items.size := by
        split at hbody
        · -- insertion sort of the window
          simp only [Option.bind_eq_some_iff] at hbody
          obtain ⟨items', ⟨⟨u, short'⟩, hins, hwb⟩, hbody⟩ := hbody
          simp only [Option.some.injEq, Prod.mk.injEq] at hwb hbody
          obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hbody
          have hshort := insertion_perm _ fuel short' hins (by rw [Array.size_extract]; omega)
          refine ⟨?_, hs, hd, hab, hb, hlen, hinv⟩
          rw [← hwb]
          exact window_writeback items short' a.toNat b.toNat hshort
        · split at hbody
          · -- heap sort of the window
            simp only [Option.bind_eq_some_iff] at hbody
            obtain ⟨⟨items4, stack4, depth4, a4, b4, limit4, bal4, part4, done4⟩,
              ⟨items', ⟨⟨u, short'⟩, hheap, hwb⟩, hmid⟩, hfin⟩ := hbody
            simp only [Option.some.injEq, Prod.mk.injEq] at hwb hmid hfin
            obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hmid
            obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hfin
            have hshort := heap_perm _ fuel short' hheap (by rw [Array.size_extract]; omega)
            refine ⟨?_, hs, hd, hab, hb, hlen, hinv⟩
            rw [← hwb]
            exact window_writeback items short' a.toNat b.toNat hshort
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
            have hp5 : items5.Perm items := by
              split at hbreak
              · simp only [Option.bind_eq_some_iff] at hbreak
                obtain ⟨⟨u, items5'⟩, hbp, hbreak⟩ := hbreak
                simp only [Option.some.injEq, Prod.mk.injEq] at hbreak
                obtain ⟨rfl, rfl⟩ := hbreak
                exact break_patterns_perm items a b fuel items5' hbp hsmall hab hb
              · simp only [Option.some.injEq, Prod.mk.injEq] at hbreak
                obtain ⟨rfl, rfl⟩ := hbreak
                exact Array.Perm.refl _
            have hsize5 : items5.size = items.size := hp5.size_eq
            -- (b) pivot selection
            obtain ⟨hitems6, hpiv_a, hpiv_b⟩ :=
              choose_pivot_spec items5 a b fuel chosen items6 hchoose (by omega) (UInt32.toNat_lt b)
            subst items6
            -- (c) optional reversal of a descending window
            have hp7 : items7.Perm items5 ∧ a.toNat ≤ pivot7.toNat ∧ pivot7.toNat < b.toNat := by
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
                exact window_writeback items5 short' a.toNat b.toNat hshort
              · simp only [Option.some.injEq, Prod.mk.injEq] at hrev
                obtain ⟨rfl, rfl, rfl⟩ := hrev
                exact ⟨Array.Perm.refl _, hpiv_a, hpiv_b⟩
            obtain ⟨hp7, hpiv7_a, hpiv7_b⟩ := hp7
            have hsize7 : items7.size = items.size := by rw [hp7.size_eq, hsize5]
            -- (d) partial insertion sort
            have hp8 : items8.Perm items7 := by
              split at hpi
              · simp only [Option.bind_eq_some_iff] at hpi
                obtain ⟨⟨r, items8'⟩, hpins, ⟨d1, h1⟩, -, hpi⟩ := hpi
                simp only [Option.some.injEq, Prod.mk.injEq] at hpi
                obtain ⟨rfl, rfl, rfl⟩ := hpi
                exact partial_insertion_perm items7 a b fuel r items8' hpins (by omega) (by omega) (by omega)
              · simp only [Option.some.injEq, Prod.mk.injEq] at hpi
                obtain ⟨rfl, rfl, rfl⟩ := hpi
                exact Array.Perm.refl _
            have hsize8 : items8.size = items.size := by rw [hp8.size_eq, hsize7]
            -- (e) the equal-elements partition
            have hp9 : items9.Perm items8 ∧ a.toNat ≤ a9.toNat ∧ a9.toNat ≤ b.toNat ∧ (handled9 = false → a9 = a) := by
              split at hpe
              · simp only [Option.bind_eq_some_iff] at hpe
                obtain ⟨⟨i', items9'⟩, hpeq, hpe⟩ := hpe
                simp only [Option.some.injEq, Prod.mk.injEq] at hpe
                obtain ⟨rfl, rfl, rfl⟩ := hpe
                obtain ⟨hperm, h1, h2⟩ :=
                  partition_equal_spec items8 a b pivot7 fuel i' items9' hpeq (by omega) (by omega) hpiv7_a hpiv7_b
                exact ⟨hperm, by omega, h2, fun hf => Bool.noConfusion hf⟩
              · simp only [Option.some.injEq, Prod.mk.injEq] at hpe
                obtain ⟨rfl, rfl, rfl⟩ := hpe
                exact ⟨Array.Perm.refl _, Nat.le_refl _, hab, fun _ => rfl⟩
            obtain ⟨hp9, ha9a, ha9b, hh9⟩ := hp9
            have hsize9 : items9.size = items.size := by rw [hp9.size_eq, hsize8]
            -- the range has at least 13 elements, so the depth is at most 27 before a push
            have hd27 : depth.toNat ≤ 27 := by
              apply Nat.le_of_not_lt
              intro hlt
              have h28 : 2 ^ 28 ≤ 2 ^ depth.toNat := Nat.pow_le_pow_right (by decide) hlt
              have h13' : 13 * 2 ^ depth.toNat ≤ (b.toNat - a.toNat) * 2 ^ depth.toNat := Nat.mul_le_mul_right _ h13
              omega
            -- (f) the partition and the push of the larger side
            have hp10 : items10.Perm items9 ∧ stack10.size = 144 ∧ depth10.toNat ≤ 28 ∧ a10.toNat ≤ b10.toNat ∧
                b10.toNat ≤ items.size ∧ (b10.toNat - a10.toNat) * 2 ^ depth10.toNat ≤ items.size ∧
                StackInv stack10 depth10.toNat items.size := by
              split at hpt
              · rename_i hnh
                rw [Bool.not_eq_true'] at hnh
                have ha9 : a9 = a := hh9 hnh
                subst a9
                simp only [Option.bind_eq_some_iff] at hpt
                obtain ⟨⟨sp, items10'⟩, hpart, ⟨na, nb, nbal, pa, pb⟩, hsides, hpt⟩ := hpt
                simp only [Option.some.injEq, Prod.mk.injEq] at hpt
                obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hpt
                obtain ⟨hperm, hmid_a, hmid_b⟩ :=
                  partition_spec items9 a b pivot7 fuel sp items10' hpart (by omega) (by omega) hpiv7_a hpiv7_b
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
                split at hsides
                · -- the left side is smaller: continue with [a, mid), push [mid + 1, b)
                  rename_i hlt
                  have hlt' : sp.mid.toNat - a.toNat < b.toNat - sp.mid.toNat := by
                    have := UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true hlt)
                    rw [hmidNat, hbmidNat] at this
                    exact this
                  simp only [Option.some.injEq, Prod.mk.injEq] at hsides
                  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hsides
                  refine ⟨hperm, hstack_size _ _ _, by rw [hd1]; omega, hmid_a, by omega, ?_, ?_⟩
                  · rw [hd1, hdouble, ← Nat.mul_assoc]
                    exact Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) hlen
                  · rw [hd1]
                    refine hpush _ _ _ (by rw [hmid1]; omega) hb ?_
                    rw [hmid1]
                    exact Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) hlen
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
                  refine ⟨hperm, hstack_size _ _ _, by rw [hd1]; omega, by rw [hmid1]; omega, hb, ?_, ?_⟩
                  · rw [hd1, hdouble, hmid1, ← Nat.mul_assoc]
                    exact Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) hlen
                  · rw [hd1]
                    exact hpush _ _ _ hmid_a (by omega) (Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) hlen)
              · simp only [Option.some.injEq, Prod.mk.injEq] at hpt
                obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hpt
                refine ⟨Array.Perm.refl _, hs, hd, ha9b, hb, ?_, hinv⟩
                exact Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) hlen
            obtain ⟨hp10, hs10, hd10, hab10, hb10, hlen10, hinv10⟩ := hp10
            exact ⟨hp10.trans (hp9.trans (hp8.trans (hp7.trans hp5))), hs10, hd10, hab10, hb10, hlen10, hinv10⟩
      obtain ⟨hp2, hs2, hd2, hab2, hb2, hlen2, hinv2⟩ := hbody'
      have hsize2 : items2.size = items.size := hp2.size_eq
      -- Step 2: the pop keeps the invariant on (depth3, a3, b3).
      have hpop' : depth3.toNat ≤ 28 ∧ a3.toNat ≤ b3.toNat ∧ b3.toNat ≤ items.size ∧
          (b3.toNat - a3.toNat) * 2 ^ depth3.toNat ≤ items.size ∧ StackInv stack2 depth3.toNat items.size := by
        split at hpop
        · split at hpop
          · simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hpop
            obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hpop
            exact ⟨hd2, hab2, hb2, hlen2, hinv2⟩
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
            rw [hi0, hi1, hd1]
            exact ⟨by omega, hk1, hk2, hk3, hinv2.mono _ (by omega)⟩
        · simp only [Option.some.injEq, Prod.mk.injEq] at hpop
          obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hpop
          exact ⟨hd2, hab2, hb2, hlen2, hinv2⟩
      obtain ⟨hd3, hab3, hb3, hlen3, hinv3⟩ := hpop'
      have hrest := ih items2 stack2 depth3 a3 b3 limit3 bal3 part3 w3 ys stack' d' a' b' l' bl' pt' w' hrec
        (by rw [hsize2]; exact hsmall) hs2 hd3 hab3 (by rw [hsize2]; exact hb3) (by rw [hsize2]; exact hlen3)
        (by rw [hsize2]; exact hinv3)
      exact hrest.trans hp2

/-! ## The permutation law for the whole sort -/

/-- `sort_span_budget_u32` returns a permutation of its input whenever it returns. -/
theorem sort_span_budget_perm (xs : Array UInt32) (limit : UInt32) (fuel : Nat) (ys : Array UInt32)
    (h : sort_span_budget_u32 xs limit fuel = some ((), ys)) (hsmall : xs.size < 2 ^ 31) : ys.Perm xs := by
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
    exact insertion_perm xs fuel zs hins (by omega)
  · simp only [Option.bind_eq_some_iff] at hbranch
    obtain ⟨⟨zs, stack', d', a', b', l', bl', pt', w'⟩, hloop, hz⟩ := hbranch
    simp only [Option.some.injEq] at hz
    subst hz
    exact span_loop_perm fuel xs (Array.replicate 144 0) 0 0 (xs.size.toUInt32) limit true true true
      zs stack' d' a' b' l' bl' pt' w' hloop hsmall (by simp) (by decide) (by rw [hn]; exact Nat.zero_le _)
      (Nat.le_of_eq hn) (by rw [hn]; simp) (fun k hk => absurd hk (Nat.not_lt_zero k))

/-- `sort_span_u32` (pdqsort with the default depth budget) returns a permutation of its input. -/
theorem sort_span_perm (xs : Array UInt32) (fuel : Nat) (ys : Array UInt32)
    (h : sort_span_u32 xs fuel = some ((), ys)) (hsmall : xs.size < 2 ^ 31) : ys.Perm xs := by
  unfold sort_span_u32 at h
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨bits, -, ⟨u, zs⟩, hbudget, hz⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hz
  subst hz
  exact sort_span_budget_perm xs bits fuel zs hbudget hsmall

/-- The public entry point `sort_u32_span` returns a permutation of its input. -/
theorem sort_u32_span_perm (xs : Array UInt32) (fuel : Nat) (ys : Array UInt32)
    (h : sort_u32_span xs fuel = some ((), ys)) (hsmall : xs.size < 2 ^ 31) : ys.Perm xs := by
  unfold sort_u32_span at h
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨u, zs⟩, hspan, hz⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hz
  subst hz
  exact sort_span_perm xs fuel zs hspan hsmall

end Oak.Stdlib.SortU32
