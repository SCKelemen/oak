import Oak.Stdlib.PdqsortWindows

set_option linter.unusedSimpArgs false

/-!
# Oak.Stdlib.PdqsortHelpers — what the pdqsort helpers leave behind

The second of three files proving that the extracted pdqsort sorts. Each
in-place helper of `sort_span_budget_u32` is a window permutation of the
range `[a, b)` it was given (`WinPerm`, from `Oak.Stdlib.PdqsortWindows`),
and the three that matter for sortedness carry a postcondition:

* `sort_partial_insertion_u32`: when it reports the range sorted, the range is
  sorted (`partial_insertion_spec`).
* `sort_partition_equal_u32`: with the pivot value `v` moved to `a`, it
  returns `i'` with every position of `[a, i')` at most `v` and every
  position of `[i', b)` above `v` (`partition_equal_post`).
* `sort_partition_u32`: it returns `mid` with `[a, mid)` at most `v`, `v` at
  `mid`, and `(mid, b)` at least `v` (`partition_post`).

The scans of both partitions keep `a + 1 ≤ i ≤ j + 1 ≤ b`, so the swap of
`i` and `j` is inside the range and the crossing point is exactly `i = j + 1`.
-/

namespace Oak.Stdlib.SortU32

/-! ## Reading conditions -/

theorem cond2_true {p q : Prop} [Decidable p] [Decidable q] (h : (decide p && decide q) = true) : p ∧ q := by
  have := (Bool.and_eq_true _ _).mp h
  exact ⟨of_decide_eq_true this.1, of_decide_eq_true this.2⟩

theorem cond2n_true {p q : Prop} [Decidable p] [Decidable q] (h : (decide p && !decide q) = true) : p ∧ ¬ q := by
  have := (Bool.and_eq_true _ _).mp h
  exact ⟨of_decide_eq_true this.1, of_decide_eq_false ((Bool.not_eq_true' _).mp this.2)⟩

theorem cond2_false {p q : Prop} [Decidable p] [Decidable q] (h : ¬ ((decide p && decide q) = true)) : ¬ p ∨ ¬ q := by
  rcases Bool.and_eq_false_iff.mp (Bool.eq_false_iff.mpr h) with h1 | h1
  · exact Or.inl (of_decide_eq_false h1)
  · exact Or.inr (of_decide_eq_false h1)

theorem cond2n_false {p q : Prop} [Decidable p] [Decidable q] (h : ¬ ((decide p && !decide q) = true)) : ¬ p ∨ q := by
  rcases Bool.and_eq_false_iff.mp (Bool.eq_false_iff.mpr h) with h1 | h1
  · exact Or.inl (of_decide_eq_false h1)
  · exact Or.inr (of_decide_eq_true ((Bool.not_eq_false' _).mp h1))

theorem condb_true {q : Prop} [Decidable q] {s : Bool} (h : (s && decide q) = true) : s = true ∧ q := by
  have := (Bool.and_eq_true _ _).mp h
  exact ⟨this.1, of_decide_eq_true this.2⟩

theorem condb_false {q : Prop} [Decidable q] {s : Bool} (h : ¬ ((s && decide q) = true)) : s = false ∨ ¬ q := by
  rcases Bool.and_eq_false_iff.mp (Bool.eq_false_iff.mpr h) with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (of_decide_eq_false h1)

theorem lt_toNat {x y : UInt32} (h : x < y) : x.toNat < y.toNat := UInt32.lt_iff_toNat_lt.mp h
theorem le_toNat {x y : UInt32} (h : x ≤ y) : x.toNat ≤ y.toNat := UInt32.le_iff_toNat_le.mp h
theorem not_lt_toNat {x y : UInt32} (h : ¬ (x < y)) : y.toNat ≤ x.toNat := by
  have : ¬ (x.toNat < y.toNat) := fun hl => h (UInt32.lt_iff_toNat_lt.mpr hl)
  omega
theorem not_le_toNat {x y : UInt32} (h : ¬ (x ≤ y)) : y.toNat < x.toNat := by
  have : ¬ (x.toNat ≤ y.toNat) := fun hl => h (UInt32.le_iff_toNat_le.mpr hl)
  omega

/-! ## The pattern breaker: a window permutation -/

theorem break_loop_win (fuel : Nat) : ∀ (xs : Array UInt32) (a length mask : UInt32) (random : UInt64)
    (middle step : UInt32) (ys : Array UInt32) (r' : UInt64) (s' : UInt32),
    sort_break_patterns_u32.loop1 xs a length mask random middle step fuel = some (ys, r', s') →
    xs.size < 2 ^ 32 → a.toNat + length.toNat ≤ xs.size → mask.toNat + 1 ≤ 2 * length.toNat →
    a.toNat + 3 ≤ middle.toNat → middle.toNat + 2 ≤ a.toNat + length.toNat →
    WinPerm a.toNat (a.toNat + length.toNat) xs ys := by
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
      obtain ⟨hwin, -⟩ := swap_win xs a.toNat (a.toNat + length.toNat) _ _ fuel xs2 hswap (by rw [hi]; omega) (by rw [hj]; omega)
        (by rw [hi]; omega) (by rw [hi]; omega) (by rw [hj]; omega) (by rw [hj]; omega)
      have hsize2 : xs2.size = xs.size := hwin.1
      have := ih xs2 a length mask _ middle (step + 1) ys r' s' h1 (by rw [hsize2]; exact hsmall)
        (by rw [hsize2]; exact hab) hmask hmid1 hmid2
      exact hwin.trans this
    · rw [if_neg hc] at h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact WinPerm.refl _ _ _

/-- The pattern breaker is a window permutation of `[a, b)`. -/
theorem break_patterns_win (xs : Array UInt32) (a b : UInt32) (fuel : Nat) (ys : Array UInt32)
    (h : sort_break_patterns_u32 xs a b fuel = some ((), ys)) (hsmall : xs.size < 2 ^ 31)
    (hab : a.toNat ≤ b.toNat) (hb : b.toNat ≤ xs.size) : WinPerm a.toNat b.toNat xs ys := by
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
    have := break_loop_win fuel xs a (b - a) _ _ _ 0 xs2 r2 s2 hloop (by omega) (by rw [hlen]; omega)
      (by rw [hlen]; exact hmask) (by rw [hmid]; omega) (by rw [hmid, hlen]; omega)
    rw [hlen] at this
    rw [show a.toNat + (b.toNat - a.toNat) = b.toNat by omega] at this
    exact this
  · simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq, true_and] at h
    rw [← h]
    exact WinPerm.refl _ _ _

/-! ## The partial insertion sort -/

/-- The forward scan extends the sorted prefix to the first disorder or the end. -/
theorem pi_loop2_spec (fuel : Nat) : ∀ (xs : Array UInt32) (a : Nat) (b i i' : UInt32),
    sort_partial_insertion_u32.loop2 xs b i fuel = some i' → a + 1 ≤ i.toNat → i.toNat ≤ b.toNat →
    SortedRange xs a i.toNat →
    i.toNat ≤ i'.toNat ∧ i'.toNat ≤ b.toNat ∧ SortedRange xs a i'.toNat ∧
      (i'.toNat < b.toNat → (xs.getD i'.toNat 0).toNat < (xs.getD (i'.toNat - 1) 0).toNat) := by
  induction fuel with
  | zero => intro xs a b i i' h; simp [sort_partial_insertion_u32.loop2] at h
  | succ fuel ih =>
    intro xs a b i i' h hai hib hsorted
    unfold sort_partial_insertion_u32.loop2 at h
    split at h
    · rename_i hc
      obtain ⟨hlt, hnlt⟩ := cond2n_true hc
      have hlt' : i.toNat < b.toNat := lt_toNat hlt
      have hge : (xs.getD (i - 1).toNat 0).toNat ≤ (xs.getD i.toNat 0).toNat := not_lt_toNat hnlt
      have hi1 : (i + 1).toNat = i.toNat + 1 := toNat_add_of_lt i 1 (by rw [toNat_one']; have := UInt32.toNat_lt b; omega)
      have him1 : (i - 1).toNat = i.toNat - 1 := uint32_toNat_sub_one i (by omega)
      rw [him1] at hge
      have hsorted' : SortedRange xs a (i.toNat + 1) := by
        intro x y hx hxy hy
        by_cases hyi : y < i.toNat
        · exact hsorted x y hx hxy hyi
        · have hyi' : y = i.toNat := by omega
          subst hyi'
          by_cases hx' : x = i.toNat - 1
          · rw [hx']; exact hge
          · exact Nat.le_trans (hsorted x (i.toNat - 1) hx (by omega) (by omega)) hge
      obtain ⟨h1, h2, h3, h4⟩ := ih xs a b (i + 1) i' h (by rw [hi1]; omega) (by rw [hi1]; omega) (by rw [hi1]; exact hsorted')
      rw [hi1] at h1
      exact ⟨by omega, h2, h3, h4⟩
    · rename_i hc
      simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      refine ⟨Nat.le_refl _, hib, hsorted, ?_⟩
      intro hlt
      rcases cond2n_false hc with h1 | h1
      · exact absurd (UInt32.lt_iff_toNat_lt.mpr hlt) h1
      · have := lt_toNat h1
        rwa [uint32_toNat_sub_one i (by omega)] at this

/-- The state of the leftward shift: positions `[a, i)` are sorted once `left`
is ignored, and the element at `left` is at most its right neighbour. -/
def ShiftInv (xs : Array UInt32) (a i left : Nat) : Prop :=
  a ≤ left ∧ left < i ∧
  (∀ x y, a ≤ x → x < y → y < i → x ≠ left → y ≠ left → (xs.getD x 0).toNat ≤ (xs.getD y 0).toNat) ∧
  (left + 1 < i → (xs.getD left 0).toNat ≤ (xs.getD (left + 1) 0).toNat)

theorem shiftinv_sorted (xs : Array UInt32) (a i left : Nat) (h : ShiftInv xs a i left)
    (hle : a < left → (xs.getD (left - 1) 0).toNat ≤ (xs.getD left 0).toNat) : SortedRange xs a i := by
  obtain ⟨hal, hli, hex, hcl⟩ := h
  intro x y hx hxy hy
  by_cases hxl : x = left
  · subst hxl
    have hc := hcl (by omega)
    by_cases hy1 : y = x + 1
    · rw [hy1]; exact hc
    · exact Nat.le_trans hc (hex (x + 1) y (by omega) (by omega) hy (by omega) (by omega))
  · by_cases hyl : y = left
    · subst hyl
      have hc := hle (by omega)
      by_cases hx1 : x = y - 1
      · rw [hx1]; exact hc
      · exact Nat.le_trans (hex x (y - 1) hx (by omega) (by omega) hxl (by omega)) hc
    · exact hex x y hx hxy hy hxl hyl

/-- The leftward shift sorts `[a, i)` and stays inside it. -/
theorem pi_loop3_spec (fuel : Nat) : ∀ (xs : Array UInt32) (a left : UInt32) (sh : Bool) (i : Nat) (ys : Array UInt32)
    (l' : UInt32) (s' : Bool),
    sort_partial_insertion_u32.loop3 xs a left sh fuel = some (ys, l', s') → i ≤ xs.size →
    (sh = true → ShiftInv xs a.toNat i left.toNat) → (sh = false → SortedRange xs a.toNat i) →
    WinPerm a.toNat i xs ys ∧ SortedRange ys a.toNat i := by
  induction fuel with
  | zero => intro xs a left sh i ys l' s' h; simp [sort_partial_insertion_u32.loop3] at h
  | succ fuel ih =>
    intro xs a left sh i ys l' s' h hi hinv hsorted
    unfold sort_partial_insertion_u32.loop3 at h
    split at h
    · rename_i hc
      obtain ⟨hsh, hgt⟩ := condb_true hc
      have hgt' : a.toNat < left.toNat := lt_toNat hgt
      obtain ⟨hal, hli, hex, hcl⟩ := hinv hsh
      have hl1 : (left - 1).toNat = left.toNat - 1 := uint32_toNat_sub_one left (by omega)
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨xs2, l2, s2⟩, h2, h1⟩ := h
      split at h2
      · rename_i hlt
        have hlt' : (xs.getD left.toNat 0).toNat < (xs.getD (left.toNat - 1) 0).toNat := by
          have := lt_toNat (of_decide_eq_true hlt); rwa [hl1] at this
        simp only [Option.bind_eq_some_iff] at h2
        obtain ⟨⟨u, xs3⟩, hswap, h2⟩ := h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl, rfl⟩ := h2
        obtain ⟨hwin, hget⟩ := swap_win xs a.toNat i left (left - 1) fuel xs3 hswap (by omega) (by rw [hl1]; omega)
          hal hli (by rw [hl1]; omega) (by rw [hl1]; omega)
        rw [hl1] at hget
        have hinv' : ShiftInv xs3 a.toNat i (left.toNat - 1) := by
          refine ⟨by omega, by omega, ?_, ?_⟩
          · intro x y hx hxy hy hxl hyl
            rw [hget x, hget y]
            by_cases hyL : y = left.toNat
            · rw [if_neg (by omega), if_pos hyL]
              rw [if_neg (by omega), if_neg (by omega)]
              exact hex x (left.toNat - 1) hx (by omega) (by omega) (by omega) (by omega)
            · rw [if_neg hyl, if_neg hyL]
              by_cases hxL : x = left.toNat
              · rw [if_neg (by omega), if_pos hxL]
                exact hex (left.toNat - 1) y (by omega) (by omega) hy (by omega) hyL
              · rw [if_neg hxl, if_neg hxL]
                exact hex x y hx hxy hy hxL hyL
          · intro _
            rw [hget (left.toNat - 1), hget (left.toNat - 1 + 1), if_pos rfl,
              if_neg (by omega), if_pos (by omega)]
            exact Nat.le_of_lt hlt'
        have := ih xs3 a (left - 1) sh i ys l' s' h1 (by rw [hwin.1]; exact hi) (fun _ => by rw [hl1]; exact hinv')
          (fun hf => by rw [hf] at hsh; cases hsh)
        exact ⟨hwin.trans this.1, this.2⟩
      · rename_i hnlt
        have hge : (xs.getD (left.toNat - 1) 0).toNat ≤ (xs.getD left.toNat 0).toNat := by
          have := not_lt_toNat (of_decide_eq_false (Bool.eq_false_iff.mpr hnlt)); rwa [hl1] at this
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl, rfl⟩ := h2
        have hsorted' : SortedRange xs a.toNat i := shiftinv_sorted xs a.toNat i left.toNat (hinv hsh) (fun _ => hge)
        exact ih xs a left false i ys l' s' h1 hi (fun hf => by cases hf) (fun _ => hsorted')
    · rename_i hc
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨WinPerm.refl _ _ _, ?_⟩
      cases sh with
      | false => exact hsorted rfl
      | true =>
        rcases condb_false hc with h1 | h1
        · cases h1
        · have hle : left.toNat ≤ a.toNat := not_lt_toNat h1
          exact shiftinv_sorted xs a.toNat i left.toNat (hinv rfl) (fun hlt => absurd hlt (by omega))

/-- The rightward shift only touches positions from `i` on. -/
theorem pi_loop4_spec (fuel : Nat) : ∀ (xs : Array UInt32) (b right : UInt32) (mv : Bool) (i : Nat) (ys : Array UInt32)
    (r' : UInt32) (m' : Bool),
    sort_partial_insertion_u32.loop4 xs b right mv fuel = some (ys, r', m') → b.toNat ≤ xs.size →
    i + 1 ≤ right.toNat → WinPerm i b.toNat xs ys := by
  induction fuel with
  | zero => intro xs b right mv i ys r' m' h; simp [sort_partial_insertion_u32.loop4] at h
  | succ fuel ih =>
    intro xs b right mv i ys r' m' h hb hright
    unfold sort_partial_insertion_u32.loop4 at h
    split at h
    · rename_i hc
      obtain ⟨hmv, hlt⟩ := condb_true hc
      have hlt' : right.toNat < b.toNat := lt_toNat hlt
      have hr1 : (right - 1).toNat = right.toNat - 1 := uint32_toNat_sub_one right (by omega)
      have hr2 : (right + 1).toNat = right.toNat + 1 := toNat_add_of_lt right 1 (by rw [toNat_one']; have := UInt32.toNat_lt b; omega)
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨xs2, r2, m2⟩, h2, h1⟩ := h
      split at h2
      · simp only [Option.bind_eq_some_iff] at h2
        obtain ⟨⟨u, xs3⟩, hswap, h2⟩ := h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl, rfl⟩ := h2
        obtain ⟨hwin, -⟩ := swap_win xs i b.toNat right (right - 1) fuel xs3 hswap (by omega) (by rw [hr1]; omega)
          (by omega) hlt' (by rw [hr1]; omega) (by rw [hr1]; omega)
        have := ih xs3 b (right + 1) mv i ys r' m' h1 (by rw [hwin.1]; exact hb) (by rw [hr2]; omega)
        exact hwin.trans this
      · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl, rfl⟩ := h2
        exact ih xs b right false i ys r' m' h1 hb hright
    · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact WinPerm.refl _ _ _

/-- A window permutation of `[i, b)` keeps a sorted `[a, i)` sorted. -/
theorem sorted_of_win_right (xs ys : Array UInt32) (a i b : Nat) (hw : WinPerm i b xs ys) (hi : i ≤ xs.size)
    (hs : SortedRange xs a i) : SortedRange ys a i := by
  intro x y hx hxy hy
  rw [hw.2.1 x (by omega) (Or.inl (by omega)), hw.2.1 y (by omega) (Or.inl hy)]
  exact hs x y hx hxy hy

theorem pi_loop1_spec (fuel : Nat) : ∀ (xs : Array UInt32) (a b i steps : UInt32) (sorted trying : Bool)
    (ys : Array UInt32) (i' st' : UInt32) (so' tr' : Bool),
    sort_partial_insertion_u32.loop1 xs a b i steps sorted trying fuel = some (ys, i', st', so', tr') →
    xs.size < 2 ^ 32 → a.toNat < b.toNat → b.toNat ≤ xs.size → a.toNat + 1 ≤ i.toNat → i.toNat ≤ b.toNat →
    SortedRange xs a.toNat i.toNat → (trying = true → sorted = false) →
    (sorted = true → SortedRange xs a.toNat b.toNat) →
    WinPerm a.toNat b.toNat xs ys ∧ (so' = true → SortedRange ys a.toNat b.toNat) := by
  induction fuel with
  | zero => intro xs a b i steps sorted trying ys i' st' so' tr' h; simp [sort_partial_insertion_u32.loop1] at h
  | succ fuel ih =>
    intro xs a b i steps sorted trying ys i' st' so' tr' h hsmall hab hb hai hib hsorted htry hso
    unfold sort_partial_insertion_u32.loop1 at h
    split at h
    · rename_i hc
      obtain ⟨htr, -⟩ := condb_true hc
      have hsf : sorted = false := htry htr
      subst hsf
      subst htr
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨i2, hi2, ⟨xs2, st2, so2, tr2⟩, hbody, hrec⟩ := h
      obtain ⟨hi2a, hi2b, hsorted2, hdis⟩ := pi_loop2_spec fuel xs a.toNat b i i2 hi2 hai hib hsorted
      split at hbody
      · -- the range is sorted
        rename_i heq
        have heq' : i2 = b := beq_iff_eq.mp heq
        subst heq'
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hbody
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hbody
        exact ih xs a i2 i2 steps true false ys i' st' so' tr' hrec hsmall hab hb (by omega) (Nat.le_refl _) hsorted2
          (fun hf => by cases hf) (fun _ => hsorted2)
      · rename_i hne
        have hne' : i2 ≠ b := fun heq => by subst heq; simp at hne
        have hlt : i2.toNat < b.toNat := by
          have : i2.toNat ≠ b.toNat := fun heq => hne' (UInt32.toNat.inj heq)
          omega
        simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at hbody
        obtain ⟨⟨xs3, st3, tr3⟩, hfix, hbody⟩ := hbody
        simp only [Option.some.injEq, Prod.mk.injEq] at hbody
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hbody
        split at hfix
        · -- give up below fifty elements
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hfix
          obtain ⟨rfl, rfl, rfl⟩ := hfix
          exact ih xs a b i2 steps false false ys i' st' so' tr' hrec hsmall hab hb (by omega) hi2b hsorted2
            (fun hf => by cases hf) (fun hf => by cases hf)
        · -- one fix-up round
          simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at hfix
          obtain ⟨⟨u, xs4⟩, hswap, xs5, hleft, xs6, hright, hfix⟩ := hfix
          simp only [Option.some.injEq, Prod.mk.injEq] at hfix
          obtain ⟨rfl, rfl, rfl⟩ := hfix
          have hi21 : (i2 - 1).toNat = i2.toNat - 1 := uint32_toNat_sub_one i2 (by omega)
          obtain ⟨hw4, hget4⟩ := swap_win xs a.toNat b.toNat i2 (i2 - 1) fuel xs4 hswap (by omega) (by rw [hi21]; omega)
            (by omega) hlt (by rw [hi21]; omega) (by rw [hi21]; omega)
          rw [hi21] at hget4
          have hsize4 : xs4.size = xs.size := hw4.1
          -- the left shift sorts [a, i2)
          have h5 : WinPerm a.toNat b.toNat xs4 xs5 ∧ SortedRange xs5 a.toNat i2.toNat := by
            split at hleft
            · rename_i hge2
              have hge2' : 2 ≤ i2.toNat - a.toNat := by
                have := le_toNat (of_decide_eq_true hge2)
                rwa [toNat_sub_of_le' i2 a (by omega), show (2 : UInt32).toNat = 2 from rfl] at this
              simp only [Option.bind_eq_some_iff] at hleft
              obtain ⟨⟨xs5', l', s'⟩, h3, hleft⟩ := hleft
              simp only [Option.some.injEq] at hleft
              subst hleft
              have hinv : ShiftInv xs4 a.toNat i2.toNat (i2 - 1).toNat := by
                rw [hi21]
                refine ⟨by omega, by omega, ?_, fun h => absurd h (by omega)⟩
                intro x y hx hxy hy hxl hyl
                rw [hget4 x, hget4 y, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
                exact hsorted2 x y hx hxy hy
              obtain ⟨hw5, hs5⟩ := pi_loop3_spec fuel xs4 a (i2 - 1) true i2.toNat xs5' l' s' h3 (by rw [hsize4]; omega)
                (fun _ => hinv) (fun hf => by cases hf)
              exact ⟨hw5.widen a.toNat b.toNat (Nat.le_refl _) (by omega), hs5⟩
            · rename_i hlt2
              have hlt2' : i2.toNat - a.toNat < 2 := by
                have := not_le_toNat (of_decide_eq_false (Bool.eq_false_iff.mpr hlt2))
                rwa [toNat_sub_of_le' i2 a (by omega), show (2 : UInt32).toNat = 2 from rfl] at this
              simp only [Option.pure_def, Option.some.injEq] at hleft
              subst hleft
              refine ⟨WinPerm.refl _ _ _, ?_⟩
              intro x y hx hxy hy
              omega
          obtain ⟨hw5, hs5⟩ := h5
          have hsize5 : xs5.size = xs.size := by rw [hw5.1, hsize4]
          -- the right shift leaves [a, i2) alone
          have h6 : WinPerm a.toNat b.toNat xs5 xs6 ∧ SortedRange xs6 a.toNat i2.toNat := by
            split at hright
            · simp only [Option.bind_eq_some_iff] at hright
              obtain ⟨⟨xs6', r', m'⟩, h4, hright⟩ := hright
              simp only [Option.some.injEq] at hright
              subst hright
              have hi2p : (i2 + 1).toNat = i2.toNat + 1 := toNat_add_of_lt i2 1 (by rw [toNat_one']; omega)
              have hw6 := pi_loop4_spec fuel xs5 b (i2 + 1) true i2.toNat xs6' r' m' h4 (by rw [hsize5]; exact hb)
                (Nat.le_of_eq hi2p.symm)
              exact ⟨hw6.widen a.toNat b.toNat (by omega) (Nat.le_refl _),
                sorted_of_win_right xs5 xs6' a.toNat i2.toNat b.toNat hw6 (by omega) hs5⟩
            · simp only [Option.pure_def, Option.some.injEq] at hright
              subst hright
              exact ⟨WinPerm.refl _ _ _, hs5⟩
          obtain ⟨hw6, hs6⟩ := h6
          have hsize6 : xs6.size = xs.size := by rw [hw6.1, hsize5]
          have := ih xs6 a b i2 (steps + 1) false true ys i' st' so' tr' hrec (by rw [hsize6]; exact hsmall) hab
            (by rw [hsize6]; exact hb) (by omega) hi2b hs6 (fun _ => rfl) (fun hf => by cases hf)
          exact ⟨hw4.trans (hw5.trans (hw6.trans this.1)), this.2⟩
    · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
      exact ⟨WinPerm.refl _ _ _, hso⟩

/-- The partial insertion sort is a window permutation, and when it reports
the range sorted, the range is sorted. -/
theorem partial_insertion_spec (xs : Array UInt32) (a b : UInt32) (fuel : Nat) (r : Bool) (ys : Array UInt32)
    (h : sort_partial_insertion_u32 xs a b fuel = some (r, ys)) (hsmall : xs.size < 2 ^ 32)
    (hab : a.toNat < b.toNat) (hb : b.toNat ≤ xs.size) :
    WinPerm a.toNat b.toNat xs ys ∧ (r = true → SortedRange ys a.toNat b.toNat) := by
  unfold sort_partial_insertion_u32 at h
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨xs2, i2, st2, so2, tr2⟩, h2, h1⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  have ha1 : (a + 1).toNat = a.toNat + 1 := toNat_add_of_lt a 1 (by rw [toNat_one']; have := UInt32.toNat_lt b; omega)
  exact pi_loop1_spec fuel xs a b (a + 1) 0 false true xs2 i2 st2 so2 tr2 h2 hsmall hab hb (Nat.le_of_eq ha1.symm)
    (by rw [ha1]; omega) (fun x y hx hxy hy => by rw [ha1] at hy; omega) (fun _ => rfl) (fun hf => by cases hf)

/-! ## The equal-elements partition -/

theorem pe_loop2_spec (fuel : Nat) : ∀ (xs : Array UInt32) (a i j i' : UInt32),
    sort_partition_equal_u32.loop2 xs a i j fuel = some i' → i.toNat ≤ j.toNat + 1 → j.toNat + 1 < 2 ^ 32 →
    (∀ x, a.toNat + 1 ≤ x → x < i.toNat → (xs.getD x 0).toNat ≤ (xs.getD a.toNat 0).toNat) →
    i.toNat ≤ i'.toNat ∧ i'.toNat ≤ j.toNat + 1 ∧
      (∀ x, a.toNat + 1 ≤ x → x < i'.toNat → (xs.getD x 0).toNat ≤ (xs.getD a.toNat 0).toNat) ∧
      (i'.toNat ≤ j.toNat → (xs.getD a.toNat 0).toNat < (xs.getD i'.toNat 0).toNat) := by
  induction fuel with
  | zero => intro xs a i j i' h; simp [sort_partition_equal_u32.loop2] at h
  | succ fuel ih =>
    intro xs a i j i' h hij hj hle
    unfold sort_partition_equal_u32.loop2 at h
    split at h
    · rename_i hc
      obtain ⟨hle', hnlt⟩ := cond2n_true hc
      have hle'' : i.toNat ≤ j.toNat := le_toNat hle'
      have hi1 : (i + 1).toNat = i.toNat + 1 := toNat_add_of_lt i 1 (by rw [toNat_one']; omega)
      obtain ⟨h1, h2, h3, h4⟩ := ih xs a (i + 1) j i' h (by rw [hi1]; omega) hj (by
        intro x hx hxi
        rw [hi1] at hxi
        by_cases hxi' : x = i.toNat
        · rw [hxi']; exact not_lt_toNat hnlt
        · exact hle x hx (by omega))
      rw [hi1] at h1
      exact ⟨by omega, h2, h3, h4⟩
    · rename_i hc
      simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      refine ⟨Nat.le_refl _, hij, hle, ?_⟩
      intro hle2
      rcases cond2n_false hc with h1 | h1
      · exact absurd (UInt32.le_iff_toNat_le.mpr hle2) h1
      · exact lt_toNat h1

theorem pe_loop3_spec (fuel : Nat) : ∀ (xs : Array UInt32) (a i j j' : UInt32),
    sort_partition_equal_u32.loop3 xs a i j fuel = some j' → i.toNat ≤ j.toNat + 1 → 1 ≤ i.toNat →
    j'.toNat ≤ j.toNat ∧ i.toNat ≤ j'.toNat + 1 ∧
      (∀ y, j'.toNat < y → y ≤ j.toNat → (xs.getD a.toNat 0).toNat < (xs.getD y 0).toNat) ∧
      (i.toNat ≤ j'.toNat → (xs.getD j'.toNat 0).toNat ≤ (xs.getD a.toNat 0).toNat) := by
  induction fuel with
  | zero => intro xs a i j j' h; simp [sort_partition_equal_u32.loop3] at h
  | succ fuel ih =>
    intro xs a i j j' h hij hi
    unfold sort_partition_equal_u32.loop3 at h
    split at h
    · rename_i hc
      obtain ⟨hle', hlt⟩ := cond2_true hc
      have hle'' : i.toNat ≤ j.toNat := le_toNat hle'
      have hj1 : (j - 1).toNat = j.toNat - 1 := uint32_toNat_sub_one j (by omega)
      obtain ⟨h1, h2, h3, h4⟩ := ih xs a i (j - 1) j' h (by rw [hj1]; omega) hi
      rw [hj1] at h1 h3
      refine ⟨by omega, h2, ?_, h4⟩
      intro y hy1 hy2
      by_cases hyj : y = j.toNat
      · rw [hyj]; exact lt_toNat hlt
      · exact h3 y hy1 (by omega)
    · rename_i hc
      simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      refine ⟨Nat.le_refl _, hij, fun y hy1 hy2 => absurd hy1 (by omega), ?_⟩
      intro hle2
      rcases cond2_false hc with h1 | h1
      · exact absurd (UInt32.le_iff_toNat_le.mpr hle2) h1
      · exact not_lt_toNat h1

theorem pe_loop1_post (fuel : Nat) : ∀ (xs : Array UInt32) (a i j : UInt32) (sc : Bool) (ys : Array UInt32)
    (i' j' : UInt32) (s' : Bool),
    sort_partition_equal_u32.loop1 xs a i j sc fuel = some (ys, i', j', s') →
    ∀ (b : Nat), b ≤ xs.size → xs.size < 2 ^ 32 → a.toNat + 1 ≤ i.toNat → i.toNat ≤ j.toNat + 1 → j.toNat + 1 ≤ b →
    (sc = false → i.toNat = j.toNat + 1) →
    (∀ x, a.toNat + 1 ≤ x → x < i.toNat → (xs.getD x 0).toNat ≤ (xs.getD a.toNat 0).toNat) →
    (∀ y, j.toNat < y → y < b → (xs.getD a.toNat 0).toNat < (xs.getD y 0).toNat) →
    WinPerm a.toNat b xs ys ∧ ys.getD a.toNat 0 = xs.getD a.toNat 0 ∧ a.toNat + 1 ≤ i'.toNat ∧ i'.toNat ≤ b ∧
      (∀ x, a.toNat + 1 ≤ x → x < i'.toNat → (ys.getD x 0).toNat ≤ (ys.getD a.toNat 0).toNat) ∧
      (∀ y, i'.toNat ≤ y → y < b → (ys.getD a.toNat 0).toNat < (ys.getD y 0).toNat) := by
  induction fuel with
  | zero => intro xs a i j sc ys i' j' s' h; simp [sort_partition_equal_u32.loop1] at h
  | succ fuel ih =>
    intro xs a i j sc ys i' j' s' h b hb hsmall hai hij hjb hsc hleft hright
    unfold sort_partition_equal_u32.loop1 at h
    cases sc with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      have hij' := hsc rfl
      refine ⟨WinPerm.refl _ _ _, rfl, hai, by omega, hleft, ?_⟩
      intro y hy1 hy2
      exact hright y (by omega) hy2
    | true =>
      simp only [↓reduceIte, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨i2, hi2, j2, hj2, ⟨xs3, i3, j3, s3⟩, hbody, hrec⟩ := h
      have hj32 : j.toNat + 1 < 2 ^ 32 := by omega
      obtain ⟨hi2a, hi2b, hle2, hstop2⟩ := pe_loop2_spec fuel xs a i j i2 hi2 hij (by omega) hleft
      obtain ⟨hj2a, hj2b, hgt3, hstop3⟩ := pe_loop3_spec fuel xs a i2 j j2 hj2 hi2b (by omega)
      have hright' : ∀ y, j2.toNat < y → y < b → (xs.getD a.toNat 0).toNat < (xs.getD y 0).toNat := by
        intro y hy1 hy2
        by_cases hyj : y ≤ j.toNat
        · exact hgt3 y hy1 hyj
        · exact hright y (by omega) hy2
      split at hbody
      · rename_i hgt
        have hgt' : j2.toNat < i2.toNat := lt_toNat (of_decide_eq_true hgt)
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hbody
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hbody
        exact ih xs a i2 j2 false ys i' j' s' hrec b hb hsmall (by omega) hj2b (by omega) (fun _ => by omega) hle2 hright'
      · rename_i hle
        have hle' : i2.toNat ≤ j2.toNat := not_lt_toNat (of_decide_eq_false (Bool.eq_false_iff.mpr hle))
        have hvi : (xs.getD a.toNat 0).toNat < (xs.getD i2.toNat 0).toNat := hstop2 (by omega)
        have hvj : (xs.getD j2.toNat 0).toNat ≤ (xs.getD a.toNat 0).toNat := hstop3 hle'
        have hne : i2.toNat < j2.toNat := by
          rcases Nat.lt_or_eq_of_le hle' with h | h
          · exact h
          · rw [h] at hvi; omega
        simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at hbody
        obtain ⟨⟨u, xs4⟩, hswap, hbody⟩ := hbody
        simp only [Option.some.injEq, Prod.mk.injEq] at hbody
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hbody
        obtain ⟨hw4, hget4⟩ := swap_win xs a.toNat b i2 j2 fuel xs4 hswap (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega)
        have hi21 : (i2 + 1).toNat = i2.toNat + 1 := toNat_add_of_lt i2 1 (by rw [toNat_one']; omega)
        have hj21 : (j2 - 1).toNat = j2.toNat - 1 := uint32_toNat_sub_one j2 (by omega)
        have hva : xs4.getD a.toNat 0 = xs.getD a.toNat 0 := by
          rw [hget4, if_neg (by omega), if_neg (by omega)]
        obtain ⟨hw, hva', h1, h2, h3, h4⟩ := ih xs4 a (i2 + 1) (j2 - 1) true ys i' j' s' hrec b (by rw [hw4.1]; exact hb)
          (by rw [hw4.1]; exact hsmall) (by rw [hi21]; omega) (by rw [hi21, hj21]; omega) (by rw [hj21]; omega) (fun hf => by cases hf)
          (by
            intro x hx hxi
            rw [hi21] at hxi
            rw [hva, hget4 x]
            by_cases hxi2 : x = i2.toNat
            · rw [if_neg (by omega), if_pos hxi2]; exact hvj
            · rw [if_neg (by omega), if_neg hxi2]; exact hle2 x hx (by omega))
          (by
            intro y hy1 hy2
            rw [hj21] at hy1
            rw [hva, hget4 y]
            by_cases hyj2 : y = j2.toNat
            · rw [if_pos hyj2]; exact hvi
            · rw [if_neg hyj2, if_neg (by omega)]; exact hright' y (by omega) hy2)
        exact ⟨hw4.trans hw, by rw [hva', hva], h1, h2, h3, h4⟩

/-- `sort_partition_equal_u32` with pivot value `v = xs[pivot]`: it returns
`i'` in `[a + 1, b]` with `[a, i')` at most `v` and `[i', b)` above `v`, as
a window permutation of `[a, b)`. -/
theorem partition_equal_post (xs : Array UInt32) (a b pivot : UInt32) (fuel : Nat) (i' : UInt32) (ys : Array UInt32)
    (h : sort_partition_equal_u32 xs a b pivot fuel = some (i', ys)) (hsmall : xs.size < 2 ^ 32)
    (hab : a.toNat < b.toNat) (hb : b.toNat ≤ xs.size) (hpa : a.toNat ≤ pivot.toNat) (hpb : pivot.toNat < b.toNat) :
    WinPerm a.toNat b.toNat xs ys ∧ a.toNat + 1 ≤ i'.toNat ∧ i'.toNat ≤ b.toNat ∧
      (∀ x, a.toNat ≤ x → x < i'.toNat → (ys.getD x 0).toNat ≤ (xs.getD pivot.toNat 0).toNat) ∧
      (∀ y, i'.toNat ≤ y → y < b.toNat → (xs.getD pivot.toNat 0).toNat < (ys.getD y 0).toNat) := by
  unfold sort_partition_equal_u32 at h
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨u, xs2⟩, hswap, ⟨xs3, i3, j3, s3⟩, hloop, h1⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  obtain ⟨hw2, hget2⟩ := swap_win xs a.toNat b.toNat a pivot fuel xs2 hswap (by omega) (by omega) (Nat.le_refl _) hab hpa hpb
  have hva : xs2.getD a.toNat 0 = xs.getD pivot.toNat 0 := by
    rw [hget2]
    by_cases hap : a.toNat = pivot.toNat
    · rw [if_pos hap, hap]
    · rw [if_neg hap, if_pos rfl]
  have ha1 : (a + 1).toNat = a.toNat + 1 := toNat_add_of_lt a 1 (by rw [toNat_one']; have := UInt32.toNat_lt b; omega)
  have hb1 : (b - 1).toNat = b.toNat - 1 := uint32_toNat_sub_one b (by omega)
  obtain ⟨hw, hva', h1, h2, h3, h4⟩ := pe_loop1_post fuel xs2 a (a + 1) (b - 1) true xs3 i3 j3 s3 hloop b.toNat
    (by rw [hw2.1]; exact hb) (by rw [hw2.1]; exact hsmall) (Nat.le_of_eq ha1.symm) (by rw [ha1, hb1]; omega) (by rw [hb1]; omega)
    (fun hf => by cases hf) (fun x hx hxi => by rw [ha1] at hxi; omega) (fun y hy1 hy2 => by rw [hb1] at hy1; omega)
  rw [hva] at hva'
  refine ⟨hw2.trans hw, h1, h2, ?_, ?_⟩
  · intro x hx hxi
    by_cases hxa : x = a.toNat
    · exact Nat.le_of_eq (congrArg UInt32.toNat (by rw [hxa, hva']))
    · rw [← hva']; exact h3 x (by omega) hxi
  · intro y hy1 hy2
    rw [← hva']; exact h4 y hy1 hy2

/-! ## The partition -/

theorem pt_loop4_eq_loop1 (fuel : Nat) : ∀ (xs : Array UInt32) (a i j : UInt32),
    sort_partition_u32.loop4 xs a i j fuel = sort_partition_u32.loop1 xs a i j fuel := by
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro xs a i j
    unfold sort_partition_u32.loop4 sort_partition_u32.loop1
    exact ite_congr rfl (fun _ => ih _ _ _ _) (fun _ => rfl)

theorem pt_loop5_eq_loop2 (fuel : Nat) : ∀ (xs : Array UInt32) (a i j : UInt32),
    sort_partition_u32.loop5 xs a i j fuel = sort_partition_u32.loop2 xs a i j fuel := by
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro xs a i j
    unfold sort_partition_u32.loop5 sort_partition_u32.loop2
    exact ite_congr rfl (fun _ => ih _ _ _ _) (fun _ => rfl)

theorem pt_loop1_spec (fuel : Nat) : ∀ (xs : Array UInt32) (a i j i' : UInt32),
    sort_partition_u32.loop1 xs a i j fuel = some i' → i.toNat ≤ j.toNat + 1 → j.toNat + 1 < 2 ^ 32 →
    (∀ x, a.toNat + 1 ≤ x → x < i.toNat → (xs.getD x 0).toNat < (xs.getD a.toNat 0).toNat) →
    i.toNat ≤ i'.toNat ∧ i'.toNat ≤ j.toNat + 1 ∧
      (∀ x, a.toNat + 1 ≤ x → x < i'.toNat → (xs.getD x 0).toNat < (xs.getD a.toNat 0).toNat) ∧
      (i'.toNat ≤ j.toNat → (xs.getD a.toNat 0).toNat ≤ (xs.getD i'.toNat 0).toNat) := by
  induction fuel with
  | zero => intro xs a i j i' h; simp [sort_partition_u32.loop1] at h
  | succ fuel ih =>
    intro xs a i j i' h hij hj hlt
    unfold sort_partition_u32.loop1 at h
    split at h
    · rename_i hc
      obtain ⟨hle', hlt'⟩ := cond2_true hc
      have hle'' : i.toNat ≤ j.toNat := le_toNat hle'
      have hi1 : (i + 1).toNat = i.toNat + 1 := toNat_add_of_lt i 1 (by rw [toNat_one']; omega)
      obtain ⟨h1, h2, h3, h4⟩ := ih xs a (i + 1) j i' h (by rw [hi1]; omega) hj (by
        intro x hx hxi
        rw [hi1] at hxi
        by_cases hxi' : x = i.toNat
        · rw [hxi']; exact lt_toNat hlt'
        · exact hlt x hx (by omega))
      rw [hi1] at h1
      exact ⟨by omega, h2, h3, h4⟩
    · rename_i hc
      simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      refine ⟨Nat.le_refl _, hij, hlt, ?_⟩
      intro hle2
      rcases cond2_false hc with h1 | h1
      · exact absurd (UInt32.le_iff_toNat_le.mpr hle2) h1
      · exact not_lt_toNat h1

theorem pt_loop2_spec (fuel : Nat) : ∀ (xs : Array UInt32) (a i j j' : UInt32),
    sort_partition_u32.loop2 xs a i j fuel = some j' → i.toNat ≤ j.toNat + 1 → 1 ≤ i.toNat →
    j'.toNat ≤ j.toNat ∧ i.toNat ≤ j'.toNat + 1 ∧
      (∀ y, j'.toNat < y → y ≤ j.toNat → (xs.getD a.toNat 0).toNat ≤ (xs.getD y 0).toNat) ∧
      (i.toNat ≤ j'.toNat → (xs.getD j'.toNat 0).toNat < (xs.getD a.toNat 0).toNat) := by
  induction fuel with
  | zero => intro xs a i j j' h; simp [sort_partition_u32.loop2] at h
  | succ fuel ih =>
    intro xs a i j j' h hij hi
    unfold sort_partition_u32.loop2 at h
    split at h
    · rename_i hc
      obtain ⟨hle', hnlt⟩ := cond2n_true hc
      have hle'' : i.toNat ≤ j.toNat := le_toNat hle'
      have hj1 : (j - 1).toNat = j.toNat - 1 := uint32_toNat_sub_one j (by omega)
      obtain ⟨h1, h2, h3, h4⟩ := ih xs a i (j - 1) j' h (by rw [hj1]; omega) hi
      rw [hj1] at h1 h3
      refine ⟨by omega, h2, ?_, h4⟩
      intro y hy1 hy2
      by_cases hyj : y = j.toNat
      · rw [hyj]; exact not_lt_toNat hnlt
      · exact h3 y hy1 (by omega)
    · rename_i hc
      simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      refine ⟨Nat.le_refl _, hij, fun y hy1 hy2 => absurd hy1 (by omega), ?_⟩
      intro hle2
      rcases cond2n_false hc with h1 | h1
      · exact absurd (UInt32.le_iff_toNat_le.mpr hle2) h1
      · exact lt_toNat h1

theorem pt_loop3_post (fuel : Nat) : ∀ (xs : Array UInt32) (a i j : UInt32) (sc : Bool) (ys : Array UInt32)
    (i' j' : UInt32) (s' : Bool),
    sort_partition_u32.loop3 xs a i j sc fuel = some (ys, i', j', s') →
    ∀ (b : Nat), b ≤ xs.size → xs.size < 2 ^ 32 → a.toNat + 1 ≤ i.toNat → i.toNat ≤ j.toNat + 1 → j.toNat + 1 ≤ b →
    (sc = false → i.toNat = j.toNat + 1) →
    (∀ x, a.toNat + 1 ≤ x → x < i.toNat → (xs.getD x 0).toNat < (xs.getD a.toNat 0).toNat) →
    (∀ y, j.toNat < y → y < b → (xs.getD a.toNat 0).toNat ≤ (xs.getD y 0).toNat) →
    WinPerm a.toNat b xs ys ∧ ys.getD a.toNat 0 = xs.getD a.toNat 0 ∧ a.toNat + 1 ≤ i'.toNat ∧
      i'.toNat = j'.toNat + 1 ∧ j'.toNat + 1 ≤ b ∧
      (∀ x, a.toNat + 1 ≤ x → x < i'.toNat → (ys.getD x 0).toNat < (ys.getD a.toNat 0).toNat) ∧
      (∀ y, j'.toNat < y → y < b → (ys.getD a.toNat 0).toNat ≤ (ys.getD y 0).toNat) := by
  induction fuel with
  | zero => intro xs a i j sc ys i' j' s' h; simp [sort_partition_u32.loop3] at h
  | succ fuel ih =>
    intro xs a i j sc ys i' j' s' h b hb hsmall hai hij hjb hsc hleft hright
    unfold sort_partition_u32.loop3 at h
    cases sc with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨WinPerm.refl _ _ _, rfl, hai, hsc rfl, hjb, hleft, hright⟩
    | true =>
      simp only [↓reduceIte, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨i2, hi2, j2, hj2, ⟨xs3, i3, j3, s3⟩, hbody, hrec⟩ := h
      rw [pt_loop4_eq_loop1] at hi2
      rw [pt_loop5_eq_loop2] at hj2
      have hj32 : j.toNat + 1 < 2 ^ 32 := by omega
      obtain ⟨hi2a, hi2b, hlt2, hstop2⟩ := pt_loop1_spec fuel xs a i j i2 hi2 hij (by omega) hleft
      obtain ⟨hj2a, hj2b, hge3, hstop3⟩ := pt_loop2_spec fuel xs a i2 j j2 hj2 hi2b (by omega)
      have hright' : ∀ y, j2.toNat < y → y < b → (xs.getD a.toNat 0).toNat ≤ (xs.getD y 0).toNat := by
        intro y hy1 hy2
        by_cases hyj : y ≤ j.toNat
        · exact hge3 y hy1 hyj
        · exact hright y (by omega) hy2
      split at hbody
      · rename_i hgt
        have hgt' : j2.toNat < i2.toNat := lt_toNat (of_decide_eq_true hgt)
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hbody
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hbody
        exact ih xs a i2 j2 false ys i' j' s' hrec b hb hsmall (by omega) hj2b (by omega) (fun _ => by omega) hlt2 hright'
      · rename_i hle
        have hle' : i2.toNat ≤ j2.toNat := not_lt_toNat (of_decide_eq_false (Bool.eq_false_iff.mpr hle))
        have hvi : (xs.getD a.toNat 0).toNat ≤ (xs.getD i2.toNat 0).toNat := hstop2 (by omega)
        have hvj : (xs.getD j2.toNat 0).toNat < (xs.getD a.toNat 0).toNat := hstop3 hle'
        have hne : i2.toNat < j2.toNat := by
          rcases Nat.lt_or_eq_of_le hle' with h | h
          · exact h
          · rw [h] at hvi; omega
        simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at hbody
        obtain ⟨⟨u, xs4⟩, hswap, hbody⟩ := hbody
        simp only [Option.some.injEq, Prod.mk.injEq] at hbody
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hbody
        obtain ⟨hw4, hget4⟩ := swap_win xs a.toNat b i2 j2 fuel xs4 hswap (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega)
        have hi21 : (i2 + 1).toNat = i2.toNat + 1 := toNat_add_of_lt i2 1 (by rw [toNat_one']; omega)
        have hj21 : (j2 - 1).toNat = j2.toNat - 1 := uint32_toNat_sub_one j2 (by omega)
        have hva : xs4.getD a.toNat 0 = xs.getD a.toNat 0 := by
          rw [hget4, if_neg (by omega), if_neg (by omega)]
        obtain ⟨hw, hva', h1, h2, h3, h4, h5⟩ := ih xs4 a (i2 + 1) (j2 - 1) true ys i' j' s' hrec b (by rw [hw4.1]; exact hb)
          (by rw [hw4.1]; exact hsmall) (by rw [hi21]; omega) (by rw [hi21, hj21]; omega) (by rw [hj21]; omega) (fun hf => by cases hf)
          (by
            intro x hx hxi
            rw [hi21] at hxi
            rw [hva, hget4 x]
            by_cases hxi2 : x = i2.toNat
            · rw [if_neg (by omega), if_pos hxi2]; exact hvj
            · rw [if_neg (by omega), if_neg hxi2]; exact hlt2 x hx (by omega))
          (by
            intro y hy1 hy2
            rw [hj21] at hy1
            rw [hva, hget4 y]
            by_cases hyj2 : y = j2.toNat
            · rw [if_pos hyj2]; exact hvi
            · rw [if_neg hyj2, if_neg (by omega)]; exact hright' y (by omega) hy2)
        exact ⟨hw4.trans hw, by rw [hva', hva], h1, h2, h3, h4, h5⟩

/-- `sort_partition_u32` with pivot value `v = xs[pivot]`: it returns `mid`
in `[a, b)` with `[a, mid)` at most `v`, `v` at `mid`, and `(mid, b)` at least
`v`, as a window permutation of `[a, b)`. -/
theorem partition_post (xs : Array UInt32) (a b pivot : UInt32) (fuel : Nat) (split : SortSplit) (ys : Array UInt32)
    (h : sort_partition_u32 xs a b pivot fuel = some (split, ys)) (hsmall : xs.size < 2 ^ 32)
    (hab : a.toNat < b.toNat) (hb : b.toNat ≤ xs.size) (hpa : a.toNat ≤ pivot.toNat) (hpb : pivot.toNat < b.toNat) :
    WinPerm a.toNat b.toNat xs ys ∧ a.toNat ≤ split.mid.toNat ∧ split.mid.toNat < b.toNat ∧
      (∀ x, a.toNat ≤ x → x < split.mid.toNat → (ys.getD x 0).toNat ≤ (xs.getD pivot.toNat 0).toNat) ∧
      ys.getD split.mid.toNat 0 = xs.getD pivot.toNat 0 ∧
      (∀ y, split.mid.toNat < y → y < b.toNat → (xs.getD pivot.toNat 0).toNat ≤ (ys.getD y 0).toNat) := by
  unfold sort_partition_u32 at h
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨u, xs2⟩, hswap, i1, hi1, j1, hj1, ⟨r2, xs5, i5, j5⟩, hbody, h1⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  obtain ⟨hw2, hget2⟩ := swap_win xs a.toNat b.toNat a pivot fuel xs2 hswap (by omega) (by omega) (Nat.le_refl _) hab hpa hpb
  have hsize2 : xs2.size = xs.size := hw2.1
  have hva : xs2.getD a.toNat 0 = xs.getD pivot.toNat 0 := by
    rw [hget2]
    by_cases hap : a.toNat = pivot.toNat
    · rw [if_pos hap, hap]
    · rw [if_neg hap, if_pos rfl]
  have ha1 : (a + 1).toNat = a.toNat + 1 := toNat_add_of_lt a 1 (by rw [toNat_one']; have := UInt32.toNat_lt b; omega)
  have hb1 : (b - 1).toNat = b.toNat - 1 := uint32_toNat_sub_one b (by omega)
  have hb32 : b.toNat < 2 ^ 32 := UInt32.toNat_lt b
  obtain ⟨hi1a, hi1b, hlt1, hstop1⟩ := pt_loop1_spec fuel xs2 a (a + 1) (b - 1) i1 hi1 (by rw [ha1, hb1]; omega)
    (by rw [hb1]; omega) (fun x hx hxi => by rw [ha1] at hxi; omega)
  rw [ha1] at hi1a
  rw [hb1] at hi1b hstop1
  obtain ⟨hj1a, hj1b, hge2, hstop2⟩ := pt_loop2_spec fuel xs2 a i1 (b - 1) j1 hj1 (by rw [hb1]; omega) (by omega)
  rw [hb1] at hj1a hge2
  split at hbody
  · -- already partitioned: the scans crossed at once
    rename_i hgt
    have hgt' : j1.toNat < i1.toNat := lt_toNat (of_decide_eq_true hgt)
    simp only [Option.bind_eq_some_iff] at hbody
    obtain ⟨⟨u3, xs3⟩, hswap3, hbody⟩ := hbody
    simp only [Option.some.injEq, Prod.mk.injEq] at hbody
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hbody
    dsimp only
    have hja : a.toNat ≤ j1.toNat := by omega
    obtain ⟨hw3, hget3⟩ := swap_win xs2 a.toNat b.toNat j1 a fuel xs3 hswap3 (by omega) (by omega) hja (by omega)
      (Nat.le_refl _) hab
    refine ⟨hw2.trans hw3, hja, by omega, ?_, ?_, ?_⟩
    · intro x hx hxm
      rw [hget3 x]
      by_cases hxa : x = a.toNat
      · rw [if_pos hxa, ← hva]
        exact Nat.le_of_lt (hlt1 j1.toNat (by omega) (by omega))
      · rw [if_neg hxa, if_neg (by omega), ← hva]
        exact Nat.le_of_lt (hlt1 x (by omega) (by omega))
    · rw [hget3, ← hva]
      by_cases hja' : j1.toNat = a.toNat
      · rw [if_pos hja', hja']
      · rw [if_neg hja', if_pos rfl]
    · intro y hy1 hy2
      rw [hget3 y, if_neg (by omega), if_neg (by omega), ← hva]
      exact hge2 y hy1 (by omega)
  · -- swap the crossing pair and keep scanning
    rename_i hle
    have hle' : i1.toNat ≤ j1.toNat := not_lt_toNat (of_decide_eq_false (Bool.eq_false_iff.mpr hle))
    have hvi : (xs2.getD a.toNat 0).toNat ≤ (xs2.getD i1.toNat 0).toNat := hstop1 (by omega)
    have hvj : (xs2.getD j1.toNat 0).toNat < (xs2.getD a.toNat 0).toNat := hstop2 hle'
    have hne : i1.toNat < j1.toNat := by
      rcases Nat.lt_or_eq_of_le hle' with h | h
      · exact h
      · rw [h] at hvi; omega
    simp only [Option.bind_eq_some_iff] at hbody
    obtain ⟨⟨u4, xs4⟩, hswap4, ⟨xs6, i6, j6, s6⟩, hloop, ⟨u7, xs7⟩, hswap7, hbody⟩ := hbody
    simp only [Option.some.injEq, Prod.mk.injEq] at hbody
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hbody
    dsimp only
    obtain ⟨hw4, hget4⟩ := swap_win xs2 a.toNat b.toNat i1 j1 fuel xs4 hswap4 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
    have hi11 : (i1 + 1).toNat = i1.toNat + 1 := toNat_add_of_lt i1 1 (by rw [toNat_one']; omega)
    have hj11 : (j1 - 1).toNat = j1.toNat - 1 := uint32_toNat_sub_one j1 (by omega)
    have hva4 : xs4.getD a.toNat 0 = xs2.getD a.toNat 0 := by
      rw [hget4, if_neg (by omega), if_neg (by omega)]
    obtain ⟨hw6, hva6, h1, h2, h3, h4, h5⟩ := pt_loop3_post fuel xs4 a (i1 + 1) (j1 - 1) true xs6 i6 j6 s6 hloop b.toNat
      (by rw [hw4.1, hsize2]; exact hb) (by rw [hw4.1, hsize2]; exact hsmall) (by rw [hi11]; omega) (by rw [hi11, hj11]; omega) (by rw [hj11]; omega)
      (fun hf => by cases hf)
      (by
        intro x hx hxi
        rw [hi11] at hxi
        rw [hva4, hget4 x]
        by_cases hxi1 : x = i1.toNat
        · rw [if_neg (by omega), if_pos hxi1]; exact hvj
        · rw [if_neg (by omega), if_neg hxi1]; exact hlt1 x hx (by omega))
      (by
        intro y hy1 hy2
        rw [hj11] at hy1
        rw [hva4, hget4 y]
        by_cases hyj1 : y = j1.toNat
        · rw [if_pos hyj1]; exact hvi
        · rw [if_neg hyj1, if_neg (by omega)]; exact hge2 y (by omega) (by omega))
    rw [hva4] at hva6
    have hja : a.toNat ≤ j6.toNat := by omega
    have hsize6 : xs6.size = xs.size := by rw [hw6.1, hw4.1, hsize2]
    obtain ⟨hw7, hget7⟩ := swap_win xs6 a.toNat b.toNat j6 a fuel xs7 hswap7 (by omega) (by omega) hja (by omega)
      (Nat.le_refl _) hab
    refine ⟨hw2.trans (hw4.trans (hw6.trans hw7)), hja, by omega, ?_, ?_, ?_⟩
    · intro x hx hxm
      rw [hget7 x]
      by_cases hxa : x = a.toNat
      · rw [if_pos hxa, ← hva, ← hva6]
        exact Nat.le_of_lt (h4 j6.toNat (by omega) (by omega))
      · rw [if_neg hxa, if_neg (by omega), ← hva, ← hva6]
        exact Nat.le_of_lt (h4 x (by omega) (by omega))
    · rw [hget7, ← hva, ← hva6]
      by_cases hja' : j6.toNat = a.toNat
      · rw [if_pos hja', hja']
      · rw [if_neg hja', if_pos rfl]
    · intro y hy1 hy2
      rw [hget7 y, if_neg (by omega), if_neg (by omega), ← hva, ← hva6]
      exact h5 y hy1 hy2

end Oak.Stdlib.SortU32
