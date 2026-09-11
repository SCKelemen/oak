import Oak.Stdlib.RandomExtracted

/-!
# Oak.Stdlib.RandomLaws — laws of the extracted `random` package

`random_next` is xoshiro256** exactly as published (Blackman and Vigna):
`refNext` below is that step written out, and `random_next_spec` says the
extracted function computes it on a one-element state array. `random_below`
never returns a value at or above its bound, and `random_range` stays inside
its inclusive range; both are properties of the extracted code, with no
assumption about the loop's fuel beyond the success of the call.
-/

namespace Oak.Stdlib.Random

theorem two_pow_64_eq : (2 : Nat) ^ 64 = 18446744073709551616 := by decide

/-- Rotate left by `k` bits; the two shift counts are the literal values the
Oak source spells (`7`/`57` and `45`/`19`). -/
def rotlRef (x : UInt64) (k : UInt64) (k' : UInt64) : UInt64 := (x <<< k) ||| (x >>> k')

/-- The reference xoshiro256** step. -/
def refNext (s : Xoshiro) : UInt64 × Xoshiro :=
  let result := rotlRef (s.s1 * 5) 7 57 * 9
  let t := s.s1 <<< 17
  let s2 := s.s2 ^^^ s.s0
  let s3 := s.s3 ^^^ s.s1
  let s1 := s.s1 ^^^ s2
  let s0 := s.s0 ^^^ s3
  let s2 := s2 ^^^ t
  let s3 := rotlRef s3 45 19
  (result, { s0 := s0, s1 := s1, s2 := s2, s3 := s3 })

/-- The extracted `random_next` is the reference step on the single state
cell, writing the successor state back. -/
theorem random_next_spec (state : Array Xoshiro) (fuel : Nat) (hs : state.size = 1) :
    random_next state fuel = some ((refNext (state.getD 0 default)).1,
      state.setIfInBounds 0 (refNext (state.getD 0 default)).2) := by
  unfold random_next rotl64 refNext rotlRef
  have h1 : (state.size.toUInt32 == (1 : UInt32)) = true := by
    rw [hs]; decide
  simp only [h1, ↓reduceIte, Option.pure_def]
  have h7 : (7 : UInt32).toUInt64 = 7 := by decide
  have h57 : ((64 : UInt32) - 7).toUInt64 = 57 := by decide
  have h45 : (45 : UInt32).toUInt64 = 45 := by decide
  have h19 : ((64 : UInt32) - 45).toUInt64 = 19 := by decide
  simp only [h7, h57, h45, h19]
  rfl

/-- `random_below` never returns a value at or above a non-zero bound: the
result is a remainder modulo the bound, or zero for bound one. -/
theorem random_below_lt (state : Array Xoshiro) (bound : UInt64) (fuel : Nat) (r : UInt64)
    (state' : Array Xoshiro) (hb : bound ≠ 0)
    (h : random_below state bound fuel = some (r, state')) : r < bound := by
  have hbpos : 0 < bound.toNat := by
    rcases Nat.eq_zero_or_pos bound.toNat with hz | hpos
    · exact absurd (UInt64.toNat.inj (by simpa using hz)) hb
    · exact hpos
  unfold random_below at h
  by_cases hle : bound ≤ 1
  · have hb1 : bound = 1 := by
      apply UInt64.toNat.inj
      have := UInt64.le_iff_toNat_le.mp hle
      simp at this ⊢; omega
    subst hb1
    simp at h
    rw [← h.1]; decide
  · simp [hle] at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨⟨r1, st1⟩, h1, h2⟩ := h
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, _⟩ := h2
    rw [Option.bind_eq_some_iff] at h1
    obtain ⟨⟨x, stx⟩, _, h1⟩ := h1
    rw [Option.bind_eq_some_iff] at h1
    obtain ⟨⟨sty, draw⟩, _, h1⟩ := h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h1, _⟩ := h1
    subst h1
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_mod]
    exact Nat.mod_lt _ hbpos

theorem uint64_max_toNat : (18446744073709551615 : UInt64).toNat = 18446744073709551615 := by decide

/-- `random_range` stays inside `[low, high]`. -/
theorem random_range_mem (state : Array Xoshiro) (low high : UInt64) (fuel : Nat) (r : UInt64)
    (state' : Array Xoshiro) (h : random_range state low high fuel = some (r, state')) :
    low ≤ r ∧ r ≤ high := by
  unfold random_range at h
  by_cases hlh : low ≤ high
  · simp [hlh] at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨⟨r1, st1⟩, h1, h2⟩ := h
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, _⟩ := h2
    have hlow64 := UInt64.toNat_lt low
    have hhigh64 := UInt64.toNat_lt high
    have hle := UInt64.le_iff_toNat_le.mp hlh
    have hsub : (high - low).toNat = high.toNat - low.toNat := by
      rw [UInt64.toNat_sub]; rw [two_pow_64_eq] at *; omega
    split at h1
    · rename_i hfull
      have hfull' := congrArg UInt64.toNat hfull
      rw [hsub, uint64_max_toNat] at hfull'
      have hlow : low.toNat = 0 := by rw [two_pow_64_eq] at hhigh64; omega
      have hhigh : high.toNat = 18446744073709551615 := by rw [two_pow_64_eq] at hhigh64; omega
      constructor
      · rw [UInt64.le_iff_toNat_le, hlow]; exact Nat.zero_le _
      · rw [UInt64.le_iff_toNat_le, hhigh]
        have := UInt64.toNat_lt r1
        rw [two_pow_64_eq] at this; omega
    · rename_i hfull
      rw [Option.bind_eq_some_iff] at h1
      obtain ⟨⟨r3, st3⟩, hb, h1⟩ := h1
      simp only [Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨h1, _⟩ := h1
      subst h1
      have hsucc : ((high - low) + 1).toNat = high.toNat - low.toNat + 1 := by
        rw [UInt64.toNat_add, hsub, show (1 : UInt64).toNat = 1 by decide]
        apply Nat.mod_eq_of_lt
        have hne : high.toNat - low.toNat ≠ 18446744073709551615 := by
          intro hc; apply hfull; apply UInt64.toNat.inj; rw [hsub, uint64_max_toNat, hc]
        rw [two_pow_64_eq] at *; omega
      have hne0 : (high - low) + 1 ≠ 0 := by
        intro hz
        have := congrArg UInt64.toNat hz
        rw [hsucc, show (0 : UInt64).toNat = 0 by decide] at this
        omega
      have hlt := UInt64.lt_iff_toNat_lt.mp (random_below_lt state _ fuel r3 st3 hne0 hb)
      rw [hsucc] at hlt
      have hadd : (low + r3).toNat = low.toNat + r3.toNat := by
        rw [UInt64.toNat_add]; apply Nat.mod_eq_of_lt; omega
      constructor
      · rw [UInt64.le_iff_toNat_le, hadd]; omega
      · rw [UInt64.le_iff_toNat_le, hadd]; omega
  · simp [hlh] at h

end Oak.Stdlib.Random
