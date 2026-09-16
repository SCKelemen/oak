import Oak.AlignmentFact

/-!
# Compiler correspondence for alignment facts

This module models the numeric alignment-fact decisions used by the checker.
The production representation uses `0` for the absent fact (`align 1`), while
the proposition in `Oak.AlignmentFact` uses the semantic divisor directly.
Declared and derived nonzero facts are powers of two, so numeric comparison is
the same order as divisibility.

The scope is deliberately narrow: this file refines normalization, flow, and
the weakest-fact join *after* the checker has established that the surrounding
view/span shapes are identical.  It does not model or refine
`sameAlignmentShape`, `latticeAtomIdentical`, function-type variance, or whole
type assignability.
-/

namespace Oak.AlignmentFactRefinement

open Oak.AlignmentFact

/-- Interpret the production `0` sentinel as the proposition `align 1`. -/
def semantic (raw : Nat) : Nat :=
  if raw = 0 then 1 else raw

/-- Canonical production facts are absent (`0`) or powers of two above one. -/
def Valid (raw : Nat) : Prop :=
  raw = 0 ∨ ∃ exponent : Nat, 0 < exponent ∧ raw = 2 ^ exponent

/-- Parser/derivation input before `align 1` is canonicalized to `0`. -/
def InputValid (raw : Nat) : Prop :=
  raw = 0 ∨ ∃ exponent : Nat, raw = 2 ^ exponent

/-- Transliteration of `alignmentFact`: `0` and `1` both mean no fact. -/
def normalize (raw : Nat) : Nat :=
  if raw ≤ 1 then 0 else raw

/-- Transliteration of the alignment component of assignability.

The argument order is `(value, target)`: a stronger value fact flows to a
weaker target fact. -/
def flows (value target : Nat) : Bool :=
  target == 0 || decide (target ≤ value)

/-- Transliteration of the binary step in `weakestAlignment`: choose the
weaker numeric fact. -/
def join (left right : Nat) : Nat :=
  Nat.min left right

@[simp] theorem semantic_zero : semantic 0 = 1 := by
  simp [semantic]

theorem semantic_of_ne_zero {raw : Nat} (h : raw ≠ 0) : semantic raw = raw := by
  simp [semantic, h]

theorem normalize_of_le_one {raw : Nat} (h : raw ≤ 1) : normalize raw = 0 := by
  simp [normalize, h]

theorem normalize_of_one_lt {raw : Nat} (h : 1 < raw) : normalize raw = raw := by
  simp [normalize, Nat.not_le.mpr h]

/-- Normalization preserves the intended divisor, treating both `0` and `1`
as the trivial alignment proposition. -/
theorem semantic_normalize (raw : Nat) :
    semantic (normalize raw) = if raw ≤ 1 then 1 else raw := by
  by_cases h : raw ≤ 1
  · simp [normalize, semantic, h]
  · have hzero : raw ≠ 0 := by omega
    simp [normalize, semantic, h, hzero]

/-- Every parser/derivation fact becomes a canonical production fact. -/
theorem normalize_valid {raw : Nat} (h : InputValid raw) : Valid (normalize raw) := by
  rcases h with rfl | ⟨exponent, rfl⟩
  · simp [normalize, Valid]
  · cases exponent with
    | zero => simp [normalize, Valid]
    | succ exponent =>
      right
      refine ⟨exponent + 1, by omega, ?_⟩
      rw [normalize_of_one_lt (Nat.one_lt_two_pow (by omega))]

@[simp] theorem flows_iff {value target : Nat} :
    flows value target = true ↔ target = 0 ∨ target ≤ value := by
  simp [flows]

/-- A canonical raw fact always denotes a power of two, with the absent fact
at exponent zero. -/
theorem valid_semantic_pow {raw : Nat} (h : Valid raw) :
    ∃ exponent : Nat, semantic raw = 2 ^ exponent := by
  rcases h with rfl | ⟨exponent, _, rfl⟩
  · exact ⟨0, by simp⟩
  · exact ⟨exponent, by simp [semantic]⟩

/-- On canonical power-of-two facts, the checker's numeric flow order is
exactly semantic divisibility. -/
theorem flows_iff_dvd {value target : Nat} (hv : Valid value) (ht : Valid target) :
    flows value target = true ↔ semantic target ∣ semantic value := by
  rcases ht with rfl | ⟨targetExponent, htargetPositive, rfl⟩
  · simp [flows, semantic]
  · have htargetNonzero : 2 ^ targetExponent ≠ 0 :=
      Nat.ne_of_gt (Nat.two_pow_pos targetExponent)
    rcases hv with rfl | ⟨valueExponent, hvaluePositive, rfl⟩
    · rw [flows_iff]
      simp only [htargetNonzero, false_or, semantic_zero,
        semantic_of_ne_zero htargetNonzero]
      constructor
      · intro hle
        have hpositive := Nat.two_pow_pos targetExponent
        omega
      · intro hdvd
        have hle : 2 ^ targetExponent ≤ 1 := Nat.le_of_dvd (by decide) hdvd
        have hone : 1 < 2 ^ targetExponent := Nat.one_lt_two_pow (by omega)
        omega
    · have hvalueNonzero : 2 ^ valueExponent ≠ 0 :=
        Nat.ne_of_gt (Nat.two_pow_pos valueExponent)
      rw [flows_iff]
      simp only [htargetNonzero, false_or,
        semantic_of_ne_zero htargetNonzero,
        semantic_of_ne_zero hvalueNonzero]
      rw [Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)]
      rw [Nat.pow_le_pow_iff_right (by decide : 1 < 2)]

/-- Every accepted flow is a sound weakening of the alignment proposition. -/
theorem flows_sound {value target base : Nat}
    (hv : Valid value) (ht : Valid target)
    (hflow : flows value target = true)
    (hbase : holds (semantic value) base) :
    holds (semantic target) base := by
  exact weaken hbase ((flows_iff_dvd hv ht).mp hflow)

theorem join_valid {left right : Nat} (hl : Valid left) (hr : Valid right) :
    Valid (join left right) := by
  rcases Nat.le_total left right with h | h
  · simpa [join, Nat.min_eq_left h] using hl
  · simpa [join, Nat.min_eq_right h] using hr

/-- Each operand flows to the weaker fact chosen by the join. -/
theorem left_flows_join (left right : Nat) : flows left (join left right) = true := by
  simp [flows, join, Nat.min_le_left]

theorem right_flows_join (left right : Nat) : flows right (join left right) = true := by
  simp [flows, join, Nat.min_le_right]

/-- The chosen fact is the strongest common weakening: every other target
accepted from both operands is also accepted from their join. -/
theorem join_least_common_weakening {left right target : Nat}
    (hl : flows left target = true) (hr : flows right target = true) :
    flows (join left right) target = true := by
  by_cases hzero : target = 0
  · subst target
    simp [flows]
  rw [flows_iff] at hl hr ⊢
  exact Or.inr ((Nat.le_min).2 ⟨hl.resolve_left hzero, hr.resolve_left hzero⟩)

/-- At the proposition level, a base from either arm carries the selected
weakest alignment fact. -/
theorem join_sound {left right base : Nat}
    (hl : Valid left) (hr : Valid right)
    (hbase : holds (semantic left) base ∨ holds (semantic right) base) :
    holds (semantic (join left right)) base := by
  have hj := join_valid hl hr
  apply Oak.AlignmentFact.join hbase
  · exact (flows_iff_dvd hl hj).mp (left_flows_join left right)
  · exact (flows_iff_dvd hr hj).mp (right_flows_join left right)

theorem join_comm (left right : Nat) : join left right = join right left := by
  simp [join, Nat.min_comm]

theorem join_assoc (a b c : Nat) : join (join a b) c = join a (join b c) := by
  simp [join, Nat.min_assoc]

@[simp] theorem join_idem (fact : Nat) : join fact fact = fact := by
  simp [join]

/-! ## Executable production-pin examples -/

example : normalize 0 = 0 := by decide
example : normalize 1 = 0 := by decide
example : normalize 2 = 2 := by decide
example : normalize 64 = 64 := by decide
example : normalize 4096 = 4096 := by decide

example : flows 0 0 = true := by decide
example : flows 4096 64 = true := by decide
example : flows 64 4096 = false := by decide
example : flows 64 0 = true := by decide
example : flows 0 64 = false := by decide
example : flows 64 64 = true := by decide

example : join 4096 64 = 64 := by decide
example : join 64 4096 = 64 := by decide
example : join 64 64 = 64 := by decide
example : join 4096 0 = 0 := by decide
example : join 0 64 = 0 := by decide
example : join (join 4096 64) 2 = join 4096 (join 64 2) := by decide

end Oak.AlignmentFactRefinement
