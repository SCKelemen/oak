/-!
# Alignment facts on views and spans

`docs/spec/50-borrowing.md` §2a: a span type may carry an alignment fact,
`[* align N]T`, meaning the base address is a multiple of `N`. The fact is
a proposition about the base, not a representation; this module states
the arithmetic the checker relies on when it derives, weakens, and carries
the fact, so each rule of §2a is one lemma here.

- `weaken`: a fact `n` implies every fact `m` dividing `n` — the direction
  of assignability (`[* align 4096]u8` stands where `[* align 64]u8` or
  `[*]u8` is required, never the reverse).
- `trivial`: `align 1` holds of every base — a declared `align 1` is the
  plain type, as a derived one is (`alignmentFact`).
- `subslice`: a start that is a multiple of `n` keeps the fact — the
  literal-multiple rule of `subslice`; `subslice_elements` is the same
  rule in elements of size `s`, which the checker approximates by
  requiring the element index itself to be a multiple of `n`
  (`subslice_index`).
- `first_field`: the field at offset zero of a record aligned to `n`
  carries `n`; `join`: a value from either of two arms satisfies the
  weaker of their facts, which is why a match or ternary joins to the
  weakest fact rather than the first arm's.
-/

namespace Oak.AlignmentFact

/-- A base address carries fact `n` when `n` divides it. -/
def holds (n base : Nat) : Prop := n ∣ base

theorem weaken {n m base : Nat} (h : holds n base) (hm : m ∣ n) : holds m base :=
  Nat.dvd_trans hm h

theorem trivial (base : Nat) : holds 1 base := Nat.one_dvd base

theorem subslice {n base k : Nat} (h : holds n base) : holds n (base + k * n) :=
  Nat.dvd_add h (Nat.dvd_mul_left n k)

/-- Elements of size `s` starting at index `i`: the byte offset is `i * s`. -/
theorem subslice_elements {n base i s : Nat} (h : holds n base) (hi : n ∣ i * s) :
    holds n (base + i * s) :=
  Nat.dvd_add h hi

/-- The checker's rule: an element index that is itself a multiple of `n`
keeps the fact for any element size. Conservative when `s > 1`. -/
theorem subslice_index {n base i s : Nat} (h : holds n base) (hi : n ∣ i) :
    holds n (base + i * s) :=
  subslice_elements h (Nat.dvd_trans hi (Nat.dvd_mul_right i s))

theorem first_field {n base : Nat} (h : holds n base) : holds n (base + 0) := by
  simpa using h

/-- Either arm's value satisfies the weaker fact: with `m ∣ n₁` and `m ∣ n₂`,
a base carrying `n₁` or `n₂` carries `m`. -/
theorem join {n₁ n₂ m base : Nat} (h : holds n₁ base ∨ holds n₂ base)
    (h₁ : m ∣ n₁) (h₂ : m ∣ n₂) : holds m base := by
  rcases h with h | h
  · exact weaken h h₁
  · exact weaken h h₂

/-- A packed record gives no fact from the element: the field after a
one-byte field sits at offset one, which no `n > 1` divides. -/
theorem packed_offset_one (n : Nat) (hn : 1 < n) : ¬ holds n 1 := by
  intro h
  have := Nat.le_of_dvd (by decide) h
  omega

end Oak.AlignmentFact
