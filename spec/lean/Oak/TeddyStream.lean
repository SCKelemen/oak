import Oak.Teddy
/-!
# Teddy: streaming

`stdlib/literals.oak` `feed` scans one chunk at a time. Its contract: the
feed of a chunk counts the occurrences that *end* in it — an occurrence at
position `p` of length `ℓ` ends in the chunk `[lo, hi)` when
`lo < p + ℓ ≤ hi` — so the feeds over the chunks of an input sum to the
occurrences of the whole. This file proves that partition statement, and
the fact that lets the kernel find every occurrence ending in a chunk from
a bounded carry: an occurrence ending in the chunk starts within the last
`longest - 1` bytes before it, so the carry of that many bytes plus the
chunk holds all of it.
-/

namespace Oak.Teddy.Stream

open Oak.Teddy
open Classical

noncomputable section

variable {L : Nat}

/-- An occurrence of literal `i` at `p` in the whole input, counted once the
input has at least `p + ℓ` bytes. -/
def occ (s : LitSet L) (t : List UInt8) (i : Fin L) (p : Nat) : Prop :=
  occursAt (s.lit i) t p ∧ p + (s.lit i).length ≤ t.length

/-- The occurrences ending in `[lo, hi)`. -/
def endsIn (s : LitSet L) (t : List UInt8) (lo hi : Nat) (i : Fin L) (p : Nat) : Prop :=
  occ s t i p ∧ lo < p + (s.lit i).length ∧ p + (s.lit i).length ≤ hi

/-- The number of occurrences ending in `[lo, hi)`, over positions below `n`. -/
def countEndsIn (s : LitSet L) (t : List UInt8) (n lo hi : Nat) : Nat :=
  ((List.range n).map fun p => ((List.finRange L).filter fun i => decide (endsIn s t lo hi i p)).length).sum

theorem sum_map_add {α : Type} (f g : α → Nat) : ∀ l : List α,
    (l.map f).sum + (l.map g).sum = (l.map fun x => f x + g x).sum
  | [] => rfl
  | x :: l => by
    simp only [List.map_cons, List.sum_cons]
    have := sum_map_add f g l
    omega

/-- At one position, the literals ending in `[lo, mid)` and those ending in
`[mid, hi)` together are those ending in `[lo, hi)`. -/
theorem filter_split (s : LitSet L) (t : List UInt8) (lo mid hi : Nat) (h1 : lo ≤ mid) (h2 : mid ≤ hi)
    (p : Nat) : ∀ l : List (Fin L),
    (l.filter fun i => decide (endsIn s t lo mid i p)).length
      + (l.filter fun i => decide (endsIn s t mid hi i p)).length
      = (l.filter fun i => decide (endsIn s t lo hi i p)).length
  | [] => rfl
  | i :: l => by
    have ih := filter_split s t lo mid hi h1 h2 p l
    simp only [List.filter_cons]
    by_cases a : endsIn s t lo mid i p
    · have c : endsIn s t lo hi i p := ⟨a.1, a.2.1, Nat.le_trans a.2.2 h2⟩
      have b : ¬ endsIn s t mid hi i p := fun b => absurd (Nat.lt_of_lt_of_le b.2.1 a.2.2) (Nat.lt_irrefl _)
      simp only [a, b, c, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega
    · by_cases b : endsIn s t mid hi i p
      · have c : endsIn s t lo hi i p := ⟨b.1, Nat.lt_of_le_of_lt h1 b.2.1, b.2.2⟩
        simp only [a, b, c, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte, List.length_cons]
        omega
      · have c : ¬ endsIn s t lo hi i p := by
          intro c
          by_cases hm : p + (s.lit i).length ≤ mid
          · exact a ⟨c.1, c.2.1, hm⟩
          · exact b ⟨c.1, Nat.lt_of_not_le hm, c.2.2⟩
        simp only [a, b, c, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact ih

/-- **Partition**: the feeds of two adjacent chunks count what one feed of
their union counts, so the feeds over the chunks of an input sum to the
occurrences of the whole. -/
theorem countEndsIn_split (s : LitSet L) (t : List UInt8) (n lo mid hi : Nat)
    (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    countEndsIn s t n lo mid + countEndsIn s t n mid hi = countEndsIn s t n lo hi := by
  unfold countEndsIn
  rw [sum_map_add]
  congr 1
  apply List.map_congr_left
  intro p _
  exact filter_split s t lo mid hi h1 h2 p (List.finRange L)

/-- Every occurrence ends in `[0, n)` when `n` is the input's length, so
one chunk holding the whole input is `count`'s notion of occurrence. -/
theorem endsIn_whole (s : LitSet L) (t : List UInt8) (i : Fin L) (p : Nat) :
    endsIn s t 0 t.length i p ↔ occ s t i p := by
  constructor
  · intro h; exact h.1
  · intro h
    have l := s.long i
    exact ⟨h, by omega, h.2⟩

/-- **The carry suffices**: an occurrence ending in the chunk that starts at
`lo` begins within `longest - 1` bytes before `lo`, where `longest` bounds
every literal's length — so the carry of the last `longest - 1` bytes of
the previous chunks, joined with the chunk, contains it whole. -/
theorem start_in_carry (s : LitSet L) (t : List UInt8) (lo hi longest : Nat) (i : Fin L) (p : Nat)
    (hl : (s.lit i).length ≤ longest) (h : endsIn s t lo hi i p) :
    lo ≤ p + (longest - 1) := by
  have := h.2.1
  omega

end

end Oak.Teddy.Stream
