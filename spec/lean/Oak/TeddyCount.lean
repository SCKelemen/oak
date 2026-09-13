import Oak.Teddy
/-!
# Teddy: the stepping and the tail

`Oak.Teddy.exact` says verifying a literal only where its bucket is a
candidate finds exactly its occurrences at one position. The kernel
(`stdlib/literals.oak` `count`) sums that over sixty-four-byte steps of
four sixteen-byte blocks and then over the remaining positions one by one.
This file proves the sum is the number of occurrences over every position:
per block, the verified count is the occurrence count at each of its
sixteen positions; the steps cover the first `64 k` positions and the tail
the rest, so the kernel's total is the total over `[0, n)` for any number
of steps `k` with `64 k ≤ n` — in particular for the guard's choice.
-/

namespace Oak.Teddy.Count

open Oak.Teddy
open Classical

noncomputable section

variable {L : Nat}

/-- The literals occurring at `p`. -/
def occAt (s : LitSet L) (t : List UInt8) (p : Nat) : Nat :=
  ((List.finRange L).filter fun i => decide (occursAt (s.lit i) t p)).length

/-- What the kernel counts at `p`: the literals whose bucket is a candidate
there and which occur there. -/
def verifiedAt (s : LitSet L) (t : List UInt8) (p : Nat) : Nat :=
  ((List.finRange L).filter fun i => decide (cand s t p (s.bkt i) ∧ occursAt (s.lit i) t p)).length

theorem verifiedAt_eq_occAt (s : LitSet L) (t : List UInt8) (p : Nat) :
    verifiedAt s t p = occAt s t p := by
  unfold verifiedAt occAt
  congr 1
  apply List.filter_congr
  intro i _
  exact decide_eq_decide.mpr (exact s t p i)

/-- The occurrences starting in `[base, base + len)`. -/
def total (s : LitSet L) (t : List UInt8) (base len : Nat) : Nat :=
  ((List.range' base len).map (occAt s t)).sum

/-- One block of the kernel: sixteen verified positions. -/
def block (s : LitSet L) (t : List UInt8) (base : Nat) : Nat :=
  ((List.range' base 16).map (verifiedAt s t)).sum

/-- One step: four blocks. -/
def step (s : LitSet L) (t : List UInt8) (base : Nat) : Nat :=
  block s t base + block s t (base + 16) + block s t (base + 32) + block s t (base + 48)

/-- The kernel's total: `k` steps, then the tail of `[64 k, n)` position by
position. -/
def kernel (s : LitSet L) (t : List UInt8) (n k : Nat) : Nat :=
  ((List.range k).map fun j => step s t (64 * j)).sum + total s t (64 * k) (n - 64 * k)

theorem block_eq_total (s : LitSet L) (t : List UInt8) (base : Nat) :
    block s t base = total s t base 16 := by
  unfold block total
  congr 1
  apply List.map_congr_left
  intro p _
  exact verifiedAt_eq_occAt s t p

theorem total_add (s : LitSet L) (t : List UInt8) (base a b : Nat) :
    total s t base (a + b) = total s t base a + total s t (base + a) b := by
  unfold total
  rw [← List.range'_append, List.map_append, List.sum_append, Nat.one_mul]

theorem step_eq_total (s : LitSet L) (t : List UInt8) (base : Nat) :
    step s t base = total s t base 64 := by
  unfold step
  rw [block_eq_total, block_eq_total, block_eq_total, block_eq_total]
  rw [show (64 : Nat) = 16 + 16 + 16 + 16 from rfl, total_add, total_add, total_add]

theorem steps_eq_total (s : LitSet L) (t : List UInt8) (k : Nat) :
    ((List.range k).map fun j => step s t (64 * j)).sum = total s t 0 (64 * k) := by
  induction k with
  | zero => simp [total]
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [step_eq_total, Nat.mul_succ, total_add, Nat.zero_add]

/-- **The kernel counts every occurrence**: for any `k` steps with
`64 k ≤ n`, the steps plus the tail are the occurrences over `[0, n)`. -/
theorem kernel_eq_total (s : LitSet L) (t : List UInt8) (n k : Nat) (h : 64 * k ≤ n) :
    kernel s t n k = total s t 0 n := by
  unfold kernel
  rw [steps_eq_total]
  have split := total_add s t 0 (64 * k) (n - 64 * k)
  rw [Nat.zero_add, Nat.add_sub_cancel' h] at split
  exact split.symm

end

end Oak.Teddy.Count
