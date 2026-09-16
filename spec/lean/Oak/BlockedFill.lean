import Oak.PairCopies

/-!
# Four-word blocked fills

The prospective AArch64 zero-fill lowering advances four words per main-loop
iteration and represents those four scalar stores as two register-pair stores.
This file proves only the algebraic final-memory equality in the total word
model shared with `Oak.PairCopies`.

It does not establish bounds, alignment, trap or partial-write preservation,
address provenance, absence of aliases or observers, machine execution,
atomicity, non-tearing, memory order, MMIO/device behavior, or page-table
publication.  Those remain separate admission obligations for code generation.
-/

namespace Oak.BlockedFill

open Oak.PairCopies

/-- Fill `n` consecutive words with `value`, one scalar store at a time. -/
def fillWords (m : Mem) (dst value : Nat) : Nat → Mem
  | 0 => m
  | n + 1 => store (fillWords m dst value n) (dst + n) value

/-- Four scalar word stores represented as two adjacent pair stores. -/
def fillBlock4 (m : Mem) (dst value : Nat) : Mem :=
  storePair (storePair m dst value value) (dst + 2) value value

/-- Fill `4 * k` words as `k` four-word blocks. -/
def fillBlocks4 (m : Mem) (dst value : Nat) : Nat → Mem
  | 0 => m
  | k + 1 => fillBlock4 (fillBlocks4 m dst value k) (dst + 4 * k) value

/-- One two-pair block has the same final memory as four scalar stores. -/
theorem fillBlock4_eq_fillWords (m : Mem) (dst value : Nat) :
    fillBlock4 m dst value = fillWords m dst value 4 := by
  simp [fillBlock4, fillWords, storePair]

/-- Consecutive scalar fills compose by adding their lengths. -/
theorem fillWords_append (m : Mem) (dst value n r : Nat) :
    fillWords (fillWords m dst value n) (dst + n) value r =
      fillWords m dst value (n + r) := by
  induction r with
  | zero => simp [fillWords]
  | succ r ih =>
      rw [show n + (r + 1) = (n + r) + 1 by omega]
      simp only [fillWords]
      rw [ih]
      congr 1 <;> omega

/-- Repeating four-word blocks has the same final memory as the corresponding
scalar prefix. -/
theorem fillBlocks4_eq_fillWords (m : Mem) (dst value k : Nat) :
    fillBlocks4 m dst value k = fillWords m dst value (4 * k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [fillBlocks4]
      rw [fillBlock4_eq_fillWords, ih, fillWords_append]
      congr 1 <;> omega

/-- The quotient-sized blocked prefix followed by its scalar remainder is the
original scalar fill for every length. -/
theorem blocked_fill_eq (m : Mem) (dst value n : Nat) :
    fillWords (fillBlocks4 m dst value (n / 4))
        (dst + 4 * (n / 4)) value (n % 4) =
      fillWords m dst value n := by
  rw [fillBlocks4_eq_fillWords, fillWords_append]
  have h := Nat.mod_add_div n 4
  congr 1 <;> omega

/-- The residual scalar tail has at most three words. -/
theorem blocked_fill_tail_lt_four (n : Nat) : n % 4 < 4 := by
  exact Nat.mod_lt n (by decide)

end Oak.BlockedFill
