/-!
# Pair copies

The native lane's aggregate copies move sixteen bytes a step as a register
pair, `ldp xA, xB, [src, #off]; stp xA, xB, [dst, #off]`, where the two
locations are 8-aligned and a whole pair remains (docs/spec/94-assembler.md
§9 "Pair copies"). The model: memory as words by address; a pair store is
two word stores, so a copy by pairs is the copy by words it replaces.
-/

namespace Oak.PairCopies

/-- Memory: words by address (a word is eight bytes; addresses count words). -/
def Mem := Nat → Nat

/-- A word store. -/
def store (m : Mem) (a v : Nat) : Mem := fun x => if x = a then v else m x

/-- `stp xA, xB, [dst]`: the two words at `dst` and `dst + 1`. -/
def storePair (m : Mem) (dst a b : Nat) : Mem := store (store m dst a) (dst + 1) b

/-- A copy of `n` words from `src` to `dst`, one word a step. -/
def copyWords (m : Mem) (src dst : Nat) : Nat → Mem
  | 0 => m
  | n + 1 => store (copyWords m src dst n) (dst + n) (m (src + n))

/-- A copy of `2k` words as `k` pairs: `ldp` reads two words, `stp` writes
them. -/
def copyPairs (m : Mem) (src dst : Nat) : Nat → Mem
  | 0 => m
  | k + 1 => storePair (copyPairs m src dst k) (dst + 2 * k) (m (src + 2 * k)) (m (src + 2 * k + 1))

/-- A pair copy is the word copy it replaces: `k` pairs move the same `2k`
words to the same places. -/
theorem pair_copy (m : Mem) (src dst k : Nat) :
    copyPairs m src dst k = copyWords m src dst (2 * k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show storePair (copyPairs m src dst k) (dst + 2 * k) (m (src + 2 * k)) (m (src + 2 * k + 1))
      = copyWords m src dst (2 * (k + 1))
    rw [ih]
    have h : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
    rw [h]
    simp only [copyWords, storePair]
    have e1 : src + (2 * k + 1) = src + 2 * k + 1 := by omega
    have e2 : dst + (2 * k + 1) = dst + 2 * k + 1 := by omega
    rw [e1, e2]

end Oak.PairCopies
