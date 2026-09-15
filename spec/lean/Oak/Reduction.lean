/-!
# Verified reduction unrolling

`nativegen/reduction.go` (docs/spec/94-assembler.md §9 "Reductions")
rewrites an integer reduction over a span before lowering,

    while i < len(v) { acc = acc + v[i]; i = i + 1 }

into a four-accumulator main loop over each block of four elements, the
remainder loop as written, and the combine `(acc + a1) + (a2 + a3)`. The
verifier proves the assembly against the rewritten body; this file is the
rewrite's own correctness: over the list of the span's elements, the
strided four-way fold equals the sequential fold. Integer addition on a
`BitVec` wraps and is associative and commutative at every width, which is
all the proof uses — a float accumulator is never rewritten.
-/

namespace Oak.Reduction

/-- The rewritten loops over the elements: each block of four feeds the
    four accumulators, the remainder feeds the first, and the combine is
    the result. -/
def unrolled4 {w : Nat} (a0 a1 a2 a3 : BitVec w) : List (BitVec w) → BitVec w
  | x0 :: x1 :: x2 :: x3 :: rest => unrolled4 (a0 + x0) (a1 + x1) (a2 + x2) (a3 + x3) rest
  | rest => (rest.foldl (· + ·) a0 + a1) + (a2 + a3)

/-- The sequential loop over the elements. -/
def sequential {w : Nat} (acc : BitVec w) (l : List (BitVec w)) : BitVec w :=
  l.foldl (· + ·) acc

/-- A summand carried outside the fold moves inside it. -/
theorem foldl_add_right {w : Nat} (l : List (BitVec w)) (a b : BitVec w) :
    l.foldl (· + ·) (a + b) = l.foldl (· + ·) a + b := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl]
    rw [← ih (a + x)]
    congr 1
    ac_rfl

/-- **The rewrite is the loop**: from any four accumulators, the unrolled
    loops compute the sequential sum starting at their combination; with
    the accumulators at zero, the sum of the elements. -/
theorem unrolled4_eq {w : Nat} (a0 a1 a2 a3 : BitVec w) (l : List (BitVec w)) :
    unrolled4 a0 a1 a2 a3 l = sequential ((a0 + a1) + (a2 + a3)) l := by
  induction a0, a1, a2, a3, l using unrolled4.induct with
  | case1 a0 a1 a2 a3 x0 x1 x2 x3 rest ih =>
    rw [unrolled4, ih]
    unfold sequential
    simp only [List.foldl]
    congr 1
    ac_rfl
  | case2 a0 a1 a2 a3 rest hrest =>
    rw [unrolled4.eq_2 _ _ _ _ _ hrest]
    unfold sequential
    have h : (a0 + a1) + (a2 + a3) = a0 + (a1 + (a2 + a3)) := by ac_rfl
    rw [h, foldl_add_right]
    ac_rfl

/-- The kernel's statement: zero accumulators, the sum of the span. -/
theorem unrolled4_sum {w : Nat} (l : List (BitVec w)) :
    unrolled4 0 0 0 0 l = sequential 0 l := by
  rw [unrolled4_eq]
  simp

end Oak.Reduction
