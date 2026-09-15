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

/-- The vectorized loops over the elements (`nativegen/vector_reduction.go`):
    each block of eight feeds the eight lane accumulators — the lanes of
    two `simd.U32x4` or four `simd.U64x2` vectors — the remainder feeds the
    scalar accumulator, and the result is the scalar plus the combined
    lanes. -/
def vector8 {w : Nat} (acc a0 a1 a2 a3 a4 a5 a6 a7 : BitVec w) : List (BitVec w) → BitVec w
  | x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest =>
      vector8 acc (a0 + x0) (a1 + x1) (a2 + x2) (a3 + x3) (a4 + x4) (a5 + x5) (a6 + x6) (a7 + x7) rest
  | rest =>
      rest.foldl (· + ·) acc + (((a0 + a1) + (a2 + a3)) + ((a4 + a5) + (a6 + a7)))

/-- **The vector rewrite is the loop**: from any scalar and eight lane
    accumulators, the vectorized loops compute the sequential sum starting
    at their combination. The lane accumulators are combined in the vector
    domain and then across the lanes, which the grouping above records; any
    grouping is the same value, since addition reassociates. -/
theorem vector8_eq {w : Nat} (acc a0 a1 a2 a3 a4 a5 a6 a7 : BitVec w) (l : List (BitVec w)) :
    vector8 acc a0 a1 a2 a3 a4 a5 a6 a7 l
      = sequential (acc + (((a0 + a1) + (a2 + a3)) + ((a4 + a5) + (a6 + a7)))) l := by
  induction a0, a1, a2, a3, a4, a5, a6, a7, l using vector8.induct with
  | case1 a0 a1 a2 a3 a4 a5 a6 a7 x0 x1 x2 x3 x4 x5 x6 x7 rest ih =>
    rw [vector8, ih]
    unfold sequential
    simp only [List.foldl]
    congr 1
    ac_rfl
  | case2 a0 a1 a2 a3 a4 a5 a6 a7 rest hrest =>
    rw [vector8.eq_2 _ _ _ _ _ _ _ _ _ _ hrest]
    unfold sequential
    rw [foldl_add_right]

/-- The kernel's statement: zero lanes, the sequential sum from the
    scalar accumulator. -/
theorem vector8_sum {w : Nat} (acc : BitVec w) (l : List (BitVec w)) :
    vector8 acc 0 0 0 0 0 0 0 0 l = sequential acc l := by
  rw [vector8_eq]
  simp

end Oak.Reduction
