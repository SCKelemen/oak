/-!
# Oak.Shape — shape in the type

Model of `stdlib/shape.oak` (docs/spec/56-kernels.md section 8b): a
row-major matrix `Mat[R, N, K]` whose dimensions are const parameters.
Shape agreement is then a typing fact — `mat_matvec(w: Mat[R, N, K], x:
[K]f32)` and `mat_matmul(a: Mat[A, N, K], b: Mat[B, K, M])` share `K` in
their signatures, so a mismatch is a type error at the call, not an
`assert` at run time — and what remains to prove is the index arithmetic:
every element of an `N × K` matrix lies inside its `N * K` elements
(`index_lt`), distinct positions have distinct indices (`index_injective`),
and a matrix-vector product reads each row from consecutive storage
(`row_contiguous`).
-/

namespace Oak.Shape

/-- The storage index of element `(i, j)` in a row-major `N × K` matrix. -/
def index (K i j : Nat) : Nat := i * K + j

/-- In range: `(i, j)` with `i < N`, `j < K` lies below `N * K`. -/
theorem index_lt {N K i j : Nat} (hi : i < N) (hj : j < K) : index K i j < N * K := by
  unfold index
  calc i * K + j < i * K + K := Nat.add_lt_add_left hj _
    _ = (i + 1) * K := by rw [Nat.succ_mul]
    _ ≤ N * K := Nat.mul_le_mul_right K hi

/-- Distinct positions have distinct indices. -/
theorem index_injective {K i j i' j' : Nat} (hj : j < K) (hj' : j' < K)
    (h : index K i j = index K i' j') : i = i' ∧ j = j' := by
  unfold index at h
  have hi : i = i' := by
    have h1 : (i * K + j) / K = i := by
      rw [Nat.mul_comm, Nat.mul_add_div (Nat.lt_of_le_of_lt (Nat.zero_le j) hj), Nat.div_eq_of_lt hj, Nat.add_zero]
    have h2 : (i' * K + j') / K = i' := by
      rw [Nat.mul_comm, Nat.mul_add_div (Nat.lt_of_le_of_lt (Nat.zero_le j') hj'), Nat.div_eq_of_lt hj', Nat.add_zero]
    rw [← h1, h, h2]
  subst hi
  exact ⟨rfl, Nat.add_left_cancel h⟩

/-- Row `i` is contiguous: the next column is the next storage word. -/
theorem row_contiguous (K i j : Nat) : index K i (j + 1) = index K i j + 1 := by
  unfold index
  omega

end Oak.Shape
