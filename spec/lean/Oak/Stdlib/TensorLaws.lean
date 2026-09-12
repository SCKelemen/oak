import Oak.Stdlib.TensorExtracted

/-!
# Oak.Stdlib.TensorLaws — laws of the tensor package over its extraction

`stdlib/tensor.oak` (docs/spec/56-kernels.md section 8) represents a rank-2
tensor as a shape, strides, and an offset over a view; transposition and
row selection are new records over the same storage. These theorems are
about the extracted definitions (`TensorExtracted.lean`, regenerated from
the Oak source by `compiler/lean_stdlib_extract_test.go`), so they hold of
the code the C backend compiles.

* `at_transpose`: reading the transpose at `(i, j)` is reading the original
  at `(j, i)` — shape check included, so an out-of-shape read fails on both
  sides alike.
* `transpose_transpose`: transposing twice is the identity.
* `at_row`: reading row `i` at `(0, j)` is reading the original at `(i, j)`.
-/

namespace Oak.Stdlib.Tensor

theorem at_transpose (t : Tensor2) (i j : UInt32) (fuel : Nat) :
    (do let tt ← tensor_transpose t fuel; tensor_at tt i j fuel) = tensor_at t j i fuel := by
  simp only [tensor_transpose, tensor_at, tensor_index, bind, Option.bind, pure]
  by_cases hi : i < t.cols <;> by_cases hj : j < t.rows <;> simp [hi, hj]
  congr 1
  ac_rfl

theorem transpose_transpose (t : Tensor2) (fuel : Nat) :
    (do let a ← tensor_transpose t fuel; tensor_transpose a fuel) = pure t := by
  simp [tensor_transpose]

theorem at_row (t : Tensor2) (i j : UInt32) (fuel : Nat) :
    (do let r ← tensor_row t i fuel; tensor_at r 0 j fuel) = tensor_at t i j fuel := by
  simp only [tensor_row, tensor_at, tensor_index, bind, Option.bind, pure]
  by_cases hi : i < t.rows <;> by_cases hj : j < t.cols <;> simp [hi, hj]

end Oak.Stdlib.Tensor
