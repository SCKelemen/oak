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

/-- **The flat store.** In a contiguous tensor (row stride `cols`, column
stride 1, offset 0) the element `(gid / cols, gid % cols)` sits at storage
index `gid`, for every `gid` below `rows * cols` — so a kernel that reads
through `tensor_at` and stores at `out.data[gid]` under the contiguity
guard writes the element `tensor_set` would (docs/spec/56-kernels.md
section 8). -/
theorem flat_index (rows cols gid : UInt32) (fuel : Nat)
    (h : gid.toNat < rows.toNat * cols.toNat) :
    tensor_index rows cols cols 1 0 (gid / cols) (gid % cols) fuel = some gid := by
  have hcols : 0 < cols.toNat := Nat.pos_of_ne_zero (fun hz => by
    rw [hz, Nat.mul_zero] at h
    exact Nat.not_lt_zero _ h)
  have hi : gid / cols < rows := by
    rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_div]
    exact (Nat.div_lt_iff_lt_mul hcols).mpr h
  have hj : gid % cols < cols := by
    rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_mod]
    exact Nat.mod_lt _ hcols
  simp only [tensor_index, hi, hj, decide_true, Bool.and_self, ite_true, bind, Option.bind, pure]
  congr 1
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_div, UInt32.toNat_mod, UInt32.toNat_ofNat]
  have hle : gid.toNat / cols.toNat * cols.toNat ≤ gid.toNat := Nat.div_mul_le_self _ _
  have hlt : gid.toNat < 2 ^ 32 := gid.toNat_lt
  have hdm : gid.toNat / cols.toNat * cols.toNat + gid.toNat % cols.toNat = gid.toNat := Nat.div_add_mod' _ _
  have hmod : gid.toNat % cols.toNat < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.mod_le _ _) hlt
  omega

end Oak.Stdlib.Tensor
