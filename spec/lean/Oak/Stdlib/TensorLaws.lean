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

/-! ## `tensor_sum` is the row-major left fold

The specification is the counted recursion of the elements in row-major
order — `rowFold` adds the `n` elements of row `i` from column `j`,
`tensorFold` the rows — and `tensor_sum_spec` shows the extracted loops
compute it, given fuel for the rows and the columns. Floating-point
addition is not associative, so the order is the whole content of the
statement: what the library computes, the host and the kernels compute. -/

/-- Element `(i, j)` as the extraction reads it: the storage index in
`u32` arithmetic, zero past the end (docs/spec/95-extraction.md, the
out-of-range modeling choice). -/
def elem (t : Tensor2) (i j : UInt32) : Float32 :=
  t.data.getD ((t.offset + i * t.row_stride) + j * t.col_stride).toNat (Float32.ofBits 0)

theorem tensor_at_some (t : Tensor2) (i j : UInt32) (fuel : Nat) (hi : i < t.rows) (hj : j < t.cols) :
    tensor_at t i j fuel = some (elem t i j) := by
  simp [tensor_at, tensor_index, hi, hj, elem]

/-- `n` elements of row `i` from column `j`, added left to right onto `acc`. -/
def rowFold (t : Tensor2) (i : UInt32) : Float32 → Nat → UInt32 → Float32
  | acc, 0, _ => acc
  | acc, n + 1, j => rowFold t i (acc + elem t i j) n (j + 1)

/-- `n` rows from row `i`, each folded whole, left to right onto `acc`. -/
def tensorFold (t : Tensor2) : Float32 → Nat → UInt32 → Float32
  | acc, 0, _ => acc
  | acc, n + 1, i => tensorFold t (rowFold t i acc t.cols.toNat 0) n (i + 1)

theorem uint32_succ_toNat (j : UInt32) (h : j.toNat + 1 < 2 ^ 32) : (j + 1).toNat = j.toNat + 1 := by
  rw [UInt32.toNat_add, UInt32.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by simpa using h)

/-- The inner loop folds the `n` remaining columns and stops at the last. -/
theorem sum_loop2_spec (t : Tensor2) (i : UInt32) (hi : i < t.rows) (fuel : Nat) :
    ∀ (acc : Float32) (j : UInt32) (n : Nat), j.toNat + n = t.cols.toNat → n < fuel →
      tensor_sum.loop2 t acc i j fuel = some (rowFold t i acc n j, t.cols) := by
  induction fuel with
  | zero => intro acc j n _ hf; omega
  | succ fuel ih =>
    intro acc j n hn hf
    unfold tensor_sum.loop2
    cases n with
    | zero =>
      have heq : j = t.cols := UInt32.toNat_inj.mp (by omega)
      subst heq
      simp [rowFold]
    | succ m =>
      have hlt : j < t.cols := UInt32.lt_iff_toNat_lt.mpr (by omega)
      simp only [hlt, decide_true, ite_true, tensor_at_some t i j fuel hi hlt, bind, Option.bind, pure]
      have hsucc : (j + 1).toNat = j.toNat + 1 := uint32_succ_toNat j (by have := t.cols.toNat_lt; omega)
      rw [ih (acc + elem t i j) (j + 1) m (by omega) (by omega)]
      rfl

/-- The outer loop folds the `n` remaining rows and stops at the last. -/
theorem sum_loop1_spec (t : Tensor2) (fuel : Nat) :
    ∀ (acc : Float32) (i : UInt32) (n : Nat), i.toNat + n = t.rows.toNat → n + t.cols.toNat < fuel →
      tensor_sum.loop1 t acc i fuel = some (tensorFold t acc n i, t.rows) := by
  induction fuel with
  | zero => intro acc i n _ hf; omega
  | succ fuel ih =>
    intro acc i n hn hf
    unfold tensor_sum.loop1
    cases n with
    | zero =>
      have heq : i = t.rows := UInt32.toNat_inj.mp (by omega)
      subst heq
      simp [tensorFold]
    | succ m =>
      have hlt : i < t.rows := UInt32.lt_iff_toNat_lt.mpr (by omega)
      simp only [hlt, decide_true, ite_true, bind, Option.bind, pure]
      rw [sum_loop2_spec t i hlt fuel acc 0 t.cols.toNat (by simp) (by omega)]
      simp only
      have hsucc : (i + 1).toNat = i.toNat + 1 := uint32_succ_toNat i (by have := t.rows.toNat_lt; omega)
      rw [ih _ (i + 1) m (by omega) (by omega)]
      rfl

/-- **`tensor_sum` is the row-major left fold from zero.** -/
theorem tensor_sum_spec (t : Tensor2) (fuel : Nat) (hf : t.rows.toNat + t.cols.toNat < fuel) :
    tensor_sum t fuel = some (tensorFold t (Float32.ofBits 0) t.rows.toNat 0) := by
  unfold tensor_sum
  simp only [bind, Option.bind, pure]
  rw [sum_loop1_spec t fuel _ 0 t.rows.toNat (by simp) hf]

/-! ## Stores are threaded

A store through a record's span field returns the record with its array
updated (docs/spec/95-extraction.md section 2, threaded parameters), so
`tensor_set` is visible to Lean: reading back the element just written
gives the value. -/

/-- **Read after write.** Writing `(i, j)` and reading it back gives the
value, when the pair is in shape and its storage index is inside the array
(the extraction drops an out-of-range store, as section 3 states). A read
through a span-holding record is threaded too and returns the record
unchanged. -/
theorem set_get (t : MutTensor2) (i j : UInt32) (v : Float32) (fuel : Nat)
    (hi : i < t.rows) (hj : j < t.cols)
    (hidx : ((t.offset + i * t.row_stride) + j * t.col_stride).toNat < t.data.size) :
    ∃ t', tensor_set t i j v fuel = some ((), t') ∧ tensor_get t' i j fuel = some (v, t') := by
  refine ⟨{ t with data := t.data.setIfInBounds ((t.offset + i * t.row_stride) + j * t.col_stride).toNat v }, ?_, ?_⟩
  · simp [tensor_set, tensor_index, hi, hj]
  · simp only [tensor_get, tensor_index, hi, hj, decide_true, Bool.and_self, ite_true, bind, Option.bind, pure]
    congr 1
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self, if_pos hidx]
    rfl

end Oak.Stdlib.Tensor
