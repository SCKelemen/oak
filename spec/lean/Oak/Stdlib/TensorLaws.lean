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

/-! ## `tensor_matmul` is the inner product

The specification of `tensor_matmul` against the mathematical definition
(docs/spec/56-kernels.md section 8): over a contiguous output that fits
its storage, the product's entry `(i, j)` is the inner product of row `i`
of `a` and column `j` of `b` — `a.cols` terms, added left to right from
zero, the order every backend computes. The proof is in two steps: the
extracted loops equal a functional model of the stores (`writeRows`),
structurally; and the model, over a contiguous layout, leaves every entry
it wrote in place, because later rows write later indices. -/

/-- `n` terms of the inner product of row `i` of `a` and column `j` of `b`
from index `k`, added left to right onto `acc`. -/
def innerFold (a b : Tensor2) (i j : UInt32) : Float32 → Nat → UInt32 → Float32
  | acc, 0, _ => acc
  | acc, n + 1, k => innerFold a b i j (acc + elem a i k * elem b k j) n (k + 1)

/-- The inner product `out[i, j]` of `tensor_matmul`: `a.cols` terms from zero. -/
def inner (a b : Tensor2) (i j : UInt32) : Float32 :=
  innerFold a b i j (Float32.ofBits 0) a.cols.toNat 0

/-- The storage index of `(i, j)` in a mutable tensor, as `tensor_index` computes it. -/
def midx (t : MutTensor2) (i j : UInt32) : Nat := ((t.offset + i * t.row_stride) + j * t.col_stride).toNat

/-- The record after a store at `(i, j)`. -/
def stored (t : MutTensor2) (i j : UInt32) (v : Float32) : MutTensor2 :=
  { t with data := t.data.setIfInBounds (midx t i j) v }

theorem tensor_set_some (t : MutTensor2) (i j : UInt32) (v : Float32) (fuel : Nat) (hi : i < t.rows) (hj : j < t.cols) :
    tensor_set t i j v fuel = some ((), stored t i j v) := by
  simp [tensor_set, tensor_index, hi, hj, stored, midx]

/-- Row `i` of the product written into `out` from column `j`, `n` columns. -/
def writeRow (a b : Tensor2) (i : UInt32) : MutTensor2 → Nat → UInt32 → MutTensor2
  | out, 0, _ => out
  | out, n + 1, j => writeRow a b i (stored out i j (inner a b i j)) n (j + 1)

/-- `n` rows of the product from row `i`, each written whole. -/
def writeRows (a b : Tensor2) : MutTensor2 → Nat → UInt32 → MutTensor2
  | out, 0, _ => out
  | out, n + 1, i => writeRows a b (writeRow a b i out b.cols.toNat 0) n (i + 1)

theorem matmul_loop3_spec (a b : Tensor2) (i j : UInt32) (hi : i < a.rows) (hj : j < b.cols) (hab : a.cols = b.rows) (fuel : Nat) :
    ∀ (acc : Float32) (k : UInt32) (n : Nat), k.toNat + n = a.cols.toNat → n < fuel →
      tensor_matmul.loop3 a b i j acc k fuel = some (innerFold a b i j acc n k, a.cols) := by
  induction fuel with
  | zero => intro acc k n _ hf; omega
  | succ fuel ih =>
    intro acc k n hn hf
    unfold tensor_matmul.loop3
    cases n with
    | zero =>
      have heq : k = a.cols := UInt32.toNat_inj.mp (by omega)
      subst heq
      simp [innerFold]
    | succ m =>
      have hlt : k < a.cols := UInt32.lt_iff_toNat_lt.mpr (by omega)
      have hlt' : k < b.rows := hab ▸ hlt
      simp only [hlt, decide_true, ite_true, tensor_at_some a i k fuel hi hlt, tensor_at_some b k j fuel hlt' hj, bind, Option.bind, pure]
      have hsucc : (k + 1).toNat = k.toNat + 1 := uint32_succ_toNat k (by have := a.cols.toNat_lt; omega)
      rw [ih (acc + elem a i k * elem b k j) (k + 1) m (by omega) (by omega)]
      rfl

theorem stored_fields (t : MutTensor2) (i j : UInt32) (v : Float32) :
    (stored t i j v).rows = t.rows ∧ (stored t i j v).cols = t.cols ∧ (stored t i j v).row_stride = t.row_stride ∧
    (stored t i j v).col_stride = t.col_stride ∧ (stored t i j v).offset = t.offset ∧ (stored t i j v).data.size = t.data.size := by
  simp [stored]

theorem writeRow_fields (a b : Tensor2) (i : UInt32) : ∀ (out : MutTensor2) (n : Nat) (j : UInt32),
    (writeRow a b i out n j).rows = out.rows ∧ (writeRow a b i out n j).cols = out.cols ∧
    (writeRow a b i out n j).row_stride = out.row_stride ∧ (writeRow a b i out n j).col_stride = out.col_stride ∧
    (writeRow a b i out n j).offset = out.offset ∧ (writeRow a b i out n j).data.size = out.data.size := by
  intro out n
  induction n generalizing out with
  | zero => intro j; simp [writeRow]
  | succ n ih =>
    intro j
    simp only [writeRow]
    have h := ih (stored out i j (inner a b i j)) (j + 1)
    simp only [stored_fields] at h
    exact h

theorem matmul_loop2_spec (a b : Tensor2) (i : UInt32) (hi : i < a.rows) (hab : a.cols = b.rows) (fuel : Nat) :
    ∀ (out : MutTensor2) (j : UInt32) (n : Nat), out.rows = a.rows → out.cols = b.cols →
      j.toNat + n = b.cols.toNat → n + a.cols.toNat < fuel →
      tensor_matmul.loop2 a b out i j fuel = some (writeRow a b i out n j, b.cols) := by
  induction fuel with
  | zero => intro out j n _ _ _ hf; omega
  | succ fuel ih =>
    intro out j n hrows hcols hn hf
    unfold tensor_matmul.loop2
    cases n with
    | zero =>
      have heq : j = b.cols := UInt32.toNat_inj.mp (by omega)
      subst heq
      simp [writeRow]
    | succ m =>
      have hlt : j < b.cols := UInt32.lt_iff_toNat_lt.mpr (by omega)
      simp only [hlt, decide_true, ite_true, bind, Option.bind, pure]
      rw [matmul_loop3_spec a b i j hi hlt hab fuel _ 0 a.cols.toNat (by simp) (by omega)]
      simp only
      rw [tensor_set_some out i j _ fuel (hrows ▸ hi) (hcols ▸ hlt)]
      simp only
      have hsucc : (j + 1).toNat = j.toNat + 1 := uint32_succ_toNat j (by have := b.cols.toNat_lt; omega)
      rw [ih (stored out i j _) (j + 1) m (by simp [stored, hrows]) (by simp [stored, hcols]) (by omega) (by omega)]
      rfl

theorem matmul_loop1_spec (a b : Tensor2) (hab : a.cols = b.rows) (fuel : Nat) :
    ∀ (out : MutTensor2) (i : UInt32) (n : Nat), out.rows = a.rows → out.cols = b.cols →
      i.toNat + n = a.rows.toNat → n + b.cols.toNat + a.cols.toNat < fuel →
      tensor_matmul.loop1 a b out i fuel = some (writeRows a b out n i, a.rows) := by
  induction fuel with
  | zero => intro out i n _ _ _ hf; omega
  | succ fuel ih =>
    intro out i n hrows hcols hn hf
    unfold tensor_matmul.loop1
    cases n with
    | zero =>
      have heq : i = a.rows := UInt32.toNat_inj.mp (by omega)
      subst heq
      simp [writeRows]
    | succ m =>
      have hlt : i < a.rows := UInt32.lt_iff_toNat_lt.mpr (by omega)
      simp only [hlt, decide_true, ite_true, bind, Option.bind, pure]
      rw [matmul_loop2_spec a b i hlt hab fuel out 0 b.cols.toNat hrows hcols (by simp) (by omega)]
      simp only
      have hsucc : (i + 1).toNat = i.toNat + 1 := uint32_succ_toNat i (by have := a.rows.toNat_lt; omega)
      have hf1 := writeRow_fields a b i out b.cols.toNat 0
      rw [ih (writeRow a b i out b.cols.toNat 0) (i + 1) m (by rw [hf1.1, hrows]) (by rw [hf1.2.1, hcols]) (by omega) (by omega)]
      rfl

/-- **`tensor_matmul` computes the store model**: the extracted function
returns `writeRows`, given fuel for the three loops. -/
theorem tensor_matmul_writes (a b : Tensor2) (out : MutTensor2) (fuel : Nat)
    (hab : a.cols = b.rows) (hrows : out.rows = a.rows) (hcols : out.cols = b.cols)
    (hf : a.rows.toNat + b.cols.toNat + a.cols.toNat < fuel) :
    tensor_matmul a b out fuel = some ((), writeRows a b out a.rows.toNat 0) := by
  unfold tensor_matmul
  simp only [hab, hrows, hcols, beq_self_eq_true, Bool.and_self, ite_true, bind, Option.bind, pure]
  rw [matmul_loop1_spec a b hab fuel out 0 a.rows.toNat hrows hcols (by simp) hf]

/-- A contiguous, row-major output that fits its storage without index
overflow: the layout `tensor_mut_of` builds. -/
structure Contiguous (t : MutTensor2) : Prop where
  row_stride : t.row_stride = t.cols
  col_stride : t.col_stride = 1
  offset : t.offset = 0
  fits : t.rows.toNat * t.cols.toNat ≤ t.data.size
  small : t.rows.toNat * t.cols.toNat < 2 ^ 32

theorem idx_lt {i j rows cols : Nat} (hi : i < rows) (hj : j < cols) : i * cols + j < rows * cols := by
  calc i * cols + j < i * cols + cols := by omega
    _ = (i + 1) * cols := by rw [Nat.succ_mul]
    _ ≤ rows * cols := Nat.mul_le_mul_right cols hi

theorem midx_contig (t : MutTensor2) (hc : Contiguous t) (i j : UInt32) (hi : i < t.rows) (hj : j < t.cols) :
    midx t i j = i.toNat * t.cols.toNat + j.toNat := by
  have hb : i.toNat * t.cols.toNat + j.toNat < 2 ^ 32 :=
    Nat.lt_trans (idx_lt (UInt32.lt_iff_toNat_lt.mp hi) (UInt32.lt_iff_toNat_lt.mp hj)) hc.small
  unfold midx
  rw [hc.offset, hc.row_stride, hc.col_stride, UInt32.toNat_add, UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_mul]
  have h0 : (0 : UInt32).toNat = 0 := rfl
  have h1 : (1 : UInt32).toNat = 1 := rfl
  rw [h0, h1]
  omega

theorem contig_stored (t : MutTensor2) (hc : Contiguous t) (i j : UInt32) (v : Float32) : Contiguous (stored t i j v) := by
  have h := stored_fields t i j v
  exact ⟨by rw [h.2.2.1, h.2.1, hc.row_stride], by rw [h.2.2.2.1, hc.col_stride], by rw [h.2.2.2.2.1, hc.offset],
    by rw [h.1, h.2.1, h.2.2.2.2.2]; exact hc.fits, by rw [h.1, h.2.1]; exact hc.small⟩

theorem contig_writeRow (a b : Tensor2) (i : UInt32) : ∀ (out : MutTensor2) (n : Nat) (j : UInt32), Contiguous out → Contiguous (writeRow a b i out n j) := by
  intro out n
  induction n generalizing out with
  | zero => intro j hc; simpa [writeRow] using hc
  | succ n ih => intro j hc; simp only [writeRow]; exact ih _ _ (contig_stored out hc i j _)

/-- Entries before column `j` of row `i`, and at or after column `j + n`, are untouched by `writeRow`. -/
theorem writeRow_outside (a b : Tensor2) (i : UInt32) : ∀ (out : MutTensor2) (n : Nat) (j : UInt32) (p : Nat),
    Contiguous out → i < out.rows → j.toNat + n ≤ out.cols.toNat →
    (p < i.toNat * out.cols.toNat + j.toNat ∨ i.toNat * out.cols.toNat + j.toNat + n ≤ p) →
    (writeRow a b i out n j).data[p]? = out.data[p]? := by
  intro out n
  induction n generalizing out with
  | zero => intro j p _ _ _ _; simp [writeRow]
  | succ n ih =>
    intro j p hc hi hn hp
    simp only [writeRow]
    have hj : j < out.cols := UInt32.lt_iff_toNat_lt.mpr (by omega)
    have hsucc : (j + 1).toNat = j.toNat + 1 := uint32_succ_toNat j (by have := out.cols.toNat_lt; omega)
    have hf := stored_fields out i j (inner a b i j)
    rw [ih (stored out i j (inner a b i j)) (j + 1) p (contig_stored out hc i j _) (by rw [hf.1]; exact hi)
      (by rw [hf.2.1]; omega) (by rw [hf.2.1]; omega)]
    simp only [stored, midx_contig out hc i j hi hj]
    rw [Array.getElem?_setIfInBounds_ne]
    omega

/-- Every entry of row `i` from column `j` to `j + n` holds the inner product after `writeRow`. -/
theorem writeRow_inside (a b : Tensor2) (i : UInt32) : ∀ (out : MutTensor2) (n : Nat) (j j' : UInt32),
    Contiguous out → i < out.rows → j.toNat + n ≤ out.cols.toNat →
    j.toNat ≤ j'.toNat → j'.toNat < j.toNat + n →
    (writeRow a b i out n j).data[i.toNat * out.cols.toNat + j'.toNat]? = some (inner a b i j') := by
  intro out n
  induction n generalizing out with
  | zero => intro j j' _ _ _ _ _; omega
  | succ n ih =>
    intro j j' hc hi hn hlo hhi
    simp only [writeRow]
    have hj : j < out.cols := UInt32.lt_iff_toNat_lt.mpr (by omega)
    have hsucc : (j + 1).toNat = j.toNat + 1 := uint32_succ_toNat j (by have := out.cols.toNat_lt; omega)
    have hf := stored_fields out i j (inner a b i j)
    by_cases heq : j' = j
    · subst heq
      rw [writeRow_outside a b i (stored out i j' (inner a b i j')) n (j' + 1) _ (contig_stored out hc i j' _)
        (by rw [hf.1]; exact hi) (by rw [hf.2.1]; omega) (by rw [hf.2.1]; left; omega)]
      simp only [stored, midx_contig out hc i j' hi hj]
      rw [Array.getElem?_setIfInBounds_self, if_pos]
      exact Nat.lt_of_lt_of_le (idx_lt (UInt32.lt_iff_toNat_lt.mp hi) (UInt32.lt_iff_toNat_lt.mp hj)) hc.fits
    · have hne : j.toNat ≠ j'.toNat := fun h => heq (UInt32.toNat_inj.mp h).symm
      have := ih (stored out i j (inner a b i j)) (j + 1) j' (contig_stored out hc i j _) (by rw [hf.1]; exact hi)
        (by rw [hf.2.1]; omega) (by omega) (by omega)
      rw [hf.2.1] at this
      exact this

theorem contig_writeRows (a b : Tensor2) : ∀ (out : MutTensor2) (n : Nat) (i : UInt32), Contiguous out → Contiguous (writeRows a b out n i) := by
  intro out n
  induction n generalizing out with
  | zero => intro i hc; simpa [writeRows] using hc
  | succ n ih => intro i hc; simp only [writeRows]; exact ih _ _ (contig_writeRow a b i out _ 0 hc)

/-- Entries before row `i` are untouched by `writeRows` from row `i`. -/
theorem writeRows_outside (a b : Tensor2) : ∀ (out : MutTensor2) (n : Nat) (i : UInt32) (p : Nat),
    Contiguous out → out.cols = b.cols → i.toNat + n ≤ out.rows.toNat → p < i.toNat * out.cols.toNat →
    (writeRows a b out n i).data[p]? = out.data[p]? := by
  intro out n
  induction n generalizing out with
  | zero => intro i p _ _ _ _; simp [writeRows]
  | succ n ih =>
    intro i p hc hcols hn hp
    simp only [writeRows]
    have hi : i < out.rows := UInt32.lt_iff_toNat_lt.mpr (by omega)
    have hsucc : (i + 1).toNat = i.toNat + 1 := uint32_succ_toNat i (by have := out.rows.toNat_lt; omega)
    have hf := writeRow_fields a b i out b.cols.toNat 0
    rw [ih (writeRow a b i out b.cols.toNat 0) (i + 1) p (contig_writeRow a b i out _ 0 hc) (by rw [hf.2.1]; exact hcols)
      (by rw [hf.1]; omega) (by rw [hf.2.1, hsucc, Nat.succ_mul]; omega)]
    exact writeRow_outside a b i out b.cols.toNat 0 p hc hi (by simp [hcols]) (by left; simpa using hp)

/-- Every entry of rows `i` to `i + n` holds the inner product after `writeRows`. -/
theorem writeRows_inside (a b : Tensor2) : ∀ (out : MutTensor2) (n : Nat) (i i' j' : UInt32),
    Contiguous out → out.cols = b.cols → i.toNat + n ≤ out.rows.toNat →
    i.toNat ≤ i'.toNat → i'.toNat < i.toNat + n → j' < out.cols →
    (writeRows a b out n i).data[i'.toNat * out.cols.toNat + j'.toNat]? = some (inner a b i' j') := by
  intro out n
  induction n generalizing out with
  | zero => intro i i' j' _ _ _ _ _ _; omega
  | succ n ih =>
    intro i i' j' hc hcols hn hlo hhi hj'
    simp only [writeRows]
    have hi : i < out.rows := UInt32.lt_iff_toNat_lt.mpr (by omega)
    have hsucc : (i + 1).toNat = i.toNat + 1 := uint32_succ_toNat i (by have := out.rows.toNat_lt; omega)
    have hf := writeRow_fields a b i out b.cols.toNat 0
    by_cases heq : i' = i
    · subst heq
      rw [writeRows_outside a b (writeRow a b i' out b.cols.toNat 0) n (i' + 1) _ (contig_writeRow a b i' out _ 0 hc)
        (by rw [hf.2.1]; exact hcols) (by rw [hf.1]; omega)
        (by rw [hf.2.1, hsucc]; have := UInt32.lt_iff_toNat_lt.mp hj'; rw [Nat.succ_mul]; omega)]
      exact writeRow_inside a b i' out b.cols.toNat 0 j' hc hi (by simp [hcols]) (by simp)
        (by have h := UInt32.lt_iff_toNat_lt.mp hj'; rw [hcols] at h; simpa using h)
    · have hne : i.toNat ≠ i'.toNat := fun h => heq (UInt32.toNat_inj.mp h).symm
      have := ih (writeRow a b i out b.cols.toNat 0) (i + 1) i' j' (contig_writeRow a b i out _ 0 hc) (by rw [hf.2.1]; exact hcols)
        (by rw [hf.1]; omega) (by omega) (by omega) (by rw [hf.2.1]; exact hj')
      rw [hf.2.1] at this
      exact this

/-- **`tensor_matmul` is the inner product.** Over a contiguous output of
the right shape, the extracted `tensor_matmul` returns a record whose
entry `(i, j)` — at storage index `i * cols + j` — is the inner product of
row `i` of `a` and column `j` of `b`, `a.cols` terms added left to right
from zero, for every `(i, j)` in shape. -/
theorem tensor_matmul_spec (a b : Tensor2) (out : MutTensor2) (fuel : Nat)
    (hab : a.cols = b.rows) (hrows : out.rows = a.rows) (hcols : out.cols = b.cols) (hc : Contiguous out)
    (hf : a.rows.toNat + b.cols.toNat + a.cols.toNat < fuel) :
    ∃ out', tensor_matmul a b out fuel = some ((), out') ∧
      ∀ i j, i < out.rows → j < out.cols → out'.data[i.toNat * out.cols.toNat + j.toNat]? = some (inner a b i j) := by
  refine ⟨writeRows a b out a.rows.toNat 0, tensor_matmul_writes a b out fuel hab hrows hcols hf, ?_⟩
  intro i j hi hj
  exact writeRows_inside a b out a.rows.toNat 0 i j hc hcols (by rw [hrows]; simp) (by simp)
    (by simp; rw [← hrows]; exact UInt32.lt_iff_toNat_lt.mp hi) hj

end Oak.Stdlib.Tensor
