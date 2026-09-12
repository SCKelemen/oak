/-! # Compiler correspondence for view and span access

`docs/spec/50-borrowing.md` gives a view `[]T` (and a span `[*]T`) one
meaning: a window of `len` elements over an owner, read (and for a span
written) by index, narrowed by `subslice`, with every access bounds-checked
against `len` and a failure trapping (`20-types.md`, `90-backend.md` §2:
never C UB). The Lean extraction (`95-extraction.md` §3) reads `arr[i]` as
`Array.getD` and clamps a window, sound for runs that took no trapping
path. The C backend realizes a view as `{ const T *base; u32 len; }` and
the accesses as the helpers `oak_view_index_T`, `oak_view_subslice_T`,
`oak_span_index_T`, `oak_span_store_T`, `oak_span_subslice_T`
(`codegen/codegen.go`, `emitViewType`/`emitSpanType`):

```c
static inline T oak_view_index_T(oak_view_T v, u64 i) {
  if (i >= (u64)v.len) { __builtin_trap(); }
  return v.base[i];
}
static inline oak_view_T oak_view_subslice_T(oak_view_T v, u64 start, u64 n) {
  if (start > (u64)v.len || n > (u64)v.len - start) { __builtin_trap(); }
  return (oak_view_T){ v.base + start, (u32)n };
}
static inline void oak_span_store_T(oak_span_T v, u64 i, T value) {
  if (i >= (u64)v.len) { __builtin_trap(); }
  v.base[i] = value;
}
```

This module states the correspondence the way `Oak.ArithmeticRefinement`
does for arithmetic: the guards are transliterated over an abstract view —
a start offset and a length into a backing array — and proved to be
exactly the bounds conditions the spec states; the accepted read is proved
to land inside the backing array and to agree with the extraction's
`getD`; and `subslice` is proved to keep the window inside its parent. The
`u64` arithmetic in the guards is modeled over `Nat`: the lengths are
`u32` values and the indices `u64` values, so no comparison wraps, and the
one subtraction `(u64)v.len - start` is evaluated only after `start >
(u64)v.len` has been found false, so it never wraps either —
`subslice_guard_iff` is the statement that the two-part C condition is the
single abstract inequality. The emitted helper text is pinned to this
transliteration by `codegen/view_refinement_test.go`.

The correspondence is scoped: it covers the guard logic and the index
arithmetic of the helpers. That `v.base[i]` reads the `i`th element after
`base`, and that `v.base + start` is the address of the `start`th, are the
C meanings of pointer indexing over a valid object, which the borrow
checker's ownership story guarantees the base points into
(`50-borrowing.md`), and which are assumed here, not proved. -/

namespace Oak.ViewRefinement

/-- An abstract view or span: `len` elements starting `start` elements into
    the backing array it was carved from. -/
structure View where
  start : Nat
  len : Nat
  deriving DecidableEq, Repr

/-- The window lies inside a backing array of `size` elements — what
    `view(&owner)` establishes and every helper below preserves. -/
def WellFormed (v : View) (size : Nat) : Prop := v.start + v.len ≤ size

/-! ## Index -/

/-- `if (i >= (u64)v.len) { __builtin_trap(); }`: the access proceeds when
    the guard is false. -/
def indexGuard (v : View) (i : Nat) : Bool := !decide (i ≥ v.len)

theorem index_guard_iff (v : View) (i : Nat) : indexGuard v i = true ↔ i < v.len := by
  unfold indexGuard; simp <;> omega

/-- The element the accepted read touches, as an index into the backing
    array (`v.base[i]` with `base` the `start`th element). -/
def indexAt (v : View) (i : Nat) : Nat := v.start + i

/-- An accepted read stays inside the backing array. -/
theorem index_in_backing (v : View) (size i : Nat) (hw : WellFormed v size) (h : i < v.len) :
    indexAt v i < size := by
  unfold WellFormed at hw; unfold indexAt; omega

/-- The accepted read is the extraction's `getD` at the same index, and the
    default is never taken: `getD` and the checked access agree. -/
theorem index_read_agrees {α : Type} (backing : Array α) (v : View) (i : Nat) (zero : α)
    (hw : WellFormed v backing.size) (h : i < v.len) :
    backing.getD (indexAt v i) zero = backing[indexAt v i]'(index_in_backing v backing.size i hw h) := by
  have hin := index_in_backing v backing.size i hw h
  simp [Array.getD, hin]

/-! ## Store

`oak_span_store_T` has the index helper's guard exactly; a store that passes
it writes inside the backing array, and `setIfInBounds` — the extraction's
write — performs it rather than dropping it. -/

theorem store_in_backing (v : View) (size i : Nat) (hw : WellFormed v size) (h : indexGuard v i = true) :
    indexAt v i < size :=
  index_in_backing v size i hw ((index_guard_iff v i).mp h)

theorem store_agrees {α : Type} (backing : Array α) (v : View) (i : Nat) (value : α)
    (hw : WellFormed v backing.size) (h : i < v.len) :
    (backing.setIfInBounds (indexAt v i) value).size = backing.size ∧
      (backing.setIfInBounds (indexAt v i) value)[indexAt v i]'(by
        rw [Array.size_setIfInBounds]; exact index_in_backing v backing.size i hw h) = value := by
  have hin := index_in_backing v backing.size i hw h
  refine ⟨Array.size_setIfInBounds .., ?_⟩
  simp [Array.setIfInBounds, hin]

/-! ## Subslice -/

/-- `if (start > (u64)v.len || n > (u64)v.len - start) { __builtin_trap(); }`
    — the second operand is evaluated only when the first is false, so the
    subtraction never wraps; over `Nat` the same two-part condition. -/
def subsliceGuard (v : View) (start n : Nat) : Bool :=
  !(decide (start > v.len) || decide (n > v.len - start))

/-- The two-part C guard is the one abstract inequality: the window
    `[start, start + n)` lies inside `[0, len)`. -/
theorem subslice_guard_iff (v : View) (start n : Nat) :
    subsliceGuard v start n = true ↔ start + n ≤ v.len := by
  unfold subsliceGuard; simp <;> omega

/-- `(oak_view_T){ v.base + start, (u32)n }`. The `(u32)n` narrowing is
    exact under the guard, since `n ≤ v.len` and `v.len` is a `u32`. -/
def subslice (v : View) (start n : Nat) : View := { start := v.start + start, len := n }

/-- An accepted subslice keeps the window inside the backing array. -/
theorem subslice_wellFormed (v : View) (size start n : Nat) (hw : WellFormed v size)
    (hg : start + n ≤ v.len) : WellFormed (subslice v start n) size := by
  unfold WellFormed at *; unfold subslice; simp; omega

/-- An accepted subslice reads exactly the parent's elements it names: index
    `i` of the child is index `start + i` of the parent. -/
theorem subslice_index (v : View) (start n i : Nat) :
    indexAt (subslice v start n) i = indexAt v (start + i) := by
  unfold indexAt subslice; simp; omega

/-- The narrowing `(u32)n` in the helper is exact: under the guard `n` fits
    the parent's `u32` length. -/
theorem subslice_len_fits (v : View) (start n : Nat) (hg : start + n ≤ v.len) (hlen : v.len < 2 ^ 32) :
    n < 2 ^ 32 := by omega


/-! ## Owned arrays (`[N]T`)

```c
static inline u64 oak_bounds_trap(void) { __builtin_trap(); return 0; }
#define oak_index(base, len, i) ((u64)(i) < (u64)(len) ? (base)[(i)] : (base)[oak_bounds_trap()])
static inline u64 oak_lv_idx(u64 i, u64 len) { if (i >= len) { __builtin_trap(); } return i; }
#define oak_store(base, len, i, v) do { if ((u64)(i) >= (u64)(len)) { __builtin_trap(); } (base)[(i)] = (v); } while (0)
```

An owned array's length is its static `N`; the read macro guards with
`(u64)i < (u64)len`, the lvalue and store helpers with the negation, so the
three are the view index guard at `start = 0`. -/

/-- `(u64)(i) < (u64)(len)`: the read proceeds. -/
def ownedIndexGuard (len i : Nat) : Bool := decide (i < len)

theorem owned_index_guard_iff (len i : Nat) : ownedIndexGuard len i = true ↔ i < len := by
  unfold ownedIndexGuard; simp

/-- The lvalue and store guards trap on `i >= len`: the same admission. -/
theorem owned_store_guard_iff (len i : Nat) : (!decide (i ≥ len)) = ownedIndexGuard len i := by
  unfold ownedIndexGuard
  by_cases h : i < len
  · have hn : ¬ i ≥ len := Nat.not_le.mpr h
    simp [h, hn]
  · have hge : i ≥ len := Nat.not_lt.mp h
    simp [h, hge]

/-- An owned array is the view of itself at offset zero: its guard is the
    view guard. -/
theorem owned_is_view_at_zero (len i : Nat) : ownedIndexGuard len i = indexGuard ⟨0, len⟩ i := by
  rw [← owned_store_guard_iff]; rfl

end Oak.ViewRefinement
