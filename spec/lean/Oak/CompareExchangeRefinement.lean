/-! # Compiler correspondence for the strong compare-exchange helper

`docs/spec/65-machine-memory.md` §3 gives Oak's strong compare-exchange a
value-oriented contract:

```text
observed = atomic_compare_exchange_<success>_<failure>(cell, expected, desired)
```

The operation atomically compares the cell with `expected`. If equal, it
writes `desired` and returns `expected`. If unequal, it does not write and
returns the value observed by the failed comparison — so `observed ==
expected` is success and `observed != expected` is the retry value. The C
backend realizes each order pair as one helper per carrier
(`codegen/compare_exchange.go`, `emitCompareExchangeHelpers`) over C11's
mutable-`expected` primitive:

```c
static inline T __oak_cas_T_<suffix>(_Atomic(T) *cell, T expected, T desired) {
  T observed = expected;
  (void)atomic_compare_exchange_strong_explicit(cell, &observed, desired, <success>, <failure>);
  return observed;
}
```

(`<success>` is the C11 constant, or under `__riscv` and AArch64 the
`OAK_ORDER_CAS_*` selection macro that strengthens an acquiring pair to
RCsc — `69-riscv-memory-refinement.md` §2; the value contract below does
not depend on it.)

This module states the correspondence the way `Oak.ArithmeticRefinement`
does: C11's strong compare-exchange is modeled as a function of the cell's
value and the `expected` object it may overwrite (C17 7.17.7.4: compare the
value pointed to by `object` with the value pointed to by `expected`; if
equal, replace the object's value with `desired`; otherwise load the
object's current value into `*expected`; return the comparison's result,
never a spurious failure for the strong form), the helper body is
transliterated over it, and the theorems below show the helper meets the
value-oriented contract for every cell value, `expected` and `desired`.
The emitted helper text is pinned to this transliteration by
`codegen/compare_exchange_refinement_test.go`.

The correspondence is scoped to the value contract: what one call
returns and what it leaves in the cell, given the value the compare
observed. Atomicity and the memory-order side of the pair are the C11
primitive's and RVWMO's/AArch64's business, stated in
`Oak.MemoryOrder`/`Oak.MemoryOrderRefinement` (legality),
`Oak.AArch64Memory` and `Oak.RiscVMemory` (ordering). -/

namespace Oak.CompareExchangeRefinement

/-- The outcome of C11 `atomic_compare_exchange_strong_explicit` on a cell
    holding `cell`, with `*expected = expected`: the flag it returns, the
    cell's value afterwards, and `*expected` afterwards. -/
structure C11Outcome (α : Type) where
  success : Bool
  cell : α
  expected : α
  deriving Repr

/-- C17 7.17.7.4 for the strong form: the compare never fails spuriously. -/
def c11Strong {α : Type} [DecidableEq α] (cell expected desired : α) : C11Outcome α :=
  if cell = expected then
    { success := true, cell := desired, expected := expected }
  else
    { success := false, cell := cell, expected := cell }

/-- The helper: `observed = expected; cas(cell, &observed, desired); return
    observed`. Its value is the `expected` object after the primitive; the
    cell after the primitive is the helper's side effect. -/
def helper {α : Type} [DecidableEq α] (cell expected desired : α) : α × α :=
  let outcome := c11Strong cell expected desired
  (outcome.expected, outcome.cell)

/-- The contract's returned value (65 §3): the value observed at the
    compare — `expected` on success, the cell's value on failure — which is
    the cell's prior value in both cases. -/
def contractObserved {α : Type} (cell _expected _desired : α) : α := cell

/-- The contract's cell afterwards: `desired` exactly when the compare
    succeeded, unchanged otherwise. -/
def contractCell {α : Type} [DecidableEq α] (cell expected desired : α) : α :=
  if cell = expected then desired else cell

/-- **The helper returns the value observed at the compare.** -/
theorem helper_returns_observed {α : Type} [DecidableEq α] (cell expected desired : α) :
    (helper cell expected desired).1 = contractObserved cell expected desired := by
  unfold helper c11Strong contractObserved
  split <;> simp_all

/-- **The helper leaves the contract's cell.** -/
theorem helper_leaves_contract_cell {α : Type} [DecidableEq α] (cell expected desired : α) :
    (helper cell expected desired).2 = contractCell cell expected desired := by
  unfold helper c11Strong contractCell
  split <;> simp

/-- **Success is exactly `observed == expected`**, the test a CAS loop
    makes on the helper's value (65 §3). -/
theorem success_iff_observed_eq_expected {α : Type} [DecidableEq α] (cell expected desired : α) :
    (c11Strong cell expected desired).success = true ↔ (helper cell expected desired).1 = expected := by
  unfold helper c11Strong
  split <;> simp_all

/-- On success the cell holds `desired`; on failure it is untouched and the
    returned value is the cell's, so a retry with it as `expected` compares
    against exactly what was seen. -/
theorem failure_returns_cell_untouched {α : Type} [DecidableEq α] (cell expected desired : α)
    (h : cell ≠ expected) :
    helper cell expected desired = (cell, cell) := by
  unfold helper c11Strong
  simp [h]

theorem success_writes_desired {α : Type} [DecidableEq α] (expected desired : α) :
    helper expected expected desired = (expected, desired) := by
  unfold helper c11Strong
  simp

end Oak.CompareExchangeRefinement
