/-!
# Read-only borrows of a by-value parameter

`view(&p…)` of a by-value record or array parameter reads the parameter and
nothing else (docs/spec/94-assembler.md §9 "Read-only borrows"): the callee
may read such a parameter in place, and a caller may pass its own storage
instead of a copy, when no writable span of that storage travels alongside.
The model: memory as words by address, a copy of the aggregate, and a view
as reads at offsets — reading through a view of the copy is reading the
storage, so long as nothing writes the storage meanwhile.
-/

namespace Oak.ReadOnlyBorrow

/-- Memory: words by address. -/
def Mem := Nat → Nat

/-- The callee's copy of `size` words at `src`, laid at address zero. -/
def copyOf (m : Mem) (src : Nat) : Mem := fun k => m (src + k)

/-- A view over memory at a base: element `k` is the word at `base + k`. -/
def viewAt (m : Mem) (base k : Nat) : Nat := m (base + k)

/-- Reading through a view of the copy is reading the caller's storage. -/
theorem view_of_copy (m : Mem) (src k : Nat) : viewAt (copyOf m src) 0 k = viewAt m src k := by
  simp [viewAt, copyOf]

/-- A store to an address outside the aggregate leaves every view read of it
unchanged: the writable spans a caller passes alongside must not reach
`[src, src + size)`. -/
def store (m : Mem) (a v : Nat) : Mem := fun x => if x = a then v else m x

theorem view_unchanged (m : Mem) (src size k a v : Nat) (hk : k < size)
    (outside : a < src ∨ src + size ≤ a) :
    viewAt (store m a v) src k = viewAt m src k := by
  simp only [viewAt, store]
  have : src + k ≠ a := by omega
  simp [this]

end Oak.ReadOnlyBorrow
