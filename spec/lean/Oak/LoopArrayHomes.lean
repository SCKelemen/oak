import Oak.FieldPromotion

/-!
# Loop-scoped array-element homes

This module generalizes the two-home algebra of `Oak.FieldPromotion` to an
arbitrary selected set of array indices. Selected cells use scalar homes;
unselected cells continue to use backing array memory. Reads and writes choose
between those homes with the same predicate, and one post-loop flush
materializes the combined array. A fully memory-resident write trace is the
reference semantics.

This is conditional algebra, not a refinement of the Go generator. The
implementation separately limits selection to eight entries and establishes
array identity, private non-aliasing provenance, bounds, constant-index
recognition, control-flow coverage, and the absence of intervening whole-array
observations. This module also proves no early-exit or exceptional flushing,
memory or atomic admission, ordering, or backend code generation property.
-/

namespace Oak.LoopArrayHomes

/-- Total logical array memory; bounds are a separate admission obligation. -/
abbrev Mem (α : Type) := Nat → α

/-- Replace exactly one logical array element. -/
def store (memory : Mem α) (index : Nat) (value : α) : Mem α :=
  fun observed => if observed = index then value else memory observed

/-- One loop write at a logical array index. -/
structure Write (α : Type) where
  index : Nat
  value : α

/-- Backing array memory and scalar homes for the selected indices. Values in
`homes` at unselected indices are deliberately unobservable. -/
structure State (α : Type) where
  memory : Mem α
  homes : Mem α

/-- Before the loop, selected scalar homes receive their array values. The
total-function model initializes every home; selection controls observation. -/
def preload (memory : Mem α) : State α :=
  { memory, homes := memory }

/-- A loop write updates the scalar home of a selected index and backing
memory for an unselected index. -/
def writeCached (selected : Nat → Bool) (state : State α)
    (write : Write α) : State α :=
  if selected write.index then
    { state with homes := store state.homes write.index write.value }
  else
    { state with memory := store state.memory write.index write.value }

/-- A loop read chooses the scalar home exactly for selected indices. -/
def readCached (selected : Nat → Bool) (state : State α)
    (index : Nat) : α :=
  if selected index then state.homes index else state.memory index

/-- The combined logical array represented by backing memory and homes. -/
def materialize (selected : Nat → Bool) (state : State α) : Mem α :=
  fun index => readCached selected state index

/-- The one post-loop flush has the same pointwise value as materialization. -/
def flush (selected : Nat → Bool) (state : State α) : Mem α :=
  materialize selected state

/-- Run arbitrary selected and unselected writes in program order. -/
def runCached (selected : Nat → Bool) (state : State α) :
    List (Write α) → State α
  | [] => state
  | write :: rest => runCached selected (writeCached selected state write) rest

/-- One reference write goes directly to array memory. -/
def writeResident (memory : Mem α) (write : Write α) : Mem α :=
  store memory write.index write.value

/-- Fully memory-resident reference execution. -/
def runResident (memory : Mem α) : List (Write α) → Mem α
  | [] => memory
  | write :: rest => runResident (writeResident memory write) rest

@[simp] theorem store_same (memory : Mem α) (index : Nat) (value : α) :
    store memory index value index = value := by
  simp [store]

theorem store_other (memory : Mem α) (index other : Nat) (value : α)
    (hne : other ≠ index) :
    store memory index value other = memory other := by
  simp [store, hne]

/-- Preloading does not change the logical array for any selected set. -/
theorem materialize_preload (selected : Nat → Bool) (memory : Mem α) :
    materialize selected (preload memory) = memory := by
  apply funext
  intro index
  cases hselected : selected index <;>
    simp [materialize, readCached, preload, hselected]

/-- A cached read is exactly a point observation of materialized state. -/
theorem readCached_eq_materialize (selected : Nat → Bool) (state : State α)
    (index : Nat) :
    readCached selected state index = materialize selected state index := rfl

/-- One cached write, whether selected or unselected, materializes to exactly
one resident write. -/
theorem materialize_writeCached (selected : Nat → Bool) (state : State α)
    (write : Write α) :
    materialize selected (writeCached selected state write) =
      writeResident (materialize selected state) write := by
  apply funext
  intro observed
  by_cases heq : observed = write.index
  · subst observed
    cases hselected : selected write.index <;>
      simp [materialize, readCached, writeCached, writeResident, store,
        hselected]
  · cases hwrite : selected write.index <;>
      cases hobserved : selected observed <;>
        simp [materialize, readCached, writeCached, writeResident, store,
          hwrite, hobserved, heq]

/-- Reading after one cached write returns exactly what the corresponding
resident write returns at the same observed index. -/
theorem readCached_after_write (selected : Nat → Bool) (state : State α)
    (write : Write α) (observed : Nat) :
    readCached selected (writeCached selected state write) observed =
      writeResident (materialize selected state) write observed := by
  exact congrFun (materialize_writeCached selected state write) observed

/-- The written index reads back the written value in either home. -/
theorem readCached_after_write_same (selected : Nat → Bool) (state : State α)
    (write : Write α) :
    readCached selected (writeCached selected state write) write.index =
      write.value := by
  rw [readCached_after_write, writeResident, store_same]

/-- A write leaves every other logical index unchanged in either home. -/
theorem readCached_after_write_other (selected : Nat → Bool) (state : State α)
    (write : Write α) (observed : Nat) (hne : observed ≠ write.index) :
    readCached selected (writeCached selected state write) observed =
      readCached selected state observed := by
  rw [readCached_after_write, writeResident,
    store_other (materialize selected state) write.index observed write.value hne]
  rfl

/-- Materialization commutes with an arbitrary mixed trace of selected and
unselected writes. -/
theorem materialize_runCached (selected : Nat → Bool) (state : State α)
    (writes : List (Write α)) :
    materialize selected (runCached selected state writes) =
      runResident (materialize selected state) writes := by
  induction writes generalizing state with
  | nil => rfl
  | cons write rest ih =>
      rw [runCached, runResident, ih, materialize_writeCached]

/-- After preload and any mixed loop trace, one flush equals fully resident
execution. No premise excludes ordinary writes to unselected cells. -/
theorem flush_after_run_eq_runResident
    (selected : Nat → Bool) (initial : Mem α) (writes : List (Write α)) :
    flush selected (runCached selected (preload initial) writes) =
      runResident initial writes := by
  rw [flush, materialize_runCached, materialize_preload]

end Oak.LoopArrayHomes
