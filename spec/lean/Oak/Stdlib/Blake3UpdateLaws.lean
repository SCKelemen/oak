import Oak.Stdlib.HashExtracted

set_option autoImplicit false

namespace Oak.Stdlib.Hash

/-!
# BLAKE3 update batching

This file pins the extracted `blake3_update.loop2` helper introduced by the
batched update loop. It proves that every successful execution of that helper
is a finite repetition of the byte-write transition used by the original
outer loop while no block boundary is reached. The boundary transition is
left abstract: it cannot be observed during such an interior run.

The inner helper carries the next block offset in `at_` and writes it back to
`block_len` only after the group. `blake3Materialize` gives that loop-carried
representation its logical state. The main correspondence theorem equates
the materialized result with repeated original byte transitions.

Extraction models indexed writes with `Array.setIfInBounds`. These theorems
therefore concern successful executions of that totalized extracted model.
They do not equate an out-of-bounds source execution, which traps, with the
extraction. They also do not claim whole-update equivalence at equal fuel:
the nested loop changes how generated fuel is distributed between the outer
loop and compression helpers. The source keeps the original first checked
write, and the inner `at_ < 64` guard prevents a valid first write from
wrapping the loop-carried block offset; those runtime facts are outside the
totalized theorem below.
-/

structure Blake3CopyCursor where
  next : Blake3State
  index : UInt32
  offset : UInt32
  deriving Repr, DecidableEq

abbrev Blake3LogicalCursor := Blake3State × UInt32

/-- The exact totalized byte write emitted in `blake3_update.loop2`. Notice
that `block_len` is deliberately not updated inside the generated helper. -/
def blake3CopyByte (src : Array UInt8)
    (cursor : Blake3CopyCursor) : Blake3CopyCursor :=
  let next := {
    cursor.next with
    block := cursor.next.block.setIfInBounds cursor.offset.toNat
      (src.getD cursor.index.toNat 0)
  }
  { next := next, index := cursor.index + 1, offset := cursor.offset + 1 }

def blake3CopyBytes (src : Array UInt8) :
    Nat → Blake3CopyCursor → Blake3CopyCursor
  | 0, cursor => cursor
  | n + 1, cursor => blake3CopyBytes src n (blake3CopyByte src cursor)

/-- The logical state after the generated outer loop writes `at_` back to
`next.block_len`. -/
def blake3Materialize (cursor : Blake3CopyCursor) : Blake3LogicalCursor :=
  ({ cursor.next with block_len := cursor.offset }, cursor.index)

/-- The representation constructed by the generated outer loop immediately
after its preserved first byte write. -/
def blake3CopyStart (next : Blake3State) (index : UInt32) :
    Blake3CopyCursor :=
  { next := next, index := index, offset := next.block_len }

@[simp] theorem blake3Materialize_copyStart (next : Blake3State)
    (index : UInt32) :
    blake3Materialize (blake3CopyStart next index) = (next, index) := by
  cases next
  rfl

/-- The original byte transition after its boundary checks are false. -/
def blake3WriteByte (src : Array UInt8)
    (cursor : Blake3LogicalCursor) : Blake3LogicalCursor :=
  let next := {
    cursor.1 with
    block := cursor.1.block.setIfInBounds cursor.1.block_len.toNat
      (src.getD cursor.2.toNat 0)
  }
  let next := { next with block_len := next.block_len + 1 }
  (next, cursor.2 + 1)

def blake3WriteBytes (src : Array UInt8) :
    Nat → Blake3LogicalCursor → Blake3LogicalCursor
  | 0, cursor => cursor
  | n + 1, cursor => blake3WriteBytes src n (blake3WriteByte src cursor)

/-- The guard emitted for the generated batching loop. -/
def blake3InteriorGuard (src : Array UInt8)
    (cursor : Blake3CopyCursor) : Bool :=
  decide (cursor.offset < (64 : UInt32)) &&
    decide (cursor.index < src.size.toUInt32)

/-- A trace records that every repeated copy was admitted by the exact
generated inner-loop guard. -/
def Blake3InteriorRun (src : Array UInt8) :
    Nat → Blake3CopyCursor → Prop
  | 0, _ => True
  | n + 1, cursor =>
      blake3InteriorGuard src cursor = true ∧
        Blake3InteriorRun src n (blake3CopyByte src cursor)

/-- Exact one-step shape of the generated helper. Regenerating a materially
different helper makes this theorem fail rather than silently proving a model
that is no longer connected to production extraction. -/
theorem blake3_update_loop2_succ (src : Array UInt8)
    (cursor : Blake3CopyCursor) (fuel : Nat) :
    blake3_update.loop2 src cursor.next cursor.index cursor.offset (fuel + 1) =
      if blake3InteriorGuard src cursor then
        blake3_update.loop2 src
          (blake3CopyByte src cursor).next
          (blake3CopyByte src cursor).index
          (blake3CopyByte src cursor).offset fuel
      else some (cursor.next, cursor.index, cursor.offset) := by
  simp [blake3_update.loop2, blake3InteriorGuard, blake3CopyByte]

theorem blake3_update_loop2_zero (src : Array UInt8)
    (cursor : Blake3CopyCursor) :
    blake3_update.loop2 src cursor.next cursor.index cursor.offset 0 = none := by
  rfl

/-- Every successful generated inner-loop execution is exactly an `n`-byte
interior run and stops precisely when the emitted guard becomes false. -/
theorem blake3_update_loop2_replay (src : Array UInt8) :
    ∀ (fuel : Nat) (cursor result : Blake3CopyCursor),
      blake3_update.loop2 src cursor.next cursor.index cursor.offset fuel =
          some (result.next, result.index, result.offset) →
        ∃ n,
          Blake3InteriorRun src n cursor ∧
          blake3CopyBytes src n cursor = result ∧
          blake3InteriorGuard src result = false := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor result h
      cases h
  | succ fuel ih =>
      intro cursor result h
      rw [blake3_update_loop2_succ] at h
      by_cases hg : blake3InteriorGuard src cursor = true
      · simp only [hg, ↓reduceIte] at h
        obtain ⟨n, hrun, hresult, hstop⟩ :=
          ih (blake3CopyByte src cursor) result h
        exact ⟨n + 1, ⟨hg, hrun⟩, hresult, hstop⟩
      · have hg' : blake3InteriorGuard src cursor = false :=
          Bool.eq_false_iff.mpr hg
        simp only [hg', Bool.false_eq_true, ↓reduceIte,
          Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨hnext, hindex, hat⟩
        cases result
        simp only at hnext hindex hat
        subst_vars
        exact ⟨0, trivial, rfl, hg'⟩

/-- Materializing one scalar-offset copy gives exactly the original byte
transition. This is the key state-representation correspondence. -/
theorem blake3Materialize_copyByte (src : Array UInt8)
    (cursor : Blake3CopyCursor) :
    blake3Materialize (blake3CopyByte src cursor) =
      blake3WriteByte src (blake3Materialize cursor) := by
  cases cursor
  simp [blake3Materialize, blake3CopyByte, blake3WriteByte]

theorem blake3Materialize_copyBytes (src : Array UInt8) :
    ∀ (n : Nat) (cursor : Blake3CopyCursor),
      blake3Materialize (blake3CopyBytes src n cursor) =
        blake3WriteBytes src n (blake3Materialize cursor) := by
  intro n
  induction n with
  | zero =>
      intro cursor
      rfl
  | succ n ih =>
      intro cursor
      rw [blake3CopyBytes, blake3WriteBytes]
      rw [← blake3Materialize_copyByte src cursor]
      exact ih (blake3CopyByte src cursor)

/-- Fields unrelated to the current block buffer are unchanged. -/
def Blake3SameNonBufferFields (before after : Blake3State) : Prop :=
  before.cv = after.cv ∧
  before.blocks_compressed = after.blocks_compressed ∧
  before.chunk_counter = after.chunk_counter ∧
  before.stack = after.stack ∧
  before.stack_len = after.stack_len

theorem Blake3SameNonBufferFields.trans {a b c : Blake3State}
    (hab : Blake3SameNonBufferFields a b)
    (hbc : Blake3SameNonBufferFields b c) :
    Blake3SameNonBufferFields a c :=
  ⟨hab.1.trans hbc.1,
    hab.2.1.trans hbc.2.1,
    hab.2.2.1.trans hbc.2.2.1,
    hab.2.2.2.1.trans hbc.2.2.2.1,
    hab.2.2.2.2.trans hbc.2.2.2.2⟩

theorem blake3CopyByte_preserves_nonBuffer (src : Array UInt8)
    (cursor : Blake3CopyCursor) :
    Blake3SameNonBufferFields cursor.next
      (blake3CopyByte src cursor).next := by
  simp [Blake3SameNonBufferFields, blake3CopyByte]

theorem blake3CopyBytes_preserves_nonBuffer (src : Array UInt8) :
    ∀ (n : Nat) (cursor : Blake3CopyCursor),
      Blake3SameNonBufferFields cursor.next
        (blake3CopyBytes src n cursor).next := by
  intro n
  induction n with
  | zero =>
      intro cursor
      simp [blake3CopyBytes, Blake3SameNonBufferFields]
  | succ n ih =>
      intro cursor
      exact (blake3CopyByte_preserves_nonBuffer src cursor).trans
        (by simpa [blake3CopyBytes] using ih (blake3CopyByte src cursor))

theorem blake3Materialize_preserves_nonBuffer (cursor : Blake3CopyCursor) :
    Blake3SameNonBufferFields cursor.next (blake3Materialize cursor).1 := by
  simp [Blake3SameNonBufferFields, blake3Materialize]

theorem blake3_update_loop2_preserves_nonBuffer (src : Array UInt8)
    (fuel : Nat) (cursor result : Blake3CopyCursor)
    (h : blake3_update.loop2 src cursor.next cursor.index cursor.offset fuel =
      some (result.next, result.index, result.offset)) :
    Blake3SameNonBufferFields cursor.next (blake3Materialize result).1 := by
  obtain ⟨n, _, hresult, _⟩ :=
    blake3_update_loop2_replay src fuel cursor result h
  subst result
  exact (blake3CopyBytes_preserves_nonBuffer src n cursor).trans
    (blake3Materialize_preserves_nonBuffer (blake3CopyBytes src n cursor))

/-- One step of the old byte-at-a-time organization. `boundary` stands for
the unchanged push/absorb transition selected when the current block is full. -/
def blake3OldByteStep
    (boundary : Blake3State → Option Blake3State)
    (src : Array UInt8) (cursor : Blake3LogicalCursor) :
    Option Blake3LogicalCursor := do
  let next ← if cursor.1.block_len == (64 : UInt32) then boundary cursor.1
    else some cursor.1
  pure (blake3WriteByte src (next, cursor.2))

def blake3OldByteSteps
    (boundary : Blake3State → Option Blake3State)
    (src : Array UInt8) :
    Nat → Blake3LogicalCursor → Option Blake3LogicalCursor
  | 0, cursor => some cursor
  | n + 1, cursor => do
      let cursor ← blake3OldByteStep boundary src cursor
      blake3OldByteSteps boundary src n cursor

theorem blake3OldByteStep_interior
    (boundary : Blake3State → Option Blake3State)
    (src : Array UInt8) (cursor : Blake3CopyCursor)
    (hguard : blake3InteriorGuard src cursor = true) :
    blake3OldByteStep boundary src (blake3Materialize cursor) =
      some (blake3Materialize (blake3CopyByte src cursor)) := by
  have hboth :
      decide (cursor.offset < (64 : UInt32)) = true ∧
        decide (cursor.index < src.size.toUInt32) = true := by
    simpa [blake3InteriorGuard, Bool.and_eq_true] using hguard
  have hlt : cursor.offset < (64 : UInt32) := of_decide_eq_true hboth.1
  have hne : ¬ cursor.offset = (64 : UInt32) := by
    intro heq
    rw [heq] at hlt
    exact (by decide : ¬ ((64 : UInt32) < (64 : UInt32))) hlt
  rw [blake3Materialize_copyByte]
  simp [blake3OldByteStep, blake3Materialize, hne]

/-- Grouping an interior run is independent of the unchanged boundary
transition: the old byte-at-a-time organization invokes no boundary action. -/
theorem blake3OldByteSteps_eq_grouped
    (boundary : Blake3State → Option Blake3State)
    (src : Array UInt8) :
    ∀ (n : Nat) (cursor : Blake3CopyCursor),
      Blake3InteriorRun src n cursor →
        blake3OldByteSteps boundary src n (blake3Materialize cursor) =
          some (blake3Materialize (blake3CopyBytes src n cursor)) := by
  intro n
  induction n with
  | zero =>
      intro cursor _
      rfl
  | succ n ih =>
      intro cursor hrun
      rw [blake3OldByteSteps]
      rw [blake3OldByteStep_interior boundary src cursor hrun.1]
      exact ih (blake3CopyByte src cursor) hrun.2

/-- The successful generated helper, including the outer `block_len := at_`
writeback represented by `blake3Materialize`, has exactly the logical result
of the original byte-at-a-time transitions for any unchanged boundary code. -/
theorem blake3_update_loop2_grouped
    (boundary : Blake3State → Option Blake3State)
    (src : Array UInt8) (fuel : Nat)
    (cursor result : Blake3CopyCursor)
    (h : blake3_update.loop2 src cursor.next cursor.index cursor.offset fuel =
      some (result.next, result.index, result.offset)) :
    ∃ n,
      Blake3InteriorRun src n cursor ∧
      blake3OldByteSteps boundary src n (blake3Materialize cursor) =
        some (blake3Materialize result) ∧
      blake3InteriorGuard src result = false := by
  obtain ⟨n, hrun, hresult, hstop⟩ :=
    blake3_update_loop2_replay src fuel cursor result h
  refine ⟨n, hrun, ?_, hstop⟩
  rw [blake3OldByteSteps_eq_grouped boundary src n cursor hrun, hresult]

/-- Specialization to the exact `at_ := next.block_len` initialization emitted
by the generated outer loop. Thus the deferred writeback is observationally
the repeated original byte transition from the actual incoming state. -/
theorem blake3_update_loop2_grouped_from_blockLen
    (boundary : Blake3State → Option Blake3State)
    (src : Array UInt8) (fuel : Nat) (next : Blake3State) (index : UInt32)
    (result : Blake3CopyCursor)
    (h : blake3_update.loop2 src next index next.block_len fuel =
      some (result.next, result.index, result.offset)) :
    ∃ n,
      Blake3InteriorRun src n (blake3CopyStart next index) ∧
      blake3OldByteSteps boundary src n (next, index) =
        some (blake3Materialize result) ∧
      blake3InteriorGuard src result = false := by
  simpa only [blake3Materialize_copyStart] using
    blake3_update_loop2_grouped boundary src fuel
      (blake3CopyStart next index) result h

end Oak.Stdlib.Hash
