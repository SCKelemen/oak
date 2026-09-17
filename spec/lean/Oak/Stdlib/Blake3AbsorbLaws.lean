import Oak.Stdlib.HashExtracted

set_option autoImplicit false

namespace Oak.Stdlib.Hash

/-!
# BLAKE3 full-block absorption

The implementation passes only the chaining value, block, counter and flags
through `blake3_absorb_cv`; the caller performs the three state updates. This
module freezes the exact prior extracted `blake3_absorb_block` transition and
proves that the new helper-plus-caller composition is the same transition for
every extracted state and fuel.

This is an extraction-level theorem. Array reads retain the generated `getD`
semantics, and no claim is made here about source traps or about the complete
`blake3_update` loop. The equality uses the same fuel at every old and new
callee; `blake3_start_flag` is total and does not consume fuel.
-/

/-- The exact generated helper chain. This theorem deliberately mentions the
production helper so extraction drift breaks the proof. -/
theorem blake3_absorb_cv_chain (cv : Array UInt32) (block : Array UInt8)
    (counter : UInt64) (flags : UInt32) (fuel : Nat) :
    blake3_absorb_cv cv block counter flags fuel = (do
      let words ← blake3_words block fuel
      let out ← blake3_compress cv words counter (64 : UInt32) flags fuel
      blake3_first8 out fuel) := by
  simp [blake3_absorb_cv]

/-- The transition from `blake3_absorb_block` in extraction commit
`4777fef6`, with temporary names and identity lets simplified. It is
intentionally a frozen specification, not production code. -/
def blake3AbsorbBlockPrior (state : Blake3State) (fuel : Nat) :
    Option Blake3State := do
  let next : Blake3State := state
  let words ← blake3_words next.block fuel
  let flags ← blake3_start_flag next fuel
  let out ← blake3_compress next.cv words next.chunk_counter
    (64 : UInt32) flags fuel
  let cv ← blake3_first8 out fuel
  let next := { next with cv := cv }
  let next := {
    next with blocks_compressed := next.blocks_compressed + (1 : UInt32)
  }
  let next := { next with block_len := (0 : UInt32) }
  pure next

/-- The exact composition performed by the new ordinary-full-block caller
branch around `blake3_absorb_cv`. -/
def blake3AbsorbBlockViaCV (state : Blake3State) (fuel : Nat) :
    Option Blake3State := do
  let flags ← blake3_start_flag state fuel
  let cv ← blake3_absorb_cv state.cv state.block state.chunk_counter flags fuel
  let next := { state with cv := cv }
  let next := {
    next with blocks_compressed := next.blocks_compressed + (1 : UInt32)
  }
  let next := { next with block_len := (0 : UInt32) }
  pure next

/-- Moving the total start-flag computation ahead of the narrowed helper does
not alter success, failure, or the resulting state. -/
theorem blake3AbsorbBlockViaCV_eq_prior (state : Blake3State) (fuel : Nat) :
    blake3AbsorbBlockViaCV state fuel = blake3AbsorbBlockPrior state fuel := by
  cases hwords : blake3_words state.block fuel with
  | none =>
      simp [blake3AbsorbBlockViaCV, blake3AbsorbBlockPrior,
        blake3_absorb_cv, blake3_start_flag, hwords]
  | some words =>
      cases hcompress : blake3_compress state.cv words state.chunk_counter
        (64 : UInt32)
        (if state.blocks_compressed = (0 : UInt32) then
          BLAKE3_CHUNK_START else (0 : UInt32)) fuel <;>
        simp [blake3AbsorbBlockViaCV, blake3AbsorbBlockPrior,
          blake3_absorb_cv, blake3_start_flag, hwords, hcompress]

/-- Successful composition has the exact three caller updates and no others. -/
theorem blake3AbsorbBlockViaCV_result (state result : Blake3State) (fuel : Nat)
    (h : blake3AbsorbBlockViaCV state fuel = some result) :
    ∃ flags cv,
      blake3_start_flag state fuel = some flags ∧
      blake3_absorb_cv state.cv state.block state.chunk_counter flags fuel =
        some cv ∧
      result = {
        state with
        cv := cv
        blocks_compressed := state.blocks_compressed + (1 : UInt32)
        block_len := (0 : UInt32)
      } := by
  unfold blake3AbsorbBlockViaCV at h
  cases hflag : blake3_start_flag state fuel with
  | none =>
      rw [hflag] at h
      cases h
  | some flags =>
      rw [hflag] at h
      simp at h
      cases hcv : blake3_absorb_cv state.cv state.block state.chunk_counter
        flags fuel with
      | none =>
          simp_all
      | some cv =>
          simp_all

theorem blake3AbsorbBlockViaCV_retains_fields
    (state result : Blake3State) (fuel : Nat)
    (h : blake3AbsorbBlockViaCV state fuel = some result) :
    result.block = state.block ∧
    result.chunk_counter = state.chunk_counter ∧
    result.stack = state.stack ∧
    result.stack_len = state.stack_len ∧
    result.blocks_compressed = state.blocks_compressed + (1 : UInt32) ∧
    result.block_len = (0 : UInt32) := by
  obtain ⟨_, cv, _, _, rfl⟩ :=
    blake3AbsorbBlockViaCV_result state result fuel h
  simp

/-- Exact production caller pin for the ordinary full-block branch. The
continuation is left untouched: only the inlined start-flag/helper/state-update
prefix is identified with `blake3AbsorbBlockViaCV`. -/
theorem blake3_update_loop1_ordinaryFullBlock
    (src : Array UInt8) (state : Blake3State) (index : UInt32) (fuel : Nat)
    (hindex : index < src.size.toUInt32)
    (hfull : state.block_len = (64 : UInt32))
    (hnotLast : state.blocks_compressed ≠ (15 : UInt32)) :
    blake3_update.loop1 src state index (fuel + 1) = (do
      let next ← blake3AbsorbBlockViaCV state fuel
      let next := {
        next with
        block := next.block.setIfInBounds next.block_len.toNat
          (src.getD index.toNat 0)
      }
      let next := { next with block_len := next.block_len + (1 : UInt32) }
      let index := index + (1 : UInt32)
      let offset : UInt32 := next.block_len
      let (next, index, offset) ←
        blake3_update.loop2 src next index offset fuel
      let next := { next with block_len := offset }
      blake3_update.loop1 src next index fuel) := by
  have hguard : decide (index < src.size.toUInt32) = true :=
    decide_eq_true hindex
  simp [blake3_update.loop1, blake3AbsorbBlockViaCV,
    hguard, hfull, hnotLast]

/-- Replacing that exact caller prefix by the frozen prior transition leaves
the production continuation identical at the same fuel. -/
theorem blake3_update_loop1_ordinaryFullBlock_prior
    (src : Array UInt8) (state : Blake3State) (index : UInt32) (fuel : Nat)
    (hindex : index < src.size.toUInt32)
    (hfull : state.block_len = (64 : UInt32))
    (hnotLast : state.blocks_compressed ≠ (15 : UInt32)) :
    blake3_update.loop1 src state index (fuel + 1) = (do
      let next ← blake3AbsorbBlockPrior state fuel
      let next := {
        next with
        block := next.block.setIfInBounds next.block_len.toNat
          (src.getD index.toNat 0)
      }
      let next := { next with block_len := next.block_len + (1 : UInt32) }
      let index := index + (1 : UInt32)
      let offset : UInt32 := next.block_len
      let (next, index, offset) ←
        blake3_update.loop2 src next index offset fuel
      let next := { next with block_len := offset }
      blake3_update.loop1 src next index fuel) := by
  rw [blake3_update_loop1_ordinaryFullBlock src state index fuel
    hindex hfull hnotLast, blake3AbsorbBlockViaCV_eq_prior]

end Oak.Stdlib.Hash
