import Std.Tactic.BVDecide

/-!
# Oak.StackArguments — parameters in the caller's outgoing area

A parameter beyond the register contract arrives in the caller's
outgoing area, at a fixed offset above the callee's entry sp
(`asm.LayoutArguments`, the shared classification `classifyArguments`).
The verifier (docs/spec/94-assembler.md §8, thirty-third increment)
holds it in the frame slot at that offset, at the size the caller stored
it: a narrow scalar its own bytes, a `Bool` the four of the C int, a
64-bit scalar eight, a span its base at the offset and its 32-bit length
eight bytes on. The body's load of the slot — `ldrb` for a byte, `ldrh`
for a halfword, `ldr wN`/`ldr xN` for the words — then reads the
parameter: the theorems below are the slot model's two facts, that a
value stored at its own width and loaded zero-extended is the value, and
that the span pair's two slots do not overlap.
-/

namespace Oak.StackArguments

/-- A byte parameter stored in a one-byte slot and read by `ldrb` (zero
    extension to the register) is the parameter. -/
theorem byte_slot_roundtrip (v : BitVec 8) : (v.setWidth 32).setWidth 8 = v := by
  bv_decide

/-- A halfword likewise. -/
theorem halfword_slot_roundtrip (v : BitVec 16) : (v.setWidth 32).setWidth 16 = v := by
  bv_decide

/-- A `Bool` crosses as the C int 0 or 1 in a four-byte slot: the low bit
    read back is the Bool. -/
theorem bool_slot_roundtrip (b : BitVec 1) : (b.setWidth 32).setWidth 1 = b := by
  bv_decide

/-- A span's base occupies eight bytes at its offset and its length four
    bytes eight on: the two slots are disjoint. -/
theorem span_pair_disjoint (off : Nat) : off + 8 ≤ off + 8 ∧ off + 8 + 4 > off + 8 := by
  omega

end Oak.StackArguments
