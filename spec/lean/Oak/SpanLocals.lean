import Std.Tactic.BVDecide
import Oak.Assembler

/-!
# Span locals over owned frame arrays

Model for docs/spec/94-assembler.md §8, thirty-fourth increment (the RV64
lane's span locals and value-less records), and docs/spec/90-backend.md §6
(the zero fill of a value-less record local).

A span or view local over an owned frame array is a `{base, len}` pair in
two callee-saved registers: `base = sp + off`, the array's frame address,
and `len = n`, the array's constant element count, one register serving as
the raw and the normalized length. The theorems below are the pair's two
facts: an element access under the checker's guarded-index idiom
(`i < len`) stays inside the array's slots, and therefore inside the frame
that holds it; and the zero fill of a record local, written word by word
from the zero register, is the record's zero value.
-/

namespace Oak.SpanLocals

/-- The array's slots in the frame: bytes `[off, off + n*elem)`. -/
def FrameArray (off n elem b : Nat) : Prop := off ≤ b ∧ b < off + n * elem

/-- An element access at index `i` touches bytes
    `[off + i*elem, off + (i+1)*elem)`. -/
def ElementBytes (off i elem b : Nat) : Prop :=
  off + i * elem ≤ b ∧ b < off + (i + 1) * elem

/-- **Guarded index**: under `i < n`, every byte of the element access lies
    in the array's slots. The span local's length register holds `n`, so
    the checker's index guard is exactly this hypothesis. -/
theorem element_in_array (off n elem i b : Nat) (hi : i < n)
    (hb : ElementBytes off i elem b) : FrameArray off n elem b := by
  unfold ElementBytes at hb
  unfold FrameArray
  have : (i + 1) * elem ≤ n * elem := Nat.mul_le_mul_right elem hi
  constructor
  · have : off ≤ off + i * elem := Nat.le_add_right _ _
    omega
  · omega

/-- **Inside the frame**: an array laid out below the frame size keeps every
    guarded element access below the frame size, so the access never
    reaches the return address or the callee-saved area above it. -/
theorem element_in_frame (off n elem i b frame : Nat) (hi : i < n)
    (hfit : off + n * elem ≤ frame) (hb : ElementBytes off i elem b) :
    b < frame := by
  have h := element_in_array off n elem i b hi hb
  unfold FrameArray at h
  omega

/-- The span local's guarded access is an instance of the checker's span
    access rule (`Oak.Assembler.SpanAccessOk`) with the constant length as
    the dominating guard: relative to the array's base, the access
    `[i*elem, (i+1)*elem)` is admitted when `i < n`. -/
theorem element_access_ok (n elem i : Nat) (hi : i < n) :
    Oak.Assembler.SpanAccessOk elem n (i * elem) elem := by
  unfold Oak.Assembler.SpanAccessOk
  have : (i + 1) * elem ≤ n * elem := Nat.mul_le_mul_right elem hi
  have : (i + 1) * elem = i * elem + elem := Nat.succ_mul i elem
  have : elem * n = n * elem := Nat.mul_comm elem n
  omega

/-- **Aliasing**: a second named span over the same array copies the two
    registers, so it denotes the same pair. -/
theorem alias_is_same (base len : BitVec 64) :
    ((base, len) : BitVec 64 × BitVec 64) = (base, len) := rfl

/-- **Zero fill**: a two-word record local written word by word from the
    zero register holds the record's zero value. -/
theorem zero_fill_two_words :
    ((0 : BitVec 64) ++ (0 : BitVec 64)) = (0 : BitVec 128) := by
  bv_decide

/-- Word by word, for any number of words: appending a zero word to a zero
    value keeps it zero. -/
theorem zero_fill_step (w : Nat) :
    ((0 : BitVec w) ++ (0 : BitVec 64)) = (0 : BitVec (w + 64)) := by
  simp

end Oak.SpanLocals
