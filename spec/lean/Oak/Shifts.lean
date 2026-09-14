import Std.Tactic.BVDecide

/-!
# Variable shift counts

Model for docs/spec/94-assembler.md §8 (variable shift counts) and
docs/spec/10-syntax.md §3b. Oak's `x << n` and `x >> n` trap when the count
reaches the operand's width; the native code guards the count and traps
the same way, and the assembler verifier drops the trapping path from its
fork. Below the width the machine's shift is Oak's; a narrow operand is
shifted in a wider register (a w register on AArch64, XLEN on RV64) and
masked back, and the verifier lowers Oak's shift at that register width so
that on the trapping counts the term is the machine's value — the
theorems: the widened shift, truncated back, is the narrow shift for every
count below the width, and the machine's count wraps at the register
width, which is the identity for those counts.
-/

namespace Oak.Shifts

/-- A byte shifted left in a 32-bit register and masked back is the byte
    shift, for every count below 8. -/
theorem shl8_in_32 (x n : BitVec 8) (h : n < 8) :
    (x.setWidth 32 <<< n.setWidth 32).setWidth 8 = x <<< n := by
  bv_decide

/-- The same at XLEN, the RV64 lane's `sll` for a narrow operand. -/
theorem shl8_in_64 (x n : BitVec 8) (h : n < 8) :
    (x.setWidth 64 <<< n.setWidth 64).setWidth 8 = x <<< n := by
  bv_decide

/-- A halfword in a 32-bit register. -/
theorem shl16_in_32 (x n : BitVec 16) (h : n < 16) :
    (x.setWidth 32 <<< n.setWidth 32).setWidth 16 = x <<< n := by
  bv_decide

/-- The right shift of a byte in a 32-bit register: zero-extended, the high
    bits are zero, so the shift is the byte's. -/
theorem shr8_in_32 (x n : BitVec 8) (h : n < 8) :
    (x.setWidth 32 >>> n.setWidth 32).setWidth 8 = x >>> n := by
  bv_decide

/-- The right shift at XLEN. -/
theorem shr8_in_64 (x n : BitVec 8) (h : n < 8) :
    (x.setWidth 64 >>> n.setWidth 64).setWidth 8 = x >>> n := by
  bv_decide

/-- A count below the width is unchanged by the machine's wrap at the
    register width, so a guarded shift at the operand's own width is the
    machine's shift (the 32-bit case, AArch64's `lsl wD, wN, wM` and RV64's
    `sllw`). -/
theorem count_below_width_wraps_to_itself (n : BitVec 32) (h : n < 32) :
    n.toNat % 32 = n.toNat := by
  have : n.toNat < 32 := by
    have := BitVec.lt_def.mp h
    simpa using this
  exact Nat.mod_eq_of_lt this

/-- The 64-bit case: the backend's guard compares the x register
    (`cmp xN, #64; b.hs trap`), and a count below 64 is its own remainder
    at XLEN, so the guarded `lsl xD, xS, xN` is Oak's shift. -/
theorem count_below_width_wraps_to_itself64 (n : BitVec 64) (h : n < 64) :
    n.toNat % 64 = n.toNat := by
  have : n.toNat < 64 := by
    have := BitVec.lt_def.mp h
    simpa using this
  exact Nat.mod_eq_of_lt this

/-- On a count at or beyond a byte's width but below the register's, the
    widened left shift masked back is zero — the machine's value on the
    path the trap removes, which the verifier's term reproduces rather than
    claiming Oak's (trapping) result. -/
theorem shl8_in_32_beyond (x n : BitVec 8) (h8 : 8 ≤ n) (h32 : n < 32) :
    (x.setWidth 32 <<< n.setWidth 32).setWidth 8 = 0 := by
  bv_decide

end Oak.Shifts
