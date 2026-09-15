import Std.Tactic.BVDecide

/-!
# Oak.StrengthReduction — the constant-arithmetic rewrites the native lane emits

The AArch64 lane lowers a multiplication by a constant power of two to a
left shift, an unsigned division by one to a right shift, and an unsigned
remainder by one to a mask (docs/spec/94-assembler.md §9.ac, the first
increment of the optimization system, docs/spec/90-backend.md §16). The
verifier proves each lowered body against its Oak source by its own
models; these theorems are the laws those models rest on, stated over
`BitVec` at the machine widths with the shift count a variable, so they
cover every constant the lowering may meet — including a count at or past
the width, where both sides are zero (or, for the remainder, the
dividend), and division by a power of two that wrapped to zero, where
`BitVec` division by zero is zero and the shift is zero too.
-/

namespace Oak.StrengthReduction

/-- `x * 2^k = x << k` at 8 bits, every `k`. -/
theorem mul_pow_two_8 (x k : BitVec 8) : x * (1#8 <<< k) = x <<< k := by bv_decide
/-- `x / 2^k = x >> k` (unsigned) at 8 bits, every `k`. -/
theorem udiv_pow_two_8 (x k : BitVec 8) : x / (1#8 <<< k) = x >>> k := by bv_decide
/-- `x % 2^k = x & (2^k - 1)` (unsigned) at 8 bits, every `k`. -/
theorem umod_pow_two_8 (x k : BitVec 8) : x % (1#8 <<< k) = x &&& ((1#8 <<< k) - 1) := by bv_decide

theorem mul_pow_two_16 (x k : BitVec 16) : x * (1#16 <<< k) = x <<< k := by bv_decide
theorem udiv_pow_two_16 (x k : BitVec 16) : x / (1#16 <<< k) = x >>> k := by bv_decide
theorem umod_pow_two_16 (x k : BitVec 16) : x % (1#16 <<< k) = x &&& ((1#16 <<< k) - 1) := by bv_decide

theorem mul_pow_two_32 (x k : BitVec 32) : x * (1#32 <<< k) = x <<< k := by bv_decide
theorem udiv_pow_two_32 (x k : BitVec 32) : x / (1#32 <<< k) = x >>> k := by bv_decide
theorem umod_pow_two_32 (x k : BitVec 32) : x % (1#32 <<< k) = x &&& ((1#32 <<< k) - 1) := by bv_decide

/-- A nonzero constant divisor never meets the zero-divisor trap: the
    lowering's `cbz` on the divisor can go. -/
theorem nonzero_divisor_no_trap {w : Nat} (b : BitVec w) (h : b ≠ 0) : ¬ (b == 0) = true := by
  simpa using h

end Oak.StrengthReduction
