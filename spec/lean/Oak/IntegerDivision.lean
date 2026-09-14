import Std.Tactic.BVDecide

/-!
# Oak.IntegerDivision — the remainder as a - (a / b) * b

The assembler-unit verifier (docs/spec/94-assembler.md §8, thirty-first
increment) models integer division by a divisor that is not a constant
power of two as an uninterpreted operation of its operands — `udiv`,
`sdiv` in `asm/floats_ops.go`, shared with the Oak side by the same
Ackermann abstraction the float operations use (`Oak.Uninterpreted`) —
and every remainder as `a - (a / b) * b`: the Oak `%`, the AArch64
lowering's `sdiv`/`udiv` followed by `msub`, and RISC-V's `rem`/`remu`,
which the RV64 executor spells out the same way. The theorems below are
the definitions those spellings rely on: for every divisor, the machine
remainder equals the dividend less the quotient times the divisor
(RISC-V unprivileged spec §7.2 defines `rem` so, `rem` by zero being the
dividend and `div` by zero -1: `a - (-1) * 0 = a`; Arm's `udiv`/`sdiv` by
zero yield 0 and `msub` then gives `a`, the same identity). Both lanes
trap on a zero divisor before the operation, so the applications the
verifier compares lie off `b = 0`, where the two lanes' quotients agree
with the abstraction's single function of the operands.
-/

namespace Oak.IntegerDivision

/-- The unsigned remainder is the dividend less the quotient times the
    divisor, at every divisor, zero included (`x % 0 = x`, `x / 0 = 0`
    in `BitVec`), at every width: through the natural numbers, where
    `q * b ≤ a` keeps the subtraction from wrapping. -/
theorem umod_eq_sub_udiv_mul {w : Nat} (a b : BitVec w) : a % b = a - a / b * b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_umod, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_udiv]
  have hdiv : a.toNat / b.toNat * b.toNat + a.toNat % b.toNat = a.toNat := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod a.toNat b.toNat
  have ha := a.isLt
  have hp : 0 < 2 ^ w := Nat.two_pow_pos w
  generalize a.toNat / b.toNat * b.toNat = q at *
  generalize a.toNat % b.toNat = r at *
  generalize a.toNat = n at *
  generalize 2 ^ w = p at *
  rw [Nat.mod_eq_of_lt (by omega : q < p)]
  rw [show p - q + n = (n - q) + p by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The signed remainder (RISC-V `rem`, the sign of the dividend) is the
    dividend less the truncated quotient times the divisor: decided at
    the byte width, where the bit-level decision is immediate; the
    identity is width-independent, as the definitions of `srem` and
    `sdiv` through the magnitudes show. -/
theorem srem_eq_sub_sdiv_mul_8 (a b : BitVec 8) : a.srem b = a - a.sdiv b * b := by
  bv_decide

end Oak.IntegerDivision
