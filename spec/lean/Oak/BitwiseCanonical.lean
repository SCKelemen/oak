import Std.Tactic.BVDecide

/-!
# Bitwise canonicalization algebra

This module proves the fixed-width bitvector identities used by the rotate,
shift, and packed-shift verifier canonicalizations. The generic lemmas are
mathematical helpers; explicit premises restrict each implementation surface
to the widths and normalized counts supported by the verifier evaluator.

This is algebra only. It does not prove a Go/verifier refinement, admission of
any rewrite, preservation of poison or undefined behavior, source-language
typing, instruction selection, Arm ASL semantics, or an end-to-end compiler
path.
-/

namespace Oak.BitwiseCanonical

/-- A mask with `bits` low ones, retained at the original width `w`. -/
def lowMask (w bits : Nat) : BitVec w :=
  (BitVec.allOnes bits).zeroExtend w

/-- Applying the same same-width mask twice is redundant. This is the exact
algebra used by the helper that requires identical constant masks. -/
theorem and_same_mask_idempotent {w : Nat} (x mask : BitVec w) :
    (x &&& mask) &&& mask = x &&& mask := by
  simp [BitVec.and_assoc]

/-- Rotate right by a normalized, nonzero in-range count. -/
theorem rotateRight_eq_shift_or {w : Nat} (x : BitVec w) (k : Nat)
    (_hk0 : 0 < k) (hkw : k < w) :
    x.rotateRight k = (x >>> k) ||| (x <<< (w - k)) := by
  rw [BitVec.rotateRight_def, Nat.mod_eq_of_lt hkw]

/-- The separately handled zero-count rotate is the identity. -/
theorem rotateRight_zero {w : Nat} (x : BitVec w) :
    x.rotateRight 0 = x := by
  simp [BitVec.rotateRight_def]

/-- Bitvector rotation normalizes an arbitrary count modulo its width. -/
theorem rotateRight_normalized {w : Nat} (x : BitVec w) (count : Nat) :
    x.rotateRight count =
      (x >>> (count % w)) ||| (x <<< (w - count % w)) := by
  exact BitVec.rotateRight_def

/-- The supported 32-bit rotate canonicalization. -/
theorem rotateRight32_eq_shift_or (x : BitVec 32) (k : Nat)
    (hk0 : 0 < k) (hkw : k < 32) :
    x.rotateRight k = (x >>> k) ||| (x <<< (32 - k)) :=
  rotateRight_eq_shift_or x k hk0 hkw

/-- The supported 64-bit rotate canonicalization. -/
theorem rotateRight64_eq_shift_or (x : BitVec 64) (k : Nat)
    (hk0 : 0 < k) (hkw : k < 64) :
    x.rotateRight k = (x >>> k) ||| (x <<< (64 - k)) :=
  rotateRight_eq_shift_or x k hk0 hkw

/-! Lean's raw shifts do not normalize their count modulo the operand width.
The implementation does, so the following corollaries state the modulo
operation explicitly rather than claiming that a raw shift by `w` is an
identity. -/

/-- A raw zero-count left shift is the identity. -/
theorem shiftLeft_zero_count {w : Nat} (x : BitVec w) :
    x <<< 0 = x := by simp

/-- A raw zero-count logical right shift is the identity. -/
theorem shiftRight_zero_count {w : Nat} (x : BitVec w) :
    x >>> 0 = x := by simp

/-- A raw zero-count arithmetic right shift is the identity. -/
theorem arithShiftRight_zero_count {w : Nat} (x : BitVec w) :
    x.sshiftRight 0 = x := by simp

/-- The normalized left-shift count is zero on the implementation's supported
width range, so the normalized operation is the identity. -/
theorem shiftLeft_normalized_zero {w : Nat} (x : BitVec w) (count : Nat)
    (_hw0 : 0 < w) (_hw64 : w ≤ 64) (hcount : count % w = 0) :
    x <<< (count % w) = x := by
  rw [hcount]
  exact shiftLeft_zero_count x

/-- The normalized logical-right-shift count is zero on widths 1 through 64. -/
theorem shiftRight_normalized_zero {w : Nat} (x : BitVec w) (count : Nat)
    (_hw0 : 0 < w) (_hw64 : w ≤ 64) (hcount : count % w = 0) :
    x >>> (count % w) = x := by
  rw [hcount]
  exact shiftRight_zero_count x

/-- The normalized arithmetic-right-shift count is zero on widths 1 through
64. -/
theorem arithShiftRight_normalized_zero {w : Nat} (x : BitVec w)
    (count : Nat) (_hw0 : 0 < w) (_hw64 : w ≤ 64)
    (hcount : count % w = 0) :
    x.sshiftRight (count % w) = x := by
  rw [hcount]
  exact arithShiftRight_zero_count x

/-- Masking at the original width is the same low-bit projection as truncating
and then zero-extending. -/
theorem and_lowMask_eq_zeroExtend_truncate {w bits : Nat} (x : BitVec w)
    (_hbits : bits ≤ w) :
    x &&& lowMask w bits = (x.truncate bits).zeroExtend w := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp [lowMask, ← BitVec.getLsbD_eq_getElem, hi, Bool.and_comm]

/-- If `x` has no significant bit at or above `bits`, masking to those low
bits returns `x` itself. This is the algebraic premise checked by the
implementation's `significantBits(x) ≤ bits` guard. -/
theorem and_lowMask_eq_self_of_high_zero {w bits : Nat} (x : BitVec w)
    (hhigh : x >>> bits = 0) :
    x &&& lowMask w bits = x := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  by_cases hib : i < bits
  · simp [lowMask, ← BitVec.getLsbD_eq_getElem, hi, hib]
  · have hbit := congrArg (fun y : BitVec w => y.getLsbD (i - bits)) hhigh
    have hindex : bits + (i - bits) = i := by omega
    simp only [BitVec.getLsbD_ushiftRight] at hbit
    rw [hindex] at hbit
    simp [lowMask, ← BitVec.getLsbD_eq_getElem, hi, hib, hbit]

/-- Shifting a value left and then back right retains exactly its low `w-k`
bits, expressed with an original-width mask. -/
theorem shiftLeft_then_right_eq_lowMask {w k : Nat} (hi : BitVec w)
    (hkw : k < w) :
    (hi <<< k) >>> k = hi &&& lowMask w (w - k) := by
  apply BitVec.eq_of_getElem_eq
  intro i hiw
  have hnot : ¬ k + i < k := by omega
  have hbound : k + i < w ↔ i < w - k := by omega
  simp [lowMask, ← BitVec.getLsbD_eq_getElem, hiw, hnot, hbound,
    Bool.and_comm]

/-- Packing `lo` below `hi` and shifting the packed word right recovers the
masked high contribution when `lo` has no significant bits at or above `k`. -/
theorem packed_shiftRight_eq_masked_hi {w k : Nat} (lo hi : BitVec w)
    (_hk0 : 0 < k) (hkw : k < w) (hlow : lo >>> k = 0) :
    (lo ||| (hi <<< k)) >>> k = hi &&& lowMask w (w - k) := by
  rw [BitVec.ushiftRight_or_distrib, hlow]
  simpa using shiftLeft_then_right_eq_lowMask hi hkw

/-- The same packing identity with the OR operands reversed. -/
theorem packed_shiftRight_commuted_eq_masked_hi {w k : Nat} (lo hi : BitVec w)
    (hk0 : 0 < k) (hkw : k < w) (hlow : lo >>> k = 0) :
    ((hi <<< k) ||| lo) >>> k = hi &&& lowMask w (w - k) := by
  simpa [BitVec.or_comm] using
    packed_shiftRight_eq_masked_hi lo hi hk0 hkw hlow

/-- The packed extraction returns `hi` directly when every significant bit of
`hi` fits in the retained `w-k` low-bit region. -/
theorem packed_shiftRight_eq_hi_of_high_fits {w k : Nat}
    (lo hi : BitVec w) (hk0 : 0 < k) (hkw : k < w)
    (hlow : lo >>> k = 0) (hhigh : hi >>> (w - k) = 0) :
    (lo ||| (hi <<< k)) >>> k = hi := by
  rw [packed_shiftRight_eq_masked_hi lo hi hk0 hkw hlow,
    and_lowMask_eq_self_of_high_zero hi hhigh]

/-- The direct-`hi` packed extraction with the OR operands reversed. -/
theorem packed_shiftRight_commuted_eq_hi_of_high_fits {w k : Nat}
    (lo hi : BitVec w) (hk0 : 0 < k) (hkw : k < w)
    (hlow : lo >>> k = 0) (hhigh : hi >>> (w - k) = 0) :
    ((hi <<< k) ||| lo) >>> k = hi := by
  rw [packed_shiftRight_commuted_eq_masked_hi lo hi hk0 hkw hlow,
    and_lowMask_eq_self_of_high_zero hi hhigh]

/-- The supported 32-bit packed-shift canonicalization. -/
theorem packed_shiftRight32_eq_masked_hi (lo hi : BitVec 32) (k : Nat)
    (hk0 : 0 < k) (hkw : k < 32) (hlow : lo >>> k = 0) :
    (lo ||| (hi <<< k)) >>> k = hi &&& lowMask 32 (32 - k) :=
  packed_shiftRight_eq_masked_hi lo hi hk0 hkw hlow

/-- The supported 64-bit packed-shift canonicalization. -/
theorem packed_shiftRight64_eq_masked_hi (lo hi : BitVec 64) (k : Nat)
    (hk0 : 0 < k) (hkw : k < 64) (hlow : lo >>> k = 0) :
    (lo ||| (hi <<< k)) >>> k = hi &&& lowMask 64 (64 - k) :=
  packed_shiftRight_eq_masked_hi lo hi hk0 hkw hlow

/-- The supported 32-bit packed-shift canonicalization with commuted OR. -/
theorem packed_shiftRight32_commuted_eq_masked_hi
    (lo hi : BitVec 32) (k : Nat)
    (hk0 : 0 < k) (hkw : k < 32) (hlow : lo >>> k = 0) :
    ((hi <<< k) ||| lo) >>> k = hi &&& lowMask 32 (32 - k) :=
  packed_shiftRight_commuted_eq_masked_hi lo hi hk0 hkw hlow

/-- The supported 64-bit packed-shift canonicalization with commuted OR. -/
theorem packed_shiftRight64_commuted_eq_masked_hi
    (lo hi : BitVec 64) (k : Nat)
    (hk0 : 0 < k) (hkw : k < 64) (hlow : lo >>> k = 0) :
    ((hi <<< k) ||| lo) >>> k = hi &&& lowMask 64 (64 - k) :=
  packed_shiftRight_commuted_eq_masked_hi lo hi hk0 hkw hlow

/-- The common 32-bit half-word packing instance. -/
theorem packed_shiftRight32_half (lo hi : BitVec 32)
    (hlow : lo >>> 16 = 0) :
    (lo ||| (hi <<< 16)) >>> 16 = hi &&& lowMask 32 16 := by
  exact packed_shiftRight32_eq_masked_hi lo hi 16 (by decide) (by decide) hlow

/-- The common 64-bit half-word packing instance. -/
theorem packed_shiftRight64_half (lo hi : BitVec 64)
    (hlow : lo >>> 32 = 0) :
    (lo ||| (hi <<< 32)) >>> 32 = hi &&& lowMask 64 32 := by
  exact packed_shiftRight64_eq_masked_hi lo hi 32 (by decide) (by decide) hlow

end Oak.BitwiseCanonical
