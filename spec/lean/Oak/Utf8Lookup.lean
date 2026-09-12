import Std.Tactic.BVDecide

/-!
# The UTF-8 lookup tables agree with Table 3-7, pair by pair

`stdlib/utf8.oak` validates UTF-8 with the three 16-entry tables of Keiser
and Lemire: for a byte `c` and the byte before it `p`, the AND of
`high1[p >> 4]`, `low1[p & 15]`, and `high2[c >> 4]` is the pair's error
class. This file states the tables exactly as the Oak source holds them and
proves, for every one of the 65,536 byte pairs, that the low seven bits are
nonzero precisely when the pair is an error on its own under Unicode
Table 3-7 (`Oak.Utf8Validity` is the sequence-level model of that table),
and that the top bit — TWO_CONTS — is set precisely when both bytes are
continuations. The stream-level argument, that TWO_CONTS cancels against a
lead byte two or three back and that a block boundary carries an open
sequence forward, is checked against the scalar validator by the
differential tests of `compiler/e2e_stdlib_utf8_test.go`.

Both theorems are decided by bit-blasting: the statement is a Boolean
formula over sixteen bits, and the kernel checks the SAT certificate.
-/

namespace Oak.Utf8Lookup

/-- `table_high1`, indexed by the previous byte's high nibble. -/
def high1 (p : BitVec 8) : BitVec 8 :=
  let n := p >>> 4
  if n < 8 then 2 else if n < 12 then 128 else if n = 12 then 33
  else if n = 13 then 1 else if n = 14 then 21 else 73

/-- `table_low1`, indexed by the previous byte's low nibble. -/
def low1 (p : BitVec 8) : BitVec 8 :=
  let n := p &&& 15
  if n = 0 then 231 else if n = 1 then 163 else if n < 4 then 131
  else if n = 4 then 139 else if n = 13 then 219 else 203

/-- `table_high2`, indexed by the current byte's high nibble. -/
def high2 (c : BitVec 8) : BitVec 8 :=
  let n := c >>> 4
  if n < 8 then 1 else if n = 8 then 230 else if n = 9 then 174
  else if n < 12 then 186 else 1

/-- The classification `special_cases` computes for one pair. -/
def sc (p c : BitVec 8) : BitVec 8 := high1 p &&& low1 p &&& high2 c

def isCont (b : BitVec 8) : Bool := 0x80 ≤ b && b ≤ 0xBF

/-- What Table 3-7 says about the pair on its own: given the previous byte's
class, the ranges its successor must fall in. A continuation as the
previous byte imposes nothing here — whether it may be followed by another
continuation depends on the lead byte before it, which is the TWO_CONTS
cancellation the stream handles. -/
def pairError (p c : BitVec 8) : Bool :=
  if p < 0x80 then isCont c                        -- ASCII, then a stray continuation
  else if p ≤ 0xBF then false                      -- decided by the bytes before
  else if p ≤ 0xC1 then true                       -- C0, C1: overlong two-byte forms
  else if p ≤ 0xDF then !isCont c                  -- two-byte lead
  else if p = 0xE0 then !(0xA0 ≤ c && c ≤ 0xBF)   -- no overlong three-byte form
  else if p = 0xED then !(0x80 ≤ c && c ≤ 0x9F)   -- no surrogates
  else if p ≤ 0xEF then !isCont c                  -- three-byte lead
  else if p = 0xF0 then !(0x90 ≤ c && c ≤ 0xBF)   -- no overlong four-byte form
  else if p ≤ 0xF3 then !isCont c                  -- four-byte lead
  else if p = 0xF4 then !(0x80 ≤ c && c ≤ 0x8F)   -- nothing above U+10FFFF
  else true                                        -- F5..FF: never a lead byte

/-- The low seven bits of the lookup are nonzero exactly on the pairs
Table 3-7 forbids on their own. -/
theorem sc_error (p c : BitVec 8) : (sc p c &&& 0x7F ≠ 0) ↔ pairError p c = true := by
  unfold sc high1 low1 high2 pairError isCont
  bv_decide

/-- The top bit is TWO_CONTS: set exactly when both bytes are continuations. -/
theorem sc_two_conts (p c : BitVec 8) : (sc p c &&& 0x80 ≠ 0) ↔ (isCont p = true ∧ isCont c = true) := by
  unfold sc high1 low1 high2 isCont
  bv_decide

/-- The block-end maxima: a byte above 0xBF in the last lane, above 0xDF in
the second-to-last, or above 0xEF in the third-to-last starts a sequence the
block cannot finish. `incomplete_max` holds 191, 223, 239 there and 255
elsewhere, so saturating subtraction is nonzero exactly in those cases. -/
theorem incomplete_last (b : BitVec 8) : (b - 191#8 ≠ 0#8 ∧ 191#8 ≤ b) ↔ 0xC0#8 ≤ b := by bv_decide
theorem incomplete_second (b : BitVec 8) : (b - 223#8 ≠ 0#8 ∧ 223#8 ≤ b) ↔ 0xE0#8 ≤ b := by bv_decide
theorem incomplete_third (b : BitVec 8) : (b - 239#8 ≠ 0#8 ∧ 239#8 ≤ b) ↔ 0xF0#8 ≤ b := by bv_decide

/-- The permission for two continuations: saturating subtraction of 0x60
from the byte two back leaves its high bit set exactly when that byte is at
or above 0xE0, and of 0x70 from the byte three back exactly when it is at or
above 0xF0. So `subs(prev2, 96) | subs(prev3, 112)` masked to 0x80 is the
TWO_CONTS bit of precisely the lanes a third or fourth continuation is
permitted in, with no comparison. -/
theorem permission (p2 p3 : BitVec 8) :
    (((if 96 ≤ p2 then p2 - 96 else 0) ||| (if 112 ≤ p3 then p3 - 112 else 0)) &&& 0x80) ≠ 0
      ↔ (0xE0 ≤ p2 ∨ 0xF0 ≤ p3) := by
  bv_decide

end Oak.Utf8Lookup
