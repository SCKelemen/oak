import Oak.AArch64Encoding

/-!
# AArch64 return encoding

The exact `RET_64R_branch_reg` instruction bits emitted by Oak.  This module
models only the generated encoding row, its `Rn` field, and the operandless
form's `X30` default.  It does not establish the provenance or value of X30,
ABI or frame correctness, target validity, dynamic execution, or observation
of a return.
-/

namespace Oak.AArch64ReturnEncoding

open Oak.AArch64Encoding

-- OAK-A64-RET-ENC-BEGIN (generated from asm/encodings_gen.go; do not edit)
def ret : Encoding := ⟨"RET_64R_branch_reg", "ret", 0xd65f0000#32, 0xfffffc1f#32, [⟨"Z", 24, 1⟩, ⟨"op", 22, 2⟩, ⟨"op2", 20, 5⟩, ⟨"A", 11, 1⟩, ⟨"M", 10, 1⟩, ⟨"Rn", 9, 5⟩, ⟨"Rm", 4, 5⟩]⟩
-- OAK-A64-RET-ENC-END

-- OAK-A64-RET-WORD-BEGIN (checked against asm/encode.go; do not edit)
def encodeRetRn (rn : BitVec 5) : BitVec 32 := (ret.value &&& ret.mask) ||| (rn.setWidth 32 <<< 5)
def retX30 : BitVec 32 := encodeRetRn 0b11110#5
theorem ret_x30_word : retX30 = 0xd65f03c0#32 := by native_decide
-- OAK-A64-RET-WORD-END

/-- Encoding a return register changes none of the generated row's fixed
bits. -/
theorem encodeRetRn_fixed_bits (rn : BitVec 5) :
    encodeRetRn rn &&& ret.mask = ret.value := by
  unfold encodeRetRn ret
  bv_decide

/-- The encoded `Rn[9:5]` field is exactly the supplied register number. -/
theorem encodeRetRn_extract (rn : BitVec 5) :
    (encodeRetRn rn).extractLsb' 5 5 = rn := by
  unfold encodeRetRn ret
  bv_decide

end Oak.AArch64ReturnEncoding
