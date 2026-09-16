import Oak.AArch64Encoding
import Oak.ObjectRelocation

/-!
# AArch64 ordinary call-branch encoding

The exact `BL_only_branch_imm` instruction bits emitted by Oak, composed with
the already-proved Branch26 relocation arithmetic. This module models only
static field packing and signed PC-relative displacement. It does not prove
the architectural value of `PC`, the dynamic write to `X30`, execution of
`BranchTo`, target validity or mapping, source-CFG label selection, object or
link correctness, or observation of a transfer.
-/

namespace Oak.AArch64CallBranchEncoding

open Oak.AArch64Encoding
open Oak.ObjectRelocation

-- OAK-A64-BL-ENC-BEGIN (generated from asm/encodings_gen.go; do not edit)
def bl : Encoding := ⟨"BL_only_branch_imm", "bl", 0x94000000#32, 0xfc000000#32, [⟨"op", 31, 1⟩, ⟨"imm26", 25, 26⟩]⟩
-- OAK-A64-BL-ENC-END

-- OAK-A64-BL-WORD-BEGIN (checked against asm/encode.go; do not edit)
def encodeBLImm26 (imm26 : BitVec 26) : BitVec 32 :=
  (bl.value &&& bl.mask) ||| imm26.zeroExtend 32
def blPlus12 : BitVec 32 := encodeBLImm26 3#26
theorem bl_plus_12_word : blPlus12 = 0x94000003#32 := by native_decide
-- OAK-A64-BL-WORD-END

/-- Filling `imm26` changes none of the generated row's fixed bits. -/
theorem encodeBLImm26_fixed_bits (imm26 : BitVec 26) :
    encodeBLImm26 imm26 &&& bl.mask = bl.value := by
  unfold encodeBLImm26 bl
  bv_decide

/-- The encoded low 26 bits are exactly the supplied word displacement. -/
theorem encodeBLImm26_extract (imm26 : BitVec 26) :
    (encodeBLImm26 imm26).extractLsb' 0 26 = imm26 := by
  unfold encodeBLImm26 bl
  bv_decide

/-- Every word built from this row has the raw ordinary `BL` opcode. -/
theorem encodeBLImm26_opcode_bits (imm26 : BitVec 26) :
    branch26Opcode (encodeBLImm26 imm26) = 0b100101#6 := by
  unfold encodeBLImm26 bl branch26Opcode
  bv_decide

/-- The raw opcode is the relocation model's call kind. -/
theorem encodeBLImm26_opcode (imm26 : BitVec 26) :
    branch26Opcode (encodeBLImm26 imm26) = Branch26Kind.call.opcode := by
  simpa [Branch26Kind.opcode] using encodeBLImm26_opcode_bits imm26

/-- The row's field packer is exactly the Branch26 low-field patch operation. -/
theorem encodeBLImm26_eq_patchBranch26 (imm26 : BitVec 26) :
    encodeBLImm26 imm26 = patchBranch26 bl.value imm26 := by
  unfold encodeBLImm26 patchBranch26 bl
  bv_decide

/-- Decoding a packed field recovers its signed word displacement in bytes. -/
theorem decode_encodeBLImm26 (imm26 : BitVec 26) :
    decodeBranch26 (encodeBLImm26 imm26) = imm26.toInt * 4 := by
  rw [encodeBLImm26_eq_patchBranch26]
  unfold decodeBranch26
  rw [patchBranch26_immediate]

/-- On the exact aligned signed range, local `BL` packing is the same operation
as the proved object/executable Branch26 call relocation. -/
theorem relocate_bl_eq_encode (place target : Int)
    (hfits : branch26Fits place target = true) :
    relocateBranch26 .call bl.value place target =
      some (encodeBLImm26 (branch26Immediate place target)) := by
  unfold relocateBranch26
  simp [hfits, branch26OpcodeMatches, branch26Opcode, Branch26Kind.opcode,
    encodeBLImm26_eq_patchBranch26, bl]

/-- Consequently the statically encoded displacement reaches the modeled
target. This remains arithmetic, not an architectural call theorem. -/
theorem encoded_bl_reaches (place target : Int)
    (hfits : branch26Fits place target = true) :
    place + decodeBranch26 (encodeBLImm26 (branch26Immediate place target)) =
      target := by
  rw [encodeBLImm26_eq_patchBranch26,
    decodeBranch26_patch bl.value place target hfits]
  unfold branch26Delta
  omega

/-! Exact signed endpoints of the admitted byte-displacement interval. -/

theorem bl_negative_endpoint_word :
    encodeBLImm26 0x2000000#26 = 0x96000000#32 := by native_decide

theorem bl_positive_endpoint_word :
    encodeBLImm26 0x1ffffff#26 = 0x95ffffff#32 := by native_decide

theorem bl_minus_four_word :
    encodeBLImm26 0x3ffffff#26 = 0x97ffffff#32 := by native_decide

end Oak.AArch64CallBranchEncoding
