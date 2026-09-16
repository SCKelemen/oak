import Oak.AArch64Encoding
import Oak.ObjectRelocation

/-!
# AArch64 ordinary direct-branch encoding

The exact `B_only_branch_imm` instruction bits emitted by Oak, composed with
the already-proved Branch26 relocation arithmetic.  This module models only
static field packing and signed PC-relative displacement.  It does not prove
the architectural value of `PC`, execution of `BranchTo`, target validity or
mapping, source-CFG label selection, `BL`/X30 behavior, conditional branches,
or observation of a transfer.
-/

namespace Oak.AArch64DirectBranchEncoding

open Oak.AArch64Encoding
open Oak.ObjectRelocation

-- OAK-A64-B-ENC-BEGIN (generated from asm/encodings_gen.go; do not edit)
def b : Encoding := ⟨"B_only_branch_imm", "b", 0x14000000#32, 0xfc000000#32, [⟨"op", 31, 1⟩, ⟨"imm26", 25, 26⟩]⟩
-- OAK-A64-B-ENC-END

-- OAK-A64-B-WORD-BEGIN (checked against asm/encode.go; do not edit)
def encodeBImm26 (imm26 : BitVec 26) : BitVec 32 :=
  (b.value &&& b.mask) ||| imm26.zeroExtend 32
def bPlus12 : BitVec 32 := encodeBImm26 3#26
theorem b_plus_12_word : bPlus12 = 0x14000003#32 := by native_decide
-- OAK-A64-B-WORD-END

/-- Filling `imm26` changes none of the generated row's fixed bits. -/
theorem encodeBImm26_fixed_bits (imm26 : BitVec 26) :
    encodeBImm26 imm26 &&& b.mask = b.value := by
  unfold encodeBImm26 b
  bv_decide

/-- The encoded low 26 bits are exactly the supplied word displacement. -/
theorem encodeBImm26_extract (imm26 : BitVec 26) :
    (encodeBImm26 imm26).extractLsb' 0 26 = imm26 := by
  unfold encodeBImm26 b
  bv_decide

/-- Every word built from this row has the ordinary `B`, not `BL`, opcode. -/
theorem encodeBImm26_opcode (imm26 : BitVec 26) :
    branch26Opcode (encodeBImm26 imm26) = Branch26Kind.jump.opcode := by
  unfold encodeBImm26 b branch26Opcode Branch26Kind.opcode
  bv_decide

/-- The row's field packer is exactly the Branch26 low-field patch operation. -/
theorem encodeBImm26_eq_patchBranch26 (imm26 : BitVec 26) :
    encodeBImm26 imm26 = patchBranch26 b.value imm26 := by
  unfold encodeBImm26 patchBranch26 b
  bv_decide

/-- Decoding a packed field recovers its signed word displacement in bytes. -/
theorem decode_encodeBImm26 (imm26 : BitVec 26) :
    decodeBranch26 (encodeBImm26 imm26) = imm26.toInt * 4 := by
  rw [encodeBImm26_eq_patchBranch26]
  unfold decodeBranch26
  rw [patchBranch26_immediate]

/-- On the exact aligned signed range, local `B` packing is the same operation
as the proved object/executable Branch26 relocation. -/
theorem relocate_b_eq_encode (place target : Int)
    (hfits : branch26Fits place target = true) :
    relocateBranch26 .jump b.value place target =
      some (encodeBImm26 (branch26Immediate place target)) := by
  unfold relocateBranch26
  simp [hfits, branch26OpcodeMatches, branch26Opcode, Branch26Kind.opcode,
    encodeBImm26_eq_patchBranch26, b]

/-- Consequently the statically encoded displacement reaches the modeled
target.  This remains arithmetic, not an architectural execution theorem. -/
theorem encoded_b_reaches (place target : Int)
    (hfits : branch26Fits place target = true) :
    place + decodeBranch26 (encodeBImm26 (branch26Immediate place target)) =
      target := by
  rw [encodeBImm26_eq_patchBranch26,
    decodeBranch26_patch b.value place target hfits]
  unfold branch26Delta
  omega

/-! Exact signed endpoints of the admitted byte-displacement interval. -/

theorem b_negative_endpoint_word :
    encodeBImm26 0x2000000#26 = 0x16000000#32 := by native_decide

theorem b_positive_endpoint_word :
    encodeBImm26 0x1ffffff#26 = 0x15ffffff#32 := by native_decide

theorem b_minus_four_word :
    encodeBImm26 0x3ffffff#26 = 0x17ffffff#32 := by native_decide

end Oak.AArch64DirectBranchEncoding
