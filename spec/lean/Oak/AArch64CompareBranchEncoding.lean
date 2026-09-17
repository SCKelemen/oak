import Oak.AArch64Encoding

/-!
# CBZ W-register encoding

The 32-bit compare-and-branch row, including the BBM slice's `CBZ W1,+28`.
Only field packing is modeled here. The generated Sail bridge separately
checks its signed offset and zero predicate against supplied register bits;
neither layer constructs an architectural PC or executes a branch.
-/

namespace Oak.AArch64CompareBranchEncoding

open Oak.AArch64Encoding

-- OAK-A64-CBZ32-ENC-BEGIN (checked against asm/encodings_gen.go)
def cbz32 : Encoding := ⟨"CBZ_32_compbranch", "cbz", 0x34000000#32, 0xff000000#32, [⟨"sf", 31, 1⟩, ⟨"op", 24, 1⟩, ⟨"imm19", 23, 19⟩, ⟨"Rt", 4, 5⟩]⟩
-- OAK-A64-CBZ32-ENC-END

def encodeCbz32 (rt : BitVec 5) (imm19 : BitVec 19) : BitVec 32 :=
  (cbz32.value &&& cbz32.mask) ||| (imm19.zeroExtend 32 <<< 5) |||
    rt.zeroExtend 32

def bbmGuard : BitVec 32 := encodeCbz32 1#5 7#19

theorem bbm_guard_word : bbmGuard = 0x340000e1#32 := by decide

theorem encodeCbz32_fixed_bits (rt : BitVec 5) (imm19 : BitVec 19) :
    encodeCbz32 rt imm19 &&& cbz32.mask = cbz32.value := by
  unfold encodeCbz32 cbz32
  bv_decide

theorem encodeCbz32_extract_rt (rt : BitVec 5) (imm19 : BitVec 19) :
    (encodeCbz32 rt imm19).extractLsb' 0 5 = rt := by
  unfold encodeCbz32 cbz32
  bv_decide

theorem encodeCbz32_extract_imm19 (rt : BitVec 5) (imm19 : BitVec 19) :
    (encodeCbz32 rt imm19).extractLsb' 5 19 = imm19 := by
  unfold encodeCbz32 cbz32
  bv_decide

theorem cbz32_negative_endpoint_word :
    encodeCbz32 1#5 0x40000#19 = 0x34800001#32 := by decide

theorem cbz32_positive_endpoint_word :
    encodeCbz32 1#5 0x3ffff#19 = 0x347fffe1#32 := by decide

theorem cbz32_minus_four_word :
    encodeCbz32 1#5 0x7ffff#19 = 0x34ffffe1#32 := by decide

end Oak.AArch64CompareBranchEncoding
