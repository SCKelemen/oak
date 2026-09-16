import Std.Tactic.BVDecide

/-!
# AArch64 barrier encodings

The A64 barrier words emitted by Oak, with the fixed bits and `CRm` field
generated from Arm's ISA XML.  `spec/sail/lean/Bridge.lean` proves these words
reach the corresponding clauses of Arm's Sail `decode64` and that
`system_barriers_decode` returns the operation, domain, and access types below.
-/

namespace Oak.AArch64Encoding

structure Field where
  name : String
  hi : Nat
  width : Nat
  deriving DecidableEq, Repr

structure Encoding where
  name : String
  mnemonic : String
  value : BitVec 32
  mask : BitVec 32
  fields : List Field
  deriving DecidableEq, Repr

-- OAK-A64-BARRIER-ENC-BEGIN (generated from asm/encodings_gen.go; do not edit)
def dmb : Encoding := ⟨"DMB_BO_barriers", "dmb", 0xd50330bf#32, 0xfffff0ff#32, [⟨"CRm", 11, 4⟩]⟩
def dsb : Encoding := ⟨"DSB_BO_barriers", "dsb", 0xd503309f#32, 0xfffff0ff#32, [⟨"CRm", 11, 4⟩]⟩
def isb : Encoding := ⟨"ISB_BI_barriers", "isb", 0xd50330df#32, 0xfffff0ff#32, [⟨"CRm", 11, 4⟩]⟩
-- OAK-A64-BARRIER-ENC-END

inductive MemBarrierOp where
  | dsb | dmb | isb | ssbb | pssbb | sb
  deriving DecidableEq, Repr

inductive MBReqDomain where
  | nonshareable | innerShareable | outerShareable | fullSystem
  deriving DecidableEq, Repr

inductive MBReqTypes where
  | reads | writes | all
  deriving DecidableEq, Repr

structure BarrierDecode where
  valid : Bool
  op : MemBarrierOp
  domain : MBReqDomain
  types : MBReqTypes
  deriving DecidableEq, Repr

/-- Write the four-bit barrier option into Arm's `CRm[11:8]` field. -/
def encodeCRm (encoding : Encoding) (crm : BitVec 4) : BitVec 32 :=
  (encoding.value &&& 0xfffff0ff#32) ||| (crm.setWidth 32 <<< 8)

def dmbIshld : BitVec 32 := encodeCRm dmb 0x9#4
def dmbIsh : BitVec 32 := encodeCRm dmb 0xb#4
def dmbSy : BitVec 32 := encodeCRm dmb 0xf#4
def dsbIsh : BitVec 32 := encodeCRm dsb 0xb#4
def dsbSy : BitVec 32 := encodeCRm dsb 0xf#4
def isbSy : BitVec 32 := encodeCRm isb 0xf#4

-- OAK-A64-BARRIER-WORD-BEGIN (checked against asm/encode.go; do not edit)
theorem dmb_ishld_word : dmbIshld = 0xd50339bf#32 := by native_decide
theorem dmb_ish_word : dmbIsh = 0xd5033bbf#32 := by native_decide
theorem dmb_sy_word : dmbSy = 0xd5033fbf#32 := by native_decide
theorem dsb_ish_word : dsbIsh = 0xd5033b9f#32 := by native_decide
theorem dsb_sy_word : dsbSy = 0xd5033f9f#32 := by native_decide
theorem isb_word : isbSy = 0xd5033fdf#32 := by native_decide
-- OAK-A64-BARRIER-WORD-END

def dmbIshldDecode : BarrierDecode := ⟨true, .dmb, .innerShareable, .reads⟩
def dmbIshDecode : BarrierDecode := ⟨true, .dmb, .innerShareable, .all⟩
def dmbSyDecode : BarrierDecode := ⟨true, .dmb, .fullSystem, .all⟩
def dsbIshDecode : BarrierDecode := ⟨true, .dsb, .innerShareable, .all⟩
def dsbSyDecode : BarrierDecode := ⟨true, .dsb, .fullSystem, .all⟩
def isbDecode : BarrierDecode := ⟨true, .isb, .fullSystem, .all⟩

end Oak.AArch64Encoding
