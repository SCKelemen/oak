import Std.Tactic.BVDecide

/-!
# AArch64 system encodings

The A64 barrier, TLBI, and PSTATE-immediate words emitted by Oak, with fields
generated from Arm's ISA XML.  `spec/sail/lean/Bridge.lean` proves these words
reach the corresponding clauses of Arm's Sail `decode64` and projects the
successful decoder results into Oak's deliberately narrow local semantics.
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

-- OAK-A64-TLBI-ENC-BEGIN (generated from asm/encodings_gen.go; do not edit)
def tlbi : Encoding := ⟨"TLBI_SYS_CR_systeminstrs", "tlbi", 0xd5088000#32, 0xfff8e000#32, [⟨"L", 21, 1⟩, ⟨"op1", 18, 3⟩, ⟨"CRn", 15, 4⟩, ⟨"CRm", 11, 4⟩, ⟨"op2", 7, 3⟩, ⟨"Rt", 4, 5⟩]⟩
-- OAK-A64-TLBI-ENC-END

-- OAK-A64-PSTATE-ENC-BEGIN (generated from asm/encodings_gen.go; do not edit)
def msrPstate : Encoding := ⟨"MSR_SI_pstate", "msr", 0xd500401f#32, 0xfff8f01f#32, [⟨"op1", 18, 3⟩, ⟨"CRm", 11, 4⟩, ⟨"op2", 7, 3⟩, ⟨"Rt", 4, 5⟩]⟩
-- OAK-A64-PSTATE-ENC-END

-- OAK-A64-SYSREG-WRITE-ENC-BEGIN (generated from asm/encodings_gen.go; do not edit)
def msrSystem : Encoding := ⟨"MSR_SR_systemmove", "msr", 0xd5100000#32, 0xfff00000#32, [⟨"L", 21, 1⟩, ⟨"o0", 19, 1⟩, ⟨"op1", 18, 3⟩, ⟨"CRn", 15, 4⟩, ⟨"CRm", 11, 4⟩, ⟨"op2", 7, 3⟩, ⟨"Rt", 4, 5⟩]⟩
-- OAK-A64-SYSREG-WRITE-ENC-END

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

/-- Fill the generated TLBI SYS encoding's table-selected fields. The caller
    must choose a tuple admitted by the generated Arm XML operand table. -/
def encodeTlbiSys (op1 : BitVec 3) (crn crm : BitVec 4)
    (op2 : BitVec 3) (rt : BitVec 5) : BitVec 32 :=
  (tlbi.value &&& tlbi.mask) |||
    (op1.setWidth 32 <<< 16) ||| (crn.setWidth 32 <<< 12) |||
    (crm.setWidth 32 <<< 8) ||| (op2.setWidth 32 <<< 5) ||| rt.setWidth 32

/-- Fill the generated PSTATE-immediate MSR encoding's table-selected fields.
    The caller must choose a tuple admitted by the generated Arm XML table. -/
def encodePstateImmediate (op1 : BitVec 3) (crm : BitVec 4)
    (op2 : BitVec 3) : BitVec 32 :=
  (msrPstate.value &&& msrPstate.mask) |||
    (op1.setWidth 32 <<< 16) ||| (crm.setWidth 32 <<< 8) |||
    (op2.setWidth 32 <<< 5)

/-- Fill the generated general system-register MSR encoding's fields. The
    caller must supply a writable tuple from the generated SysReg XML table. -/
def encodeSystemMsr (o0 : BitVec 1) (op1 : BitVec 3)
    (crn crm : BitVec 4) (op2 : BitVec 3) (rt : BitVec 5) : BitVec 32 :=
  (msrSystem.value &&& msrSystem.mask) ||| (o0.setWidth 32 <<< 19) |||
    (op1.setWidth 32 <<< 16) ||| (crn.setWidth 32 <<< 12) |||
    (crm.setWidth 32 <<< 8) ||| (op2.setWidth 32 <<< 5) ||| rt.setWidth 32

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

-- OAK-A64-TLBI-WORD-BEGIN (checked against asm/encode.go; do not edit)
def tlbiVmalls12e1is : BitVec 32 :=
  encodeTlbiSys 0b100#3 0b1000#4 0b0011#4 0b110#3 0b11111#5
theorem tlbi_vmalls12e1is_word : tlbiVmalls12e1is = 0xd50c83df#32 := by native_decide
-- OAK-A64-TLBI-WORD-END

-- OAK-A64-DAIFSET-WORD-BEGIN (checked against asm/encode.go; do not edit)
def msrDaifSetIrq : BitVec 32 :=
  encodePstateImmediate 0b011#3 0b0010#4 0b110#3
theorem msr_daifset_irq_word : msrDaifSetIrq = 0xd50342df#32 := by native_decide
-- OAK-A64-DAIFSET-WORD-END

-- OAK-A64-HCR-EL2-WORD-BEGIN (checked against asm/encode.go; do not edit)
def msrHcrEl2X0 : BitVec 32 :=
  encodeSystemMsr 0b1#1 0b100#3 0b0001#4 0b0001#4 0b000#3 0b00000#5
theorem msr_hcr_el2_x0_word : msrHcrEl2X0 = 0xd51c1100#32 := by native_decide
-- OAK-A64-HCR-EL2-WORD-END

-- OAK-A64-VTTBR-EL2-WORD-BEGIN (checked against asm/encode.go; do not edit)
def msrVttbrEl2X1 : BitVec 32 :=
  encodeSystemMsr 0b1#1 0b100#3 0b0010#4 0b0001#4 0b000#3 0b00001#5
theorem msr_vttbr_el2_x1_word : msrVttbrEl2X1 = 0xd51c2101#32 := by native_decide
-- OAK-A64-VTTBR-EL2-WORD-END

-- OAK-A64-VTCR-EL2-WORD-BEGIN (checked against asm/encode.go; do not edit)
def msrVtcrEl2X2 : BitVec 32 :=
  encodeSystemMsr 0b1#1 0b100#3 0b0010#4 0b0001#4 0b010#3 0b00010#5
theorem msr_vtcr_el2_x2_word : msrVtcrEl2X2 = 0xd51c2142#32 := by native_decide
-- OAK-A64-VTCR-EL2-WORD-END

-- OAK-A64-CNTHCTL-EL2-WORD-BEGIN (checked against asm/encode.go; do not edit)
def msrCnthctlEl2X3 : BitVec 32 :=
  encodeSystemMsr 0b1#1 0b100#3 0b1110#4 0b0001#4 0b000#3 0b00011#5
theorem msr_cnthctl_el2_x3_word : msrCnthctlEl2X3 = 0xd51ce103#32 := by native_decide
-- OAK-A64-CNTHCTL-EL2-WORD-END

def dmbIshldDecode : BarrierDecode := ⟨true, .dmb, .innerShareable, .reads⟩
def dmbIshDecode : BarrierDecode := ⟨true, .dmb, .innerShareable, .all⟩
def dmbSyDecode : BarrierDecode := ⟨true, .dmb, .fullSystem, .all⟩
def dsbIshDecode : BarrierDecode := ⟨true, .dsb, .innerShareable, .all⟩
def dsbSyDecode : BarrierDecode := ⟨true, .dsb, .fullSystem, .all⟩
def isbDecode : BarrierDecode := ⟨true, .isb, .fullSystem, .all⟩

end Oak.AArch64Encoding
