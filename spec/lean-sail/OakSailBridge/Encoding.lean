import LeanRV64D
import Std.Tactic.BVDecide

-- `encdec_forwards` is a four-thousand-line match: its per-clause equation
-- lemmas do not generate within the heartbeat budget, so each theorem
-- unfolds the definition once and lets the match reduce on its constructor.
-- The word's width is a nest of `hi - lo + 1` sums the elaborator must unify
-- with 32: `congr` on the monadic `pure` does not manage it within the
-- heartbeat budget, `congrArg pure` does.

/-!
# Oak's RV64 encoder against the Sail RISC-V model's encoder

The Sail model's `encdec` mapping is the ISA's own statement of what bits
an instruction is; its Lean export spells the forward direction as
`encdec_forwards : instruction → SailM (BitVec 32)`, one clause per
instruction form. Oak's encoder (`asm/rv64_encode.go`) writes the same words
from the riscv-opcodes table (`asm/rv64_encodings_gen.go`). Each theorem
below states that, for every register number, immediate, or offset, the word
Oak writes for a mnemonic is the word the Sail model encodes for the
instruction the mnemonic spells — so the machine words are a consequence of
the ISA's specification, not only of agreement with GNU as
(`docs/spec/94-assembler.md` §9). `encdec` is a bijection by construction,
so the decoder reads them back as the same instruction.

The Oak definitions are restated verbatim (the OAK-DEF block, holding the
generated OAK-ENC table); `asm/rv64_sail_bridge_test.go` checks them
against `spec/lean/Oak/RiscV.lean` and `asm/rv64_encoding_lean_test.go`
holds the table to the encoder's.
-/

namespace OakSailBridge.Enc

open LeanRV64D
-- The export puts encdec_forwards and the operand mappings under LeanRV64D.Functions.
open LeanRV64D.Functions
open Sail

-- OAK-DEF-BEGIN
/-- One operand field of an encoding: the bits `[hi:lo]` of the word. -/
structure Field where
  name : String
  hi : Nat
  lo : Nat
  deriving Repr, DecidableEq

/-- A table entry: the fixed bits, their mask, and the operand fields. -/
structure Encoding where
  mnemonic : String
  value : BitVec 32
  mask : BitVec 32
  fields : List Field
  deriving Repr

/-- The encoder's placement of one operand (`encodeRV64Instruction`): masked
    to the field's width, truncated to the word, shifted to its low bit. -/
def placeField (word : BitVec 32) (f : Field) (v : BitVec 64) : BitVec 32 :=
  word ||| (((v &&& BitVec.ofNat 64 (2 ^ (f.hi - f.lo + 1) - 1)).truncate 32) <<< f.lo)

/-- The word of an instruction: the fixed bits with every field placed. -/
def encode (e : Encoding) (operand : String → BitVec 64) : BitVec 32 :=
  e.fields.foldl (fun word f => placeField word f (operand f.name)) e.value

/-- Register operands, as the encoder numbers them. -/
def rOperands (rd rs1 rs2 : BitVec 5) : String → BitVec 64 := fun n =>
  if n = "rd" then rd.zeroExtend 64 else if n = "rs1" then rs1.zeroExtend 64 else if n = "rs2" then rs2.zeroExtend 64 else 0

/-- An I-type immediate is the 12-bit two's complement the operand carried
    (`fields["imm12"] = value`, a signed 64-bit value masked to 12 bits). -/
def iOperands (rd rs1 : BitVec 5) (imm : BitVec 12) : String → BitVec 64 := fun n =>
  if n = "rd" then rd.zeroExtend 64 else if n = "rs1" then rs1.zeroExtend 64 else if n = "imm12" then imm.signExtend 64 else 0

/-- A shift amount (`shamtd`, 0..63). -/
def shiftOperands (rd rs1 : BitVec 5) (shamt : BitVec 6) : String → BitVec 64 := fun n =>
  if n = "rd" then rd.zeroExtend 64 else if n = "rs1" then rs1.zeroExtend 64 else if n = "shamtd" then shamt.zeroExtend 64 else 0

/-- The branch immediate's permuted halves, from the 13-bit offset `delta`
    (bit 0 always zero): `bimm12hi = delta[12] ‖ delta[10:5]`,
    `bimm12lo = delta[4:1] ‖ delta[11]` (`encodeRV64Instruction`). -/
def bimm12hi (delta : BitVec 64) : BitVec 64 :=
  (((delta >>> 12) &&& 1) <<< 6) ||| ((delta >>> 5) &&& 0x3f)
def bimm12lo (delta : BitVec 64) : BitVec 64 :=
  (((delta >>> 1) &&& 0xf) <<< 1) ||| ((delta >>> 11) &&& 1)
def bOperands (rs1 rs2 : BitVec 5) (delta : BitVec 13) : String → BitVec 64 := fun n =>
  if n = "rs1" then rs1.zeroExtend 64 else if n = "rs2" then rs2.zeroExtend 64
  else if n = "bimm12hi" then bimm12hi (delta.signExtend 64) else if n = "bimm12lo" then bimm12lo (delta.signExtend 64) else 0

-- OAK-ENC-BEGIN (generated from asm/rv64_encodings_gen.go by asm/rv64_encoding_lean_test.go; do not edit)
def add : Encoding := ⟨"add", 0x00000033#32, 0xfe00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩]⟩
def sub : Encoding := ⟨"sub", 0x40000033#32, 0xfe00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩]⟩
def sll : Encoding := ⟨"sll", 0x00001033#32, 0xfe00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩]⟩
def slt : Encoding := ⟨"slt", 0x00002033#32, 0xfe00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩]⟩
def sltu : Encoding := ⟨"sltu", 0x00003033#32, 0xfe00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩]⟩
def xor_ : Encoding := ⟨"xor", 0x00004033#32, 0xfe00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩]⟩
def srl : Encoding := ⟨"srl", 0x00005033#32, 0xfe00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩]⟩
def sra : Encoding := ⟨"sra", 0x40005033#32, 0xfe00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩]⟩
def or_ : Encoding := ⟨"or", 0x00006033#32, 0xfe00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩]⟩
def and_ : Encoding := ⟨"and", 0x00007033#32, 0xfe00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩]⟩
def addw : Encoding := ⟨"addw", 0x0000003b#32, 0xfe00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩]⟩
def subw : Encoding := ⟨"subw", 0x4000003b#32, 0xfe00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩]⟩
def sllw : Encoding := ⟨"sllw", 0x0000103b#32, 0xfe00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩]⟩
def srlw : Encoding := ⟨"srlw", 0x0000503b#32, 0xfe00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩]⟩
def sraw : Encoding := ⟨"sraw", 0x4000503b#32, 0xfe00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩]⟩
def addi : Encoding := ⟨"addi", 0x00000013#32, 0x0000707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"imm12", 31, 20⟩]⟩
def slti : Encoding := ⟨"slti", 0x00002013#32, 0x0000707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"imm12", 31, 20⟩]⟩
def sltiu : Encoding := ⟨"sltiu", 0x00003013#32, 0x0000707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"imm12", 31, 20⟩]⟩
def xori : Encoding := ⟨"xori", 0x00004013#32, 0x0000707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"imm12", 31, 20⟩]⟩
def ori : Encoding := ⟨"ori", 0x00006013#32, 0x0000707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"imm12", 31, 20⟩]⟩
def andi : Encoding := ⟨"andi", 0x00007013#32, 0x0000707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"imm12", 31, 20⟩]⟩
def slli : Encoding := ⟨"slli", 0x00001013#32, 0xfc00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"shamtd", 25, 20⟩]⟩
def srli : Encoding := ⟨"srli", 0x00005013#32, 0xfc00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"shamtd", 25, 20⟩]⟩
def srai : Encoding := ⟨"srai", 0x40005013#32, 0xfc00707f#32, [⟨"rd", 11, 7⟩, ⟨"rs1", 19, 15⟩, ⟨"shamtd", 25, 20⟩]⟩
def beq : Encoding := ⟨"beq", 0x00000063#32, 0x0000707f#32, [⟨"bimm12hi", 31, 25⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩, ⟨"bimm12lo", 11, 7⟩]⟩
def bne : Encoding := ⟨"bne", 0x00001063#32, 0x0000707f#32, [⟨"bimm12hi", 31, 25⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩, ⟨"bimm12lo", 11, 7⟩]⟩
def blt : Encoding := ⟨"blt", 0x00004063#32, 0x0000707f#32, [⟨"bimm12hi", 31, 25⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩, ⟨"bimm12lo", 11, 7⟩]⟩
def bge : Encoding := ⟨"bge", 0x00005063#32, 0x0000707f#32, [⟨"bimm12hi", 31, 25⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩, ⟨"bimm12lo", 11, 7⟩]⟩
def bltu : Encoding := ⟨"bltu", 0x00006063#32, 0x0000707f#32, [⟨"bimm12hi", 31, 25⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩, ⟨"bimm12lo", 11, 7⟩]⟩
def bgeu : Encoding := ⟨"bgeu", 0x00007063#32, 0x0000707f#32, [⟨"bimm12hi", 31, 25⟩, ⟨"rs1", 19, 15⟩, ⟨"rs2", 24, 20⟩, ⟨"bimm12lo", 11, 7⟩]⟩
-- OAK-ENC-END
-- OAK-DEF-END

/-- The register index the export spells. -/
abbrev reg (r : BitVec 5) : regidx := .Regidx r

/-! ## R-type: `funct7 ‖ rs2 ‖ rs1 ‖ funct3 ‖ rd ‖ 0110011`. -/

theorem add_encoding (rd rs1 rs2 : BitVec 5) :
    encdec_forwards (.RTYPE (reg rs2, reg rs1, reg rd, .ADD)) = pure (encode add (rOperands rd rs1 rs2)) := by
  unfold encdec_forwards
  simp only [encdec_reg_forwards, encdec_iop_forwards, encdec_bop_forwards, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
  refine congrArg pure ?_
  simp only [encode, add, placeField, List.foldl, rOperands, iOperands, shiftOperands, bOperands, bimm12hi, bimm12lo]
  bv_decide
theorem sub_encoding (rd rs1 rs2 : BitVec 5) :
    encdec_forwards (.RTYPE (reg rs2, reg rs1, reg rd, .SUB)) = pure (encode sub (rOperands rd rs1 rs2)) := by
  unfold encdec_forwards
  simp only [encdec_reg_forwards, encdec_iop_forwards, encdec_bop_forwards, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
  refine congrArg pure ?_
  simp only [encode, sub, placeField, List.foldl, rOperands, iOperands, shiftOperands, bOperands, bimm12hi, bimm12lo]
  bv_decide
theorem sll_encoding (rd rs1 rs2 : BitVec 5) :
    encdec_forwards (.RTYPE (reg rs2, reg rs1, reg rd, .SLL)) = pure (encode sll (rOperands rd rs1 rs2)) := by
  unfold encdec_forwards
  simp only [encdec_reg_forwards, encdec_iop_forwards, encdec_bop_forwards, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
  refine congrArg pure ?_
  simp only [encode, sll, placeField, List.foldl, rOperands, iOperands, shiftOperands, bOperands, bimm12hi, bimm12lo]
  bv_decide
theorem slt_encoding (rd rs1 rs2 : BitVec 5) :
    encdec_forwards (.RTYPE (reg rs2, reg rs1, reg rd, .SLT)) = pure (encode slt (rOperands rd rs1 rs2)) := by
  unfold encdec_forwards
  simp only [encdec_reg_forwards, encdec_iop_forwards, encdec_bop_forwards, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
  refine congrArg pure ?_
  simp only [encode, slt, placeField, List.foldl, rOperands, iOperands, shiftOperands, bOperands, bimm12hi, bimm12lo]
  bv_decide
theorem sltu_encoding (rd rs1 rs2 : BitVec 5) :
    encdec_forwards (.RTYPE (reg rs2, reg rs1, reg rd, .SLTU)) = pure (encode sltu (rOperands rd rs1 rs2)) := by
  unfold encdec_forwards
  simp only [encdec_reg_forwards, encdec_iop_forwards, encdec_bop_forwards, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
  refine congrArg pure ?_
  simp only [encode, sltu, placeField, List.foldl, rOperands, iOperands, shiftOperands, bOperands, bimm12hi, bimm12lo]
  bv_decide
theorem xor__encoding (rd rs1 rs2 : BitVec 5) :
    encdec_forwards (.RTYPE (reg rs2, reg rs1, reg rd, .XOR)) = pure (encode xor_ (rOperands rd rs1 rs2)) := by
  unfold encdec_forwards
  simp only [encdec_reg_forwards, encdec_iop_forwards, encdec_bop_forwards, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
  refine congrArg pure ?_
  simp only [encode, xor_, placeField, List.foldl, rOperands, iOperands, shiftOperands, bOperands, bimm12hi, bimm12lo]
  bv_decide
theorem srl_encoding (rd rs1 rs2 : BitVec 5) :
    encdec_forwards (.RTYPE (reg rs2, reg rs1, reg rd, .SRL)) = pure (encode srl (rOperands rd rs1 rs2)) := by
  unfold encdec_forwards
  simp only [encdec_reg_forwards, encdec_iop_forwards, encdec_bop_forwards, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
  refine congrArg pure ?_
  simp only [encode, srl, placeField, List.foldl, rOperands, iOperands, shiftOperands, bOperands, bimm12hi, bimm12lo]
  bv_decide
theorem sra_encoding (rd rs1 rs2 : BitVec 5) :
    encdec_forwards (.RTYPE (reg rs2, reg rs1, reg rd, .SRA)) = pure (encode sra (rOperands rd rs1 rs2)) := by
  unfold encdec_forwards
  simp only [encdec_reg_forwards, encdec_iop_forwards, encdec_bop_forwards, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
  refine congrArg pure ?_
  simp only [encode, sra, placeField, List.foldl, rOperands, iOperands, shiftOperands, bOperands, bimm12hi, bimm12lo]
  bv_decide
theorem or__encoding (rd rs1 rs2 : BitVec 5) :
    encdec_forwards (.RTYPE (reg rs2, reg rs1, reg rd, .OR)) = pure (encode or_ (rOperands rd rs1 rs2)) := by
  unfold encdec_forwards
  simp only [encdec_reg_forwards, encdec_iop_forwards, encdec_bop_forwards, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
  refine congrArg pure ?_
  simp only [encode, or_, placeField, List.foldl, rOperands, iOperands, shiftOperands, bOperands, bimm12hi, bimm12lo]
  bv_decide
theorem and__encoding (rd rs1 rs2 : BitVec 5) :
    encdec_forwards (.RTYPE (reg rs2, reg rs1, reg rd, .AND)) = pure (encode and_ (rOperands rd rs1 rs2)) := by
  unfold encdec_forwards
  simp only [encdec_reg_forwards, encdec_iop_forwards, encdec_bop_forwards, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
  refine congrArg pure ?_
  simp only [encode, and_, placeField, List.foldl, rOperands, iOperands, shiftOperands, bOperands, bimm12hi, bimm12lo]
  bv_decide
/-! ## The word forms: `‖ 0111011`. -/

theorem addw_encoding (rd rs1 rs2 : BitVec 5) :
    encdec_forwards (.RTYPEW (reg rs2, reg rs1, reg rd, .ADDW)) = pure (encode addw (rOperands rd rs1 rs2)) := by
  unfold encdec_forwards
  simp only [encdec_reg_forwards, encdec_iop_forwards, encdec_bop_forwards, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
  refine congrArg pure ?_
  simp only [encode, addw, placeField, List.foldl, rOperands, iOperands, shiftOperands, bOperands, bimm12hi, bimm12lo]
  bv_decide
theorem subw_encoding (rd rs1 rs2 : BitVec 5) :
    encdec_forwards (.RTYPEW (reg rs2, reg rs1, reg rd, .SUBW)) = pure (encode subw (rOperands rd rs1 rs2)) := by
  unfold encdec_forwards
  simp only [encdec_reg_forwards, encdec_iop_forwards, encdec_bop_forwards, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
  refine congrArg pure ?_
  simp only [encode, subw, placeField, List.foldl, rOperands, iOperands, shiftOperands, bOperands, bimm12hi, bimm12lo]
  bv_decide
theorem sllw_encoding (rd rs1 rs2 : BitVec 5) :
    encdec_forwards (.RTYPEW (reg rs2, reg rs1, reg rd, .SLLW)) = pure (encode sllw (rOperands rd rs1 rs2)) := by
  unfold encdec_forwards
  simp only [encdec_reg_forwards, encdec_iop_forwards, encdec_bop_forwards, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
  refine congrArg pure ?_
  simp only [encode, sllw, placeField, List.foldl, rOperands, iOperands, shiftOperands, bOperands, bimm12hi, bimm12lo]
  bv_decide
theorem srlw_encoding (rd rs1 rs2 : BitVec 5) :
    encdec_forwards (.RTYPEW (reg rs2, reg rs1, reg rd, .SRLW)) = pure (encode srlw (rOperands rd rs1 rs2)) := by
  unfold encdec_forwards
  simp only [encdec_reg_forwards, encdec_iop_forwards, encdec_bop_forwards, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
  refine congrArg pure ?_
  simp only [encode, srlw, placeField, List.foldl, rOperands, iOperands, shiftOperands, bOperands, bimm12hi, bimm12lo]
  bv_decide
theorem sraw_encoding (rd rs1 rs2 : BitVec 5) :
    encdec_forwards (.RTYPEW (reg rs2, reg rs1, reg rd, .SRAW)) = pure (encode sraw (rOperands rd rs1 rs2)) := by
  unfold encdec_forwards
  simp only [encdec_reg_forwards, encdec_iop_forwards, encdec_bop_forwards, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
  refine congrArg pure ?_
  simp only [encode, sraw, placeField, List.foldl, rOperands, iOperands, shiftOperands, bOperands, bimm12hi, bimm12lo]
  bv_decide
/-! ## I-type: `imm ‖ rs1 ‖ funct3 ‖ rd ‖ 0010011`. -/

theorem addi_encoding (rd rs1 : BitVec 5) (imm : BitVec 12) :
    encdec_forwards (.ITYPE (imm, reg rs1, reg rd, .ADDI)) = pure (encode addi (iOperands rd rs1 imm)) := by
  unfold encdec_forwards
  simp only [encdec_reg_forwards, encdec_iop_forwards, encdec_bop_forwards, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
  refine congrArg pure ?_
  simp only [encode, addi, placeField, List.foldl, rOperands, iOperands, shiftOperands, bOperands, bimm12hi, bimm12lo]
  bv_decide
theorem slti_encoding (rd rs1 : BitVec 5) (imm : BitVec 12) :
    encdec_forwards (.ITYPE (imm, reg rs1, reg rd, .SLTI)) = pure (encode slti (iOperands rd rs1 imm)) := by
  unfold encdec_forwards
  simp only [encdec_reg_forwards, encdec_iop_forwards, encdec_bop_forwards, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
  refine congrArg pure ?_
  simp only [encode, slti, placeField, List.foldl, rOperands, iOperands, shiftOperands, bOperands, bimm12hi, bimm12lo]
  bv_decide
theorem sltiu_encoding (rd rs1 : BitVec 5) (imm : BitVec 12) :
    encdec_forwards (.ITYPE (imm, reg rs1, reg rd, .SLTIU)) = pure (encode sltiu (iOperands rd rs1 imm)) := by
  unfold encdec_forwards
  simp only [encdec_reg_forwards, encdec_iop_forwards, encdec_bop_forwards, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
  refine congrArg pure ?_
  simp only [encode, sltiu, placeField, List.foldl, rOperands, iOperands, shiftOperands, bOperands, bimm12hi, bimm12lo]
  bv_decide
theorem xori_encoding (rd rs1 : BitVec 5) (imm : BitVec 12) :
    encdec_forwards (.ITYPE (imm, reg rs1, reg rd, .XORI)) = pure (encode xori (iOperands rd rs1 imm)) := by
  unfold encdec_forwards
  simp only [encdec_reg_forwards, encdec_iop_forwards, encdec_bop_forwards, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
  refine congrArg pure ?_
  simp only [encode, xori, placeField, List.foldl, rOperands, iOperands, shiftOperands, bOperands, bimm12hi, bimm12lo]
  bv_decide
theorem ori_encoding (rd rs1 : BitVec 5) (imm : BitVec 12) :
    encdec_forwards (.ITYPE (imm, reg rs1, reg rd, .ORI)) = pure (encode ori (iOperands rd rs1 imm)) := by
  unfold encdec_forwards
  simp only [encdec_reg_forwards, encdec_iop_forwards, encdec_bop_forwards, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
  refine congrArg pure ?_
  simp only [encode, ori, placeField, List.foldl, rOperands, iOperands, shiftOperands, bOperands, bimm12hi, bimm12lo]
  bv_decide
theorem andi_encoding (rd rs1 : BitVec 5) (imm : BitVec 12) :
    encdec_forwards (.ITYPE (imm, reg rs1, reg rd, .ANDI)) = pure (encode andi (iOperands rd rs1 imm)) := by
  unfold encdec_forwards
  simp only [encdec_reg_forwards, encdec_iop_forwards, encdec_bop_forwards, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
  refine congrArg pure ?_
  simp only [encode, andi, placeField, List.foldl, rOperands, iOperands, shiftOperands, bOperands, bimm12hi, bimm12lo]
  bv_decide
/-! ## Shifts by an immediate: `funct6 ‖ shamt ‖ rs1 ‖ funct3 ‖ rd ‖ 0010011`. -/

theorem slli_encoding (rd rs1 : BitVec 5) (shamt : BitVec 6) :
    encdec_forwards (.SHIFTIOP (shamt, reg rs1, reg rd, .SLLI)) = pure (encode slli (shiftOperands rd rs1 shamt)) := by
  unfold encdec_forwards
  simp only [encdec_reg_forwards, encdec_iop_forwards, encdec_bop_forwards, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
  refine congrArg pure ?_
  simp only [encode, slli, placeField, List.foldl, rOperands, iOperands, shiftOperands, bOperands, bimm12hi, bimm12lo]
  bv_decide
theorem srli_encoding (rd rs1 : BitVec 5) (shamt : BitVec 6) :
    encdec_forwards (.SHIFTIOP (shamt, reg rs1, reg rd, .SRLI)) = pure (encode srli (shiftOperands rd rs1 shamt)) := by
  unfold encdec_forwards
  simp only [encdec_reg_forwards, encdec_iop_forwards, encdec_bop_forwards, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
  refine congrArg pure ?_
  simp only [encode, srli, placeField, List.foldl, rOperands, iOperands, shiftOperands, bOperands, bimm12hi, bimm12lo]
  bv_decide
theorem srai_encoding (rd rs1 : BitVec 5) (shamt : BitVec 6) :
    encdec_forwards (.SHIFTIOP (shamt, reg rs1, reg rd, .SRAI)) = pure (encode srai (shiftOperands rd rs1 shamt)) := by
  unfold encdec_forwards
  simp only [encdec_reg_forwards, encdec_iop_forwards, encdec_bop_forwards, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
  refine congrArg pure ?_
  simp only [encode, srai, placeField, List.foldl, rOperands, iOperands, shiftOperands, bOperands, bimm12hi, bimm12lo]
  bv_decide
/-! ## Branches: the 13-bit offset's halves permuted as the ISA lays them out. -/

theorem beq_encoding (rs1 rs2 : BitVec 5) (delta : BitVec 13) (even : delta.extractLsb 0 0 = 0#1) :
    encdec_forwards (.BTYPE (delta, reg rs2, reg rs1, .BEQ)) = pure (encode beq (bOperands rs1 rs2 delta)) := by
  unfold encdec_forwards
  simp only [encdec_reg_forwards, encdec_iop_forwards, encdec_bop_forwards, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb, even, beq_self_eq_true, ite_true]
  refine congrArg pure ?_
  simp only [encode, beq, placeField, List.foldl, rOperands, iOperands, shiftOperands, bOperands, bimm12hi, bimm12lo]
  bv_decide
theorem bne_encoding (rs1 rs2 : BitVec 5) (delta : BitVec 13) (even : delta.extractLsb 0 0 = 0#1) :
    encdec_forwards (.BTYPE (delta, reg rs2, reg rs1, .BNE)) = pure (encode bne (bOperands rs1 rs2 delta)) := by
  unfold encdec_forwards
  simp only [encdec_reg_forwards, encdec_iop_forwards, encdec_bop_forwards, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb, even, beq_self_eq_true, ite_true]
  refine congrArg pure ?_
  simp only [encode, bne, placeField, List.foldl, rOperands, iOperands, shiftOperands, bOperands, bimm12hi, bimm12lo]
  bv_decide
theorem blt_encoding (rs1 rs2 : BitVec 5) (delta : BitVec 13) (even : delta.extractLsb 0 0 = 0#1) :
    encdec_forwards (.BTYPE (delta, reg rs2, reg rs1, .BLT)) = pure (encode blt (bOperands rs1 rs2 delta)) := by
  unfold encdec_forwards
  simp only [encdec_reg_forwards, encdec_iop_forwards, encdec_bop_forwards, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb, even, beq_self_eq_true, ite_true]
  refine congrArg pure ?_
  simp only [encode, blt, placeField, List.foldl, rOperands, iOperands, shiftOperands, bOperands, bimm12hi, bimm12lo]
  bv_decide
theorem bge_encoding (rs1 rs2 : BitVec 5) (delta : BitVec 13) (even : delta.extractLsb 0 0 = 0#1) :
    encdec_forwards (.BTYPE (delta, reg rs2, reg rs1, .BGE)) = pure (encode bge (bOperands rs1 rs2 delta)) := by
  unfold encdec_forwards
  simp only [encdec_reg_forwards, encdec_iop_forwards, encdec_bop_forwards, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb, even, beq_self_eq_true, ite_true]
  refine congrArg pure ?_
  simp only [encode, bge, placeField, List.foldl, rOperands, iOperands, shiftOperands, bOperands, bimm12hi, bimm12lo]
  bv_decide
theorem bltu_encoding (rs1 rs2 : BitVec 5) (delta : BitVec 13) (even : delta.extractLsb 0 0 = 0#1) :
    encdec_forwards (.BTYPE (delta, reg rs2, reg rs1, .BLTU)) = pure (encode bltu (bOperands rs1 rs2 delta)) := by
  unfold encdec_forwards
  simp only [encdec_reg_forwards, encdec_iop_forwards, encdec_bop_forwards, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb, even, beq_self_eq_true, ite_true]
  refine congrArg pure ?_
  simp only [encode, bltu, placeField, List.foldl, rOperands, iOperands, shiftOperands, bOperands, bimm12hi, bimm12lo]
  bv_decide
theorem bgeu_encoding (rs1 rs2 : BitVec 5) (delta : BitVec 13) (even : delta.extractLsb 0 0 = 0#1) :
    encdec_forwards (.BTYPE (delta, reg rs2, reg rs1, .BGEU)) = pure (encode bgeu (bOperands rs1 rs2 delta)) := by
  unfold encdec_forwards
  simp only [encdec_reg_forwards, encdec_iop_forwards, encdec_bop_forwards, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb, even, beq_self_eq_true, ite_true]
  refine congrArg pure ?_
  simp only [encode, bgeu, placeField, List.foldl, rOperands, iOperands, shiftOperands, bOperands, bimm12hi, bimm12lo]
  bv_decide
end OakSailBridge.Enc
