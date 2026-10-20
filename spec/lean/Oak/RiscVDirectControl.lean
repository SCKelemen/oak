import Oak.RiscVCallExecution
import Oak.RiscVBranchEncoding
import Oak.RiscVCompressedBranchEncoding

/-! Direct control execution under IALIGN=16. Connects the existing B/J/CB/CJ
encoding proofs to modular PC transitions and register effects. No instruction
fetch, trap, memory, or universal Go/CFG refinement is claimed. -/
namespace Oak.RiscVDirectControl
open Oak.RiscVCallExecution
open Oak.RiscVBranchEncoding Oak.RiscVCompressedBranchEncoding

def condition : Branch → Oak.RiscV.Br
  | .beq => .beq | .bne => .bne | .blt => .blt
  | .bge => .bge | .bltu => .bltu | .bgeu => .bgeu

def branch (kind : Branch) (rs1 rs2 : Reg) (delta : Int) (length : X) (s : State) : State :=
  ⟨s.pc + (if (condition kind).holds (read s rs1) (read s rs2)
    then BitVec.ofInt 64 delta else length), s.regs⟩
def jump (rd : Reg) (delta : Int) (length : X) (s : State) : State :=
  ⟨s.pc + BitVec.ofInt 64 delta, write s rd (s.pc + length)⟩

def decodeKind (word : BitVec 32) : Option Branch :=
  if word &&& 0x707f = 0x63 then some .beq
  else if word &&& 0x707f = 0x1063 then some .bne
  else if word &&& 0x707f = 0x4063 then some .blt
  else if word &&& 0x707f = 0x5063 then some .bge
  else if word &&& 0x707f = 0x6063 then some .bltu
  else if word &&& 0x707f = 0x7063 then some .bgeu
  else none

def wide (word : BitVec 32) (s : State) : Option State :=
  if word &&& 0x7f = 0x6f then some (jump (word.extractLsb' 7 5) (decodeJ word) 4 s)
  else do
    let kind ← decodeKind word
    return branch kind (word.extractLsb' 15 5) (word.extractLsb' 20 5) (decodeB word) 4 s

def short (word : BitVec 16) (s : State) : Option State :=
  let rs : Reg := 1#2 ++ word.extractLsb' 7 3
  if word &&& 0xe003 = 0xc001 then some (branch .beq rs 0 (decodeCB word) 2 s)
  else if word &&& 0xe003 = 0xe001 then some (branch .bne rs 0 (decodeCB word) 2 s)
  else if word &&& 0xe003 = 0xa001 then some (jump 0 (decodeCJ word) 2 s)
  else none

theorem branch_pc (kind : Branch) (rs1 rs2 : Reg) (delta : Int) (length : X) (s : State) :
    (branch kind rs1 rs2 delta length s).pc =
      if (condition kind).holds (read s rs1) (read s rs2)
      then s.pc + BitVec.ofInt 64 delta else s.pc + length := by
  simp only [branch]; split <;> rfl

theorem branch_preserves (kind : Branch) (rs1 rs2 : Reg) (delta : Int) (length : X) (s : State) :
    (branch kind rs1 rs2 delta length s).regs = s.regs := rfl

theorem jump_link (rd : Reg) (hr : rd ≠ 0#5) (delta : Int) (length : X) (s : State) :
    (jump rd delta length s).regs rd = s.pc + length := by simp [jump, write, hr]
theorem jump_preserves (rd r : Reg) (hz : r ≠ 0#5) (hr : r ≠ rd)
    (delta : Int) (length : X) (s : State) :
    (jump rd delta length s).regs r = s.regs r := by simp [jump, write, hz, hr]
theorem jump_zero (rd : Reg) (delta : Int) (length : X) (s : State) :
    (jump rd delta length s).regs 0 = 0 := by simp [jump, write]

theorem decodeKind_encode (kind : Branch) (rs1 rs2 : Reg) (half : BitVec 12) :
    decodeKind (encodeB kind rs1 rs2 half) = some kind := by
  have h := (encodeB_fields kind rs1 rs2 half).2.2.2
  cases kind <;> simp_all [decodeKind, Branch.row, Oak.RiscV.Enc.beq, Oak.RiscV.Enc.bne,
    Oak.RiscV.Enc.blt, Oak.RiscV.Enc.bge, Oak.RiscV.Enc.bltu, Oak.RiscV.Enc.bgeu]

theorem execute_encoded_branch (kind : Branch) (rs1 rs2 : Reg) (half : BitVec 12) (s : State) :
    wide (encodeB kind rs1 rs2 half) s = some (branch kind rs1 rs2 (half.toInt * 2) 4 s) := by
  have hf := encodeB_fields kind rs1 rs2 half
  have hn : encodeB kind rs1 rs2 half &&& 0x7f#32 ≠ 0x6f#32 := by
    have hh := hf.2.2.2
    cases kind <;> simp only [Branch.row, Oak.RiscV.Enc.beq, Oak.RiscV.Enc.bne,
      Oak.RiscV.Enc.blt, Oak.RiscV.Enc.bge, Oak.RiscV.Enc.bltu, Oak.RiscV.Enc.bgeu] at hh <;> bv_decide
  simp [wide, hn, decodeKind_encode, hf.2.1, hf.2.2.1, decode_encodeB]

theorem execute_encoded_jump (rd : Reg) (half : BitVec 20) (s : State) :
    wide (encodeJ rd half) s = some (jump rd (half.toInt * 2) 4 s) := by
  have hf := encodeJ_fields rd half
  simp only [jal] at hf
  simp [wide, hf.2.2, hf.2.1, decode_encodeJ]

theorem execute_encoded_cb (nonzero : Bool) (rs : BitVec 3) (half : BitVec 8) (s : State) :
    short (encodeCB nonzero rs half) s =
      some (branch (if nonzero then .bne else .beq) (1#2 ++ rs) 0 (half.toInt * 2) 2 s) := by
  have hf := encodeCB_fields nonzero rs half
  cases nonzero <;> simp_all [short, branchRow, cbeqz, cbnez, decode_encodeCB]

theorem execute_encoded_cj (half : BitVec 11) (s : State) :
    short (encodeCJ half) s = some (jump 0 (half.toInt * 2) 2 s) := by
  have hf := encodeCJ_fields half
  have hh : encodeCJ half &&& 0xe003#16 = 0xa001#16 := hf.2
  simp [short, hh, decode_encodeCJ]

-- One instruction, supplied as exactly two or four little-endian bytes.
def bytes (code : List (BitVec 8)) (s : State) : Option State :=
  match code with
  | [b0,b1] => if b0 &&& 3 = 3 then none else short (b1 ++ b0) s
  | [b0,b1,b2,b3] => if b0 &&& 3 = 3 then wide (b3 ++ b2 ++ b1 ++ b0) s else none
  | _ => none

def observe (code : List (BitVec 8)) (pc a b : X) (r1 r2 dest : Reg) : Option (X × X × X) := do
  let s ← bytes code ⟨pc, fun r => if r = 0#5 then 0 else if r = r1 then a else if r = r2 then b else 99⟩
  return (s.pc, s.regs dest, s.regs 0)
example : decodeKind 0x2063 = none := by decide
example : decodeKind 0x3063 = none := by decide
example : bytes [0x63,0,0] ⟨0, fun _ => 0⟩ = none := by decide
example : short 0x2001 ⟨0, fun _ => 0⟩ = none := by decide -- RV64 C.ADDIW, not C.JAL
end Oak.RiscVDirectControl
