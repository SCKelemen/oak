import Oak.RiscV

/-!
# RV64 local branch and jump encoding

B/J immediates are signed halfword displacements. These proofs connect the
pinned opcode table and operand permutation to independent field decoders,
then to exact mathematical place/target arithmetic and little-endian bytes.
The B rows already have an external Sail encoding bridge. The J row is pinned
here to riscv-opcodes; this module does not claim a new Sail execution bridge.

The model covers 32-bit instructions, including those in mixed RVC streams.
It proves displacement encoding, not instruction-address alignment, branch
conditions, JAL's link-register effect, CFG layout, compressed encodings,
linker relocations, or execution. Go correspondence is bounded test evidence,
not a universal refinement proof of the Go implementation.

ISA reference: https://docs.riscv.org/reference/isa/unpriv/rv32.html
-/

namespace Oak.RiscVBranchEncoding

open Oak.RiscV.Enc

inductive Branch where
  | beq | bne | blt | bge | bltu | bgeu
  deriving DecidableEq, Repr

def Branch.row : Branch → Encoding
  | .beq => Oak.RiscV.Enc.beq | .bne => Oak.RiscV.Enc.bne | .blt => Oak.RiscV.Enc.blt
  | .bge => Oak.RiscV.Enc.bge | .bltu => Oak.RiscV.Enc.bltu | .bgeu => Oak.RiscV.Enc.bgeu

-- OAK-RV64-J-ENC-BEGIN (generated from asm/rv64_encodings_gen.go)
def jal : Encoding := ⟨"jal", 0x0000006f#32, 0x0000007f#32, [⟨"rd", 11, 7⟩, ⟨"jimm20", 31, 12⟩]⟩
-- OAK-RV64-J-ENC-END

/-- Production J-immediate permutation, before table field placement. -/
def jimm20 (delta : BitVec 64) : BitVec 64 :=
  (((delta >>> 20) &&& 1) <<< 19) |||
  (((delta >>> 1) &&& 0x3ff) <<< 9) |||
  (((delta >>> 11) &&& 1) <<< 8) ||| ((delta >>> 12) &&& 0xff)

def jOperands (rd : BitVec 5) (delta : BitVec 21) : String → BitVec 64 := fun n =>
  if n = "rd" then rd.zeroExtend 64
  else if n = "jimm20" then jimm20 (delta.signExtend 64) else 0

/-- Encode a signed halfword displacement, guaranteeing a zero byte-offset bit 0. -/
def encodeB (kind : Branch) (rs1 rs2 : BitVec 5) (half : BitVec 12) : BitVec 32 :=
  encode kind.row (bOperands rs1 rs2 (half.signExtend 13 <<< 1))

def encodeJ (rd : BitVec 5) (half : BitVec 20) : BitVec 32 :=
  encode jal (jOperands rd (half.signExtend 21 <<< 1))

/-- Reassemble the immediate in significance order, independently of the encoder. -/
def decodeBHalf (word : BitVec 32) : BitVec 12 :=
  word.extractLsb' 31 1 ++ word.extractLsb' 7 1 ++
  word.extractLsb' 25 6 ++ word.extractLsb' 8 4

def decodeJHalf (word : BitVec 32) : BitVec 20 :=
  word.extractLsb' 31 1 ++ word.extractLsb' 12 8 ++
  word.extractLsb' 20 1 ++ word.extractLsb' 21 10

def decodeB (word : BitVec 32) : Int := (decodeBHalf word).toInt * 2
def decodeJ (word : BitVec 32) : Int := (decodeJHalf word).toInt * 2

/-- All six B forms preserve both source registers and every fixed opcode bit,
and recover every signed immediate, including the two endpoints. -/
theorem encodeB_fields (kind : Branch) (rs1 rs2 : BitVec 5) (half : BitVec 12) :
    decodeBHalf (encodeB kind rs1 rs2 half) = half ∧
    (encodeB kind rs1 rs2 half).extractLsb' 15 5 = rs1 ∧
    (encodeB kind rs1 rs2 half).extractLsb' 20 5 = rs2 ∧
    encodeB kind rs1 rs2 half &&& kind.row.mask = kind.row.value := by
  cases kind <;>
    simp only [encodeB, Branch.row, encode, placeField, List.foldl,
      bOperands, bimm12hi, bimm12lo, Oak.RiscV.Enc.beq, Oak.RiscV.Enc.bne,
      Oak.RiscV.Enc.blt, Oak.RiscV.Enc.bge, Oak.RiscV.Enc.bltu, Oak.RiscV.Enc.bgeu, decodeBHalf] <;>
    bv_decide

theorem encodeJ_fields (rd : BitVec 5) (half : BitVec 20) :
    decodeJHalf (encodeJ rd half) = half ∧
    (encodeJ rd half).extractLsb' 7 5 = rd ∧
    encodeJ rd half &&& jal.mask = jal.value := by
  simp only [encodeJ, encode, placeField, List.foldl, jOperands, jimm20,
    jal, decodeJHalf]
  bv_decide

theorem decode_encodeB (kind : Branch) (rs1 rs2 : BitVec 5) (half : BitVec 12) :
    decodeB (encodeB kind rs1 rs2 half) = half.toInt * 2 := by
  unfold decodeB
  rw [(encodeB_fields kind rs1 rs2 half).1]

theorem decode_encodeJ (rd : BitVec 5) (half : BitVec 20) :
    decodeJ (encodeJ rd half) = half.toInt * 2 := by
  unfold decodeJ
  rw [(encodeJ_fields rd half).1]

/-- Exact byte-offset admission. Individual instruction addresses/alignment
are a separate layout obligation; the encoder checks the displacement. -/
def branchFits (place target : Int) : Bool :=
  decide ((target - place) % 2 = 0 ∧ -4096 ≤ target - place ∧ target - place < 4096)

def jumpFits (place target : Int) : Bool :=
  decide ((target - place) % 2 = 0 ∧ -1048576 ≤ target - place ∧ target - place < 1048576)

def localB (kind : Branch) (rs1 rs2 : BitVec 5) (place target : Int) : Option (BitVec 32) :=
  if branchFits place target then
    some (encodeB kind rs1 rs2 (BitVec.ofInt 12 ((target - place) / 2))) else none

def localJ (rd : BitVec 5) (place target : Int) : Option (BitVec 32) :=
  if jumpFits place target then
    some (encodeJ rd (BitVec.ofInt 20 ((target - place) / 2))) else none

theorem localB_some_iff (kind : Branch) (rs1 rs2 : BitVec 5) (place target : Int) :
    (∃ word, localB kind rs1 rs2 place target = some word) ↔ branchFits place target = true := by
  by_cases h : branchFits place target = true <;> simp [localB, h]

theorem localJ_some_iff (rd : BitVec 5) (place target : Int) :
    (∃ word, localJ rd place target = some word) ↔ jumpFits place target = true := by
  by_cases h : jumpFits place target = true <;> simp [localJ, h]

/-- An accepted local branch's decoded displacement reaches the exact target
in unbounded arithmetic, so host-integer wraparound is never acceptance. -/
theorem localB_reaches {kind : Branch} {rs1 rs2 : BitVec 5} {place target : Int}
    {word : BitVec 32} (h : localB kind rs1 rs2 place target = some word) :
    place + decodeB word = target := by
  unfold localB at h
  split at h
  next hfits =>
    simp only [Option.some.injEq] at h
    rw [← h, decode_encodeB]
    simp only [branchFits, decide_eq_true_eq] at hfits
    rw [BitVec.toInt_ofInt_eq_self (by decide)
      (show -(2 ^ 11) ≤ (target - place) / 2 by omega)
      (show (target - place) / 2 < 2 ^ 11 by omega)]
    omega
  next => contradiction

theorem localJ_reaches {rd : BitVec 5} {place target : Int}
    {word : BitVec 32} (h : localJ rd place target = some word) :
    place + decodeJ word = target := by
  unfold localJ at h
  split at h
  next hfits =>
    simp only [Option.some.injEq] at h
    rw [← h, decode_encodeJ]
    simp only [jumpFits, decide_eq_true_eq] at hfits
    rw [BitVec.toInt_ofInt_eq_self (by decide)
      (show -(2 ^ 19) ≤ (target - place) / 2 by omega)
      (show (target - place) / 2 < 2 ^ 19 by omega)]
    omega
  next => contradiction

/-- Byte order used by encodeRV64Function (least significant byte first). -/
def wordBytes (word : BitVec 32) : List (BitVec 8) :=
  [word.truncate 8, (word >>> 8).truncate 8,
    (word >>> 16).truncate 8, (word >>> 24).truncate 8]

def fromBytes (b0 b1 b2 b3 : BitVec 8) : BitVec 32 := b3 ++ b2 ++ b1 ++ b0

theorem bytes_round_trip (word : BitVec 32) :
    fromBytes (word.truncate 8) ((word >>> 8).truncate 8)
      ((word >>> 16).truncate 8) ((word >>> 24).truncate 8) = word := by
  unfold fromBytes
  bv_decide

theorem branch_negative_endpoint : decodeB (encodeB .beq 0 0 0x800) = -4096 := by decide
theorem branch_positive_endpoint : decodeB (encodeB .beq 0 0 0x7ff) = 4094 := by decide
theorem jump_negative_endpoint : decodeJ (encodeJ 1 0x80000) = -1048576 := by decide
theorem jump_positive_endpoint : decodeJ (encodeJ 1 0x7ffff) = 1048574 := by decide

end Oak.RiscVBranchEncoding
