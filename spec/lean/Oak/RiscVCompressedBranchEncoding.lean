import Oak.RiscV

/-!
# RV64 compressed local branches and jumps

The pinned C.BEQZ/C.BNEZ/C.J rows and production operand permutations recover
all signed halfword displacements and preserve source registers/opcodes.
Admission uses exact mathematical subtraction, even displacement, and range.
RV64 has no C.JAL: only JAL with rd=x0 is eligible for C.J.

These are encoding proofs, not execution semantics or a universal refinement
of the Go encoder/layout algorithm. Production correspondence is tested
separately. Individual instruction-address alignment is a layout obligation.

ISA reference: https://docs.riscv.org/reference/isa/unpriv/c-st-ext.html
-/

namespace Oak.RiscVCompressedBranchEncoding

open Oak.RiscV.Enc

-- OAK-RV64-CONTROL-C-ENC-BEGIN (generated from asm/rv64_encodings_gen.go)
def cbeqz : Encoding := ⟨"c.beqz", 0x0000c001#32, 0x0000e003#32, [⟨"rs1_p", 9, 7⟩, ⟨"c_bimm9lo", 6, 2⟩, ⟨"c_bimm9hi", 12, 10⟩]⟩
def cbnez : Encoding := ⟨"c.bnez", 0x0000e001#32, 0x0000e003#32, [⟨"rs1_p", 9, 7⟩, ⟨"c_bimm9lo", 6, 2⟩, ⟨"c_bimm9hi", 12, 10⟩]⟩
def cj : Encoding := ⟨"c.j", 0x0000a001#32, 0x0000e003#32, [⟨"c_imm12", 12, 2⟩]⟩
-- OAK-RV64-CONTROL-C-ENC-END

def branchRow (nonzero : Bool) : Encoding := if nonzero then cbnez else cbeqz

def cbimmHi (delta : BitVec 64) : BitVec 64 :=
  (((delta >>> 8) &&& 1) <<< 2) ||| ((delta >>> 3) &&& 3)

def cbimmLo (delta : BitVec 64) : BitVec 64 :=
  (((delta >>> 6) &&& 3) <<< 3) ||| (((delta >>> 1) &&& 3) <<< 1) |||
  ((delta >>> 5) &&& 1)

def cjimm (delta : BitVec 64) : BitVec 64 :=
  (((delta >>> 11) &&& 1) <<< 10) ||| (((delta >>> 4) &&& 1) <<< 9) |||
  (((delta >>> 8) &&& 3) <<< 7) ||| (((delta >>> 10) &&& 1) <<< 6) |||
  (((delta >>> 6) &&& 1) <<< 5) ||| (((delta >>> 7) &&& 1) <<< 4) |||
  (((delta >>> 1) &&& 7) <<< 1) ||| ((delta >>> 5) &&& 1)

def cbOperands (rs : BitVec 3) (delta : BitVec 9) : String → BitVec 64 := fun n =>
  if n = "rs1_p" then rs.zeroExtend 64
  else if n = "c_bimm9hi" then cbimmHi (delta.signExtend 64)
  else if n = "c_bimm9lo" then cbimmLo (delta.signExtend 64) else 0

def cjOperands (delta : BitVec 12) : String → BitVec 64 := fun n =>
  if n = "c_imm12" then cjimm (delta.signExtend 64) else 0

def encodeCB (nonzero : Bool) (rs : BitVec 3) (half : BitVec 8) : BitVec 16 :=
  (encode (branchRow nonzero) (cbOperands rs (half.signExtend 9 <<< 1))).truncate 16

def encodeCJ (half : BitVec 11) : BitVec 16 :=
  (encode cj (cjOperands (half.signExtend 12 <<< 1))).truncate 16

/-- Independent decoders concatenate immediate fields in significance order. -/
def decodeCBHalf (word : BitVec 16) : BitVec 8 :=
  word.extractLsb' 12 1 ++ word.extractLsb' 5 2 ++ word.extractLsb' 2 1 ++
  word.extractLsb' 10 2 ++ word.extractLsb' 3 2

def decodeCJHalf (word : BitVec 16) : BitVec 11 :=
  word.extractLsb' 12 1 ++ word.extractLsb' 8 1 ++ word.extractLsb' 9 2 ++
  word.extractLsb' 6 1 ++ word.extractLsb' 7 1 ++ word.extractLsb' 2 1 ++
  word.extractLsb' 11 1 ++ word.extractLsb' 3 3

def decodeCB (word : BitVec 16) : Int := (decodeCBHalf word).toInt * 2
def decodeCJ (word : BitVec 16) : Int := (decodeCJHalf word).toInt * 2

/- The finite domain is small enough for kernel reduction with `decide`;
these field proofs do not use native evaluation or a SAT solver. -/
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem encodeCB_fields : ∀ (nonzero : Bool) (rs : BitVec 3) (half : BitVec 8),
    decodeCBHalf (encodeCB nonzero rs half) = half ∧
    (encodeCB nonzero rs half).extractLsb' 7 3 = rs ∧
    encodeCB nonzero rs half &&& 0xe003 = (branchRow nonzero).value.truncate 16 := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem encodeCJ_fields : ∀ (half : BitVec 11),
    decodeCJHalf (encodeCJ half) = half ∧ encodeCJ half &&& 0xe003 = 0xa001 := by
  decide

theorem decode_encodeCB (nonzero : Bool) (rs : BitVec 3) (half : BitVec 8) :
    decodeCB (encodeCB nonzero rs half) = half.toInt * 2 := by
  unfold decodeCB
  rw [(encodeCB_fields nonzero rs half).1]

theorem decode_encodeCJ (half : BitVec 11) :
    decodeCJ (encodeCJ half) = half.toInt * 2 := by
  unfold decodeCJ
  rw [(encodeCJ_fields half).1]

def branchFits (place target : Int) : Bool :=
  decide ((target - place) % 2 = 0 ∧ -256 ≤ target - place ∧ target - place < 256)

def jumpFits (place target : Int) : Bool :=
  decide ((target - place) % 2 = 0 ∧ -2048 ≤ target - place ∧ target - place < 2048)

/-- Go's operand admission is ordered: rs1 in x8..x15, rs2=x0. -/
def localCB (nonzero : Bool) (rs1 rs2 : Nat) (place target : Int) : Option (BitVec 16) :=
  if 8 ≤ rs1 ∧ rs1 < 16 ∧ rs2 = 0 ∧ branchFits place target = true then
    some (encodeCB nonzero (BitVec.ofNat 3 (rs1 - 8))
      (BitVec.ofInt 8 ((target - place) / 2))) else none

def localCJ (rd : Nat) (place target : Int) : Option (BitVec 16) :=
  if rd = 0 ∧ jumpFits place target = true then
    some (encodeCJ (BitVec.ofInt 11 ((target - place) / 2))) else none

theorem localCB_some_iff (nonzero : Bool) (rs1 rs2 : Nat) (place target : Int) :
    (∃ word, localCB nonzero rs1 rs2 place target = some word) ↔
      8 ≤ rs1 ∧ rs1 < 16 ∧ rs2 = 0 ∧ branchFits place target = true := by
  simp only [localCB]
  split <;> simp_all

theorem localCJ_some_iff (rd : Nat) (place target : Int) :
    (∃ word, localCJ rd place target = some word) ↔ rd = 0 ∧ jumpFits place target = true := by
  simp only [localCJ]
  split <;> simp_all

theorem localCB_reaches {nonzero : Bool} {rs1 rs2 : Nat} {place target : Int}
    {word : BitVec 16} (h : localCB nonzero rs1 rs2 place target = some word) :
    place + decodeCB word = target := by
  unfold localCB at h
  split at h
  next hfits =>
    simp only [Option.some.injEq] at h
    rw [← h, decode_encodeCB]
    simp only [branchFits, decide_eq_true_eq] at hfits
    rw [BitVec.toInt_ofInt_eq_self (by decide)
      (show -(2 ^ 7) ≤ (target - place) / 2 by omega)
      (show (target - place) / 2 < 2 ^ 7 by omega)]
    omega
  next => contradiction

theorem localCJ_reaches {rd : Nat} {place target : Int}
    {word : BitVec 16} (h : localCJ rd place target = some word) :
    place + decodeCJ word = target := by
  unfold localCJ at h
  split at h
  next hfits =>
    simp only [Option.some.injEq] at h
    rw [← h, decode_encodeCJ]
    simp only [jumpFits, decide_eq_true_eq] at hfits
    rw [BitVec.toInt_ofInt_eq_self (by decide)
      (show -(2 ^ 10) ≤ (target - place) / 2 by omega)
      (show (target - place) / 2 < 2 ^ 10 by omega)]
    omega
  next => contradiction

theorem localCB_register {nonzero : Bool} {rs1 rs2 : Nat} {place target : Int}
    {word : BitVec 16} (h : localCB nonzero rs1 rs2 place target = some word) :
    (word.extractLsb' 7 3).toNat + 8 = rs1 := by
  unfold localCB at h
  split at h
  next hfits =>
    simp only [Option.some.injEq] at h
    rw [← h, (encodeCB_fields _ _ _).2.1]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show rs1 - 8 < 2 ^ 3 by omega)]
    omega
  next => contradiction

/-- Least-significant byte first, matching the function writer. -/
def wordBytes (word : BitVec 16) : List (BitVec 8) :=
  [word.extractLsb' 0 8, word.extractLsb' 8 8]

def fromBytes (b0 b1 : BitVec 8) : BitVec 16 := b1 ++ b0

theorem bytes_round_trip (word : BitVec 16) :
    fromBytes (word.extractLsb' 0 8) (word.extractLsb' 8 8) = word := by
  exact BitVec.extractLsb'_append_extractLsb'

end Oak.RiscVCompressedBranchEncoding
