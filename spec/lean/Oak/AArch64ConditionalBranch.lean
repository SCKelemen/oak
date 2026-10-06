import Oak.AArch64CompareBranchEncoding

/-!
# AArch64 conditional imm19 branches

Ordinary B.cond and CBZ/CBNZ W/X field packing and exact displacement
arithmetic, including the executable writer's CONDBR19 patch operation.
The row definitions are checked against the generated Arm XML table.
The range follows AAELF64's R_AARCH64_CONDBR19 (S + A - P); this slice has
an already-resolved target and zero addend.
https://github.com/ARM-software/abi-aa/blob/main/aaelf64/aaelf64.rst

These are universal theorems about the model, with bounded production
correspondence tests. They do not prove Go/Oak implementation refinement,
condition evaluation, architectural PC, fall-through, BranchTo, traps,
source CFG selection, symbol resolution, ELF/Mach-O layout, or loading.
-/

namespace Oak.AArch64ConditionalBranch

open Oak.AArch64Encoding

-- OAK-A64-COND19-ENC-BEGIN (checked against asm/encodings_gen.go)
def bcond : Encoding := ⟨"B_only_condbranch", "b.", 0x54000000#32, 0xff000010#32, [⟨"imm19", 23, 19⟩, ⟨"o0", 4, 1⟩, ⟨"cond", 3, 4⟩]⟩
def cbz32 : Encoding := ⟨"CBZ_32_compbranch", "cbz", 0x34000000#32, 0xff000000#32, [⟨"sf", 31, 1⟩, ⟨"op", 24, 1⟩, ⟨"imm19", 23, 19⟩, ⟨"Rt", 4, 5⟩]⟩
def cbz64 : Encoding := ⟨"CBZ_64_compbranch", "cbz", 0xb4000000#32, 0xff000000#32, [⟨"sf", 31, 1⟩, ⟨"op", 24, 1⟩, ⟨"imm19", 23, 19⟩, ⟨"Rt", 4, 5⟩]⟩
def cbnz32 : Encoding := ⟨"CBNZ_32_compbranch", "cbnz", 0x35000000#32, 0xff000000#32, [⟨"sf", 31, 1⟩, ⟨"op", 24, 1⟩, ⟨"imm19", 23, 19⟩, ⟨"Rt", 4, 5⟩]⟩
def cbnz64 : Encoding := ⟨"CBNZ_64_compbranch", "cbnz", 0xb5000000#32, 0xff000000#32, [⟨"sf", 31, 1⟩, ⟨"op", 24, 1⟩, ⟨"imm19", 23, 19⟩, ⟨"Rt", 4, 5⟩]⟩
-- OAK-A64-COND19-ENC-END

inductive Kind where
  | bcond | cbz32 | cbz64 | cbnz32 | cbnz64
  deriving DecidableEq, Repr

def Kind.row : Kind → Encoding
  | .bcond => Oak.AArch64ConditionalBranch.bcond
  | .cbz32 => Oak.AArch64ConditionalBranch.cbz32
  | .cbz64 => Oak.AArch64ConditionalBranch.cbz64
  | .cbnz32 => Oak.AArch64ConditionalBranch.cbnz32
  | .cbnz64 => Oak.AArch64ConditionalBranch.cbnz64

/-- The low field is a condition (4 bits) or register (5 bits). -/
def operand (kind : Kind) (low : BitVec 5) : BitVec 32 :=
  match kind with
  | .bcond => (low.extractLsb' 0 4).zeroExtend 32
  | _ => low.zeroExtend 32

def encode (kind : Kind) (low : BitVec 5) (imm : BitVec 19) : BitVec 32 :=
  kind.row.value ||| operand kind low ||| (imm.zeroExtend 32 <<< 5)

def opcodeMatches (word : BitVec 32) : Bool :=
  (word &&& 0xff000010#32) == 0x54000000#32 ||
    (word &&& 0x7e000000#32) == 0x34000000#32

def fits (place target : Int) : Bool :=
  decide (place % 4 = 0 ∧ target % 4 = 0 ∧
    -(2 ^ 20) ≤ target - place ∧ target - place < 2 ^ 20)

def immediate (place target : Int) : BitVec 19 :=
  BitVec.ofInt 19 ((target - place) / 4)

def patch (word : BitVec 32) (imm : BitVec 19) : BitVec 32 :=
  (word &&& 0xff00001f#32) ||| (imm.zeroExtend 32 <<< 5)

def decode (word : BitVec 32) : Int :=
  (word.extractLsb' 5 19).toInt * 4

def localBranch (kind : Kind) (low : BitVec 5) (place target : Int) : Option (BitVec 32) :=
  if fits place target then some (encode kind low (immediate place target)) else none

/-- Mathematical addresses; the uint64 production domain is a subset. -/
def relocate (word : BitVec 32) (place target : Int) : Option (BitVec 32) :=
  if fits place target && opcodeMatches word then
    some (patch word (immediate place target)) else none

/-- The compact production predicate admits exactly these five table rows. -/
theorem opcodeMatches_iff_rows (word : BitVec 32) :
    opcodeMatches word =
      ((word &&& bcond.mask == bcond.value) ||
       (word &&& cbz32.mask == cbz32.value) ||
       (word &&& cbz64.mask == cbz64.value) ||
       (word &&& cbnz32.mask == cbnz32.value) ||
       (word &&& cbnz64.mask == cbnz64.value)) := by
  unfold opcodeMatches bcond cbz32 cbz64 cbnz32 cbnz64
  bv_decide

theorem encode_fields (kind : Kind) (low : BitVec 5) (imm : BitVec 19) :
    encode kind low imm &&& kind.row.mask = kind.row.value ∧
    (encode kind low imm).extractLsb' 5 19 = imm ∧
    encode kind low imm &&& 0x1f#32 = operand kind low ∧
    opcodeMatches (encode kind low imm) = true := by
  cases kind <;>
    simp only [encode, Kind.row, bcond, cbz32, cbz64, cbnz32, cbnz64,
      operand, opcodeMatches] <;> bv_decide

/-- Reuse the existing CBZ W/Sail seam without changing its meaning. -/
theorem encode_cbz32_eq_existing (rt : BitVec 5) (imm : BitVec 19) :
    encode .cbz32 rt imm = Oak.AArch64CompareBranchEncoding.encodeCbz32 rt imm := by
  unfold encode Kind.row cbz32 operand
    Oak.AArch64CompareBranchEncoding.encodeCbz32 Oak.AArch64CompareBranchEncoding.cbz32
  bv_decide

theorem patch_fields (word : BitVec 32) (imm : BitVec 19) :
    patch word imm &&& 0xff00001f#32 = word &&& 0xff00001f#32 ∧
    (patch word imm).extractLsb' 5 19 = imm ∧
    opcodeMatches (patch word imm) = opcodeMatches word := by
  unfold patch opcodeMatches
  bv_decide

theorem patch_encode (kind : Kind) (low : BitVec 5) (old imm : BitVec 19) :
    patch (encode kind low old) imm = encode kind low imm := by
  cases kind <;>
    simp only [patch, encode, Kind.row, bcond, cbz32, cbz64, cbnz32, cbnz64, operand] <;>
    bv_decide

theorem immediate_decode (place target : Int) (h : fits place target = true) :
    (immediate place target).toInt * 4 = target - place := by
  simp only [fits, decide_eq_true_eq] at h
  unfold immediate
  rw [BitVec.toInt_ofInt_eq_self (by decide)
    (show -(2 ^ 18) ≤ (target - place) / 4 by omega)
    (show (target - place) / 4 < 2 ^ 18 by omega)]
  omega

theorem local_some_iff (kind : Kind) (low : BitVec 5) (place target : Int) :
    (∃ word, localBranch kind low place target = some word) ↔ fits place target = true := by
  by_cases h : fits place target = true <;> simp [localBranch, h]

theorem local_reaches {kind : Kind} {low : BitVec 5} {place target : Int}
    {word : BitVec 32} (h : localBranch kind low place target = some word) :
    place + decode word = target := by
  unfold localBranch at h
  split at h
  next hfits =>
    simp only [Option.some.injEq] at h
    rw [← h, decode, (encode_fields kind low _).2.1, immediate_decode _ _ hfits]
    omega
  next => contradiction

theorem relocate_some_iff (word patched : BitVec 32) (place target : Int) :
    relocate word place target = some patched ↔
      fits place target = true ∧ opcodeMatches word = true ∧
      patched = patch word (immediate place target) := by
  unfold relocate
  by_cases hf : fits place target = true <;>
    by_cases ho : opcodeMatches word = true <;> simp [hf, ho, eq_comm]

theorem relocate_reaches {word patched : BitVec 32} {place target : Int}
    (h : relocate word place target = some patched) :
    place + decode patched = target := by
  have hs := (relocate_some_iff word patched place target).mp h
  rw [hs.2.2, decode, (patch_fields _ _).2.1, immediate_decode _ _ hs.1]
  omega

/-- Fixed bits include width/op, register/condition, and reserved bit 4. -/
theorem relocate_preserves_fields {word patched : BitVec 32} {place target : Int}
    (h : relocate word place target = some patched) :
    patched &&& 0xff00001f#32 = word &&& 0xff00001f#32 ∧
      opcodeMatches patched = true := by
  have hs := (relocate_some_iff word patched place target).mp h
  rw [hs.2.2]
  exact ⟨(patch_fields _ _).1, (patch_fields _ _).2.2.trans hs.2.1⟩

/-- Local assembly and relocation agree for every old immediate. -/
theorem relocate_encode_eq_local (kind : Kind) (low : BitVec 5)
    (old : BitVec 19) (place target : Int) :
    relocate (encode kind low old) place target = localBranch kind low place target := by
  simp [relocate, localBranch, (encode_fields kind low old).2.2.2, patch_encode]

def wordBytes (word : BitVec 32) : List (BitVec 8) :=
  [word.extractLsb' 0 8, word.extractLsb' 8 8,
    word.extractLsb' 16 8, word.extractLsb' 24 8]

theorem bytes_round_trip (word : BitVec 32) :
    word.extractLsb' 24 8 ++ word.extractLsb' 16 8 ++
      word.extractLsb' 8 8 ++ word.extractLsb' 0 8 = word := by
  bv_decide

end Oak.AArch64ConditionalBranch
