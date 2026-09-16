import Std.Tactic.BVDecide

/-!
# AArch64 direct-branch relocation semantics

This module specifies the small arithmetic and bit-patching core shared by the
AArch64 `call26`, `jump26`, and legacy `branch26` relocation spellings.  It
models only already-decoded relocation inputs: a relocation kind, one 32-bit
instruction word, and unbounded-integer place/target addresses.

The theorems below do not refine the Go object/executable writers.  In
particular, symbol resolution, section layout, addends, byte order, relocation
record emission, file-format correctness, linking, loading, and the provenance
of the instruction word remain separate obligations.
-/

namespace Oak.ObjectRelocation

/-- The two closed AArch64 direct-branch instruction classes. -/
inductive Branch26Kind where
  | call
  | jump
  deriving DecidableEq, Repr

/-- The fixed high six opcode bits of `BL` and `B`. -/
def Branch26Kind.opcode : Branch26Kind → BitVec 6
  | .call => 0b100101
  | .jump => 0b000101

/-- Decode only the three relocation spellings admitted by this slice.

The legacy `branch26` spelling has jump (`B`) rather than call (`BL`)
semantics.  Every other spelling fails closed. -/
def branch26Kind? : String → Option Branch26Kind
  | "call26" => some .call
  | "jump26" => some .jump
  | "branch26" => some .jump
  | _ => none

/-- The PC-relative byte displacement, before the architectural `/ 4`. -/
def branch26Delta (place target : Int) : Int := target - place

/-- Exact production admission: both the relocation place and resolved target
must be four-byte aligned, and their difference must lie in the signed 28-bit
byte range induced by a signed 26-bit word offset.

Checking both addresses intentionally rejects jointly misaligned equal
residues (for example, place `1` and target `5`) even though their difference
alone is divisible by four. -/
def branch26Fits (place target : Int) : Bool :=
  let delta := branch26Delta place target
  decide (place % 4 = 0 ∧ target % 4 = 0 ∧
    -(2 ^ 27) ≤ delta ∧ delta < 2 ^ 27)

/-- The instruction's fixed high-six-bit opcode field. -/
def branch26Opcode (word : BitVec 32) : BitVec 6 :=
  word.extractLsb' 26 6

/-- A call relocation may patch only `BL`; a jump relocation only `B`. -/
def branch26OpcodeMatches (kind : Branch26Kind) (word : BitVec 32) : Bool :=
  branch26Opcode word == kind.opcode

/-- Encode the signed word displacement in the low 26 bits.  This function is
used by `relocateBranch26` only after `branch26Fits` succeeds. -/
def branch26Immediate (place target : Int) : BitVec 26 :=
  BitVec.ofInt 26 (branch26Delta place target / 4)

/-- Replace exactly the low 26 bits, retaining the high opcode bits. -/
def patchBranch26 (word : BitVec 32) (immediate : BitVec 26) : BitVec 32 :=
  (word &&& 0xfc000000#32) ||| immediate.zeroExtend 32

/-- Decode the signed low-26 word displacement back to bytes. -/
def decodeBranch26 (word : BitVec 32) : Int :=
  (word.extractLsb' 0 26).toInt * 4

/-- The complete fail-closed abstract patch operation. -/
def relocateBranch26 (kind : Branch26Kind) (word : BitVec 32)
    (place target : Int) : Option (BitVec 32) :=
  if branch26Fits place target && branch26OpcodeMatches kind word then
    some (patchBranch26 word (branch26Immediate place target))
  else
    none

theorem patchBranch26_opcode (word : BitVec 32) (immediate : BitVec 26) :
    branch26Opcode (patchBranch26 word immediate) = branch26Opcode word := by
  unfold branch26Opcode patchBranch26
  bv_decide

theorem patchBranch26_immediate (word : BitVec 32) (immediate : BitVec 26) :
    (patchBranch26 word immediate).extractLsb' 0 26 = immediate := by
  unfold patchBranch26
  bv_decide

/-- Successful relocation is exactly opcode/range admission and the specified
low-26 patch; there is no additional accepting case. -/
theorem relocateBranch26_eq_some_iff (kind : Branch26Kind) (word patched : BitVec 32)
    (place target : Int) :
    relocateBranch26 kind word place target = some patched ↔
      branch26Fits place target = true ∧
      branch26OpcodeMatches kind word = true ∧
      patched = patchBranch26 word (branch26Immediate place target) := by
  unfold relocateBranch26
  by_cases hfits : branch26Fits place target = true <;>
    by_cases hopcode : branch26OpcodeMatches kind word = true <;>
      simp [hfits, hopcode, eq_comm]

/-- Existential success has exactly the mathematical signed/aligned range and
the matching instruction class. -/
theorem relocateBranch26_some_iff (kind : Branch26Kind) (word : BitVec 32)
    (place target : Int) :
    (∃ patched, relocateBranch26 kind word place target = some patched) ↔
      branch26Opcode word = kind.opcode ∧
      place % 4 = 0 ∧ target % 4 = 0 ∧
      -(2 ^ 27) ≤ branch26Delta place target ∧
      branch26Delta place target < 2 ^ 27 := by
  simp only [relocateBranch26_eq_some_iff]
  simp [branch26Fits, branch26OpcodeMatches, and_comm, and_assoc]

/-- Under the exact byte-range check, the signed 26-bit word displacement
round-trips to the original byte displacement. -/
theorem branch26Immediate_decode (place target : Int)
    (hfits : branch26Fits place target = true) :
    (branch26Immediate place target).toInt * 4 = branch26Delta place target := by
  simp only [branch26Fits, decide_eq_true_eq] at hfits
  have haligned : branch26Delta place target % 4 = 0 := by
    unfold branch26Delta
    omega
  have hlo : -(2 ^ 25) ≤ branch26Delta place target / 4 := by omega
  have hhi : branch26Delta place target / 4 < 2 ^ 25 := by omega
  have hround :
      (BitVec.ofInt 26 (branch26Delta place target / 4)).toInt =
        branch26Delta place target / 4 :=
    BitVec.toInt_ofInt_eq_self (by omega) hlo hhi
  unfold branch26Immediate
  rw [hround]
  omega

theorem decodeBranch26_patch (word : BitVec 32) (place target : Int)
    (hfits : branch26Fits place target = true) :
    decodeBranch26 (patchBranch26 word (branch26Immediate place target)) =
      branch26Delta place target := by
  simp only [decodeBranch26, patchBranch26_immediate]
  exact branch26Immediate_decode place target hfits

/-- Relocation preserves the original instruction's fixed opcode field. -/
theorem relocateBranch26_preserves_opcode {kind : Branch26Kind}
    {word patched : BitVec 32} {place target : Int}
    (h : relocateBranch26 kind word place target = some patched) :
    branch26Opcode patched = branch26Opcode word := by
  have hs := (relocateBranch26_eq_some_iff kind word patched place target).mp h
  rw [hs.2.2, patchBranch26_opcode]

/-- Admission additionally pins the preserved opcode to the selected kind. -/
theorem relocateBranch26_opcode {kind : Branch26Kind}
    {word patched : BitVec 32} {place target : Int}
    (h : relocateBranch26 kind word place target = some patched) :
    branch26Opcode patched = kind.opcode := by
  have hs := (relocateBranch26_eq_some_iff kind word patched place target).mp h
  rw [relocateBranch26_preserves_opcode h]
  simpa [branch26OpcodeMatches] using hs.2.1

/-- Decoding a successful patch recovers the admitted target-place delta. -/
theorem relocateBranch26_decode {kind : Branch26Kind}
    {word patched : BitVec 32} {place target : Int}
    (h : relocateBranch26 kind word place target = some patched) :
    decodeBranch26 patched = branch26Delta place target := by
  have hs := (relocateBranch26_eq_some_iff kind word patched place target).mp h
  rw [hs.2.2]
  exact decodeBranch26_patch word place target hs.1

/-- The patched direct branch reaches the modeled target from its place. -/
theorem relocateBranch26_reaches {kind : Branch26Kind}
    {word patched : BitVec 32} {place target : Int}
    (h : relocateBranch26 kind word place target = some patched) :
    place + decodeBranch26 patched = target := by
  rw [relocateBranch26_decode h]
  unfold branch26Delta
  omega

/-! ## Exact executable examples -/

example : branch26Kind? "call26" = some .call := by decide
example : branch26Kind? "jump26" = some .jump := by decide
example : branch26Kind? "branch26" = some .jump := by decide
example : branch26Kind? "unknown" = none := by decide

-- Exact signed lower and upper accepted byte displacements.
example : branch26Fits 0 (-(2 ^ 27)) = true := by decide
example : branch26Fits 0 (2 ^ 27 - 4) = true := by decide

-- One step outside either boundary, and a misaligned displacement, fail.
example : branch26Fits 0 (-(2 ^ 27) - 4) = false := by decide
example : branch26Fits 0 (2 ^ 27) = false := by decide
example : branch26Fits 0 2 = false := by decide

-- Production also rejects two equally misaligned addresses.
example : branch26Fits 1 5 = false := by decide

-- A call relocation refuses a `B` word even when its displacement fits.
example : relocateBranch26 .call 0x14000000#32 0 12 = none := by decide

-- `BL +12`: the signed word displacement is three and only imm26 changes.
example :
    relocateBranch26 .call 0x94000000#32 0x10000 0x1000c =
      some 0x94000003#32 := by decide

end Oak.ObjectRelocation
