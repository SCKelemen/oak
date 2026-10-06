import Oak.AArch64ConditionalBranch
import Oak.ArmASL

/-!
# Decoded conditional branch transitions

This is the no-fault PC/register/NZCV projection for the five ordinary
conditional imm19 forms. It decodes the actual word, selects the register
view or flags predicate, and produces a taken/fall-through event and next PC.
PC arithmetic is 64-bit; other state components are preserved.

`ConditionHolds` is the existing ArmASL definition, already connected to the
Sail-generated function in `spec/sail/lean/Bridge.lean`. Register 31 reads
zero; W-register comparisons discard the upper 32 bits.

This does not execute Arm's complete PostDecode/BranchTo machinery. Fetch,
alignment faults, address translation, branch instrumentation, interrupts,
and the enclosing fetch loop are outside the projection. Fall-through PC+4
is the explicit sequential-fetch convention. The Go verifier correspondence
tests are finite evidence, not a universal proof of its implementation.
-/

namespace Oak.AArch64BranchExecution

open Oak.AssemblerSemantics
open Oak.AArch64ConditionalBranch

abbrev Registers := BitVec 5 → BitVec 64

def readX (regs : Registers) (rt : BitVec 5) : BitVec 64 :=
  if rt == 31#5 then 0 else regs rt

def taken (kind : Kind) (low : BitVec 5) (flags : Flags) (regs : Registers) : Bool :=
  match kind with
  | .bcond => Oak.ArmASL.ConditionHolds (low.extractLsb' 0 4) flags
  | .cbz32 => (readX regs low).extractLsb' 0 32 == 0#32
  | .cbz64 => readX regs low == 0#64
  | .cbnz32 => !((readX regs low).extractLsb' 0 32 == 0#32)
  | .cbnz64 => !(readX regs low == 0#64)

structure Decoded where
  kind : Kind
  low : BitVec 5
  imm : BitVec 19
  deriving DecidableEq, Repr

/-- Decode each fixed row independently of the field packer. -/
def decodeBranch (word : BitVec 32) : Option Decoded :=
  let low := word.extractLsb' 0 5
  let imm := word.extractLsb' 5 19
  if word &&& 0xff000010#32 == 0x54000000#32 then some ⟨.bcond, low, imm⟩
  else if word &&& 0xff000000#32 == 0x34000000#32 then some ⟨.cbz32, low, imm⟩
  else if word &&& 0xff000000#32 == 0xb4000000#32 then some ⟨.cbz64, low, imm⟩
  else if word &&& 0xff000000#32 == 0x35000000#32 then some ⟨.cbnz32, low, imm⟩
  else if word &&& 0xff000000#32 == 0xb5000000#32 then some ⟨.cbnz64, low, imm⟩
  else none

def normalizedLow (kind : Kind) (low : BitVec 5) : BitVec 5 :=
  match kind with
  | .bcond => low &&& 15#5
  | _ => low

theorem encoded_top (kind : Kind) (low : BitVec 5) (imm : BitVec 19) :
    encode kind low imm &&& 0xff000000#32 = kind.row.value := by
  cases kind <;>
    simp only [encode, Kind.row, bcond, cbz32, cbz64, cbnz32, cbnz64, operand] <;> bv_decide

theorem encoded_bcond_tag (kind : Kind) (low : BitVec 5) (imm : BitVec 19) :
    (encode kind low imm &&& 0xff000010#32 == 0x54000000#32) =
      (match kind with | .bcond => true | _ => false) := by
  cases kind <;>
    simp only [encode, Kind.row, bcond, cbz32, cbz64, cbnz32, cbnz64, operand] <;> bv_decide

theorem encoded_low (kind : Kind) (low : BitVec 5) (imm : BitVec 19) :
    (encode kind low imm).extractLsb' 0 5 = normalizedLow kind low := by
  cases kind <;>
    simp only [encode, Kind.row, bcond, cbz32, cbz64, cbnz32, cbnz64,
      operand, normalizedLow] <;> bv_decide

theorem decode_encode (kind : Kind) (low : BitVec 5) (imm : BitVec 19) :
    decodeBranch (encode kind low imm) = some ⟨kind, normalizedLow kind low, imm⟩ := by
  simp only [decodeBranch, encoded_bcond_tag, encoded_top, encoded_low,
    (encode_fields kind low imm).2.1]
  cases kind <;> rfl

theorem taken_normalized (kind : Kind) (low : BitVec 5) (flags : Flags) (regs : Registers) :
    taken kind (normalizedLow kind low) flags regs = taken kind low flags regs := by
  cases kind <;> simp only [taken, normalizedLow]
  congr 1
  bv_decide

def offset (imm : BitVec 19) : BitVec 64 := (imm ++ 0#2).signExtend 64

theorem offset_toInt (imm : BitVec 19) : (offset imm).toInt = imm.toInt * 4 := by
  rw [offset, BitVec.toInt_signExtend_of_le (by omega), BitVec.toInt_append]
  simp
  omega

structure State where
  pc : BitVec 64
  flags : Flags
  regs : Registers

structure Transition where
  isTaken : Bool
  next : State

def execute (d : Decoded) (s : State) : Transition :=
  let yes := taken d.kind d.low s.flags s.regs
  ⟨yes, { s with pc := if yes then s.pc + offset d.imm else s.pc + 4 }⟩

def step (word : BitVec 32) (s : State) : Option Transition :=
  (decodeBranch word).map (fun d => execute d s)

/-- Operand-level branch continuation, with the target already resolved. -/
def branchTo (kind : Kind) (low : BitVec 5) (target : BitVec 64) (s : State) : Transition :=
  let yes := taken kind low s.flags s.regs
  ⟨yes, { s with pc := if yes then target else s.pc + 4 }⟩

theorem step_encode (kind : Kind) (low : BitVec 5) (imm : BitVec 19) (s : State) :
    step (encode kind low imm) s = some (branchTo kind low (s.pc + offset imm) s) := by
  simp only [step, decode_encode, Option.map_some, execute, branchTo, taken_normalized]

theorem step_preserves_registers_and_flags {word : BitVec 32} {s : State} {t : Transition}
    (h : step word s = some t) : t.next.regs = s.regs ∧ t.next.flags = s.flags := by
  unfold step at h
  cases hd : decodeBranch word <;> simp [hd] at h
  subst t
  exact ⟨rfl, rfl⟩

theorem step_taken_pc {word : BitVec 32} {s : State} {t : Transition}
    (h : step word s = some t) (ht : t.isTaken = true) :
    ∃ d, decodeBranch word = some d ∧ t.next.pc = s.pc + offset d.imm := by
  unfold step at h
  cases hd : decodeBranch word <;> simp [hd] at h
  next d =>
    subst t
    change taken d.kind d.low s.flags s.regs = true at ht
    exact ⟨d, rfl, by simp [execute, ht]⟩

theorem step_fallthrough_pc {word : BitVec 32} {s : State} {t : Transition}
    (h : step word s = some t) (ht : t.isTaken = false) : t.next.pc = s.pc + 4 := by
  unfold step at h
  cases hd : decodeBranch word <;> simp [hd] at h
  next d =>
    subst t
    change taken d.kind d.low s.flags s.regs = false at ht
    simp [execute, ht]

/-- Link the previous arithmetic proof to 64-bit PC addition, including
addresses above 2^63. The target is represented modulo 2^64. -/
theorem relocated_target (pc : BitVec 64) (target : Int)
    (h : fits pc.toNat target = true) :
    pc + offset (immediate pc.toNat target) = BitVec.ofInt 64 target := by
  have hoff : (offset (immediate pc.toNat target)).toInt = target - (pc.toNat : Int) := by
    rw [offset_toInt, immediate_decode _ _ h]
  calc
    pc + offset (immediate pc.toNat target) =
        BitVec.ofInt 64 ((pc.toNat : Int) + (offset (immediate pc.toNat target)).toInt) := by
          rw [BitVec.ofInt_add]
          simp
    _ = BitVec.ofInt 64 target := by rw [hoff]; congr 1; omega

/-- The accepted bytes choose the same taken/fall-through event and complete
projected state as the operand-level branch to the resolved target. -/
theorem relocated_step {kind : Kind} {low : BitVec 5} {old patched : BitVec 32}
    {imm : BitVec 19} {target : Int} {s : State}
    (hold : old = encode kind low imm)
    (h : relocate old s.pc.toNat target = some patched) :
    step patched s = some (branchTo kind low (BitVec.ofInt 64 target) s) := by
  subst old
  have hs := (relocate_some_iff _ patched _ target).mp h
  rw [hs.2.2, patch_encode, step_encode, relocated_target _ _ hs.1]

theorem always_conditions (flags : Flags) (regs : Registers) :
    taken .bcond 14 flags regs = true ∧ taken .bcond 15 flags regs = true := by
  simp [taken, Oak.ArmASL.ConditionHolds]

theorem zero_register (flags : Flags) (regs : Registers) :
    taken .cbz32 31 flags regs = true ∧ taken .cbz64 31 flags regs = true ∧
    taken .cbnz32 31 flags regs = false ∧ taken .cbnz64 31 flags regs = false := by
  simp [taken, readX]

theorem compare_complements (rt : BitVec 5) (flags : Flags) (regs : Registers) :
    taken .cbnz32 rt flags regs = !(taken .cbz32 rt flags regs) ∧
    taken .cbnz64 rt flags regs = !(taken .cbz64 rt flags regs) := ⟨rfl, rfl⟩

/-- This composes with the existing Sail `ConditionHolds_bridge`. -/
theorem bcond_matches_verifier_condition (c : Cond) (flags : Flags) (regs : Registers) :
    taken .bcond ((Oak.ArmASL.Cond.encode c).zeroExtend 5) flags regs = c.holds flags := by
  rw [taken]
  have h : ((Oak.ArmASL.Cond.encode c).zeroExtend 5).extractLsb' 0 4 = Oak.ArmASL.Cond.encode c := by
    generalize Oak.ArmASL.Cond.encode c = b
    bv_decide
  rw [h, ← Oak.ArmASL.holds_eq_ConditionHolds]

end Oak.AArch64BranchExecution
