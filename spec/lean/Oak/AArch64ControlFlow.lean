import Oak.AArch64BranchExecution
import Oak.AArch64DirectBranchEncoding

/-!
# OptIR Boolean terminator routing to AArch64 bytes

The register-resident, empty-edge-copy slice of
`machine/optir_aarch64.go:optIRArm64Selector.terminator`: equal successors,
either successor placed next, or neither placed next. The last case emits
CBNZ followed by B. `checked_successor` connects the selected plan, physical
fall-through layout, actual words, and decoded no-fault transitions.

The result is a finite terminator trace ending at the selected block address,
not a whole-program interpreter. It assumes the tested W register represents
the OptIR Bool by zero/nonzero. Computing that value, allocation, spills,
edge copies, block bodies, padding, and architectural faults remain outside
this theorem. Production certificates are finite correspondence evidence.
-/

namespace Oak.AArch64ControlFlow

open Oak.AArch64BranchExecution
open Oak.AArch64ConditionalBranch
open Oak.AArch64DirectBranchEncoding
open Oak.ObjectRelocation

def offset26 (imm : BitVec 26) : BitVec 64 := (imm ++ 0#2).signExtend 64

theorem offset26_toInt (imm : BitVec 26) : (offset26 imm).toInt = imm.toInt * 4 := by
  rw [offset26, BitVec.toInt_signExtend_of_le (by omega), BitVec.toInt_append]
  simp
  omega

/-- Extend the previous projection by ordinary B, with no BL/X30 behavior. -/
def stepControl (word : BitVec 32) (s : State) : Option Transition :=
  if word &&& 0xfc000000#32 == 0x14000000#32 then
    some ⟨true, { s with pc := s.pc + offset26 (word.extractLsb' 0 26) }⟩
  else step word s

theorem stepControl_cond (kind : Kind) (rt : BitVec 5) (imm : BitVec 19) (s : State) :
    stepControl (encode kind rt imm) s = step (encode kind rt imm) s := by
  have hn : (encode kind rt imm &&& 0xfc000000#32 == 0x14000000#32) = false := by
    cases kind <;>
      simp only [encode, Kind.row, bcond, cbz32, cbz64, cbnz32, cbnz64, operand] <;> bv_decide
  simp [stepControl, hn]

theorem stepControl_direct (imm : BitVec 26) (s : State) :
    stepControl (encodeBImm26 imm) s = some ⟨true, { s with pc := s.pc + offset26 imm }⟩ := by
  have ht : encodeBImm26 imm &&& 0xfc000000#32 = 0x14000000#32 := encodeBImm26_fixed_bits imm
  simp [stepControl, ht, encodeBImm26_extract]

def jumpWord (pc target : BitVec 64) : Option (BitVec 32) :=
  if branch26Fits pc.toNat target.toNat then
    some (encodeBImm26 (branch26Immediate pc.toNat target.toNat))
  else none

theorem jumpWord_step {pc target : BitVec 64} {word : BitVec 32}
    (h : jumpWord pc target = some word) (flags : Oak.AssemblerSemantics.Flags) (regs : Registers) :
    stepControl word ⟨pc, flags, regs⟩ = some ⟨true, ⟨target, flags, regs⟩⟩ := by
  unfold jumpWord at h
  split at h
  next hf =>
    simp only [Option.some.injEq] at h
    subst word
    rw [stepControl_direct]
    have hoff : (offset26 (branch26Immediate pc.toNat target.toNat)).toInt =
        (target.toNat : Int) - pc.toNat := by
      rw [offset26_toInt, branch26Immediate_decode _ _ hf]
      rfl
    have hp : pc + offset26 (branch26Immediate pc.toNat target.toNat) = target := by
      calc
        _ = BitVec.ofInt 64 ((pc.toNat : Int) +
            (offset26 (branch26Immediate pc.toNat target.toNat)).toInt) := by
              rw [BitVec.ofInt_add]; simp
        _ = BitVec.ofInt 64 (target.toNat : Int) := by rw [hoff]; congr 1; omega
        _ = target := by simp
    simp [hp]
  next => contradiction

theorem localWord_step {kind : Kind} {rt : BitVec 5} {pc target : BitVec 64} {word : BitVec 32}
    (h : localBranch kind rt pc.toNat target.toNat = some word)
    (flags : Oak.AssemblerSemantics.Flags) (regs : Registers) :
    stepControl word ⟨pc, flags, regs⟩ =
      some (branchTo kind rt target ⟨pc, flags, regs⟩) := by
  unfold localBranch at h
  split at h
  next hf =>
    simp only [Option.some.injEq] at h
    subst word
    rw [stepControl_cond, step_encode, relocated_target _ _ hf]
    simp
  next => contradiction

inductive Plan
  | fall | jump (target : Nat) | zero (target : Nat) | nonzero (target : Nat)
  | pair (yes no : Nat)
  deriving DecidableEq, Repr

def Plan.words : Plan → Nat
  | .fall => 0
  | .pair _ _ => 2
  | _ => 1

/-- The production selector's empty-edge-copy cases, in the same order. -/
def selectPlan (yes no : Nat) (next : Option Nat) : Plan :=
  if yes = no then
    if next = some yes then .fall else .jump yes
  else if next = some yes then .zero no
  else if next = some no then .nonzero yes
  else .pair yes no

def boolValue (regs : Registers) (rt : BitVec 5) : Bool :=
  !((readX regs rt).extractLsb' 0 32 == 0#32)

def destination (p : Plan) (fall : BitVec 64) (addr : Nat → BitVec 64) (value : Bool) : BitVec 64 :=
  match p with
  | .fall => fall
  | .jump t => addr t
  | .zero t => if value then fall else addr t
  | .nonzero t => if value then addr t else fall
  | .pair yes no => if value then addr yes else addr no

def assemble (p : Plan) (pc : BitVec 64) (addr : Nat → BitVec 64) (rt : BitVec 5) :
    Option (List (BitVec 32)) :=
  match p with
  | .fall => some []
  | .jump t => (jumpWord pc (addr t)).map fun w => [w]
  | .zero t => (localBranch .cbz32 rt pc.toNat (addr t).toNat).map fun w => [w]
  | .nonzero t => (localBranch .cbnz32 rt pc.toNat (addr t).toNat).map fun w => [w]
  | .pair yes no => do
    let first ← localBranch .cbnz32 rt pc.toNat (addr yes).toNat
    let second ← jumpWord (pc + 4) (addr no)
    pure [first, second]

/-- Follow sequential instructions only on fall-through; stop on a transfer
to the successor block. This is the terminator's finite trace boundary. -/
def run : List (BitVec 32) → State → Option State
  | [], s => some s
  | word :: rest, s => do
    let t ← stepControl word s
    if t.isTaken then some t.next else run rest t.next

theorem assemble_sound (p : Plan) (pc : BitVec 64) (addr : Nat → BitVec 64) (rt : BitVec 5)
    (flags : Oak.AssemblerSemantics.Flags) (regs : Registers) {words : List (BitVec 32)}
    (h : assemble p pc addr rt = some words) :
    run words ⟨pc, flags, regs⟩ =
      some ⟨destination p (pc + BitVec.ofNat 64 (4 * p.words)) addr (boolValue regs rt), flags, regs⟩ := by
  cases p with
  | fall => simp [assemble] at h; subst words; simp [run, destination, Plan.words]
  | jump t =>
    cases hw : jumpWord pc (addr t) <;> simp [assemble, hw] at h
    next word =>
      subst words
      simp [run, jumpWord_step hw, destination]
  | zero t =>
    cases hw : localBranch .cbz32 rt pc.toNat (addr t).toNat <;> simp [assemble, hw] at h
    next word =>
      subst words
      rw [run, localWord_step hw]
      cases hc : ((readX regs rt).extractLsb' 0 32 == 0#32) <;>
        simp [branchTo, taken, boolValue, hc, destination, Plan.words, run]
  | nonzero t =>
    cases hw : localBranch .cbnz32 rt pc.toNat (addr t).toNat <;> simp [assemble, hw] at h
    next word =>
      subst words
      rw [run, localWord_step hw]
      cases hc : ((readX regs rt).extractLsb' 0 32 == 0#32) <;>
        simp [branchTo, taken, boolValue, hc, destination, Plan.words, run]
  | pair yes no =>
    cases hw : localBranch .cbnz32 rt pc.toNat (addr yes).toNat <;> simp [assemble, hw] at h
    next first =>
      cases hj : jumpWord (pc + 4#64) (addr no) <;> simp [hj] at h
      next second =>
        subst words
        rw [run, localWord_step hw]
        cases hc : ((readX regs rt).extractLsb' 0 32 == 0#32) <;>
          simp [branchTo, taken, boolValue, hc, destination, run, jumpWord_step hj]

def layoutAgrees (p : Plan) (pc : BitVec 64) (addr : Nat → BitVec 64) (next : Option Nat) : Bool :=
  match next with
  | none => true
  | some id => pc + BitVec.ofNat 64 (4 * p.words) == addr id

theorem select_destination (yes no : Nat) (next : Option Nat) (pc : BitVec 64)
    (addr : Nat → BitVec 64) (value : Bool)
    (h : layoutAgrees (selectPlan yes no next) pc addr next = true) :
    destination (selectPlan yes no next)
      (pc + BitVec.ofNat 64 (4 * (selectPlan yes no next).words)) addr value =
      if value then addr yes else addr no := by
  by_cases he : yes = no
  · subst no
    by_cases hn : next = some yes
    · subst next; simpa [selectPlan, destination, layoutAgrees, Plan.words] using h
    · simp [selectPlan, hn, destination]
  · by_cases hy : next = some yes
    · subst next
      have hp : pc + 4 = addr yes := by simpa [layoutAgrees, selectPlan, he, Plan.words] using h
      simp only [selectPlan, if_neg he, destination, Plan.words]
      change (if value then pc + 4 else addr no) = _
      rw [hp]
    · by_cases hn : next = some no
      · subst next
        have hp : pc + 4 = addr no := by simpa [layoutAgrees, selectPlan, he, hy, Plan.words] using h
        simp only [selectPlan, if_neg he, if_neg hy, destination, Plan.words]
        change (if value then addr yes else pc + 4) = _
        rw [hp]
      · simp [selectPlan, he, hy, hn, destination]

/-- A decidable certificate for one actual production terminator and layout. -/
def check (yes no : Nat) (next : Option Nat) (pc : BitVec 64)
    (addr : Nat → BitVec 64) (rt : BitVec 5) (words : List (BitVec 32)) : Bool :=
  assemble (selectPlan yes no next) pc addr rt == some words &&
    layoutAgrees (selectPlan yes no next) pc addr next

/-- All register/flag states, not just sampled Bool values, for every accepted
certificate. The source Bool must agree with `boolValue regs rt`. -/
theorem checked_successor (yes no : Nat) (next : Option Nat) (pc : BitVec 64)
    (addr : Nat → BitVec 64) (rt : BitVec 5) (words : List (BitVec 32))
    (h : check yes no next pc addr rt words = true)
    (flags : Oak.AssemblerSemantics.Flags) (regs : Registers) :
    run words ⟨pc, flags, regs⟩ =
      some ⟨if boolValue regs rt then addr yes else addr no, flags, regs⟩ := by
  simp only [check, Bool.and_eq_true, beq_iff_eq] at h
  rw [assemble_sound _ _ _ _ flags regs h.1, select_destination _ _ _ _ _ _ h.2]

end Oak.AArch64ControlFlow
