import Oak.RiscVDirectControl

/-! Certificates for register-resident Bool terminators with empty edge copies,
ordinary four-byte instructions, and IALIGN=16. Source Bool provenance, spills,
edge copies, RVC layout, fetch and traps are separate obligations. -/
namespace Oak.RiscVControlFlow
open Oak.RiscVCallExecution Oak.RiscVBranchEncoding
open Oak.RiscVDirectControl
abbrev Registers := Reg → X
structure Transition where
  isTaken : Bool
  next : State

def boolValue (regs : Registers) (rt : Reg) : Bool :=
  decide (read ⟨0, regs⟩ rt ≠ 0#64)
def branchTo (nonzero : Bool) (rt : Reg) (target : X) (s : State) : Transition :=
  let taken := if nonzero then boolValue s.regs rt else !boolValue s.regs rt
  ⟨taken, ⟨if taken then target else s.pc + 4, s.regs⟩⟩
def stepControl (word : BitVec 32) (s : State) : Option Transition := do
  let next ← Oak.RiscVDirectControl.wide word s
  let taken := match decodeKind word with
    | some kind => (condition kind).holds (read s (word.extractLsb' 15 5)) (read s (word.extractLsb' 20 5))
    | none => true
  return ⟨taken, next⟩

def jumpWord (pc target : X) := localJ 0 pc.toNat target.toNat
def localWord (nonzero : Bool) (rt : Reg) (pc target : X) :=
  localB (if nonzero then .bne else .beq) rt 0 pc.toNat target.toNat

theorem modular_target (pc target : X) (delta : Int)
    (h : (pc.toNat : Int) + delta = target.toNat) : pc + BitVec.ofInt 64 delta = target := by
  have hv := congrArg (BitVec.ofInt 64) h
  simpa [BitVec.ofInt_add] using hv

theorem jump_not_branch (w : BitVec 32) (h : w &&& 0x7f#32 = 0x6f#32) :
    decodeKind w = none := by
  have hn : w &&& 0x707f#32 ≠ 0x63#32 ∧ w &&& 0x707f#32 ≠ 0x1063#32 ∧
      w &&& 0x707f#32 ≠ 0x4063#32 ∧ w &&& 0x707f#32 ≠ 0x5063#32 ∧
      w &&& 0x707f#32 ≠ 0x6063#32 ∧ w &&& 0x707f#32 ≠ 0x7063#32 := by bv_decide
  simp_all [decodeKind]

theorem jumpWord_step {pc target : X} {word : BitVec 32}
    (h : jumpWord pc target = some word) (regs : Registers) (hz : regs 0#5 = 0#64) :
    stepControl word ⟨pc, regs⟩ = some ⟨true, ⟨target, regs⟩⟩ := by
  have ht := modular_target pc target _ (localJ_reaches h)
  unfold jumpWord localJ at h
  split at h
  next hf =>
    simp only [Option.some.injEq] at h
    subst word
    rw [decode_encodeJ] at ht
    have hn : decodeKind (encodeJ 0#5 (BitVec.ofInt 20 (((target.toNat : Int) - pc.toNat) / 2))) = none := by
      apply jump_not_branch
      exact (encodeJ_fields 0#5 (BitVec.ofInt 20 (((target.toNat : Int) - pc.toNat) / 2))).2.2
    have hw : write ⟨pc, regs⟩ 0#5 (pc + 4#64) = regs := by
      funext r
      by_cases hr : r = 0#5 <;> simp [write, hr, hz]
    simp_all [stepControl, execute_encoded_jump, jump]
  next => contradiction

theorem localWord_step {nonzero : Bool} {rt : Reg} {pc target : X} {word : BitVec 32}
    (h : localWord nonzero rt pc target = some word) (regs : Registers) :
    stepControl word ⟨pc, regs⟩ = some (branchTo nonzero rt target ⟨pc, regs⟩) := by
  have ht := modular_target pc target _ (localB_reaches h)
  unfold localWord localB at h
  split at h
  next hf =>
    simp only [Option.some.injEq] at h
    subst word
    rw [decode_encodeB] at ht
    have fields := encodeB_fields (if nonzero then .bne else .beq) rt 0
      (BitVec.ofInt 12 (((target.toNat : Int) - pc.toNat) / 2))
    simp only [stepControl, execute_encoded_branch, decodeKind_encode, fields.2.1, fields.2.2.1]
    cases nonzero <;> simp [branch, branchTo, boolValue, condition, Oak.RiscV.Br.holds, Oak.RiscVCallExecution.read] at * <;>
      split <;> simp_all
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
  | .zero t => (localWord false rt pc (addr t)).map fun w => [w]
  | .nonzero t => (localWord true rt pc (addr t)).map fun w => [w]
  | .pair yes no => do
    let first ← localWord true rt pc (addr yes)
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
    (regs : Registers) (hz : regs 0#5 = 0#64) {words : List (BitVec 32)}
    (h : assemble p pc addr rt = some words) :
    run words ⟨pc, regs⟩ =
      some ⟨destination p (pc + BitVec.ofNat 64 (4 * p.words)) addr (boolValue regs rt), regs⟩ := by
  cases p with
  | fall => simp [assemble] at h; subst words; simp [run, destination, Plan.words]
  | jump t =>
    cases hw : jumpWord pc (addr t) <;> simp [assemble, hw] at h
    next word =>
      subst words
      simp [run, jumpWord_step hw regs hz, destination]
  | zero t =>
    cases hw : localWord false rt pc (addr t) <;> simp [assemble, hw] at h
    next word =>
      subst words
      rw [run, localWord_step hw regs]
      cases hc : (boolValue regs rt) <;>
        simp [branchTo, hc, destination, Plan.words, run]
  | nonzero t =>
    cases hw : localWord true rt pc (addr t) <;> simp [assemble, hw] at h
    next word =>
      subst words
      rw [run, localWord_step hw regs]
      cases hc : (boolValue regs rt) <;>
        simp [branchTo, hc, destination, Plan.words, run]
  | pair yes no =>
    cases hw : localWord true rt pc (addr yes) <;> simp [assemble, hw] at h
    next first =>
      cases hj : jumpWord (pc + 4#64) (addr no) <;> simp [hj] at h
      next second =>
        subst words
        rw [run, localWord_step hw regs]
        cases hc : (boolValue regs rt) <;>
          simp [branchTo, hc, destination, run, jumpWord_step hj regs hz]

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

/-- All register states, not just sampled Bool values, for every accepted
certificate. The source Bool must agree with `boolValue regs rt`. -/
theorem checked_successor (yes no : Nat) (next : Option Nat) (pc : BitVec 64)
    (addr : Nat → BitVec 64) (rt : BitVec 5) (words : List (BitVec 32))
    (h : check yes no next pc addr rt words = true)
    (regs : Registers) (hz : regs 0#5 = 0#64) :
    run words ⟨pc, regs⟩ =
      some ⟨if boolValue regs rt then addr yes else addr no, regs⟩ := by
  simp only [check, Bool.and_eq_true, beq_iff_eq] at h
  rw [assemble_sound _ _ _ _ regs hz h.1, select_destination _ _ _ _ _ _ h.2]


end Oak.RiscVControlFlow
