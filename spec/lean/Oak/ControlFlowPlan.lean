import Std

/-! Shared planning and layout laws for fixed-width native Bool terminators.
Instruction encoding, execution and condition provenance remain target-owned.
This module describes four-byte instructions; it does not cover RVC or Wasm. -/
namespace Oak.ControlFlowPlan

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

end Oak.ControlFlowPlan
