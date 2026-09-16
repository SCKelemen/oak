import Oak.CNFDenseAllocation

/-!
# Boolean meaning of the narrow native CNF replay operation

This is the nonnegative projection of `nativeCNFReplay.apply` in
`asm/native_bitwise_certificate.go`, including its sorted operands, exact
constant/identity/complement fold precedence, unique-table lookup and output
integer guards.  A successful replay preserves the requested Boolean
operation when the memo table denotes its gates.  This module states that
memo condition explicitly; it does not infer allocation or input provenance
from folded operands, prove the Go projection, or authorize native verdicts.
-/

set_option autoImplicit false

namespace Oak.CNFReplayApply

open Oak.RupCheck Oak.CNFDenseAllocation

/-- Edges zero and one are Boolean constants; other edges name a DIMACS
variable, complemented exactly when the edge is odd. -/
def evalEdge (assignment : Assignment) (edge : Nat) : Bool :=
  let value := if edge / 2 = 0 then false else assignment (edge / 2)
  if edge % 2 = 0 then value else !value

/-- The nonnegative arithmetic meaning of the production `edge ^ 1`. -/
def flipEdge (edge : Nat) : Nat :=
  if edge % 2 = 0 then edge + 1 else edge - 1

@[simp] theorem evalEdge_zero (assignment : Assignment) :
    evalEdge assignment 0 = false := by simp [evalEdge]

@[simp] theorem evalEdge_one (assignment : Assignment) :
    evalEdge assignment 1 = true := by simp [evalEdge]

theorem evalEdge_flip (assignment : Assignment) (edge : Nat) :
    evalEdge assignment (flipEdge edge) = !(evalEdge assignment edge) := by
  by_cases even : edge % 2 = 0
  · have quotient : (edge + 1) / 2 = edge / 2 := by omega
    have odd : (edge + 1) % 2 ≠ 0 := by omega
    simp [evalEdge, flipEdge, even, quotient, odd]
  · have quotient : (edge - 1) / 2 = edge / 2 := by omega
    have evenBefore : (edge - 1) % 2 = 0 := by omega
    simp [evalEdge, flipEdge, even, quotient, evenBefore]

theorem evalEdge_positive (assignment : Assignment) (output : Nat)
    (positive : 0 < output) :
    evalEdge assignment (2 * output) = assignment output := by
  simp [evalEdge, Nat.mul_comm, Nat.mul_div_left, Nat.ne_of_gt positive]

/-- Nonconstant replay edges agree with the signed-literal decoder used by
the checked clause trace. -/
theorem evalEdge_literal (assignment : Assignment) (edge : Nat)
    (nonconstant : 2 ≤ edge) :
    evalEdge assignment edge =
      Oak.TseitinCNF.evalLiteral assignment ⟨edge / 2, edge % 2 == 0⟩ := by
  have positive : edge / 2 ≠ 0 := by omega
  by_cases even : edge % 2 = 0
  · simp [evalEdge, Oak.TseitinCNF.evalLiteral, positive, even]
  · simp [evalEdge, Oak.TseitinCNF.evalLiteral, positive, even]

/-- Production tags zero, one and two mean AND, OR and XOR. -/
def binaryValue (op : Nat) (left right : Bool) : Bool :=
  match op with
  | 0 => left && right
  | 1 => left || right
  | 2 => xor left right
  | _ => false

theorem binaryValue_comm (op : Nat) (left right : Bool) :
    binaryValue op left right = binaryValue op right left := by
  cases op with
  | zero => cases left <;> cases right <;> rfl
  | succ op =>
      cases op with
      | zero => cases left <;> cases right <;> rfl
      | succ op =>
          cases op with
          | zero => cases left <;> cases right <;> rfl
          | succ op => rfl

/-- Every binary unique-table lookup has the Boolean meaning of its key. -/
def MemoSound (assignment : Assignment) (memo : List MemoEntry) : Prop :=
  ∀ op x y output, op < 3 →
    lookupMemo? memo (.binary op x y) = some output →
    assignment output = binaryValue op (evalEdge assignment x) (evalEdge assignment y)

/-- Inner switch, after operation admission and operand sorting. -/
def applySorted (variables maxInt : Nat) (memo : List MemoEntry)
    (op x y : Nat) : Option Nat :=
  if x = y then
    some (if op = 2 then 0 else x)
  else if flipEdge x = y then
    some (if op = 0 then 0 else 1)
  else if x = 0 then
    some (if op = 0 then 0 else y)
  else if x = 1 then
    some (if op = 0 then y else if op = 1 then 1 else flipEdge y)
  else
    match lookupMemo? memo (.binary op x y) with
    | none => none
    | some output =>
        if 0 < output ∧ output ≤ variables ∧ output ≤ maxInt / 2 then
          some (2 * output)
        else none

/-- Exact successful-result projection of the production replay, with
negative Go operands rejected before entry to this natural-number model. -/
def replayApply (variables maxInt : Nat) (memo : List MemoEntry)
    (op x y : Nat) : Option Nat :=
  if op < 3 then
    if x > y then applySorted variables maxInt memo op y x
    else applySorted variables maxInt memo op x y
  else none

private theorem op_cases {op : Nat} (admitted : op < 3) :
    op = 0 ∨ op = 1 ∨ op = 2 := by omega

theorem applySorted_sound {assignment : Assignment} {variables maxInt : Nat}
    {memo : List MemoEntry} {op x y result : Nat}
    (sound : MemoSound assignment memo) (admitted : op < 3)
    (accepted : applySorted variables maxInt memo op x y = some result) :
    evalEdge assignment result =
      binaryValue op (evalEdge assignment x) (evalEdge assignment y) := by
  unfold applySorted at accepted
  split at accepted
  · rename_i equal
    subst y
    rcases op_cases admitted with rfl | rfl | rfl
    all_goals simp only [ite_true, ite_false, reduceCtorEq, Option.some.injEq] at accepted
    all_goals subst result
    all_goals cases value : evalEdge assignment x <;> simp_all [binaryValue]
  · split at accepted
    · rename_i complement
      subst y
      rcases op_cases admitted with rfl | rfl | rfl
      all_goals simp only [ite_true, ite_false, reduceCtorEq, Option.some.injEq] at accepted
      all_goals subst result
      all_goals rw [evalEdge_flip]
      all_goals cases value : evalEdge assignment x <;> simp_all [binaryValue]
    · split at accepted
      · rename_i zero
        subst x
        rcases op_cases admitted with rfl | rfl | rfl
        all_goals simp only [ite_true, ite_false, reduceCtorEq, Option.some.injEq] at accepted
        all_goals subst result
        all_goals cases value : evalEdge assignment y <;> simp_all [binaryValue]
      · split at accepted
        · rename_i one
          subst x
          rcases op_cases admitted with rfl | rfl | rfl
          all_goals simp only [ite_true, ite_false, reduceCtorEq, Option.some.injEq] at accepted
          all_goals subst result
          all_goals cases value : evalEdge assignment y <;> simp_all [binaryValue, evalEdge_flip]
        · cases found : lookupMemo? memo (.binary op x y) with
          | none => simp [found] at accepted
          | some output =>
              simp only [found] at accepted
              split at accepted
              · rename_i range
                simp only [Option.some.injEq] at accepted
                subst result
                rw [evalEdge_positive assignment output range.1]
                exact sound op x y output admitted found
              · contradiction

theorem replayApply_admitted {variables maxInt : Nat} {memo : List MemoEntry}
    {op x y result : Nat}
    (accepted : replayApply variables maxInt memo op x y = some result) :
    op < 3 := by
  unfold replayApply at accepted
  split at accepted
  · assumption
  · contradiction

/-- Every successful result has the requested meaning.  No allocation or
range premise on folded inputs is claimed or needed. -/
theorem replayApply_sound {assignment : Assignment} {variables maxInt : Nat}
    {memo : List MemoEntry} {op x y result : Nat}
    (sound : MemoSound assignment memo)
    (accepted : replayApply variables maxInt memo op x y = some result) :
    evalEdge assignment result =
      binaryValue op (evalEdge assignment x) (evalEdge assignment y) := by
  have admitted := replayApply_admitted accepted
  unfold replayApply at accepted
  simp only [admitted, if_true] at accepted
  split at accepted
  · rw [binaryValue_comm]
    exact applySorted_sound sound admitted accepted
  · exact applySorted_sound sound admitted accepted

end Oak.CNFReplayApply
