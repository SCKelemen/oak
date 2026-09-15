/-!
# Constant conditions

A conditional whose scrutinee is the literal `true` or `false` lowers as the
selected arm alone (docs/spec/94-assembler.md §9 "Constant conditions"): no
Bool is materialized and tested, no label, no dead arm. The model is the
conditional itself: `if true then a else b` is `a`, `if false then a else b`
is `b`, and a branch on a literal is taken always or never — so the emitted
arm is the value the conditional denotes, and the verifier's lowering of a
literal condition is its bit.
-/

namespace Oak.ConstantConditions

/-- `true ? a | b` is `a`. -/
theorem select_true {α : Type} (a b : α) : (if true then a else b) = a := rfl

/-- `false ? a | b` is `b`. -/
theorem select_false {α : Type} (a b : α) : (if false then a else b) = b := rfl

/-- The branch a literal condition takes: `b target` when the literal
differs from the sense that falls through (`jumpIfFalse`), nothing
otherwise — the fall-through then runs the selected arm. -/
def branchTaken (value jumpIfFalse : Bool) : Bool := value != jumpIfFalse

theorem branch_true_never_falls_when_false (jumpIfFalse : Bool) :
    branchTaken true jumpIfFalse = !jumpIfFalse := by
  cases jumpIfFalse <;> rfl

theorem branch_false_falls_when_true (jumpIfFalse : Bool) :
    branchTaken false jumpIfFalse = jumpIfFalse := by
  cases jumpIfFalse <;> rfl

/-- The verifier's bit for a literal condition. -/
def bit (value : Bool) : Nat := if value then 1 else 0

theorem bit_true : bit true = 1 := rfl
theorem bit_false : bit false = 0 := rfl

end Oak.ConstantConditions
