import Oak.BitwiseSource
import Oak.LoweringRefinement

/-!
# Connect the restricted source grammar to the existing typed expression model

The independent source checker resolves two distinct parameter names. Here
those two bound variables are alpha-renamed to arg0/arg1 in the pre-existing
`LoweringRefinement.Expr` model. No substituted production AST is trusted:
`grammar_evaluation` proves named source evaluation, and `lowering_success`
proves evaluation of the translated typed expression by the existing `evalX`.
Whole-language parsing, project contexts and the actual Go parser remain outside
this bridge. This is not a declaration that every Oak expression is admitted.
-/
set_option autoImplicit false
namespace Oak.BitwiseSourceLowering
open Oak.BitwiseFunction
open Oak.BitwiseSource
open Oak.LoweringRefinement

def loweringOp : Op → BitOp
  | .and => .and | .or => .or | .xor => .xor

def parameters : Params := fun name =>
  if name = "arg0" ∨ name = "arg1" then some .u32 else none

def noLocals : Locals := fun _ => none

def noSpans : Spans := fun _ => none

/-- Typed alpha-renaming by declaration position, after source name resolution. -/
def toExpr (d : Decl) : Expr parameters noSpans noLocals .u32 :=
  .bit (loweringOp d.op)
    (.var .u32 "arg0" (by simp [resolve, parameters, noLocals]))
    (.var .u32 "arg1" (by simp [resolve, parameters, noLocals])) rfl

def inputs (left right : BitVec 32) : Env := fun name =>
  if name = "arg0" then left.toNat else if name = "arg1" then right.toNat else 0

/-- Same-width bitwise evaluation in the established typed source model. No
fuel bound is needed because this translated expression has no call or loop. -/
theorem lowering_success (d : Decl) (left right : BitVec 32) (fuel : Nat) :
    evalX (toExpr d) (inputs left right) (fun _ => 0) fuel =
      some (eval d.op left right) := by
  cases op : d.op <;>
    simp [toExpr, evalX, noLocals, varX, inputs, loweringOp, bitX, eval, op, Ty.width] <;> rfl

/-- The independently checked, named source expression and the existing typed
expression interpreter agree for every input pair and every fuel. -/
theorem grammar_to_existing {source : Bytes} {d : Decl} (grammar : Grammar source d)
    (left right : BitVec 32) (fuel : Nat) :
    evaluate d left right = evalX (toExpr d) (inputs left right) (fun _ => 0) fuel := by
  rw [grammar_evaluation grammar left right, lowering_success]

/-- Original-byte grammar membership is retained in the semantic bridge. -/
theorem means_iff_existing (source : Bytes) (d : Decl)
    (left right value : BitVec 32) (fuel : Nat) :
    Means source d left right value ↔ Grammar source d ∧
      evalX (toExpr d) (inputs left right) (fun _ => 0) fuel = some value := by
  constructor
  · intro ⟨grammar, result⟩
    exact ⟨grammar, (grammar_to_existing grammar left right fuel) ▸ result⟩
  · intro ⟨grammar, result⟩
    exact ⟨grammar, (grammar_to_existing grammar left right fuel).symm ▸ result⟩

/-- An accepted actual source/module pair also has successful meaning under
that existing typed source interpreter, retaining exact original-byte grammar. -/
theorem accepted_module_existing {source bytes : Bytes} {claim : Decl}
    {target : Target} {abi : ABI}
    (accepted : BitwiseSource.accepts source claim target abi bytes = true)
    (left right : BitVec 32) (fuel : Nat) :
    Grammar source claim ∧
    evalX (toExpr claim) (inputs left right) (fun _ => 0) fuel = some (eval claim.op left right) ∧
    BitwiseModule.invokeModule claim.name bytes left right = .ok (eval claim.op left right) := by
  have result := accepted_source_to_module accepted left right
  have existing := (means_iff_existing source claim left right (eval claim.op left right) fuel).mp result.1
  exact ⟨existing.1, existing.2, result.2⟩

end Oak.BitwiseSourceLowering
