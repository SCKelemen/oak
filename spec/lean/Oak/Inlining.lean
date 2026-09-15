/-!
# Aggregate helpers inlined

The native lane expands a small helper at its call (docs/spec/94-assembler.md
§9 "Aggregate helpers"). A parameter the callee never assigns is bound to
its argument in one of two ways: a copy declared under a fresh name, or —
when the argument is a field path whose storage nothing in the callee can
reach — the path itself substituted for the parameter at every use. The
model is a small expression language with variables; the theorem is the
substitution lemma: evaluating the body with the parameter replaced by the
argument equals evaluating the body in the environment that binds the
parameter to the argument's value (the copy), so the two bindings read
alike wherever the argument's value does not change during the body.
-/

namespace Oak.Inlining

/-- Expressions: a variable, a literal, a sum. -/
inductive Expr
  | var (x : String)
  | lit (n : Nat)
  | add (a b : Expr)

/-- Evaluation in an environment. -/
def eval (env : String → Nat) : Expr → Nat
  | .var x => env x
  | .lit n => n
  | .add a b => eval env a + eval env b

/-- `e[x := a]`: the argument for the parameter at every use. -/
def subst (x : String) (a : Expr) : Expr → Expr
  | .var y => if y = x then a else .var y
  | .lit n => .lit n
  | .add e f => .add (subst x a e) (subst x a f)

/-- The environment with `x` bound to a value: the declared copy. -/
def bind (env : String → Nat) (x : String) (v : Nat) : String → Nat :=
  fun y => if y = x then v else env y

/-- Substituting the argument reads as binding a copy of its value. -/
theorem eval_subst (env : String → Nat) (x : String) (a e : Expr) :
    eval env (subst x a e) = eval (bind env x (eval env a)) e := by
  induction e with
  | var y =>
    simp only [subst, eval, bind]
    by_cases h : y = x
    · simp [h]
    · simp [h, eval]
  | lit n => rfl
  | add e f ihe ihf => simp only [subst, eval, ihe, ihf]

end Oak.Inlining
