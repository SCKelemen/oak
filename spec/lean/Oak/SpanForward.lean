/-!
# The register budget: single-use span locals forwarded

A span local used once, in the statement that follows its declaration, as an
argument of a call, is replaced by its defining expression at that use
(docs/spec/94-assembler.md §9 "The register budget"): the callee-saved pair
the local would have taken is not needed. The model: a small expression
language with `let`; the theorem is that `let x = a in f x`, with `x` used
once and `a` pure, evaluates as `f a`.
-/

namespace Oak.SpanForward

/-- Expressions: a variable, a literal, an application of a pure function
to an argument, a let binding. -/
inductive Expr
  | var (x : String)
  | lit (n : Nat)
  | app (f : Nat → Nat) (arg : Expr)
  | letIn (x : String) (a : Expr) (body : Expr)

/-- The environment with `x` bound. -/
def bind (env : String → Nat) (x : String) (v : Nat) : String → Nat :=
  fun y => if y = x then v else env y

/-- Evaluation: a let binds the value of `a` for the body. -/
def eval (env : String → Nat) : Expr → Nat
  | .var x => env x
  | .lit n => n
  | .app f arg => f (eval env arg)
  | .letIn x a body => eval (bind env x (eval env a)) body

/-- `e[x := a]`. -/
def subst (x : String) (a : Expr) : Expr → Expr
  | .var y => if y = x then a else .var y
  | .lit n => .lit n
  | .app f arg => .app f (subst x a arg)
  | .letIn y b body => .letIn y (subst x a b) (if y = x then body else subst x a body)

/-- The forwarded call: `let x = a in f x` is `f a`. -/
theorem let_forward (env : String → Nat) (x : String) (a : Expr) (f : Nat → Nat) :
    eval env (.letIn x a (.app f (.var x))) = eval env (.app f a) := by
  simp [eval, bind]

/-- More generally, the argument's occurrence is the let's value: the
substitution reads as the binding wherever the body only reads `x` and
does not rebind it (the forwarded span is used once, as an argument). -/
theorem eval_subst_app (env : String → Nat) (x : String) (a arg : Expr) (f : Nat → Nat)
    (h : eval env (subst x a arg) = eval (bind env x (eval env a)) arg) :
    eval env (subst x a (.app f arg)) = eval env (.letIn x a (.app f arg)) := by
  simp [eval, subst, h]

end Oak.SpanForward
