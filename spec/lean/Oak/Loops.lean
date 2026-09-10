/-!
# Oak.Loops — a semantics for loop termination obligations

The REPL's `:lean` command (docs/spec/83-modules.md section 10,
docs/spec/85-discipline.md section 3) turns every `OAK-D0103` obligation —
a `while` loop the discipline analysis could not bound by shape — into a
Lean theorem statement. Stating termination needs a semantics for the loop,
and this module is that semantics for the fragment the compiler translates:
integer and Boolean locals, arithmetic and comparison, Boolean connectives,
`?` conditionals, and assignments. Anything outside the fragment is reported
as untranslatable rather than approximated.

An `Env` maps variable indices to unbounded integers; every assignment wraps
its value to the variable's declared width (`Ty.wrap`), so the modeled loop
overflows exactly where the compiled program does. A `Loop` is a guard and a
*simultaneous* assignment: the translator symbolically executes the
sequential Oak body so every right-hand side reads the pre-iteration
environment (`Loop.step`). `Run L env m` is a run of `m` guarded iterations
ending with the guard false; `Terminates L env` says such a run exists.

The discharge law is `ranking_terminates`: a function into `Nat` that
strictly decreases across every guarded step proves termination from every
start, and `run_le_rank` gives the static iteration bound the discipline
profile asks for.
-/

namespace Oak.Loops

/-- Variable environments: index ↦ value. Values are unbounded; wrapping
happens at assignment. -/
abbrev Env := Nat → Int

/-- Declared representation of a loop variable: unsigned or signed of a bit
width, or Boolean. -/
inductive Ty
  | u (w : Nat)
  | s (w : Nat)
  | b
  deriving Repr, DecidableEq

/-- Wrap a value to a representation: unsigned modulo `2^w`, signed two's
complement, Boolean to `0`/`1`. -/
def Ty.wrap : Ty → Int → Int
  | .u w, v => v % ((2 : Int) ^ w)
  | .s w, v =>
    let m : Int := (2 : Int) ^ w
    let r := v % m
    if r < (2 : Int) ^ (w - 1) then r else r - m
  | .b, v => if v = 0 then 0 else 1

inductive Op
  | add | sub | mul | div | rem
  | lt | le | gt | ge | eq | ne
  | and | or
  deriving Repr, DecidableEq

/-- Expressions of the translated fragment. Booleans are integers: `0` is
false, anything else true. `wrap` is the value of a variable assigned earlier
in the same iteration, as the sequential program stored it — the translator
inserts it when substituting, so wrap-around happens where the compiled code
wraps. -/
inductive Expr
  | lit (v : Int)
  | var (i : Nat)
  | bin (op : Op) (a b : Expr)
  | not (a : Expr)
  | neg (a : Expr)
  | cond (c t e : Expr)
  | wrap (ty : Ty) (a : Expr)
  deriving Repr

def ofBool (b : Bool) : Int := if b then 1 else 0

/-- Binary operators. Division and remainder truncate toward zero as in C
(`Int.tdiv`, `Int.tmod`); the compiled program traps on a zero divisor, so
runs that reach one are outside the modeled behavior. -/
def Op.apply : Op → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a.tdiv b
  | .rem, a, b => a.tmod b
  | .lt, a, b => ofBool (decide (a < b))
  | .le, a, b => ofBool (decide (a ≤ b))
  | .gt, a, b => ofBool (decide (b < a))
  | .ge, a, b => ofBool (decide (b ≤ a))
  | .eq, a, b => ofBool (decide (a = b))
  | .ne, a, b => ofBool (decide (a ≠ b))
  | .and, a, b => ofBool (decide (a ≠ 0 ∧ b ≠ 0))
  | .or, a, b => ofBool (decide (a ≠ 0 ∨ b ≠ 0))

def Expr.eval (env : Env) : Expr → Int
  | .lit v => v
  | .var i => env i
  | .bin op a b => op.apply (a.eval env) (b.eval env)
  | .not a => ofBool (decide (a.eval env = 0))
  | .neg a => - a.eval env
  | .cond c t e => if c.eval env ≠ 0 then t.eval env else e.eval env
  | .wrap ty a => ty.wrap (a.eval env)

/-- One variable's new value per iteration, wrapped to its representation. -/
structure Assign where
  var : Nat
  ty : Ty
  value : Expr
  deriving Repr

/-- A loop: guard plus the simultaneous assignment one iteration performs.
Variables the body does not assign keep their value. -/
structure Loop where
  guard : Expr
  body : List Assign
  deriving Repr

/-- The environment after one iteration. Every right-hand side reads the
pre-iteration environment. -/
def Loop.step (L : Loop) (env : Env) : Env := fun i =>
  match L.body.find? (fun a => a.var == i) with
  | some a => a.ty.wrap (a.value.eval env)
  | none => env i

/-- The guard holds: its value is nonzero. -/
def Loop.holds (L : Loop) (env : Env) : Prop := L.guard.eval env ≠ 0

instance (L : Loop) (env : Env) : Decidable (L.holds env) := by
  unfold Loop.holds; infer_instance

/-- `Run L env m`: `m` guarded iterations from `env`, after which the guard
is false. -/
inductive Run (L : Loop) : Env → Nat → Prop
  | done {env : Env} (h : ¬ L.holds env) : Run L env 0
  | step {env : Env} {m : Nat} (h : L.holds env) (rest : Run L (L.step env) m) :
      Run L env (m + 1)

/-- The loop terminates from `env`: some finite run exists. -/
def Terminates (L : Loop) (env : Env) : Prop := ∃ m, Run L env m

/-- A ranking function that strictly decreases across guarded steps bounds
every run from an environment of rank at most `n`. -/
theorem terminates_of_rank_le (L : Loop) (rank : Env → Nat)
    (h : ∀ env, L.holds env → rank (L.step env) < rank env) :
    ∀ n env, rank env ≤ n → Terminates L env := by
  intro n
  induction n with
  | zero =>
    intro env hle
    by_cases hg : L.holds env
    · have := h env hg
      omega
    · exact ⟨0, Run.done hg⟩
  | succ n ih =>
    intro env hle
    by_cases hg : L.holds env
    · obtain ⟨m, r⟩ := ih (L.step env) (by have := h env hg; omega)
      exact ⟨m + 1, Run.step hg r⟩
    · exact ⟨0, Run.done hg⟩

/-- **Discharge law.** A ranking function into `Nat` that strictly
decreases across every guarded step proves termination from every start. -/
theorem ranking_terminates (L : Loop) (rank : Env → Nat)
    (h : ∀ env, L.holds env → rank (L.step env) < rank env) :
    ∀ env, Terminates L env :=
  fun env => terminates_of_rank_le L rank h (rank env) env (Nat.le_refl _)

/-- **Static bound.** Under a ranking function, no run from `env` is longer
than `rank env`. -/
theorem run_le_rank (L : Loop) (rank : Env → Nat)
    (h : ∀ env, L.holds env → rank (L.step env) < rank env)
    {env : Env} {m : Nat} (r : Run L env m) : m ≤ rank env := by
  induction r with
  | done _ => exact Nat.zero_le _
  | step hg _ ih =>
    have := h _ hg
    omega

/-- A loop whose guard is false everywhere terminates immediately. -/
theorem terminates_of_never_holds (L : Loop) (h : ∀ env, ¬ L.holds env) :
    ∀ env, Terminates L env :=
  fun env => ⟨0, Run.done (h env)⟩

end Oak.Loops
