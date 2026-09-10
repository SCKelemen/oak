/-!
# Oak.Loops — a semantics for loop termination obligations

The REPL's `:lean` command (docs/spec/83-modules.md section 10,
docs/spec/85-discipline.md section 3) turns every `OAK-D0103` obligation —
a `while` loop the discipline analysis could not bound by shape — into a
Lean theorem statement. Stating termination needs a semantics for the loop,
and this module is that semantics for the fragment the compiler translates:
integer and Boolean locals, arithmetic and comparison, Boolean connectives,
`?` conditionals, assignments, loop-local declarations, array reads and
writes, records, and calls (inlined when the callee is an expression-bodied
function of the fragment, otherwise uninterpreted). Records never reach this
semantics: the translator flattens a record into one variable per scalar
leaf (`p.v`) and an array of records into one memory per leaf (`cs.v`), so a
field store is a variable assignment and a field read a variable. Anything
outside the fragment is reported as untranslatable rather than approximated.

A `State` is the variables (index ↦ unbounded integer) and the memory
(array ↦ index ↦ value). Oak's fixed-width arithmetic is total and wraps at
every operation (docs/spec/20-types.md section 11.1), so the translator wraps
each arithmetic result and each stored value to its representation
(`Expr.wrap`, `Ty.wrap`); intermediate values are unbounded only where the
program's are. A `Loop` is a guard, a *simultaneous* assignment of variables,
and an ordered list of array writes; the translator symbolically executes
the sequential Oak body so every right-hand side reads the pre-iteration
state (`Loop.step`). Calls the translator could not inline are uninterpreted
functions `Funs`, a parameter of every statement: the programmer constrains
them with hypotheses. `Run F L s m` is a run of `m` guarded iterations ending
with the guard false; `Terminates F L s` says such a run exists.

The discharge law is `ranking_terminates`: a function into `Nat` that
strictly decreases across every guarded step proves termination from every
start, and `run_le_rank` gives the static iteration bound the discipline
profile asks for.
-/

namespace Oak.Loops

/-- Variables: index ↦ value. Values are unbounded; wrapping happens at
arithmetic and at storage. -/
abbrev Vars := Nat → Int

/-- Memory: array ↦ element index ↦ value. -/
abbrev Mem := Nat → Int → Int

/-- Uninterpreted functions the loop calls: function ↦ arguments ↦ result. -/
abbrev Funs := Nat → List Int → Int

structure State where
  vars : Vars
  mem : Mem

/-- Declared representation of a value: unsigned or signed of a bit width, or
Boolean. -/
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
false, anything else true. `wrap` is a value at its representation — an
arithmetic result, or a variable assigned earlier in the same iteration as
the program stored it. `index` reads memory; `call` is an uninterpreted
function. -/
inductive Expr
  | lit (v : Int)
  | var (i : Nat)
  | bin (op : Op) (a b : Expr)
  | not (a : Expr)
  | neg (a : Expr)
  | cond (c t e : Expr)
  | wrap (ty : Ty) (a : Expr)
  | index (arr : Nat) (i : Expr)
  | call (f : Nat) (args : List Expr)
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

def Expr.eval (F : Funs) (s : State) : Expr → Int
  | .lit v => v
  | .var i => s.vars i
  | .bin op a b => op.apply (a.eval F s) (b.eval F s)
  | .not a => ofBool (decide (a.eval F s = 0))
  | .neg a => - a.eval F s
  | .cond c t e => if c.eval F s ≠ 0 then t.eval F s else e.eval F s
  | .wrap ty a => ty.wrap (a.eval F s)
  | .index arr i => s.mem arr (i.eval F s)
  | .call f args => F f (args.attach.map fun ⟨a, _⟩ => a.eval F s)
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals try omega
  · rename_i h
    have := List.sizeOf_lt_of_mem h
    omega

/-- One variable's new value per iteration, wrapped to its representation. -/
structure Assign where
  var : Nat
  ty : Ty
  value : Expr
  deriving Repr

/-- One array store per iteration: `arr[index] = value`, the value wrapped
to the element representation. Index and value read the pre-iteration
state. -/
structure Write where
  arr : Nat
  ty : Ty
  index : Expr
  value : Expr
  deriving Repr

/-- A loop: guard, the simultaneous assignment one iteration performs, and
its array writes in program order (a later write to the same cell wins).
Variables the body does not assign and cells it does not write keep their
values. -/
structure Loop where
  guard : Expr
  body : List Assign
  writes : List Write
  deriving Repr

/-- Apply one write, evaluated against the pre-iteration state `s`, to
memory `m`. -/
def Write.apply (F : Funs) (s : State) (w : Write) (m : Mem) : Mem :=
  fun a j => if a = w.arr ∧ j = w.index.eval F s then w.ty.wrap (w.value.eval F s) else m a j

/-- The state after one iteration. Every right-hand side reads the
pre-iteration state. -/
def Loop.step (F : Funs) (L : Loop) (s : State) : State :=
  { vars := fun i =>
      match L.body.find? (fun a => a.var == i) with
      | some a => a.ty.wrap (a.value.eval F s)
      | none => s.vars i,
    mem := L.writes.foldl (fun m w => w.apply F s m) s.mem }

/-- The guard holds: its value is nonzero. -/
def Loop.holds (F : Funs) (L : Loop) (s : State) : Prop := L.guard.eval F s ≠ 0

instance (F : Funs) (L : Loop) (s : State) : Decidable (L.holds F s) := by
  unfold Loop.holds; infer_instance

/-- `Run F L s m`: `m` guarded iterations from `s`, after which the guard is
false. -/
inductive Run (F : Funs) (L : Loop) : State → Nat → Prop
  | done {s : State} (h : ¬ L.holds F s) : Run F L s 0
  | step {s : State} {m : Nat} (h : L.holds F s) (rest : Run F L (L.step F s) m) :
      Run F L s (m + 1)

/-- The loop terminates from `s`: some finite run exists. -/
def Terminates (F : Funs) (L : Loop) (s : State) : Prop := ∃ m, Run F L s m

/-- A ranking function that strictly decreases across guarded steps bounds
every run from a state of rank at most `n`. -/
theorem terminates_of_rank_le (F : Funs) (L : Loop) (rank : State → Nat)
    (h : ∀ s, L.holds F s → rank (L.step F s) < rank s) :
    ∀ n s, rank s ≤ n → Terminates F L s := by
  intro n
  induction n with
  | zero =>
    intro s hle
    by_cases hg : L.holds F s
    · have := h s hg
      omega
    · exact ⟨0, Run.done hg⟩
  | succ n ih =>
    intro s hle
    by_cases hg : L.holds F s
    · obtain ⟨m, r⟩ := ih (L.step F s) (by have := h s hg; omega)
      exact ⟨m + 1, Run.step hg r⟩
    · exact ⟨0, Run.done hg⟩

/-- **Discharge law.** A ranking function into `Nat` that strictly
decreases across every guarded step proves termination from every start. -/
theorem ranking_terminates (F : Funs) (L : Loop) (rank : State → Nat)
    (h : ∀ s, L.holds F s → rank (L.step F s) < rank s) :
    ∀ s, Terminates F L s :=
  fun s => terminates_of_rank_le F L rank h (rank s) s (Nat.le_refl _)

/-- **Static bound.** Under a ranking function, no run from `s` is longer
than `rank s`. -/
theorem run_le_rank (F : Funs) (L : Loop) (rank : State → Nat)
    (h : ∀ s, L.holds F s → rank (L.step F s) < rank s)
    {s : State} {m : Nat} (r : Run F L s m) : m ≤ rank s := by
  induction r with
  | done _ => exact Nat.zero_le _
  | step hg _ ih =>
    have := h _ hg
    omega

/-- A loop whose guard is false everywhere terminates immediately. -/
theorem terminates_of_never_holds (F : Funs) (L : Loop) (h : ∀ s, ¬ L.holds F s) :
    ∀ s, Terminates F L s :=
  fun s => ⟨0, Run.done (h s)⟩

/-- Reading a variable the body does not assign is the identity: the step
changes only assigned variables. -/
theorem step_vars_unassigned (F : Funs) (L : Loop) (s : State) (i : Nat)
    (h : L.body.find? (fun a => a.var == i) = none) : (L.step F s).vars i = s.vars i := by
  simp [Loop.step, h]

end Oak.Loops
