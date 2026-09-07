import Std

/-!
Boolean Tseitin encoding with symbolic auxiliary names. This specifies the
logical clauses, not Go's numeric allocation, optimizations, or serialization.
-/
set_option autoImplicit false
namespace OakVerification.BooleanCNF

inductive Expr where
  | constant (value : Bool)
  | input (index : Nat)
  | neg (child : Expr)
  | conj (left right : Expr)
  | disj (left right : Expr)
  deriving DecidableEq, BEq, Repr

inductive Atom where
  | one
  | input (index : Nat)
  | gate (expression : Expr)
  deriving DecidableEq, BEq, Repr

structure Lit where
  atom : Atom
  positive : Bool
  deriving DecidableEq, BEq, Repr

abbrev Clause := List Lit
abbrev CNF := List Clause
abbrev Assignment := Atom → Bool

def pos (a : Atom) : Lit := ⟨a, true⟩
def negate (l : Lit) : Lit := ⟨l.atom, !l.positive⟩
def holds (a : Assignment) (l : Lit) : Bool := if l.positive then a l.atom else !a l.atom

def eval (input : Nat → Bool) : Expr → Bool
  | .constant b => b
  | .input n => input n
  | .neg x => !(eval input x)
  | .conj x y => eval input x && eval input y
  | .disj x y => eval input x || eval input y

def root : Expr → Lit
  | .constant b => ⟨.one, b⟩
  | .input n => pos (.input n)
  | .neg x => negate (root x)
  | .conj x y => pos (.gate (.conj x y))
  | .disj x y => pos (.gate (.disj x y))

def andClauses (x y : Lit) (z : Atom) : CNF :=
  [[negate (pos z), x], [negate (pos z), y], [pos z, negate x, negate y]]
def orClauses (x y : Lit) (z : Atom) : CNF :=
  [[pos z, negate x], [pos z, negate y], [negate (pos z), x, y]]

def body : Expr → CNF
  | .constant _ | .input _ => []
  | .neg x => body x
  | .conj x y => body x ++ (body y ++ andClauses (root x) (root y) (.gate (.conj x y)))
  | .disj x y => body x ++ (body y ++ orClauses (root x) (root y) (.gate (.disj x y)))

def encode (e : Expr) : CNF := [[pos .one]] ++ (body e ++ [[root e]])
def clauseSat (a : Assignment) (c : Clause) : Bool := c.any (holds a)
def cnfSat (a : Assignment) (f : CNF) : Bool := f.all (clauseSat a)

@[simp] theorem holds_pos (a : Assignment) (x : Atom) : holds a (pos x) = a x := rfl
@[simp] theorem holds_negate (a : Assignment) (l : Lit) : holds a (negate l) = !(holds a l) := by
  cases l with
  | mk atom positive => cases positive <;> simp [holds, negate]

@[simp] theorem cnfSat_append (a : Assignment) (f g : CNF) :
    cnfSat a (f ++ g) = (cnfSat a f && cnfSat a g) := by
  simp [cnfSat, List.all_append]

theorem andClauses_correct (a : Assignment) (x y : Lit) (z : Atom) :
    cnfSat a (andClauses x y z) = true ↔ a z = (holds a x && holds a y) := by
  cases hx : holds a x <;> cases hy : holds a y <;> cases hz : a z <;>
    simp [andClauses, cnfSat, clauseSat, hx, hy, hz]

theorem orClauses_correct (a : Assignment) (x y : Lit) (z : Atom) :
    cnfSat a (orClauses x y z) = true ↔ a z = (holds a x || holds a y) := by
  cases hx : holds a x <;> cases hy : holds a y <;> cases hz : a z <;>
    simp [orClauses, cnfSat, clauseSat, hx, hy, hz]

-- Arbitrary satisfying auxiliary assignments must agree with expression
-- evaluation. No assumption that they were produced by an evaluator is used.
theorem body_sound (e : Expr) (a : Assignment) (one : a .one = true)
    (sat : cnfSat a (body e) = true) :
    holds a (root e) = eval (fun n => a (.input n)) e := by
  induction e with
  | constant b => cases b <;> simp [root, holds, eval, one]
  | input n => simp [root, eval]
  | neg x ih => simpa [root, eval] using congrArg Bool.not (ih sat)
  | conj x y ihx ihy =>
    have parts : cnfSat a (body x) = true ∧ cnfSat a (body y) = true ∧
        cnfSat a (andClauses (root x) (root y) (.gate (.conj x y))) = true := by
      simpa only [body, cnfSat_append, Bool.and_eq_true] using sat
    simp only [root, holds_pos, eval]
    rw [← ihx parts.1, ← ihy parts.2.1]
    exact (andClauses_correct a (root x) (root y) _).mp parts.2.2
  | disj x y ihx ihy =>
    have parts : cnfSat a (body x) = true ∧ cnfSat a (body y) = true ∧
        cnfSat a (orClauses (root x) (root y) (.gate (.disj x y))) = true := by
      simpa only [body, cnfSat_append, Bool.and_eq_true] using sat
    simp only [root, holds_pos, eval]
    rw [← ihx parts.1, ← ihy parts.2.1]
    exact (orClauses_correct a (root x) (root y) _).mp parts.2.2

-- A concrete extension for every input valuation, including false expressions.
-- Only the asserted root needs the additional hypothesis that the result is true.
def canonical (input : Nat → Bool) : Assignment
  | .one => true
  | .input n => input n
  | .gate e => eval input e

@[simp] theorem canonical_root (input : Nat → Bool) (e : Expr) :
    holds (canonical input) (root e) = eval input e := by
  induction e with
  | constant b => cases b <;> rfl
  | input n => rfl
  | neg x ih => simp [root, eval, ih]
  | conj x y => rfl
  | disj x y => rfl

theorem body_complete (input : Nat → Bool) (e : Expr) :
    cnfSat (canonical input) (body e) = true := by
  induction e with
  | constant b => rfl
  | input n => rfl
  | neg x ih => exact ih
  | conj x y ihx ihy =>
    simp only [body, cnfSat_append, ihx, ihy, Bool.true_and]
    apply (andClauses_correct _ _ _ _).mpr
    simp [canonical, eval]
  | disj x y ihx ihy =>
    simp only [body, cnfSat_append, ihx, ihy, Bool.true_and]
    apply (orClauses_correct _ _ _ _).mpr
    simp [canonical, eval]

theorem encode_sound (e : Expr) (a : Assignment) (sat : cnfSat a (encode e) = true) :
    eval (fun n => a (.input n)) e = true := by
  have parts : a .one = true ∧ cnfSat a (body e) = true ∧ holds a (root e) = true := by
    simpa [encode, cnfSat_append, cnfSat, clauseSat] using sat
  rw [← body_sound e a parts.1 parts.2.1]
  exact parts.2.2

theorem encode_complete (input : Nat → Bool) (e : Expr) (value : eval input e = true) :
    cnfSat (canonical input) (encode e) = true := by
  simp only [encode, cnfSat_append, body_complete]
  simpa [cnfSat, clauseSat, canonical] using value

theorem encoding_iff (input : Nat → Bool) (e : Expr) :
    eval input e = true ↔ ∃ a : Assignment,
      (∀ n, a (.input n) = input n) ∧ cnfSat a (encode e) = true := by
  constructor
  · intro value
    exact ⟨canonical input, fun _ => rfl, encode_complete input e value⟩
  · rintro ⟨a, agrees, sat⟩
    have inputs : (fun n => a (.input n)) = input := funext agrees
    simpa only [inputs] using encode_sound e a sat

#print axioms andClauses_correct
#print axioms orClauses_correct
#print axioms encode_sound
#print axioms encode_complete
#print axioms encoding_iff
end OakVerification.BooleanCNF
