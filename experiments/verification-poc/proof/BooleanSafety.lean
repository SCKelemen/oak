import NumberedCNF

/-! Invariant induction over arbitrary finite paths of a Boolean transition model. -/
set_option autoImplicit false
namespace OakVerification.BooleanSafety
open BooleanCNF

abbrev State := Nat → Bool
structure Model where
  initial : Expr
  step : Expr
  invariant : Expr

def rename (f : Nat → Nat) : Expr → Expr
  | .constant b => .constant b
  | .input n => .input (f n)
  | .neg e => .neg (rename f e)
  | .conj a b => .conj (rename f a) (rename f b)
  | .disj a b => .disj (rename f a) (rename f b)

theorem eval_rename (f : Nat → Nat) (input : State) (e : Expr) :
    eval input (rename f e) = eval (fun n => input (f n)) e := by
  induction e with
  | constant b => rfl
  | input n => rfl
  | neg e ih => simp only [rename, eval, ih]
  | conj a b ia ib => simp only [rename, eval, ia, ib]
  | disj a b ia ib => simp only [rename, eval, ia, ib]

def pair (s t : State) (n : Nat) : Bool :=
  if n % 2 = 0 then s (n / 2) else t (n / 2)

theorem pair_even (s t : State) (n : Nat) : pair s t (2*n) = s n := by
  have mod : (2*n) % 2 = 0 := by omega
  have div : (2*n) / 2 = n := by omega
  simp only [pair, mod, div, ite_true]

theorem pair_odd (s t : State) (n : Nat) : pair s t (2*n+1) = t n := by
  have mod : (2*n+1) % 2 = 1 := by omega
  have div : (2*n+1) / 2 = n := by omega
  simp only [pair, mod, div, Nat.one_ne_zero, ite_false]

def base (m : Model) : Expr := .conj m.initial (.neg m.invariant)
def preservation (m : Model) : Expr :=
  .conj (rename (fun n => 2*n) m.invariant)
    (.conj m.step (.neg (rename (fun n => 2*n+1) m.invariant)))

inductive Reachable (m : Model) : State → Prop
  | initial (s : State) (holds : eval s m.initial = true) : Reachable m s
  | step (s t : State) (before : Reachable m s)
      (allowed : eval (pair s t) m.step = true) : Reachable m t

def checkSafety (m : Model) (baseProof stepProof : List Instruction) : Bool :=
  NumberedCNF.checkEncoded (base m) baseProof &&
    NumberedCNF.checkEncoded (preservation m) stepProof

theorem checkSafety_sound (m : Model) (baseProof stepProof : List Instruction)
    (accepted : checkSafety m baseProof stepProof = true) :
    ∀ s, Reachable m s → eval s m.invariant = true := by
  obtain ⟨baseAccepted, stepAccepted⟩ := Bool.and_eq_true.mp accepted
  have hb := NumberedCNF.checkEncoded_sound (base m) baseProof baseAccepted
  have hs := NumberedCNF.checkEncoded_sound (preservation m) stepProof stepAccepted
  intro s reachable
  induction reachable with
  | initial s initial =>
    have h := hb s
    cases inv : eval s m.invariant <;> simp [base, eval, initial, inv] at h ⊢
  | step s t before allowed ih =>
    have h := hs (pair s t)
    have left : (fun n => pair s t (2*n)) = s := funext (pair_even s t)
    have right : (fun n => pair s t (2*n+1)) = t := funext (pair_odd s t)
    have violation : eval (pair s t) (preservation m) =
        (eval s m.invariant && (eval (pair s t) m.step && !eval t m.invariant)) := by
      simp only [preservation, eval, eval_rename, left, right]
    rw [violation] at h
    cases inv : eval t m.invariant <;> simp [ih, allowed, inv] at h ⊢

#print axioms eval_rename
#print axioms checkSafety_sound
end OakVerification.BooleanSafety
