/-!
# Oak.Floats — the floating-point evaluation discipline

`docs/spec/20-types.md` section 11.3 fixes how Oak evaluates floating-point
expressions: every operation is computed exactly and then rounded once to
its own type (round to nearest, ties to even), grouping is the parse tree,
operands are never reassociated and multiply-add is never contracted, and
`fma` is a single rounding of `a * b + c`. The point of those rules is
reproducibility: two conforming implementations — the interpreter and the C
backend on any host — produce identical bits for the core operations.

This model states the discipline over a small family of binary formats and
proves what the specification claims of it:

* `eval` is total and structural: the value of an expression is a function
  of its parse tree (`eval_add`, `eval_fma`), which is the whole content of
  "grouping is the parse tree".
* Any two implementations that satisfy the per-operation equations agree
  on every expression (`conforming_agree`): the reproducibility theorem.
* Rounding is exact on representable values (`round_small`), so widening
  `f32 -> f64` is exact and the parse-tree rule loses nothing a narrower
  format could express.
* Addition and multiplication commute under rounding (`add_comm`,
  `mul_comm`): commutativity is not the reproducibility problem.
* Reassociation changes results (`reassociation_changes_result`) and
  contracting `a * b + c` into a fused multiply-add changes results
  (`contraction_changes_result`), both decided on concrete witnesses in a
  3-bit format — the reason the backend emits `#pragma STDC FP_CONTRACT
  OFF` and `-ffp-contract=off` and the checker never reassociates.

The format is idealised: `p` significant bits, unbounded exponent, no
infinities or NaNs, values as integers (a scaled view of the significand
and exponent). Overflow, subnormals, and special values are outside this
model; they are specified by IEEE 754-2019 and executed by the witness
tests (`compiler/differential_float_test.go`, `compiler/e2e_math_test.go`).
-/

namespace Oak.Floats

/-- Bit length of a natural number by fuel-bounded halving, so that `decide`
can reduce it: `bitlen 0 = 0`, `bitlen 8 = 4`. -/
def bitlenFuel : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n = 0 then 0 else bitlenFuel fuel (n / 2) + 1

def bitlen (n : Nat) : Nat := bitlenFuel n n

/-- Round a natural magnitude to `p` significant bits, ties to even. Values
below `2^p` are representable and unchanged; otherwise the low
`bitlen a - p` bits are rounded away. -/
def roundNat (p : Nat) (a : Nat) : Nat :=
  if a < 2 ^ p then a
  else
    let shift := bitlen a - p
    let unit := 2 ^ shift
    let q := a / unit
    let r := a % unit
    let half := unit / 2
    let q' :=
      if r < half then q
      else if half < r then q + 1
      else if q % 2 = 0 then q else q + 1
    q' * unit

/-- Round an exact integer value to the `p`-bit format: the magnitude is
rounded and the sign restored, which is round to nearest even. -/
def round (p : Nat) (x : Int) : Int :=
  if x < 0 then -(Int.ofNat (roundNat p x.natAbs)) else Int.ofNat (roundNat p x.natAbs)

/-- Exact values below `2^p` in magnitude are representable, and rounding
leaves them unchanged: rounding is the identity on the format itself, so
widening a value to a format with more bits (`f32 -> f64`) is exact. -/
theorem roundNat_small {p a : Nat} (h : a < 2 ^ p) : roundNat p a = a := by
  unfold roundNat
  simp [h]

theorem round_small {p : Nat} {x : Int} (h : x.natAbs < 2 ^ p) : round p x = x := by
  unfold round
  rw [roundNat_small h]
  split
  · rename_i hx
    have habs := Int.ofNat_natAbs_of_nonpos (Int.le_of_lt hx)
    simp only [Int.ofNat_eq_natCast] at habs ⊢
    omega
  · rename_i hx
    have habs := Int.natAbs_of_nonneg (Int.not_lt.mp hx)
    simp only [Int.ofNat_eq_natCast] at habs ⊢
    omega

/-- Expressions of the core floating-point set: literals (already
representable, as the scanner rounds them once), the four arithmetic
operators, negation, and fused multiply-add. Every node names its own
rounding; there is no node for "evaluate at higher precision". -/
inductive Expr where
  | lit : Int → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | neg : Expr → Expr
  | fma : Expr → Expr → Expr → Expr
  deriving Repr, DecidableEq

/-- The evaluation discipline of section 11.3.3: each operation computes
its exact result over the already-rounded operand values and rounds once
to the format. Division is omitted here because exact division leaves the
integers; it follows the same shape (exact quotient, one rounding). -/
def eval (p : Nat) : Expr → Int
  | .lit v => round p v
  | .add a b => round p (eval p a + eval p b)
  | .sub a b => round p (eval p a - eval p b)
  | .mul a b => round p (eval p a * eval p b)
  | .neg a => -(eval p a)
  | .fma a b c => round p (eval p a * eval p b + eval p c)

/-- Grouping is the parse tree: the value of `a + b` is the rounding of the
sum of the values of `a` and `b`, whatever `a` and `b` are. -/
theorem eval_add (p : Nat) (a b : Expr) :
    eval p (.add a b) = round p (eval p a + eval p b) := rfl

/-- `fma` is one rounding of the exact `a * b + c`. -/
theorem eval_fma (p : Nat) (a b c : Expr) :
    eval p (.fma a b c) = round p (eval p a * eval p b + eval p c) := rfl

/-- An implementation conforms when it satisfies the per-operation
equations of section 11.3.3 — the interpreter and the C backend each do,
by construction and by the differential witnesses. -/
structure Conforms (p : Nat) (f : Expr → Int) : Prop where
  lit : ∀ v, f (.lit v) = round p v
  add : ∀ a b, f (.add a b) = round p (f a + f b)
  sub : ∀ a b, f (.sub a b) = round p (f a - f b)
  mul : ∀ a b, f (.mul a b) = round p (f a * f b)
  neg : ∀ a, f (.neg a) = -(f a)
  fma : ∀ a b c, f (.fma a b c) = round p (f a * f b + f c)

/-- A conforming implementation computes exactly `eval`. -/
theorem conforming_eq_eval {p : Nat} {f : Expr → Int} (h : Conforms p f) :
    ∀ e, f e = eval p e := by
  intro e
  induction e with
  | lit v => simp [h.lit, eval]
  | add a b iha ihb => rw [h.add, iha, ihb]; rfl
  | sub a b iha ihb => rw [h.sub, iha, ihb]; rfl
  | mul a b iha ihb => rw [h.mul, iha, ihb]; rfl
  | neg a iha => rw [h.neg, iha]; rfl
  | fma a b c iha ihb ihc => rw [h.fma, iha, ihb, ihc]; rfl

/-- The reproducibility theorem (section 11.3.3): two conforming
implementations produce identical results for every expression. Bit
identity across the interpreter and every backend is not a hope but a
consequence of the discipline. -/
theorem conforming_agree {p : Nat} {f g : Expr → Int}
    (hf : Conforms p f) (hg : Conforms p g) : ∀ e, f e = g e := by
  intro e
  rw [conforming_eq_eval hf, conforming_eq_eval hg]

/-- Addition commutes under rounding: swapping operands never changes a
result. The ordering rule of section 11.3.3 is about association and
evaluation order of effects, not about commutativity. -/
theorem add_comm (p : Nat) (a b : Expr) : eval p (.add a b) = eval p (.add b a) := by
  simp [eval, Int.add_comm]

theorem mul_comm (p : Nat) (a b : Expr) : eval p (.mul a b) = eval p (.mul b a) := by
  simp [eval, Int.mul_comm]

/-- Reassociation changes results. In the 3-bit format, `(8 + 1) + 1`
rounds twice to `8` (`9` is a tie and rounds to the even significand),
while `8 + (1 + 1) = 10` is representable. A compiler that reassociated
`(a + b) + c` into `a + (b + c)` would change the program's value; Oak's
checker never does, and the emitted C is compiled without fast-math. -/
theorem reassociation_changes_result :
    eval 3 (.add (.add (.lit 8) (.lit 1)) (.lit 1)) ≠
      eval 3 (.add (.lit 8) (.add (.lit 1) (.lit 1))) := by
  decide

/-- Contraction changes results. In the 3-bit format `3 * 3 = 9` rounds to
`8`, then `8 + 1 = 9` rounds to `8` again, while the fused `3 * 3 + 1 = 10`
is representable. A C compiler contracting `a * b + c` into an fma would
change the value of a program that wrote two operations, which is why the
backend disables contraction and offers `fma` as an explicit intrinsic. -/
theorem contraction_changes_result :
    eval 3 (.add (.mul (.lit 3) (.lit 3)) (.lit 1)) ≠
      eval 3 (.fma (.lit 3) (.lit 3) (.lit 1)) := by
  decide

/-- The witnesses' concrete values, as the reader would check by hand. -/
example : eval 3 (.add (.add (.lit 8) (.lit 1)) (.lit 1)) = 8 := by decide
example : eval 3 (.add (.lit 8) (.add (.lit 1) (.lit 1))) = 10 := by decide
example : eval 3 (.fma (.lit 3) (.lit 3) (.lit 1)) = 10 := by decide

/-- Ties round to even: 9 (between the 3-bit values 8 and 10) goes to 8,
11 (between 10 and 12) goes to 12. -/
example : round 3 9 = 8 := by decide
example : round 3 11 = 12 := by decide
example : round 3 (-9) = -8 := by decide

end Oak.Floats
