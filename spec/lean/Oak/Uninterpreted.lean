/-!
# Uninterpreted operations in the bit-level decider

Model for `docs/spec/94-assembler.md` §8 ("floating point as uninterpreted
operations") and `asm/floats_ops.go`, `asm/blast.go`. The verifier decides an
asm unit against its Oak body at the bit level; a floating-point operation
(add, multiply, fma, sqrt, the conversions) is not a bit operation it can
blast, so the decider abstracts each application as an *uninterpreted*
function of its operands: a fresh value, shared by every application of the
same operation to the same operand bits, with Ackermann's functional
consistency between applications whose operands turn out equal.

The theorem below is the soundness of that abstraction: if two terms are
equal under **every** consistent assignment of values to the applications,
they are equal under the actual operations — IEEE arithmetic in particular
(whose bit-level model is `Oak.FloatOps`). Hence "proven" from the decider
means "equal up to the IEEE operations themselves": the unit applies the
same operations to the same operands in the same order as its body.

The converse direction is deliberately absent: two terms may be equal under
IEEE arithmetic (`x * 2` and `x + x`) and unequal under some other
interpretation; the decider then reports a mismatch, which is the
conservative side (the unit is not accepted as proven).
-/

namespace Oak.Uninterpreted

/-- Terms over variables and applications of operation symbols of arity
one, two, or three (the shapes `asm/floats_ops.go` uses: unary sqrt and
conversions, binary arithmetic, ternary fma). `k` names the operation
(with its width). -/
inductive Term where
  | var (n : Nat)
  | app1 (k : Nat) (a : Term)
  | app2 (k : Nat) (a b : Term)
  | app3 (k : Nat) (a b c : Term)
  deriving Repr

/-- An interpretation of the operation symbols over a value domain. -/
structure Interp (α : Type) where
  op1 : Nat → α → α
  op2 : Nat → α → α → α
  op3 : Nat → α → α → α → α

/-- Evaluation under an interpretation and a variable assignment. -/
def eval {α : Type} (I : Interp α) (ρ : Nat → α) : Term → α
  | .var n => ρ n
  | .app1 k a => I.op1 k (eval I ρ a)
  | .app2 k a b => I.op2 k (eval I ρ a) (eval I ρ b)
  | .app3 k a b c => I.op3 k (eval I ρ a) (eval I ρ b) (eval I ρ c)

/-- The decider's view: an application's value is looked up in a table `v`
indexed by the operation and the operand *values* (the blaster keys the
fresh block by the operands' canonical bits, so equal operand values share
a block — the table form states exactly that sharing). Any such table is
"consistent" in Ackermann's sense by construction. -/
structure Table (α : Type) where
  v1 : Nat → α → α
  v2 : Nat → α → α → α
  v3 : Nat → α → α → α → α

/-- A table is an interpretation: the decider evaluates a term by looking
each application up. -/
def Table.interp {α : Type} (t : Table α) : Interp α := ⟨t.v1, t.v2, t.v3⟩

/-- **Soundness of the abstraction.** If two terms agree under every table
(every consistent assignment of values to the applications), they agree
under any interpretation — the IEEE operations included. -/
theorem ackermann_sound {α : Type} (s t : Term)
    (h : ∀ (tab : Table α) (ρ : Nat → α), eval tab.interp ρ s = eval tab.interp ρ t)
    (I : Interp α) (ρ : Nat → α) : eval I ρ s = eval I ρ t := by
  -- The interpretation itself is a table: apply the hypothesis to it.
  have := h ⟨I.op1, I.op2, I.op3⟩ ρ
  simpa [Table.interp] using this

/-- **Sharing is sound.** Two applications of one operation to equal operand
values evaluate equal under every interpretation: the block the blaster
shares between them holds one value. -/
theorem shared_application {α : Type} (I : Interp α) (ρ : Nat → α) (k : Nat) (a b a' b' : Term)
    (ha : eval I ρ a = eval I ρ a') (hb : eval I ρ b = eval I ρ b') :
    eval I ρ (.app2 k a b) = eval I ρ (.app2 k a' b') := by
  simp [eval, ha, hb]

/-- **Different structure is not equated.** The decider does not assume
commutativity, associativity, or any algebraic law: `app2 k a b` and
`app2 k b a` differ under some table, so a unit that reorders operands of a
non-commutative operation, or regroups a reduction, is a mismatch, never a
proof. -/
theorem no_commutativity_assumed :
    ∃ (tab : Table Nat) (ρ : Nat → Nat),
      eval tab.interp ρ (.app2 0 (.var 0) (.var 1)) ≠ eval tab.interp ρ (.app2 0 (.var 1) (.var 0)) := by
  refine ⟨⟨fun _ a => a, fun _ a _ => a, fun _ a _ _ => a⟩, fun n => n, ?_⟩
  simp [eval, Table.interp]

/-- **Structural equality is a proof.** A term equal to itself as a tree is
equal under every interpretation — the case the blaster settles by shared
canonical nodes. -/
theorem structural_eq {α : Type} (I : Interp α) (ρ : Nat → α) (s t : Term) (h : s = t) :
    eval I ρ s = eval I ρ t := by subst h; rfl

/-! ### Verdicts up to the NaN payload

A float result is compared after every NaN pattern is mapped to one
canonical NaN (`asm/floats_lowering.go` floatCanonicalNaN): the payload is
the platform's (docs/spec/20-types.md §11.3.5). Two NaNs compare equal,
and two numbers compare equal exactly when they are equal. -/

/-- Canonicalization over an abstract NaN predicate and canonical value. -/
def canon {α : Type} (isNaN : α → Prop) [DecidablePred isNaN] (c : α) (x : α) : α :=
  if isNaN x then c else x

theorem canon_eq_of_nan {α : Type} (isNaN : α → Prop) [DecidablePred isNaN] (c x y : α)
    (hx : isNaN x) (hy : isNaN y) : canon isNaN c x = canon isNaN c y := by
  simp [canon, hx, hy]

theorem canon_eq_iff_of_not_nan {α : Type} (isNaN : α → Prop) [DecidablePred isNaN] (c x y : α)
    (hx : ¬ isNaN x) (hy : ¬ isNaN y) : canon isNaN c x = canon isNaN c y ↔ x = y := by
  simp [canon, hx, hy]

/-- A number and a NaN never compare equal when the canonical value is a NaN. -/
theorem canon_ne_of_nan_not_nan {α : Type} (isNaN : α → Prop) [DecidablePred isNaN] (c x y : α)
    (hc : isNaN c) (hx : isNaN x) (hy : ¬ isNaN y) : canon isNaN c x ≠ canon isNaN c y := by
  simp only [canon, hx, hy, ↓reduceIte]
  intro h; exact hy (h ▸ hc)

end Oak.Uninterpreted
