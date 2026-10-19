import Oak.CNFTypedCircuit

/-!
# Typed syntax and the concrete-memory embedding

Read classes are complete structural keys: the exact span and the complete
32-bit index syntax, with widths retained in the indexed syntax. Independent
class words admit every concrete memory, including cross-class aliases and
reads whose indices depend on earlier reads. No alias-disjointness premise or
sampled valuation is used. The supplied production graph still needs a checked
projection into this grammar and an exact read-key-to-source allocation.
-/

set_option autoImplicit false

namespace Oak.CNFTypedMemory

open Oak.CNFTypedCircuit

inductive BinaryOp where
  | and | or | xor | add | sub | shl | shr
  deriving DecidableEq, Repr

inductive CompareOp where
  | eq | ne | lo | hs
  deriving DecidableEq, Repr

inductive Word : Nat → Type where
  | constant {width : Nat} (value : BitVec width) : Word width
  | parameter (declared : Nat) (name : String) : Word declared
  | view {width : Nat} (useWidth : Nat) (value : Word width) : Word useWidth
  | binary {width : Nat} (op : BinaryOp) (left right : Word width) : Word width
  | compare {width : Nat} (op : CompareOp) (left right : Word width) : Word 1
  | ite {width guardWidth : Nat} (guard : Word guardWidth)
      (thenValue elseValue : Word width) : Word width
  | read (span : String) (index : Word 32) : Word 32

abbrev Scalars := String → BitVec 64
abbrev Memory := String → BitVec 32 → BitVec 32
abbrev IndependentReads := String → Word 32 → BitVec 32

def binaryValue {width : Nat} : BinaryOp → BitVec width → BitVec width → BitVec width
  | .and, left, right => left &&& right
  | .or, left, right => left ||| right
  | .xor, left, right => left ^^^ right
  | .add, left, right => left + right
  | .sub, left, right => left - right
  | .shl, left, right => left <<< (right.toNat % width)
  | .shr, left, right => left >>> (right.toNat % width)

def compareValue {width : Nat} : CompareOp → BitVec width → BitVec width → Bool
  | .eq, left, right => left == right
  | .ne, left, right => left != right
  | .lo, left, right => left.ult right
  | .hs, left, right => decide (right.toNat ≤ left.toNat)

def concreteEval (scalars : Scalars) (memory : Memory) : {width : Nat} → Word width → BitVec width
  | _, .constant value => value
  | _, .parameter declared name => (scalars name).setWidth declared
  | _, .view useWidth value => (concreteEval scalars memory value).setWidth useWidth
  | _, .binary op left right =>
      binaryValue op (concreteEval scalars memory left) (concreteEval scalars memory right)
  | _, .compare op left right =>
      BitVec.ofBool (compareValue op (concreteEval scalars memory left) (concreteEval scalars memory right))
  | _, .ite guard thenValue elseValue =>
      if (concreteEval scalars memory guard).toNat != 0 then
        concreteEval scalars memory thenValue else concreteEval scalars memory elseValue
  | _, .read span index => memory span (concreteEval scalars memory index)

def abstractEval (scalars : Scalars) (reads : IndependentReads) : {width : Nat} → Word width → BitVec width
  | _, .constant value => value
  | _, .parameter declared name => (scalars name).setWidth declared
  | _, .view useWidth value => (abstractEval scalars reads value).setWidth useWidth
  | _, .binary op left right =>
      binaryValue op (abstractEval scalars reads left) (abstractEval scalars reads right)
  | _, .compare op left right =>
      BitVec.ofBool (compareValue op (abstractEval scalars reads left) (abstractEval scalars reads right))
  | _, .ite guard thenValue elseValue =>
      if (abstractEval scalars reads guard).toNat != 0 then
        abstractEval scalars reads thenValue else abstractEval scalars reads elseValue
  | _, .read span index => reads span index

/-- Assign every structural read class the value it has in the concrete
memory. This is a total construction, even when an index contains reads. -/
def embedReads (scalars : Scalars) (memory : Memory) : IndependentReads :=
  fun span index => memory span (concreteEval scalars memory index)

/-- Structural induction discharges the semantic embedding; no supplied
term/root equality or memory-realizability premise occurs here. -/
theorem concrete_embeds {width : Nat} (term : Word width) (scalars : Scalars) (memory : Memory) :
    abstractEval scalars (embedReads scalars memory) term = concreteEval scalars memory term := by
  induction term with
  | constant value => rfl
  | parameter declared name => rfl
  | view useWidth value ih => simp only [abstractEval, concreteEval, ih]
  | binary op left right leftIH rightIH => simp only [abstractEval, concreteEval, leftIH, rightIH]
  | compare op left right leftIH rightIH => simp only [abstractEval, concreteEval, leftIH, rightIH]
  | ite guard thenValue elseValue guardIH thenIH elseIH =>
      simp only [abstractEval, concreteEval, guardIH, thenIH, elseIH]
  | read span index ih => rfl

/-- Different structural classes that alias concretely automatically receive
the same word from the embedding. Abstract assignments need not obey this. -/
theorem alias_values_equal (scalars : Scalars) (memory : Memory) (span : String)
    (left right : Word 32)
    (alias : concreteEval scalars memory left = concreteEval scalars memory right) :
    embedReads scalars memory span left = embedReads scalars memory span right := by
  simp [embedReads, alias]

def implication {width : Nat} (premise : Word 1) (left right : Word width) : Word 1 :=
  .ite premise (.compare .eq left right) (.constant (BitVec.ofBool true))

theorem implication_false_iff {width : Nat} (premise : Word 1) (left right : Word width)
    (scalars : Scalars) (memory : Memory) :
    (concreteEval scalars memory (implication premise left right)).toNat = 0 ↔
      (concreteEval scalars memory premise).toNat ≠ 0 ∧
        concreteEval scalars memory left ≠ concreteEval scalars memory right := by
  by_cases premiseNonzero : (concreteEval scalars memory premise).toNat ≠ 0
  · simp [implication, concreteEval, compareValue, premiseNonzero]
  · simp [implication, concreteEval, compareValue, premiseNonzero]

/-- Any universally refuted abstract violation implies the concrete memory
implication. This theorem establishes the abstraction direction only; a CNF
refutation must first be connected to abstractEval by the checked DAG rules. -/
theorem abstract_implication_implies_concrete {width : Nat}
    (premise : Word 1) (left right : Word width)
    (abstractValid : ∀ scalars reads,
      (abstractEval scalars reads premise).toNat ≠ 0 →
        abstractEval scalars reads left = abstractEval scalars reads right) :
    ∀ scalars memory, (concreteEval scalars memory premise).toNat ≠ 0 →
      concreteEval scalars memory left = concreteEval scalars memory right := by
  intro scalars memory premiseTrue
  have valid := abstractValid scalars (embedReads scalars memory)
  simp only [concrete_embeds] at valid
  exact valid premiseTrue

end Oak.CNFTypedMemory
