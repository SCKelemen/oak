import Oak.NativeEqualityCertificate

/-!
# Direct fixed-width result disequality for native CNF certificates

The narrow native bitwise audit asserts one root built by XORing corresponding
result bits and ORing those differences from least to most significant.  This
module states that operation independently of comparisons or condition flags
and proves that it is true exactly when the two fixed-width words differ.

`DirectEncoding` composes that exact obligation with the existing abstract
RUP certificate theorem.  This is the formal law used by the new bounded Go
audit; it is not a universal refinement proof of Go term construction,
symbolic machine execution, Oak lowering, DIMACS serialization, or LRAT
parsing.  Those remain distinct links.
-/

set_option autoImplicit false

namespace Oak.CNFBitwiseWordRoot

open Oak.RupCheck

/-- OR the per-bit XORs in the same low-to-high order as the native audit. -/
def differencePrefix {width : Nat} (lhs rhs : BitVec width) : Nat → Bool
  | 0 => false
  | bit + 1 =>
      differencePrefix lhs rhs bit || xor (lhs.getLsbD bit) (rhs.getLsbD bit)

/-- The direct result-disequality root over every bit of a fixed-width word. -/
def differs {width : Nat} (lhs rhs : BitVec width) : Bool :=
  differencePrefix lhs rhs width

private theorem or_xor_eq_false_iff (prior left right : Bool) :
    (prior || xor left right) = false ↔ prior = false ∧ left = right := by
  cases prior <;> cases left <;> cases right <;> decide

theorem differencePrefix_eq_false_iff {width : Nat} (lhs rhs : BitVec width)
    (count : Nat) :
    differencePrefix lhs rhs count = false ↔
      ∀ bit, bit < count → lhs.getLsbD bit = rhs.getLsbD bit := by
  induction count with
  | zero => simp [differencePrefix]
  | succ count induction =>
      rw [differencePrefix, or_xor_eq_false_iff, induction]
      constructor
      · rintro ⟨prior, current⟩ bit before
        rcases Nat.lt_succ_iff_lt_or_eq.mp before with earlier | rfl
        · exact prior bit earlier
        · exact current
      · intro equal
        refine ⟨(fun bit before => equal bit (Nat.lt_succ_of_lt before)), ?_⟩
        exact equal count (Nat.lt_succ_self count)

theorem differs_eq_false_iff {width : Nat} (lhs rhs : BitVec width) :
    differs lhs rhs = false ↔ lhs = rhs := by
  rw [differs, differencePrefix_eq_false_iff]
  constructor
  · intro equalBits
    apply BitVec.eq_of_getLsbD_eq
    intro bit inside
    exact equalBits bit inside
  · rintro rfl bit _
    rfl

/-- The asserted direct root is a counterexample exactly when the words
differ. -/
theorem differs_eq_true_iff {width : Nat} (lhs rhs : BitVec width) :
    differs lhs rhs = true ↔ lhs ≠ rhs := by
  constructor
  · intro differentRoot equalWords
    have falseRoot := (differs_eq_false_iff lhs rhs).2 equalWords
    rw [falseRoot] at differentRoot
    contradiction
  · intro unequal
    cases root : differs lhs rhs with
    | false => exact absurd ((differs_eq_false_iff lhs rhs).1 root) unequal
    | true => rfl

/-! ## Composition with the existing abstract certificate contract -/

abbrev Inputs (n : Nat) := Oak.NativeEqualityCertificate.Inputs n

/-- A clause encoding whose asserted obligation is exactly the direct
per-result-bit disequality above. -/
structure DirectEncoding (n width : Nat) (Gate : Type) where
  lhs : Inputs n → BitVec width
  rhs : Inputs n → BitVec width
  circuit : Inputs n → Gate → Bool
  obligation : Inputs n → (Gate → Bool) → Bool
  database : Database
  difference_exact : ∀ input,
    obligation input (circuit input) = differs (lhs input) (rhs input)
  cnf_complete : Oak.Tseitin.Satisfiable circuit obligation →
    ∃ assignment, Models assignment database

def DirectEncoding.asNative {n width : Nat} {Gate : Type}
    (encoding : DirectEncoding n width Gate) :
    Oak.NativeEqualityCertificate.Encoding n width Gate where
  lhs := encoding.lhs
  rhs := encoding.rhs
  circuit := encoding.circuit
  obligation := encoding.obligation
  database := encoding.database
  counterexample_iff := by
    intro input
    rw [encoding.difference_exact input, differs_eq_true_iff]
  cnf_complete := encoding.cnf_complete

/-- An accepted RUP derivation for the exact direct-disequality database
implies equality at every bounded scalar input. -/
theorem accepted_implies_equal {n width : Nat} {Gate : Type}
    (encoding : DirectEncoding n width Gate) (accepted : Accepted encoding.database) :
    ∀ input, encoding.lhs input = encoding.rhs input :=
  Oak.NativeEqualityCertificate.accepted_implies_equal encoding.asNative accepted

example : differs (0xff#8) (0x7f#8) = true := by decide
example : differs (0xa5#8) (0xa5#8) = false := by decide

end Oak.CNFBitwiseWordRoot
