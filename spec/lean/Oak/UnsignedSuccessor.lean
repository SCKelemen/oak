import Std

/-!
# Same-width unsigned successor under a strict guard

Arithmetic and premise-composition laws for asm/unsigned_successor.go. Pointer
identity supplies unchanged operands in the Go matcher; one-bit AND descent
supplies the strict unsigned premise. These theorems do not formalize the Go
matcher, its term DAG representation, or its execution. The source controls
exercise those separate refinement obligations. No new axiom is introduced.
-/
set_option autoImplicit false
namespace Oak.UnsignedSuccessor

/-- A strict unsigned bound keeps a unit increment below the modulus. -/
theorem successor_no_wrap {k bound modulus : Nat}
    (guard : k < bound) (boundFits : bound < modulus) :
    k + 1 < modulus ∧ (k + 1) % modulus ≤ bound := by
  have fits : k + 1 < modulus := by omega
  constructor
  · exact fits
  · rw [Nat.mod_eq_of_lt fits]
    omega

/-- The actual modular bitvector addition agrees with the unsigned successor. -/
theorem bitvec_successor {w : Nat} (positive : 0 < w)
    (k bound : BitVec w) (guard : k.toNat < bound.toNat) :
    (k + 1).toNat ≤ bound.toNat := by
  have fits := successor_no_wrap guard bound.isLt
  rw [BitVec.toNat_add, BitVec.ofNat_eq_ofNat, BitVec.toNat_one positive]
  exact fits.2

/-- The redundant weak invariant is not needed for this arithmetic fact. -/
theorem guarded_invariant {w : Nat} (positive : 0 < w)
    (k bound : BitVec w)
    (premise : k.toNat ≤ bound.toNat ∧ k.toNat < bound.toNat) :
    (k + 1).toNat ≤ bound.toNat :=
  bitvec_successor positive k bound premise.2

/-- Descending a one-bit AND preserves an entailed guard. -/
theorem and_entails_left (p q : Bool) (h : p && q = true) : p = true := by
  cases p <;> cases q <;> simp_all

theorem and_entails_right (p q : Bool) (h : p && q = true) : q = true := by
  cases p <;> cases q <;> simp_all

/-- Any premise that entails the strict guard establishes the target equality. -/
theorem premise_successor {w : Nat} (positive : 0 < w)
    (premise : Bool) (k bound : BitVec w)
    (entails : premise = true → k.toNat < bound.toNat)
    (holds : premise = true) :
    decide ((k + 1).toNat ≤ bound.toNat) = true := by
  exact decide_eq_true (bitvec_successor positive k bound (entails holds))

/-- Boundary controls: maximum minus one succeeds; maximum cannot satisfy <. -/
theorem boundary_predecessor : (((254 : BitVec 8) + 1).toNat ≤ (255 : BitVec 8).toNat) := by decide
theorem maximum_not_below (bound : BitVec 8) : ¬ ((255 : BitVec 8).toNat < bound.toNat) := by
  have fits := bound.isLt
  change ¬ (255 < bound.toNat)
  change bound.toNat < 256 at fits
  omega

/-- Removing the guard or changing the bound invalidates the proposed rule. -/
theorem guard_needed : ¬ (((0 : BitVec 8) + 1).toNat ≤ (0 : BitVec 8).toNat) := by decide
theorem unchanged_bound_needed : (3 : BitVec 8).toNat < (4 : BitVec 8).toNat ∧
    ¬ (((3 : BitVec 8) + 1).toNat ≤ (2 : BitVec 8).toNat) := by decide

end Oak.UnsignedSuccessor

-- Named axiom audit: no sorryAx, native_decide, or custom axioms are permitted.
#print axioms Oak.UnsignedSuccessor.successor_no_wrap
#print axioms Oak.UnsignedSuccessor.bitvec_successor
#print axioms Oak.UnsignedSuccessor.guarded_invariant
#print axioms Oak.UnsignedSuccessor.and_entails_left
#print axioms Oak.UnsignedSuccessor.and_entails_right
#print axioms Oak.UnsignedSuccessor.premise_successor
#print axioms Oak.UnsignedSuccessor.boundary_predecessor
#print axioms Oak.UnsignedSuccessor.maximum_not_below
#print axioms Oak.UnsignedSuccessor.guard_needed
#print axioms Oak.UnsignedSuccessor.unchanged_bound_needed
