import Oak.UnsignedSuccessor
import Lean

/-! Pin the unsigned-successor statements and audit their standard-only proof
authority. This checks the arithmetic and premise laws; the Go matcher and its
internal DAG representation remain a separate reviewed and tested boundary. -/

open Lean Elab Command
open Oak.UnsignedSuccessor

example {k bound modulus : Nat} (guard : k < bound) (fits : bound < modulus) :
    k + 1 < modulus ∧ (k + 1) % modulus ≤ bound := successor_no_wrap guard fits

example {w : Nat} (positive : 0 < w) (k bound : BitVec w)
    (guard : k.toNat < bound.toNat) : (k + 1).toNat ≤ bound.toNat :=
  bitvec_successor positive k bound guard

example {w : Nat} (positive : 0 < w) (k bound : BitVec w)
    (premise : k.toNat ≤ bound.toNat ∧ k.toNat < bound.toNat) :
    (k + 1).toNat ≤ bound.toNat := guarded_invariant positive k bound premise

example (p q : Bool) (h : p && q = true) : p = true := and_entails_left p q h
example (p q : Bool) (h : p && q = true) : q = true := and_entails_right p q h

example {w : Nat} (positive : 0 < w) (premise : Bool) (k bound : BitVec w)
    (entails : premise = true → k.toNat < bound.toNat) (holds : premise = true) :
    decide ((k + 1).toNat ≤ bound.toNat) = true :=
  premise_successor positive premise k bound entails holds

example : (((254 : BitVec 8) + 1).toNat ≤ (255 : BitVec 8).toNat) := boundary_predecessor
example (bound : BitVec 8) : ¬ ((255 : BitVec 8).toNat < bound.toNat) := maximum_not_below bound
example : ¬ (((0 : BitVec 8) + 1).toNat ≤ (0 : BitVec 8).toNat) := guard_needed
example : (3 : BitVec 8).toNat < (4 : BitVec 8).toNat ∧
    ¬ (((3 : BitVec 8) + 1).toNat ≤ (2 : BitVec 8).toNat) := unchanged_bound_needed

run_cmd do
  for name in [``Oak.UnsignedSuccessor.successor_no_wrap,
               ``Oak.UnsignedSuccessor.bitvec_successor,
               ``Oak.UnsignedSuccessor.guarded_invariant,
               ``Oak.UnsignedSuccessor.and_entails_left,
               ``Oak.UnsignedSuccessor.and_entails_right,
               ``Oak.UnsignedSuccessor.premise_successor,
               ``Oak.UnsignedSuccessor.boundary_predecessor,
               ``Oak.UnsignedSuccessor.maximum_not_below,
               ``Oak.UnsignedSuccessor.guard_needed,
               ``Oak.UnsignedSuccessor.unchanged_bound_needed] do
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "{name} depends on nonstandard axiom {axiomName}"
