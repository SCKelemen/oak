import Oak.AssemblerSemantics
import Oak.RupCheck
import Oak.Tseitin

/-!
# The abstract native-equality certificate contract

A certificate-backed native equality decision needs one logical link beyond
the existing RUP and Tseitin laws: the clauses checked by LRAT must encode the
disequality of the two fixed-width results being compared.  This module states
that link explicitly for a bounded scalar input domain.

`Encoding` deliberately asks only for the direction an UNSAT proof needs:
whenever the determined circuit has a satisfying disequality obligation, the
RUP database has a model.  An accepted RUP derivation says that no such model
exists, so the two `BitVec` results agree on every input.  The reverse direction
is useful for validating SAT counterexamples, but is not needed to authorize a
proved equality verdict.

This is a formal contract, not yet an implementation-refinement theorem.  In
particular, it does not prove that `asm/cnf.go` constructs `database`, that the
Go or Oak LRAT parser/checker produces `Oak.RupCheck.Accepted`, or that the
native verifier's concrete terms are `lhs` and `rhs`.  Source lowering, ISA
encoding, object writing, relocation, and linking are also outside this module.
A production certificate consumer must reconstruct the exact database from
authenticated terms; acceptance of an unrelated DIMACS formula is not enough.
-/

set_option autoImplicit false

namespace Oak.NativeEqualityCertificate

open Oak.RupCheck

/-- A bounded scalar environment flattened to its `n` input bits. -/
abbrev Inputs (n : Nat) := Fin n → Bool

/-- The exact logical obligations needed to turn acceptance of one clause
database into equality of two fixed-width scalar results.

`counterexample_iff` identifies the determined circuit's obligation with a
result disequality.  `cnf_complete` is one-way completeness of the clauses:
every satisfying circuit obligation extends to a model of the database. -/
structure Encoding (n width : Nat) (Gate : Type) where
  lhs : Inputs n → BitVec width
  rhs : Inputs n → BitVec width
  circuit : Inputs n → Gate → Bool
  obligation : Inputs n → (Gate → Bool) → Bool
  database : Database
  counterexample_iff : ∀ input,
    obligation input (circuit input) = true ↔ lhs input ≠ rhs input
  cnf_complete : Oak.Tseitin.Satisfiable circuit obligation →
    ∃ assignment, Models assignment database

/-- If the exact disequality database has an accepted RUP derivation, the two
fixed-width results agree for every input-bit assignment. -/
theorem accepted_implies_equal {n width : Nat} {Gate : Type}
    (encoding : Encoding n width Gate) (accepted : Accepted encoding.database) :
    ∀ input, encoding.lhs input = encoding.rhs input := by
  intro input
  apply Classical.byContradiction
  intro differs
  have holds : encoding.obligation input (encoding.circuit input) = true :=
    (encoding.counterexample_iff input).2 differs
  have satisfiable : Oak.Tseitin.Satisfiable encoding.circuit encoding.obligation :=
    (Oak.Tseitin.determined encoding.circuit encoding.obligation).2 ⟨input, holds⟩
  obtain ⟨assignment, model⟩ := encoding.cnf_complete satisfiable
  exact accepted_unsatisfiable accepted assignment model

/-! A fully concrete, deliberately tiny instance exercises the composition.
Its obligation is constantly false, its two results are definitionally the
same input bit, and its database already contains the empty clause. -/

namespace Example

def passthrough (input : Inputs 1) : BitVec 1 := BitVec.ofBool (input 0)

def noGates (_ : Inputs 1) (_ : Unit) : Bool := false

def noCounterexamples (_ : Inputs 1) (_ : Unit → Bool) : Bool := false

def contradictionDB : Database := fun id => if id = 1 then some [] else none

theorem contradictionDB_accepted : Accepted contradictionDB := by
  refine ⟨contradictionDB, 1, Steps.refl contradictionDB, ?_⟩
  simp [contradictionDB]

def identityEncoding : Encoding 1 1 Unit where
  lhs := passthrough
  rhs := passthrough
  circuit := noGates
  obligation := noCounterexamples
  database := contradictionDB
  counterexample_iff := by
    intro input
    simp [noCounterexamples]
  cnf_complete := by
    rintro ⟨input, gates, _determined, holds⟩
    simp [noCounterexamples] at holds

example (input : Inputs 1) :
    identityEncoding.lhs input = identityEncoding.rhs input :=
  accepted_implies_equal identityEncoding contradictionDB_accepted input

end Example

end Oak.NativeEqualityCertificate
