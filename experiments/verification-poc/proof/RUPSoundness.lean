import Std

/-!
Abstract soundness of the experiment's supported RUP/deletion calculus.

This models the logical justification of unit propagation, conflict, tautology,
clause addition, and deletion. It is not a proof that the Go parser, clause-ID
bookkeeping, CNF encoder, or executable checker implements this relation.
The relation deliberately omits operational restrictions that only reject more
proofs (fresh/increasing IDs, resource limits, and live hints for tautologies).
-/
set_option autoImplicit false
namespace OakVerification

structure Literal where
  index : Nat
  positive : Bool
  deriving DecidableEq, Repr

abbrev Assignment := Nat → Bool
abbrev Clause := List Literal
abbrev Database := Nat → Option Clause

def negate (l : Literal) : Literal := ⟨l.index, !l.positive⟩
def Holds (a : Assignment) (l : Literal) : Prop := a l.index = l.positive
def SatisfiesClause (a : Assignment) (c : Clause) : Prop :=
  ∃ l, l ∈ c ∧ Holds a l
def Models (a : Assignment) (db : Database) : Prop :=
  ∀ id c, db id = some c → SatisfiesClause a c
def Assigned (a : Assignment) (xs : List Literal) : Prop :=
  ∀ l, l ∈ xs → Holds a l

-- These side conditions inspect literal membership, not semantic entailment.
def Falsified (xs : List Literal) (c : Clause) : Prop :=
  ∀ l, l ∈ c → negate l ∈ xs
def UnitUnder (xs : List Literal) (c : Clause) (u : Literal) : Prop :=
  u ∈ c ∧ ∀ l, l ∈ c → l = u ∨ negate l ∈ xs

theorem negate_holds_iff (a : Assignment) (l : Literal) :
    Holds a (negate l) ↔ ¬ Holds a l := by
  cases l with
  | mk index positive =>
    cases positive <;> cases h : a index <;> simp [Holds, negate, h]

theorem holds_not_negate {a : Assignment} {l : Literal}
    (h : Holds a l) (hn : Holds a (negate l)) : False :=
  (negate_holds_iff a l).mp hn h

theorem unit_sound {a : Assignment} {xs : List Literal} {c : Clause} {u : Literal}
    (hc : SatisfiesClause a c) (hu : UnitUnder xs c u)
    (ha : Assigned a xs) : Holds a u := by
  obtain ⟨l, hl, hv⟩ := hc
  rcases hu.2 l hl with eq | neg
  · simpa [eq] using hv
  · exact False.elim (holds_not_negate hv (ha _ neg))

-- The list of IDs is the ordered RUP hint chain. Conflict must be its final
-- hint. A unit hint extends the assumed-true literals before the next hint.
inductive Propagate (db : Database) : List Literal → List Nat → Prop where
  | clash {xs : List Literal} {hints : List Nat} {l : Literal}
      (present : l ∈ xs) (opposite : negate l ∈ xs) :
      Propagate db xs hints
  | conflict {xs : List Literal} {id : Nat} {c : Clause}
      (lookup : db id = some c) (falsified : Falsified xs c) :
      Propagate db xs [id]
  | unit {xs : List Literal} {id : Nat} {c : Clause} {u : Literal} {tail : List Nat}
      (lookup : db id = some c) (unit : UnitUnder xs c u)
      (next : Propagate db (u :: xs) tail) :
      Propagate db xs (id :: tail)

theorem propagation_sound {db : Database} {xs : List Literal} {hints : List Nat}
    (p : Propagate db xs hints) (a : Assignment) (hm : Models a db) :
    ¬ Assigned a xs := by
  induction p with
  | clash present opposite =>
    intro ha
    exact holds_not_negate (ha _ present) (ha _ opposite)
  | conflict lookup falsified =>
    intro ha
    obtain ⟨l, hl, hv⟩ := hm _ _ lookup
    exact holds_not_negate hv (ha _ (falsified l hl))
  | unit lookup unit next ih =>
    intro ha
    apply ih
    intro l hl
    rcases List.mem_cons.mp hl with eq | member
    · subst l
      exact unit_sound (hm _ _ lookup) unit ha
    · exact ha l member

-- Negating every target literal is the RUP assumption set. No entailment or
-- unsatisfiability premise is smuggled into the propagation constructors.
theorem rup_entails {db : Database} {c : Clause} {hints : List Nat}
    (p : Propagate db (c.map negate) hints) (a : Assignment) (hm : Models a db) :
    SatisfiesClause a c := by
  classical
  by_contra notClause
  apply propagation_sound p a hm
  intro l member
  obtain ⟨original, originalMember, eq⟩ := List.mem_map.mp member
  subst l
  apply (negate_holds_iff a original).mpr
  intro holds
  exact notClause ⟨original, originalMember, holds⟩

def insert (db : Database) (id : Nat) (c : Clause) : Database :=
  fun key => if key = id then some c else db key

def erase (db : Database) (ids : List Nat) : Database :=
  fun key => if key ∈ ids then none else db key

theorem insert_preserves {db : Database} {a : Assignment} {id : Nat} {c : Clause}
    (hm : Models a db) (hc : SatisfiesClause a c) : Models a (insert db id c) := by
  intro key target lookup
  by_cases eq : key = id
  · subst key
    simp [insert] at lookup
    cases lookup
    exact hc
  · exact hm key target (by simpa [insert, eq] using lookup)

theorem erase_preserves {db : Database} {a : Assignment} (ids : List Nat)
    (hm : Models a db) : Models a (erase db ids) := by
  intro key target lookup
  by_cases member : key ∈ ids
  · simp [erase, member] at lookup
  · exact hm key target (by simpa [erase, member] using lookup)

inductive Step : Database → Database → Prop where
  | add (db : Database) (id : Nat) (c : Clause) (hints : List Nat)
      (proof : Propagate db (c.map negate) hints) : Step db (insert db id c)
  | delete (db : Database) (ids : List Nat) : Step db (erase db ids)

theorem step_preserves {before after : Database} (step : Step before after)
    (a : Assignment) (hm : Models a before) : Models a after := by
  cases step with
  | add db id c hints proof => exact insert_preserves hm (rup_entails proof a hm)
  | delete db ids => exact erase_preserves ids hm

inductive Steps : Database → Database → Prop where
  | refl (db : Database) : Steps db db
  | next {initial middle final : Database}
      (prior : Steps initial middle) (step : Step middle final) : Steps initial final

theorem steps_preserve {initial final : Database} (steps : Steps initial final)
    (a : Assignment) (hm : Models a initial) : Models a final := by
  induction steps with
  | refl => exact hm
  | next prior step ih => exact step_preserves step a ih

-- Acceptance means that some checked prefix establishes an empty clause.
-- It may subsequently be deleted; its derivation already proves refutation.
def Accepted (initial : Database) : Prop :=
  ∃ final id, Steps initial final ∧ final id = some []

def Unsatisfiable (db : Database) : Prop := ∀ a, ¬ Models a db

theorem accepted_unsatisfiable {initial : Database} (accepted : Accepted initial) :
    Unsatisfiable initial := by
  obtain ⟨final, id, steps, empty⟩ := accepted
  intro a hm
  have finalModel := steps_preserve steps a hm
  obtain ⟨l, impossible, _⟩ := finalModel id [] empty
  simp at impossible

#print axioms propagation_sound
#print axioms rup_entails
#print axioms accepted_unsatisfiable
end OakVerification
