import ClauseClassifier

/-! A proof-producing propagation chain using the computed classifier.
Certificates are semantic: no call to the older checkRUP supplies the answer.
Proof fields erase during execution. Concrete Oak-loop refinement is separate. -/
set_option autoImplicit false
namespace OakVerification.PropagationChain
open PropagationState

theorem assigned_tail (a : Assignment) (l : Literal) (rest : List Literal)
    (h : Assigned a (l :: rest)) : Assigned a rest := by
  intro next member
  exact h next (List.mem_cons_of_mem l member)

theorem literal_write (a : Assignment) (s : Scratch) (l : Literal)
    (positive : 0 < l.index) (compatible : Extends a s) (holds : Holds a l) :
    Extends a (write s (l.index - 1) l.positive) := by
  apply write_extends a s (l.index - 1) l.positive compatible
  have index : l.index - 1 + 1 = l.index := by omega
  rw [index]
  exact holds

inductive Prepared (s : Scratch) (xs : List Literal) where
  | ready (next : Scratch)
      (preserves : ∀ a, Extends a s → Assigned a xs → Extends a next)
  | clash (impossible : ∀ a, Extends a s → ¬ Assigned a xs)

-- Forward target assumptions preserve every compatible interpretation. Detecting
-- the opposite value produces a contradiction certificate rather than a write.
def prepare (s : Scratch) : (xs : List Literal) → Option (Prepared s xs)
  | [] => some (.ready s (fun _ compatible _ => compatible))
  | l :: rest =>
    if positive : 0 < l.index then
      if falsified : FalseUnder s l then
        some (.clash (fun a compatible assumptions =>
          false_excludes a s l positive compatible falsified (assumptions l (by simp))))
      else
        match prepare (write s (l.index - 1) l.positive) rest with
        | none => none
        | some (.ready next preserves) =>
          some (.ready next (fun a compatible assumptions =>
            preserves a (literal_write a s l positive compatible (assumptions l (by simp)))
              (assigned_tail a l rest assumptions)))
        | some (.clash impossible) =>
          some (.clash (fun a compatible assumptions =>
            impossible a (literal_write a s l positive compatible (assumptions l (by simp)))
              (assigned_tail a l rest assumptions)))
    else none

structure Refutation (db : Database) (s : Scratch) : Type where
  sound : ∀ a, Models a db → Extends a s → False

-- Each recursive call consumes a hint. Conflict is accepted only at the final
-- hint; satisfied and unresolved clauses reject. Every unit uses the proved
-- duplicate-aware classifier and carries its assignment-preservation theorem.
def chain (variables : Nat) (db : Database) (s : Scratch) :
    (hints : List Nat) → Option (Refutation db s)
  | [] => none
  | id :: rest =>
    if id = 0 then none
    else match lookup : db id with
    | none => none
    | some clause =>
      if bounds : ∀ l ∈ clause, 0 < l.index ∧ l.index ≤ variables then
        match result : ClauseClassifier.classify s clause with
        | .conflict =>
          match rest with
          | [] => some ⟨fun a model compatible =>
              ClauseClassifier.classified_conflict_sound a s clause
                (fun l member => (bounds l member).1) compatible result (model id clause lookup)⟩
          | _ :: _ => none
        | .unit u =>
          match chain variables db (write s (u.index - 1) u.positive) rest with
          | none => none
          | some next => some ⟨fun a model compatible =>
              next.sound a model (ClauseClassifier.classified_unit_write a s clause u
                (fun l member => (bounds l member).1) compatible (model id clause lookup) result)⟩
        | _ => none
      else none

structure CertifiedClause (db : Database) (target : Clause) : Type where
  entails : ∀ a, Models a db → SatisfiesClause a target

theorem assumptions_entail (db : Database) (target : Clause)
    (refutes : ∀ a, Models a db → ¬ Assigned a (target.map negate)) :
    ∀ a, Models a db → SatisfiesClause a target := by
  intro a model
  classical
  apply Classical.byContradiction
  intro notClause
  apply refutes a model
  intro l member
  obtain ⟨original, present, same⟩ := List.mem_map.mp member
  subst l
  apply (negate_holds_iff a original).mpr
  intro holds
  exact notClause ⟨original, present, holds⟩

def check (variables : Nat) (db : Database) (target : Clause) (hints : List Nat) :
    Option (CertifiedClause db target) :=
  if variables = 0 ∨ 64 < variables then none
  else if ¬ target.all (fun l => decide (0 < l.index ∧ l.index ≤ variables)) then none
  else if !(hints.all fun id => decide (0 < id) && (db id).isSome) then none
  else
    match prepare (fun _ => none) (target.map negate) with
    | none => none
    | some (.clash impossible) =>
      some ⟨assumptions_entail db target (fun a _ assumptions =>
        impossible a (empty_extends a) assumptions)⟩
    | some (.ready scratch preserves) =>
      match chain variables db scratch hints with
      | none => none
      | some refutation =>
        some ⟨assumptions_entail db target (fun a model assumptions =>
          refutation.sound a model (preserves a (empty_extends a) assumptions))⟩

theorem check_entails (variables : Nat) (db : Database) (target : Clause) (hints : List Nat)
    (accepted : (check variables db target hints).isSome = true) :
    ∀ a, Models a db → SatisfiesClause a target := by
  cases result : check variables db target hints with
  | none => simp [result] at accepted
  | some certificate => exact certificate.entails

theorem checked_insert_preserves (variables : Nat) (db : Database) (target : Clause)
    (hints : List Nat) (id : Nat) (accepted : (check variables db target hints).isSome = true)
    (a : Assignment) (model : Models a db) : Models a (insert db id target) :=
  insert_preserves model (check_entails variables db target hints accepted a model)

theorem checked_empty_unsatisfiable (variables : Nat) (db : Database) (hints : List Nat)
    (accepted : (check variables db [] hints).isSome = true) : Unsatisfiable db := by
  intro a model
  obtain ⟨l, member, _⟩ := check_entails variables db [] hints accepted a model
  simp at member

#print axioms assigned_tail
#print axioms literal_write
#print axioms prepare
#print axioms chain
#print axioms assumptions_entail
#print axioms check
#print axioms check_entails
#print axioms checked_insert_preserves
#print axioms checked_empty_unsatisfiable
end OakVerification.PropagationChain
