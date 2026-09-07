import RUPSoundness

/-!
A proof-producing, executable checker for decoded RUP/deletion instructions.
Proof fields are erased during execution. Successful checks carry derivations
in RUPSoundness; the Go implementation and input decoders are not verified here.
-/
set_option autoImplicit false
namespace OakVerification

instance (xs : List Literal) (c : Clause) : Decidable (Falsified xs c) :=
  inferInstanceAs (Decidable (∀ l ∈ c, negate l ∈ xs))
instance (xs : List Literal) (c : Clause) (u : Literal) : Decidable (UnitUnder xs c u) :=
  inferInstanceAs (Decidable (u ∈ c ∧ ∀ l ∈ c, l = u ∨ negate l ∈ xs))

structure CheckedPropagation (db : Database) (xs : List Literal) (hints : List Nat) : Type where
  derivation : Propagate db xs hints

-- Searching the finite clause avoids assuming the existence of a unit literal.
-- Repeated literals have set semantics, as in Go's Clause map.
def findUnit (xs : List Literal) (c : Clause) :
    List Literal → Option { u : Literal // UnitUnder xs c u }
  | [] => none
  | u :: rest =>
    if h : UnitUnder xs c u then some ⟨u, h⟩ else findUnit xs c rest

def checkChain (db : Database) (xs : List Literal) :
    (hints : List Nat) → Option (CheckedPropagation db xs hints)
  | [] => none
  | id :: tail =>
    match lookup : db id with
    | none => none
    | some c =>
      if ∃ l ∈ c, l ∈ xs then none
      else if falsified : Falsified xs c then
        match tail with
        | [] => some ⟨Propagate.conflict lookup falsified⟩
        | _ :: _ => none
      else
        match findUnit xs c c with
        | none => none
        | some u =>
          match checkChain db (u.val :: xs) tail with
          | none => none
          | some next => some ⟨Propagate.unit lookup u.property next.derivation⟩

def checkRUP (db : Database) (c : Clause) (hints : List Nat) :
    Option (CheckedPropagation db (c.map negate) hints) :=
  -- Prevalidate even the hints attached to a tautological target.
  if hints.all (fun id => decide (0 < id) && (db id).isSome) then
    if clash : ∃ l ∈ c.map negate, negate l ∈ c.map negate then
      some ⟨by
        obtain ⟨l, present, opposite⟩ := clash
        exact Propagate.clash present opposite⟩
    else checkChain db (c.map negate) hints
  else none

theorem checkRUP_sound {db : Database} {c : Clause} {hints : List Nat}
    (accepted : (checkRUP db c hints).isSome = true) :
    Propagate db (c.map negate) hints := by
  cases result : checkRUP db c hints with
  | none => simp [result] at accepted
  | some checked => exact checked.derivation

inductive Instruction where
  | add (id : Nat) (clause : Clause) (hints : List Nat)
  | delete (stamp : Nat) (ids : List Nat)
  deriving Repr

-- The table is finite at initialization, with DIMACS IDs starting at one.
def initialDatabase (clauses : List Clause) : Database :=
  fun id => if id = 0 then none else clauses[id - 1]?

def findEmpty (db : Database) : List Nat → Option { id : Nat // db id = some [] }
  | [] => none
  | id :: rest => if h : db id = some [] then some ⟨id, h⟩ else findEmpty db rest

structure CheckedState (initial : Database) where
  database : Database
  last : Nat
  steps : Steps initial database
  empty : Bool
  sound : empty = true → Unsatisfiable initial

def initialState (clauses : List Clause) : CheckedState (initialDatabase clauses) :=
  let db := initialDatabase clauses
  match findEmpty db ((List.range clauses.length).map (· + 1)) with
  | none => ⟨db, clauses.length, Steps.refl db, false, by simp⟩
  | some found =>
    ⟨db, clauses.length, Steps.refl db, true,
      fun _ => accepted_unsatisfiable ⟨db, found.val, Steps.refl db, found.property⟩⟩

theorem steps_trans {a b c : Database} (ab : Steps a b) (bc : Steps b c) : Steps a c := by
  induction bc with
  | refl => exact ab
  | next prior step ih => exact Steps.next ih step

-- Deletions are checked sequentially: absent IDs and repeated IDs both fail.
def eraseChecked (db : Database) : List Nat → Option { next : Database // Steps db next }
  | [] => some ⟨db, Steps.refl db⟩
  | id :: rest =>
    if id = 0 ∨ (db id).isNone then none
    else
      match eraseChecked (erase db [id]) rest with
      | none => none
      | some next =>
        some ⟨next.val, steps_trans
          (Steps.next (Steps.refl db) (Step.delete db [id])) next.property⟩

def checkInstruction {initial : Database} (variables : Nat)
    (state : CheckedState initial) : Instruction → Option (CheckedState initial)
  | .add id c hints =>
    if id ≤ state.last ∨ ¬ c.all (fun l => decide (0 < l.index ∧ l.index ≤ variables)) then none
    else
      match checkRUP state.database c hints with
      | none => none
      | some checked =>
        let db := insert state.database id c
        let steps := Steps.next state.steps (Step.add state.database id c hints checked.derivation)
        if empty : c = [] then
          some ⟨db, id, steps, true, fun _ =>
            accepted_unsatisfiable ⟨db, id, steps, by simp [db, insert, empty]⟩⟩
        else some ⟨db, id, steps, state.empty, state.sound⟩
  | .delete stamp ids =>
    if stamp < state.last then none
    else
      match eraseChecked state.database ids with
      | none => none
      | some next =>
        some ⟨next.val, state.last, steps_trans state.steps next.property,
          state.empty, state.sound⟩

def checkInstructions {initial : Database} (variables : Nat)
    (state : CheckedState initial) : List Instruction → Option (CheckedState initial)
  | [] => some state
  | command :: rest =>
    match checkInstruction variables state command with
    | none => none
    | some next => checkInstructions variables next rest

def checkProof (variables : Nat) (clauses : List Clause) (commands : List Instruction) : Bool :=
  match checkInstructions variables (initialState clauses) commands with
  | none => false
  | some state => state.empty

theorem checkProof_sound {variables : Nat} {clauses : List Clause} {commands : List Instruction}
    (accepted : checkProof variables clauses commands = true) :
    Unsatisfiable (initialDatabase clauses) := by
  unfold checkProof at accepted
  cases result : checkInstructions variables (initialState clauses) commands with
  | none => simp [result] at accepted
  | some state =>
    exact state.sound (by simpa [result] using accepted)

#print axioms checkRUP_sound
#print axioms checkProof_sound
end OakVerification
