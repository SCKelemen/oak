import LiveTable
import PropagationChain

set_option autoImplicit false
namespace OakVerification.CertifiedStream
open Ranges

def origin (raw : Layout) : Database :=
  LiveTable.database raw.pool (LiveTable.initialTable (raw.starts.zip raw.sizes))

structure State (pool : List Nat) (initial : Database) where
  table : LiveTable.Table
  last : Nat
  refuted : Bool
  preserves : ∀ a, Models a initial → Models a (LiveTable.database pool table)
  sound : refuted = true → Unsatisfiable initial

theorem empty_database (db : Database) (id : Nat) (empty : db id = some []) :
    Unsatisfiable db := by
  intro a model
  obtain ⟨l, impossible, _⟩ := model id [] empty
  simp at impossible

def initialState (raw : Layout) : State raw.pool (origin raw) :=
  let table := LiveTable.initialTable (raw.starts.zip raw.sizes)
  match findEmpty (origin raw) ((List.range raw.starts.length).map (· + 1)) with
  | none => ⟨table, raw.starts.length, false, fun _ model => model, by simp⟩
  | some found => ⟨table, raw.starts.length, true, fun _ model => model,
      fun _ => empty_database (origin raw) found.val found.property⟩

def publishCertified {pool : List Nat} {initial : Database} (s : State pool initial)
    (id start count : Nat) (positive : 0 < id) (clause : Clause)
    (decoded : readClause pool start count = some clause)
    (certificate : PropagationChain.CertifiedClause (LiveTable.database pool s.table) clause) :
    State pool initial :=
  let table := LiveTable.publish s.table (id - 1) start count
  let preserves : ∀ a, Models a initial → Models a (LiveTable.database pool table) := by
    intro a model
    rw [LiveTable.publish_refines pool s.table id start count positive clause decoded]
    exact insert_preserves (s.preserves a model) (certificate.entails a (s.preserves a model))
  if empty : clause = [] then
    ⟨table, id, true, preserves, fun _ a model => by
      obtain ⟨l, impossible, _⟩ := certificate.entails a (s.preserves a model)
      simp [empty] at impossible⟩
  else ⟨table, id, s.refuted, preserves, s.sound⟩

def eraseOne {pool : List Nat} {initial : Database} (s : State pool initial)
    (id : Nat) (positive : 0 < id) : State pool initial :=
  ⟨LiveTable.clear s.table (id - 1), s.last, s.refuted, (by
    intro a model
    rw [LiveTable.clear_refines pool s.table id positive]
    exact erase_preserves [id] (s.preserves a model)), s.sound⟩

theorem deletion_keeps_refutation {pool : List Nat} {initial : Database}
    (s : State pool initial) (id : Nat) (positive : 0 < id) :
    (eraseOne s id positive).refuted = s.refuted := rfl

theorem deletion_keeps_last {pool : List Nat} {initial : Database}
    (s : State pool initial) (id : Nat) (positive : 0 < id) :
    (eraseOne s id positive).last = s.last := rfl

-- Sequential rejection makes absent and duplicate deletions invalid.
def deleteIDs {pool : List Nat} {initial : Database} (s : State pool initial) :
    List Nat → Option (State pool initial)
  | [] => some s
  | id :: rest =>
    if positive : 0 < id ∧ id ≤ 256 then
      if (s.table (id - 1)).live then deleteIDs (eraseOne s id positive.1) rest else none
    else none

def command {initial : Database} (raw : Layout) (s : State raw.pool initial)
    (c : Command) : Option (State raw.pool initial) :=
  if c.id > 2147483647 then none
  else match readRange raw.refs c.refsStart c.refsCount with
  | none => none
  | some refs =>
    if c.addition then
      if fresh : s.last < c.id ∧ c.id ≤ 256 then
        if c.refsCount > 256 then none
        else if !(refs.all fun id => decide (0 < id ∧ id ≤ 256) && (s.table (id - 1)).live) then none
        else match decoded : readClause raw.pool c.start c.count with
        | none => none
        | some clause =>
          match PropagationChain.check raw.variables (LiveTable.database raw.pool s.table) clause refs with
          | none => none
          | some certificate => some (publishCertified s c.id c.start c.count
              (by omega) clause decoded certificate)
      else none
    else if c.id < s.last then none else deleteIDs s refs

def commands {initial : Database} (raw : Layout) (s : State raw.pool initial) :
    List Command → Option (State raw.pool initial)
  | [] => some s
  | c :: rest =>
    match command raw s c with
    | none => none
    | some next => commands raw next rest

-- The entire suffix is checked even after refutation, including deletions of
-- an already-derived empty clause. All format/resource guards are executable.
def run (raw : Layout) : Option (State raw.pool (origin raw)) :=
  if ¬ (0 < raw.variables ∧ raw.variables ≤ 64 ∧ raw.pool.length ≤ 4096 ∧
      raw.refs.length ≤ 4096 ∧ raw.starts.length = raw.sizes.length ∧
      raw.starts.length ≤ 256 ∧ raw.commands.length ≤ 256) then none
  else if !(raw.pool.all fun n => decide (n / 2 < raw.variables)) then none
  else if !((raw.starts.zip raw.sizes).all fun r => (readRange raw.pool r.1 r.2).isSome) then none
  else commands raw (initialState raw) raw.commands

def check (raw : Layout) : Bool :=
  match run raw with
  | none => false
  | some s => s.refuted

theorem check_sound (raw : Layout) (accepted : check raw = true) :
    Unsatisfiable (origin raw) := by
  unfold check at accepted
  cases result : run raw with
  | none => simp [result] at accepted
  | some s => exact s.sound (by simpa [result] using accepted)

-- The range representation premise is explicit. No semantic assumption or
-- unsatisfiability premise is needed to transport soundness to decoded clauses.
theorem decoded_sound (raw : Layout) (clauses : List Clause)
    (decoded : ∀ slot : Nat, ((raw.starts.zip raw.sizes)[slot]?).bind
      (fun r => readClause raw.pool r.1 r.2) = clauses[slot]?)
    (accepted : check raw = true) : Unsatisfiable (initialDatabase clauses) := by
  have same := LiveTable.initialize_refines raw.pool (raw.starts.zip raw.sizes) clauses decoded
  rw [← same]
  exact check_sound raw accepted

#print axioms empty_database
#print axioms initialState
#print axioms publishCertified
#print axioms eraseOne
#print axioms deletion_keeps_refutation
#print axioms deletion_keeps_last
#print axioms deleteIDs
#print axioms command
#print axioms commands
#print axioms run
#print axioms check_sound
#print axioms decoded_sound
end OakVerification.CertifiedStream
