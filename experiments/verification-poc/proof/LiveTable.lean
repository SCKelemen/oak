import RangeBridge

/-! Zero-based live range table and its one-based logical database.
Updates below describe publication, not permission to publish: add_step requires
an actual RUP derivation. Concrete Oak array correspondence is tested separately. -/
set_option autoImplicit false
namespace OakVerification.LiveTable
open Ranges

structure Entry where
  start : Nat
  count : Nat
  live : Bool
  deriving Repr
abbrev Table := Nat → Entry

def dead : Entry := ⟨0, 0, false⟩
def meaning (pool : List Nat) (e : Entry) : Option Clause :=
  if e.live then readClause pool e.start e.count else none
def database (pool : List Nat) (t : Table) : Database :=
  fun id => if id = 0 then none else meaning pool (t (id - 1))
def publish (t : Table) (slot start count : Nat) : Table :=
  fun key => if key = slot then ⟨start, count, true⟩ else t key
def clear (t : Table) (slot : Nat) : Table :=
  fun key => if key = slot then { t key with live := false } else t key
def initialTable (ranges : List (Nat × Nat)) : Table :=
  fun slot => match ranges[slot]? with
    | none => dead
    | some r => ⟨r.1, r.2, true⟩

theorem initialize_lookup (pool : List Nat) (ranges : List (Nat × Nat)) (id : Nat) :
    database pool (initialTable ranges) id =
      if id = 0 then none else (ranges[id - 1]?).bind (fun r => readClause pool r.1 r.2) := by
  by_cases h : id = 0
  · simp [database, h]
  · simp only [database, h, ↓reduceIte, initialTable]
    cases ranges[id - 1]? <;> rfl

-- The premise states per-index range decoding, including out-of-range indices.
-- It is a representation premise, not an unsatisfiability assumption.
theorem initialize_refines (pool : List Nat) (ranges : List (Nat × Nat))
    (clauses : List Clause)
    (decoded : ∀ slot, (ranges[slot]?).bind (fun r => readClause pool r.1 r.2) = clauses[slot]?) :
    database pool (initialTable ranges) = initialDatabase clauses := by
  funext id
  rw [initialize_lookup]
  simp only [initialDatabase, decoded]

theorem publish_refines (pool : List Nat) (t : Table) (id start count : Nat)
    (positive : 0 < id) (clause : Clause)
    (decoded : readClause pool start count = some clause) :
    database pool (publish t (id - 1) start count) = insert (database pool t) id clause := by
  funext key
  by_cases zero : key = 0
  · subst key
    have nz : ¬ 0 = id := by omega
    simp [database, insert, nz]
  · by_cases same : key = id
    · subst key
      simp [database, publish, meaning, insert, zero, decoded]
    · have different : key - 1 ≠ id - 1 := by omega
      simp [database, publish, insert, zero, same, different]

theorem clear_refines (pool : List Nat) (t : Table) (id : Nat) (positive : 0 < id) :
    database pool (clear t (id - 1)) = erase (database pool t) [id] := by
  funext key
  by_cases zero : key = 0
  · subst key
    have nz : ¬ 0 = id := by omega
    simp [database, erase, nz]
  · by_cases same : key = id
    · subst key
      simp [database, clear, meaning, erase, zero]
    · have different : key - 1 ≠ id - 1 := by omega
      simp [database, clear, erase, zero, same, different]

theorem clear_metadata (t : Table) (slot : Nat) :
    (clear t slot slot).start = (t slot).start ∧
    (clear t slot slot).count = (t slot).count ∧
    (clear t slot slot).live = false := by simp [clear]

theorem publish_other (t : Table) (slot start count key : Nat) (h : key ≠ slot) :
    publish t slot start count key = t key := by simp [publish, h]

theorem clear_twice (t : Table) (slot : Nat) : clear (clear t slot) slot = clear t slot := by
  funext key
  by_cases h : key = slot <;> simp [clear, h]

theorem add_step (pool : List Nat) (t : Table) (id start count : Nat)
    (positive : 0 < id) (clause : Clause) (hints : List Nat)
    (decoded : readClause pool start count = some clause)
    (justified : Propagate (database pool t) (clause.map negate) hints) :
    Step (database pool t) (database pool (publish t (id - 1) start count)) := by
  rw [publish_refines pool t id start count positive clause decoded]
  exact Step.add _ _ _ _ justified

theorem delete_step (pool : List Nat) (t : Table) (id : Nat) (positive : 0 < id) :
    Step (database pool t) (database pool (clear t (id - 1))) := by
  rw [clear_refines pool t id positive]
  exact Step.delete _ _

-- Snapshot execution follows the bounded operational guards. The theorems above
-- concern its table primitives; a whole-run refinement theorem remains future work.
structure State where
  table : Table
  last : Nat
  refuted : Bool
  valid : Bool

def snapshot (s : State) : List Nat :=
  [s.last, if s.refuted then 1 else 0, if s.valid then 1 else 0] ++
  (List.range 256).flatMap (fun slot =>
    let e := s.table slot
    [e.start, e.count, if e.live then 1 else 0])

def deleteIDs : State → List Nat → State
  | s, [] => s
  | s, id :: rest =>
    if !s.valid then s
    else if id = 0 ∨ 256 < id then { s with valid := false }
    else deleteIDs { s with table := clear s.table (id - 1), valid := (s.table (id - 1)).live } rest

def command (raw : Layout) (s : State) (c : Command) : State := Id.run do
  if c.id > 2147483647 then return { s with valid := false }
  let some refs := readRange raw.refs c.refsStart c.refsCount | return { s with valid := false }
  if c.addition then
    if c.id ≤ s.last ∨ c.id > 256 ∨ c.refsCount > 256 then return { s with valid := false }
    let some clause := readClause raw.pool c.start c.count | return { s with valid := false }
    if !(refs.all fun id => decide (0 < id ∧ id ≤ 256) && (s.table (id - 1)).live) then
      return { s with valid := false }
    if (checkRUP (database raw.pool s.table) clause refs).isNone then return { s with valid := false }
    return ⟨publish s.table (c.id - 1) c.start c.count, c.id, s.refuted || c.count == 0, true⟩
  else
    if c.id < s.last then return { s with valid := false }
    return deleteIDs s refs

def trace (raw : Layout) : List Nat := Id.run do
  let mut s : State := ⟨fun _ => dead, raw.starts.length, false,
    decide (0 < raw.variables ∧ raw.variables ≤ 64 ∧ raw.pool.length ≤ 4096 ∧
      raw.refs.length ≤ 4096 ∧ raw.starts.length = raw.sizes.length ∧
      raw.starts.length ≤ 256 ∧ raw.commands.length ≤ 256)⟩
  if !(raw.pool.all fun n => decide (n / 2 < raw.variables)) then s := { s with valid := false }
  let mut slot := 0
  for r in raw.starts.zip raw.sizes do
    if s.valid then
      if (readRange raw.pool r.1 r.2).isSome then
        s := { s with table := publish s.table slot r.1 r.2, refuted := s.refuted || r.2 == 0 }
      else s := { s with valid := false }
    slot := slot + 1
  let mut out := snapshot s
  for c in raw.commands do
    if s.valid then
      s := command raw s c
      out := out ++ snapshot s
  return out

#print axioms initialize_lookup
#print axioms initialize_refines
#print axioms publish_refines
#print axioms clear_refines
#print axioms clear_metadata
#print axioms publish_other
#print axioms clear_twice
#print axioms add_step
#print axioms delete_step
end OakVerification.LiveTable
