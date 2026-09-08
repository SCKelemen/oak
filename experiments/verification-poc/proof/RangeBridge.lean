import PackedBuffers
import RUPExecutable

set_option autoImplicit false
namespace OakVerification.Ranges
open OakVerification.Decimal

def encodeLiteral (l : Literal) : Nat := (l.index - 1) * 2 + if l.positive then 1 else 0
def decodeLiteral (n : Nat) : Literal := ⟨n / 2 + 1, decide (n % 2 = 1)⟩

theorem decode_encode (l : Literal) (h : 0 < l.index) :
    decodeLiteral (encodeLiteral l) = l := by
  cases l with
  | mk index positive =>
    cases positive <;> simp [encodeLiteral, decodeLiteral] <;> omega

theorem encode_decode (n : Nat) : encodeLiteral (decodeLiteral n) = n := by
  by_cases h : n % 2 = 1 <;> simp [encodeLiteral, decodeLiteral, h] <;> omega

theorem decoded_bounds (n variables : Nat) (h : n / 2 < variables) :
    0 < (decodeLiteral n).index ∧ (decodeLiteral n).index ≤ variables := by
  simp only [decodeLiteral]
  omega

def readRange (pool : List Nat) (start count : Nat) : Option (List Nat) :=
  if rangeSafe start count pool.length then some ((pool.drop start).take count) else none

theorem readRange_refines (pool : List Nat) (start count : Nat) :
    readRange pool start count =
      if start + count ≤ pool.length then some ((pool.drop start).take count) else none := by
  simp only [readRange, rangeSafe_refines]

theorem drop_prefix (prefix tail : List Nat) : (prefix ++ tail).drop prefix.length = tail := by
  induction prefix with
  | nil => rfl
  | cons x xs ih => simpa using ih

theorem take_prefix (items suffix : List Nat) : (items ++ suffix).take items.length = items := by
  induction items with
  | nil => rfl
  | cons x xs ih => simpa using ih

-- Closed ranges survive all subsequent appends to the same initialized pool.
theorem range_contents (prefix items suffix : List Nat) :
    readRange (prefix ++ items ++ suffix) prefix.length items.length = some items := by
  rw [readRange_refines]
  have h : prefix.length + items.length ≤ (prefix ++ items ++ suffix).length := by simp
  rw [if_pos h, List.append_assoc, drop_prefix, take_prefix]

theorem completed_pending (b : Packed.Buffer) (h : Packed.WellFormed b) :
    readRange (Packed.closeSegment b).pool (Packed.start b) b.pending.length = some b.pending := by
  have hs := (Packed.pending_range b h).1
  have hp := h.1
  change readRange b.pool (Packed.start b) b.pending.length = some b.pending
  rw [hs, hp]
  simpa using range_contents b.closed.flatten b.pending []

def readClause (pool : List Nat) (start count : Nat) : Option Clause :=
  (readRange pool start count).map (List.map decodeLiteral)

theorem clause_contents (prefix items suffix : List Nat) :
    readClause (prefix ++ items ++ suffix) prefix.length items.length = some (items.map decodeLiteral) := by
  simp [readClause, range_contents]

theorem reference_contents (prefix ids suffix : List Nat) :
    readRange (prefix ++ ids ++ suffix) prefix.length ids.length = some ids :=
  range_contents prefix ids suffix

structure Command where
  addition : Bool
  id : Nat
  start : Nat
  count : Nat
  refsStart : Nat
  refsCount : Nat
  deriving Repr
structure Layout where
  variables : Nat
  pool : List Nat
  starts : List Nat
  sizes : List Nat
  refs : List Nat
  commands : List Command
structure Decoded where
  clauses : List Clause
  commands : List Instruction

-- These are representation/profile guards. Liveness, RUP and ID evolution
-- remain the responsibility of the independently proved decoded checker.
def decodeCommand (pool refs : List Nat) (c : Command) : Option Instruction := do
  if c.id > 2147483647 then none else do
    let ids ← readRange refs c.refsStart c.refsCount
    if !(ids.all (fun id => decide (0 < id ∧ id ≤ 256))) then none else do
      if c.addition then
        if c.id > 256 || c.refsCount > 256 then none else do
          let clause ← readClause pool c.start c.count
          return .add c.id clause ids
      else return .delete c.id ids

def decodeLayout (raw : Layout) : Option Decoded := do
  if raw.variables = 0 || raw.variables > 64 || raw.pool.length > 4096 ||
      raw.refs.length > 4096 || raw.starts.length != raw.sizes.length ||
      raw.starts.length > 256 || raw.commands.length > 256 then none else do
    if !(raw.pool.all (fun n => decide (n / 2 < raw.variables))) then none else do
      let clauses ← (raw.starts.zip raw.sizes).mapM (fun r => readClause raw.pool r.1 r.2)
      let commands ← raw.commands.mapM (decodeCommand raw.pool raw.refs)
      return ⟨clauses, commands⟩

def checkLayout (raw : Layout) : Bool :=
  match decodeLayout raw with
  | none => false
  | some d => checkProof raw.variables d.clauses d.commands

-- No assumed Oak correspondence premise: this is a theorem about the executable
-- range decoder composed with the already proved Lean proof-stream checker.
theorem checkLayout_sound (raw : Layout) (h : checkLayout raw = true) :
    ∃ d, decodeLayout raw = some d ∧ Unsatisfiable (initialDatabase d.clauses) := by
  cases hd : decodeLayout raw with
  | none => simp [checkLayout, hd] at h
  | some d =>
    exact ⟨d, hd, checkProof_sound (by simpa [checkLayout, hd] using h)⟩

#print axioms decode_encode
#print axioms encode_decode
#print axioms decoded_bounds
#print axioms readRange_refines
#print axioms range_contents
#print axioms completed_pending
#print axioms clause_contents
#print axioms reference_contents
#print axioms checkLayout_sound
end OakVerification.Ranges
