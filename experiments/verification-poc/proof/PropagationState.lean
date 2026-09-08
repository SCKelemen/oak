import RangeBridge

set_option autoImplicit false
namespace OakVerification.PropagationState

abbrev Scratch := Nat → Option Bool
abbrev Cells := Nat → Nat

def encode : Option Bool → Nat
  | none => 0
  | some false => 1
  | some true => 2
def decode (n : Nat) : Option Bool :=
  if n = 1 then some false else if n = 2 then some true else none
def project (cells : Cells) : Scratch := fun slot => decode (cells slot)
def write (s : Scratch) (slot : Nat) (b : Bool) : Scratch :=
  fun key => if key = slot then some b else s key
def storeCell (cells : Cells) (slot value : Nat) : Cells :=
  fun key => if key = slot then value else cells key

theorem decode_encode (v : Option Bool) : decode (encode v) = v := by
  cases v with
  | none => rfl
  | some b => cases b <;> rfl

theorem encode_decode (n : Nat) (valid : n ≤ 2) : encode (decode n) = n := by
  have h : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases h with h | h | h <;> subst n <;> rfl

theorem store_refines (cells : Cells) (slot : Nat) (b : Bool) :
    project (storeCell cells slot (encode (some b))) = write (project cells) slot b := by
  funext key
  by_cases h : key = slot <;> simp [project, storeCell, write, h, decode_encode]

theorem store_other (cells : Cells) (slot value key : Nat) (h : key ≠ slot) :
    storeCell cells slot value key = cells key := by simp [storeCell, h]

def Extends (a : Assignment) (s : Scratch) : Prop :=
  ∀ slot b, s slot = some b → a (slot + 1) = b

theorem empty_extends (a : Assignment) : Extends a (fun _ => none) := by
  intro slot b h
  cases h

theorem write_extends (a : Assignment) (s : Scratch) (slot : Nat) (b : Bool)
    (old : Extends a s) (value : a (slot + 1) = b) : Extends a (write s slot b) := by
  intro key v h
  by_cases same : key = slot
  · subst key
    simp [write] at h
    cases h
    exact value
  · exact old key v (by simpa [write, same] using h)

def FalseUnder (s : Scratch) (l : Literal) : Prop :=
  s (l.index - 1) = some (!l.positive)

theorem false_excludes (a : Assignment) (s : Scratch) (l : Literal)
    (positive : 0 < l.index) (compatible : Extends a s) (f : FalseUnder s l) : ¬ Holds a l := by
  have value := compatible (l.index - 1) (!l.positive) f
  have index : l.index - 1 + 1 = l.index := by omega
  rw [index] at value
  intro holds
  unfold Holds at holds
  rw [holds] at value
  cases l.positive <;> simp at value

theorem conflict_sound (a : Assignment) (s : Scratch) (clause : Clause)
    (bounds : ∀ l ∈ clause, 0 < l.index)
    (compatible : Extends a s) (f : ∀ l ∈ clause, FalseUnder s l) :
    ¬ SatisfiesClause a clause := by
  intro sat
  obtain ⟨l, member, holds⟩ := sat
  exact false_excludes a s l (bounds l member) compatible (f l member) holds

theorem unit_sound (a : Assignment) (s : Scratch) (clause : Clause) (u : Literal)
    (bounds : ∀ l ∈ clause, 0 < l.index)
    (compatible : Extends a s) (sat : SatisfiesClause a clause)
    (unit : ∀ l ∈ clause, l = u ∨ FalseUnder s l) : Holds a u := by
  obtain ⟨l, member, holds⟩ := sat
  rcases unit l member with same | falsified
  · simpa [same] using holds
  · exact False.elim (false_excludes a s l (bounds l member) compatible falsified holds)

theorem unit_write_extends (a : Assignment) (s : Scratch) (clause : Clause) (u : Literal)
    (bounds : ∀ l ∈ clause, 0 < l.index) (positive : 0 < u.index)
    (compatible : Extends a s) (sat : SatisfiesClause a clause)
    (unit : ∀ l ∈ clause, l = u ∨ FalseUnder s l) :
    Extends a (write s (u.index - 1) u.positive) := by
  apply write_extends a s (u.index - 1) u.positive compatible
  have h := unit_sound a s clause u bounds compatible sat unit
  have index : u.index - 1 + 1 = u.index := by omega
  rw [index]
  exact h

-- Bounded executable trace model. The semantic lemmas above do not yet prove
-- that this whole executor establishes every classification premise universally.
structure Input where
  variables : Nat
  clauses : List (List Nat)
  target : List Nat
  hints : List Nat -- One-based IDs; zero represents an invalid hint.

def literalValue (n : Nat) : Nat := if n % 2 = 1 then 2 else 1
def falseValue (n : Nat) : Nat := if n % 2 = 1 then 1 else 2
structure State where
  cells : Cells
  valid : Bool
  contradictory : Bool
  conflict : Bool

def snapshot (s : State) : List Nat :=
  [if s.valid then 1 else 0, if s.contradictory then 1 else 0, if s.conflict then 1 else 0] ++
  (List.range 64).map s.cells

def assumeLiteral (variables : Nat) (s : State) (n : Nat) : State :=
  if n / 2 ≥ variables then { s with valid := false }
  else
    let prior := s.cells (n / 2)
    { s with contradictory := (prior != 0 && prior != (falseValue n)),
      cells := if prior = 0 then storeCell s.cells (n / 2) (falseValue n) else s.cells }

def hintStep (variables : Nat) (s : State) (clause : List Nat) (finalHint : Bool) : State := Id.run do
  let mut valid := true
  let mut satisfied := false
  let mut unknown : List Nat := []
  let mut seen : List Nat := []
  for n in clause do
    if valid && !satisfied then
      if n / 2 ≥ variables then valid := false
      else if !seen.contains n then
        let assigned := s.cells (n / 2)
        satisfied := assigned != 0 && assigned == literalValue n
        if assigned == 0 then unknown := unknown ++ [n]
      seen := n :: seen
  if !valid || satisfied then return { s with valid := false }
  match unknown with
  | [] => return { s with valid := finalHint, conflict := finalHint }
  | [n] => return { s with cells := storeCell s.cells (n / 2) (literalValue n) }
  | _ => return { s with valid := false }

def trace (input : Input) : List Nat := Id.run do
  let valid := decide (0 < input.variables ∧ input.variables ≤ 64)
  -- Every caller cell starts poisoned; only the declared variable prefix resets.
  let cells : Cells := fun slot => if valid && slot < input.variables then 0 else 7
  let mut s : State := ⟨cells, valid && input.hints.all (fun id => decide (0 < id ∧ id ≤ input.clauses.length)), false, false⟩
  let mut out := snapshot s
  for n in input.target do
    if s.valid && !s.contradictory then
      s := assumeLiteral input.variables s n
      out := out ++ snapshot s
  let mut index := 0
  for id in input.hints do
    if s.valid && !s.contradictory && !s.conflict then
      s := hintStep input.variables s (input.clauses[id - 1]?.getD []) (index + 1 == input.hints.length)
      out := out ++ snapshot s
    index := index + 1
  return out

#print axioms decode_encode
#print axioms encode_decode
#print axioms store_refines
#print axioms store_other
#print axioms empty_extends
#print axioms write_extends
#print axioms false_excludes
#print axioms conflict_sound
#print axioms unit_sound
#print axioms unit_write_extends
end OakVerification.PropagationState
