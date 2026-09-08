import ScannerState

set_option autoImplicit false
namespace OakVerification.Packed
open OakVerification.Decimal OakVerification.Scanner

structure Buffer where
  capacity : Nat
  pool : List Nat
  closed : List (List Nat)
  pending : List Nat
  deriving BEq, Repr, DecidableEq

def WellFormed (b : Buffer) : Prop :=
  b.pool = b.closed.flatten ++ b.pending ∧ b.pool.length ≤ b.capacity

def empty (capacity : Nat) : Buffer := ⟨capacity, [], [], []⟩
def push (b : Buffer) (item : Nat) : Option Buffer :=
  if b.pool.length < b.capacity then
    some { b with pool := b.pool ++ [item], pending := b.pending ++ [item] }
  else none

def closeSegment (b : Buffer) : Buffer :=
  { b with closed := b.closed ++ [b.pending], pending := [] }

theorem empty_wellFormed (capacity : Nat) : WellFormed (empty capacity) := by
  simp [WellFormed, empty]

theorem push_preserves {b after : Buffer} {item : Nat}
    (hb : WellFormed b) (h : push b item = some after) : WellFormed after := by
  unfold push at h
  split at h
  · rename_i room
    cases Option.some.inj h
    obtain ⟨hp, _⟩ := hb
    constructor
    · simp [hp, List.append_assoc]
    · simp only [List.length_append, List.length_singleton]; omega
  · simp at h

theorem push_layout {b after : Buffer} {item : Nat}
    (h : push b item = some after) :
    after.pool = b.pool ++ [item] ∧ after.pending = b.pending ++ [item] ∧
    after.closed = b.closed ∧ after.capacity = b.capacity ∧ b.pool.length < b.capacity := by
  unfold push at h
  split at h
  · cases Option.some.inj h; exact ⟨rfl, rfl, rfl, rfl, by assumption⟩
  · simp at h

theorem push_full (b : Buffer) (item : Nat) (h : b.capacity ≤ b.pool.length) : push b item = none := by
  simp [push, show ¬ b.pool.length < b.capacity by omega]

theorem seal_preserves (b : Buffer) (h : WellFormed b) : WellFormed (closeSegment b) := by
  obtain ⟨hp, hc⟩ := h
  constructor
  · simpa [closeSegment, List.flatten_append] using hp
  · exact hc

theorem seal_layout (b : Buffer) :
    (closeSegment b).pool = b.pool ∧ (closeSegment b).closed = b.closed ++ [b.pending] ∧
    (closeSegment b).pending = [] := by simp [closeSegment]

-- The decoder stores this start/count pair when it sees a zero terminator.
def start (b : Buffer) : Nat := b.pool.length - b.pending.length

theorem pending_range (b : Buffer) (h : WellFormed b) :
    start b = b.closed.flatten.length ∧
    start b + b.pending.length = b.pool.length ∧
    rangeSafe (start b) b.pending.length b.pool.length := by
  obtain ⟨hp, _⟩ := h
  have hl : b.pool.length = b.closed.flatten.length + b.pending.length := by
    rw [hp, List.length_append]
  unfold start rangeSafe
  omega

theorem pending_index (b : Buffer) (h : WellFormed b) (offset : Nat)
    (hi : offset < b.pending.length) : start b + offset < b.pool.length := by
  obtain ⟨_, _, hr⟩ := pending_range b h
  exact range_index hr hi

inductive Mode where
  | literal | hint | deletion
  deriving BEq, Repr, DecidableEq

-- The exact spelling of deletion's terminator is checked by the byte adapter.
def tokenStep (mode : Mode) (variables : Nat) (b : Buffer) (t : Token) : Option Buffer :=
  if t.kind = 2 ∧ (t.sign = 1 ∨ t.sign = 2) then
    if t.magnitude = 0 then some (closeSegment b)
    else if mode = .literal then
      if t.magnitude ≤ variables then
        push b ((t.magnitude - 1) * 2 + if t.sign = 1 then 1 else 0)
      else none
    else if t.sign = 1 then push b t.magnitude else none
  else none

theorem tokenStep_preserves {mode : Mode} {variables : Nat} {b after : Buffer} {t : Token}
    (hb : WellFormed b) (h : tokenStep mode variables b t = some after) :
    WellFormed after := by
  unfold tokenStep at h
  split at h
  · split at h
    · cases Option.some.inj h; exact seal_preserves b hb
    · split at h
      · split at h
        · exact push_preserves hb h
        · simp at h
      · split at h
        · exact push_preserves hb h
        · simp at h
  · simp at h

theorem zero_seals (mode : Mode) (variables : Nat) (b : Buffer) (t : Token)
    (hk : t.kind = 2) (hs : t.sign = 1 ∨ t.sign = 2) (hz : t.magnitude = 0) :
    tokenStep mode variables b t = some (closeSegment b) := by
  simp [tokenStep, hk, hs, hz]

def tokens (mode : Mode) (variables : Nat) (b : Buffer) : List Token → Option Buffer
  | [] => some b
  | t :: ts => (tokenStep mode variables b t).bind (fun after => tokens mode variables after ts)

theorem tokens_preserve (mode : Mode) (variables : Nat) (b : Buffer) (ts : List Token)
    (hb : WellFormed b) (after : Buffer) (h : tokens mode variables b ts = some after) :
    WellFormed after := by
  induction ts generalizing b with
  | nil => simp only [tokens, Option.some.injEq] at h; subst after; exact hb
  | cons t ts ih =>
    simp only [tokens] at h
    cases hs : tokenStep mode variables b t with
    | none => simp [hs] at h
    | some next =>
      simp only [hs, Option.bind] at h
      exact ih next (tokenStep_preserves hb hs) h

-- Byte-to-token adapter for one zero-terminated segment, not a full file parser.
def segmentLoop (mode : Mode) (variables : Nat) (bytes : List Nat)
    (pos : Nat) (b : Buffer) : Nat → Option Buffer
  | 0 => none
  | fuel + 1 =>
    let t := scan bytes pos
    if t.kind = 0 then none
    else if t.kind = 1 then segmentLoop mode variables bytes t.next b fuel
    else if mode = .deletion ∧ t.magnitude = 0 ∧
        ¬ (t.stop = t.start + 1 ∧ bytes[t.start]? = some 48) then none
    else (tokenStep mode variables b t).bind fun after =>
      if t.magnitude = 0 then
        if (scan bytes t.next).kind = 0 then some after else none
      else segmentLoop mode variables bytes t.next after fuel

def segment (mode : Mode) (variables : Nat) (b : Buffer) (text : String) : Option Buffer :=
  let bytes := text.toUTF8.toList.map UInt8.toNat
  segmentLoop mode variables bytes 0 b (bytes.length + 1)

theorem segmentLoop_preserves (mode : Mode) (variables : Nat) (bytes : List Nat)
    (fuel : Nat) (pos : Nat) (b after : Buffer) (hb : WellFormed b)
    (h : segmentLoop mode variables bytes pos b fuel = some after) : WellFormed after := by
  induction fuel generalizing pos b with
  | zero => simp [segmentLoop] at h
  | succ fuel ih =>
    simp only [segmentLoop] at h
    split at h
    · simp at h
    · split at h
      · exact ih _ b hb h
      · split at h
        · simp at h
        · cases hs : tokenStep mode variables b (scan bytes pos) with
          | none => simp [hs] at h
          | some next =>
            simp only [hs, Option.bind] at h
            have hn := tokenStep_preserves hb hs
            split at h
            · split at h
              · cases Option.some.inj h; exact hn
              · simp at h
            · exact ih _ next hn h

#print axioms empty_wellFormed
#print axioms push_preserves
#print axioms push_layout
#print axioms push_full
#print axioms seal_preserves
#print axioms seal_layout
#print axioms pending_range
#print axioms pending_index
#print axioms tokenStep_preserves
#print axioms zero_seals
#print axioms tokens_preserve
#print axioms segmentLoop_preserves
end OakVerification.Packed
