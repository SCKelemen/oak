import ProofPacking

set_option autoImplicit false
namespace OakVerification.SegmentPublication
open Packed Scanner Ranges

-- A segment may begin with pending data. Successful completion appends exactly
-- the newly scanned suffix, closes one segment, and leaves no pending data.
def Completes (before after : Buffer) : Prop :=
  ∃ items : List Nat, after.pool = before.pool ++ items ∧
    after.closed = before.closed ++ [before.pending ++ items] ∧
    after.pending = [] ∧ after.capacity = before.capacity

theorem close_completes (b : Buffer) : Completes b (closeSegment b) := by
  exact ⟨[], by simp [closeSegment], by simp [closeSegment], rfl, rfl⟩

theorem push_completion (before middle after : Buffer) (item : Nat)
    (pushed : push before item = some middle) (completed : Completes middle after) :
    Completes before after := by
  obtain ⟨pool, pending, closed, capacity, _⟩ := push_layout pushed
  obtain ⟨items, hp, hc, hn, hs⟩ := completed
  refine ⟨item :: items, ?_, ?_, hn, hs.trans capacity⟩
  · simpa [pool, List.append_assoc] using hp
  · simpa [closed, pending, List.append_assoc] using hc

theorem nonzero_push (mode : Mode) (variables : Nat) (before after : Buffer) (t : Token)
    (nonzero : t.magnitude ≠ 0) (stepped : tokenStep mode variables before t = some after) :
    ∃ item, push before item = some after := by
  unfold tokenStep at stepped
  split at stepped
  · simp only [nonzero, ↓reduceIte] at stepped
    split at stepped
    · split at stepped
      · exact ⟨_, stepped⟩
      · simp at stepped
    · split at stepped
      · exact ⟨_, stepped⟩
      · simp at stepped
  · simp at stepped

theorem zero_closes (mode : Mode) (variables : Nat) (before after : Buffer) (t : Token)
    (zero : t.magnitude = 0) (stepped : tokenStep mode variables before t = some after) :
    after = closeSegment before := by
  unfold tokenStep at stepped
  split at stepped
  · have same : closeSegment before = after := by simpa [zero] using stepped
    exact same.symm
  · simp at stepped

theorem segmentLoop_completes (mode : Mode) (variables : Nat) (bytes : List Nat)
    (fuel pos : Nat) (before after : Buffer)
    (decoded : segmentLoop mode variables bytes pos before fuel = some after) :
    Completes before after := by
  induction fuel generalizing pos before with
  | zero => simp [segmentLoop] at decoded
  | succ fuel ih =>
    simp only [segmentLoop] at decoded
    split at decoded
    · simp at decoded
    · split at decoded
      · exact ih _ before decoded
      · split at decoded
        · simp at decoded
        · cases stepped : tokenStep mode variables before (scan bytes pos) with
          | none => simp [stepped] at decoded
          | some next =>
            simp only [stepped, Option.bind] at decoded
            split at decoded
            · rename_i zero
              split at decoded
              · cases Option.some.inj decoded
                rw [zero_closes mode variables before next (scan bytes pos) zero stepped]
                exact close_completes before
              · simp at decoded
            · rename_i nonzero
              obtain ⟨item, pushed⟩ := nonzero_push mode variables before next (scan bytes pos) nonzero stepped
              exact push_completion before next after item pushed (ih _ next decoded)

theorem segment_completes (mode : Mode) (variables : Nat) (before after : Buffer) (text : String)
    (decoded : segment mode variables before text = some after) : Completes before after :=
  segmentLoop_completes mode variables _ _ _ before after decoded

-- The metadata sequence used by the proved packer grows by one final range.
theorem segments_append (offset : Nat) (before after : List (List Nat)) :
    ProofPacking.segments offset (before ++ after) =
      ProofPacking.segments offset before ++ ProofPacking.segments (offset + before.flatten.length) after := by
  induction before generalizing offset with
  | nil => simp [ProofPacking.segments]
  | cons xs rest ih => simp [ProofPacking.segments, ih, Nat.add_assoc]

structure State where
  buffer : Buffer
  ranges : List (Nat × Nat)
  deriving Repr

def Valid (s : State) : Prop :=
  Packed.WellFormed s.buffer ∧ s.buffer.pending = [] ∧
    s.ranges = ProofPacking.segments 0 s.buffer.closed

def emptyState (capacity : Nat) : State := ⟨empty capacity, []⟩

def publish (mode : Mode) (variables : Nat) (s : State) (text : String) : Option State :=
  (segment mode variables s.buffer text).map fun after =>
    ⟨after, s.ranges ++ [(s.buffer.pool.length, after.pool.length - s.buffer.pool.length)]⟩

theorem empty_valid (capacity : Nat) : Valid (emptyState capacity) := by
  exact ⟨empty_wellFormed capacity, rfl, rfl⟩

theorem publish_layout (mode : Mode) (variables : Nat) (s after : State) (text : String)
    (valid : Valid s) (published : publish mode variables s text = some after) :
    ∃ items : List Nat,
      after.buffer.pool = s.buffer.pool ++ items ∧
      after.buffer.closed = s.buffer.closed ++ [items] ∧ after.buffer.pending = [] ∧
      after.ranges = s.ranges ++ [(s.buffer.pool.length, items.length)] := by
  unfold publish at published
  cases decoded : segment mode variables s.buffer text with
  | none => simp [decoded] at published
  | some next =>
    simp only [decoded, Option.map_some, Option.some.injEq] at published
    subst after
    obtain ⟨items, pool, closed, pending, _⟩ := segment_completes mode variables s.buffer next text decoded
    refine ⟨items, pool, ?_, pending, ?_⟩
    · simpa [valid.2.1] using closed
    · simp [pool]

theorem publish_valid (mode : Mode) (variables : Nat) (s after : State) (text : String)
    (valid : Valid s) (published : publish mode variables s text = some after) : Valid after := by
  obtain ⟨items, pool, closed, pending, ranges⟩ := publish_layout mode variables s after text valid published
  have wellFormed : Packed.WellFormed after.buffer := by
    unfold publish at published
    cases decoded : segment mode variables s.buffer text with
    | none => simp [decoded] at published
    | some next =>
      simp only [decoded, Option.map_some, Option.some.injEq] at published
      subst after
      exact segmentLoop_preserves mode variables _ _ _ s.buffer next valid.1 decoded
  refine ⟨wellFormed, pending, ?_⟩
  have initialPool : s.buffer.pool = s.buffer.closed.flatten := by simpa [valid.2.1] using valid.1.1
  rw [ranges, closed, segments_append, valid.2.2]
  simp [ProofPacking.segments, initialPool]

-- Later literal/hint writes cannot alter a published segment's meaning.
theorem published_contents (mode : Mode) (variables : Nat) (s after : State) (text : String)
    (valid : Valid s) (published : publish mode variables s text = some after) :
    ∃ items : List Nat, after.ranges = s.ranges ++ [(s.buffer.pool.length, items.length)] ∧
      ∀ suffix : List Nat,
        readRange (after.buffer.pool ++ suffix) s.buffer.pool.length items.length = some items ∧
        readClause (after.buffer.pool ++ suffix) s.buffer.pool.length items.length = some (items.map decodeLiteral) := by
  obtain ⟨items, pool, _, _, ranges⟩ := publish_layout mode variables s after text valid published
  refine ⟨items, ranges, fun suffix => ?_⟩
  rw [pool]
  exact ⟨range_contents s.buffer.pool items suffix, clause_contents s.buffer.pool items suffix⟩

def publications (mode : Mode) (variables : Nat) (s : State) : List String → Option State
  | [] => some s
  | text :: rest => (publish mode variables s text).bind (fun next => publications mode variables next rest)

theorem publications_valid (mode : Mode) (variables : Nat) (texts : List String)
    (s after : State) (valid : Valid s)
    (decoded : publications mode variables s texts = some after) : Valid after := by
  induction texts generalizing s with
  | nil => simp only [publications, Option.some.injEq] at decoded; subst after; exact valid
  | cons text rest ih =>
    simp only [publications] at decoded
    cases step : publish mode variables s text with
    | none => simp [step] at decoded
    | some next =>
      simp only [step, Option.bind] at decoded
      exact ih next (publish_valid mode variables s next text valid step) decoded

#print axioms close_completes
#print axioms push_completion
#print axioms nonzero_push
#print axioms zero_closes
#print axioms segmentLoop_completes
#print axioms segment_completes
#print axioms segments_append
#print axioms empty_valid
#print axioms publish_layout
#print axioms publish_valid
#print axioms published_contents
#print axioms publications_valid
end OakVerification.SegmentPublication
