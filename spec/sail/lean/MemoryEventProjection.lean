import Std

/-!
Conditional projection of a SUPPLIED prompt-event view, not an Arm execution
model or an exporter. The existing audited Lem harness runs the original
generated __WriteMemory and observes E_read_reg, E_write_ea, E_write_mem.
There is no kernel-verified raw Lem trace importer here. The caller must supply
and justify its observation adapter and the independently expected call list.

The two write constructors below mean Write_plain only. All other event kinds
must map to `other`; readReg carries a supplied selector response of the
appropriate register-value constructor. Selector and payload are abstract:
no selector-width, defined-bit, byte-count, or initialization check is implied.
In particular normal prompt completion permits either acknowledgement.

These are request occurrences, not CAT W/TTD events. Trace provenance,
translation, cacheability, invalidation scope, coherence, and correspondence
between Lean's Unit tags and Lem's actual tag map remain separate obligations.

Read-only source anchors: spec/sail/lem/write_memory_trace_test.ml exercises
the original wrapper; state_replay_test.ml separates prompt completion from
state replay. Sail's sail2_prompt_monad.lem event/emitEvent declarations retain
the exact register name, write kind, address, size, payload, and response bit.
-/

namespace Oak.MemoryEventProjection

inductive View (Selector Payload : Type) where
  | readReg (name : String) (selector : Selector)
  | writeEA (address size : Nat)
  | writeMem (address size : Nat) (payload : Payload) (acknowledged : Bool)
  | other
  deriving DecidableEq

structure Block (Selector Payload : Type) where
  selector : Selector
  address : Nat
  size : Nat
  payload : Payload
  acknowledged : Bool
  deriving DecidableEq

def Block.events (block : Block Selector Payload) : List (View Selector Payload) :=
  [.readReg "__defaultRAM" block.selector, .writeEA block.address block.size,
    .writeMem block.address block.size block.payload block.acknowledged]

structure Occurrence (Selector Payload : Type) where
  readPosition : Nat
  block : Block Selector Payload
  deriving DecidableEq

def Occurrence.eaPosition (event : Occurrence Selector Payload) : Nat := event.readPosition + 1
def Occurrence.dataPosition (event : Occurrence Selector Payload) : Nat := event.readPosition + 2

def events (blocks : List (Block Selector Payload)) : List (View Selector Payload) :=
  blocks.flatMap Block.events

def positioned (start : Nat) : List (Block Selector Payload) → List (Occurrence Selector Payload)
  | [] => []
  | block :: rest => ⟨start, block⟩ :: positioned (start + 3) rest

structure ScanResult (Selector Payload : Type) where
  accepted : List (Occurrence Selector Payload)
  failureAt : Option Nat
  deriving DecidableEq

/-- A failure retains earlier matched triples. The error position denotes the
start of the first unmatched triple, not an invented architectural exception. -/
def scan (start : Nat) : List (View Selector Payload) → ScanResult Selector Payload
  | [] => ⟨[], none⟩
  | .readReg name selector :: .writeEA address size ::
      .writeMem address' size' payload acknowledged :: rest =>
    if name = "__defaultRAM" ∧ address = address' ∧ size = size' then
      let suffix := scan (start + 3) rest
      ⟨⟨start, ⟨selector, address, size, payload, acknowledged⟩⟩ :: suffix.accepted,
        suffix.failureAt⟩
    else ⟨[], some start⟩
  | _ => ⟨[], some start⟩

theorem positioned_blocks (start : Nat) (blocks : List (Block Selector Payload)) :
    (positioned start blocks).map Occurrence.block = blocks := by
  induction blocks generalizing start with
  | nil => rfl
  | cons block rest ih => simp [positioned, ih]

theorem events_append (left right : List (Block Selector Payload)) :
    events (left ++ right) = events left ++ events right := by
  simp [events]

theorem events_length (blocks : List (Block Selector Payload)) :
    (events blocks).length = 3 * blocks.length := by
  induction blocks with
  | nil => rfl
  | cons block rest ih => simp [events, Block.events, events] at ih ⊢; omega

theorem positioned_at (start : Nat) (blocks : List (Block Selector Payload)) (index : Nat) :
    (positioned start blocks)[index]? =
      blocks[index]?.map (fun block => ⟨start + 3 * index, block⟩) := by
  induction blocks generalizing start index with
  | nil => simp [positioned]
  | cons block rest ih =>
    cases index with
    | zero => simp [positioned]
    | succ index =>
      simp only [positioned, List.getElem?_cons_succ, ih]
      have h : start + 3 + 3 * index = start + 3 * (index + 1) := by omega
      rw [h]

theorem positioned_append (start : Nat) (left right : List (Block Selector Payload)) :
    positioned start (left ++ right) =
      positioned start left ++ positioned (start + 3 * left.length) right := by
  induction left generalizing start with
  | nil => simp [positioned]
  | cons block rest ih =>
    simp only [List.cons_append, positioned, ih, List.length_cons, Nat.mul_add,
      Nat.mul_one, List.cons.injEq, true_and]
    congr 2 <;> omega

theorem scan_prefix (start : Nat) (blocks : List (Block Selector Payload))
    (tail : List (View Selector Payload)) :
    scan start (events blocks ++ tail) =
      let suffix := scan (start + 3 * blocks.length) tail
      ⟨positioned start blocks ++ suffix.accepted, suffix.failureAt⟩ := by
  induction blocks generalizing start with
  | nil => simp [events, positioned]
  | cons block rest ih =>
    simp only [events, List.flatMap_cons, Block.events,
      List.cons_append, List.nil_append, scan, and_self, ↓reduceIte,
      positioned, List.length_cons]
    change _ = _
    rw [show List.flatMap Block.events rest = events rest from rfl, ih]
    have h : start + 3 * (rest.length + 1) = start + 3 + 3 * rest.length := by omega
    simp [h]

theorem scan_complete (start : Nat) (blocks : List (Block Selector Payload)) :
    scan start (events blocks) = ⟨positioned start blocks, none⟩ := by
  simpa [scan] using scan_prefix start blocks []

/-- Successful validation explicitly checks lossless reconstruction and source
positions. It does not trust an arbitrary candidate or silently drop events. -/
def ValidProjection (start : Nat) (source : List (View Selector Payload))
    (output : List (Occurrence Selector Payload)) : Prop :=
  source = events (output.map Occurrence.block) ∧
    output = positioned start (output.map Occurrence.block)

instance [DecidableEq Selector] [DecidableEq Payload] (start : Nat)
    (source : List (View Selector Payload)) (output : List (Occurrence Selector Payload)) :
    Decidable (ValidProjection start source output) := inferInstanceAs (Decidable (_ ∧ _))

def project [DecidableEq Selector] [DecidableEq Payload]
    (start : Nat) (source : List (View Selector Payload)) :
    Option (List (Occurrence Selector Payload)) :=
  let result := scan start source
  if result.failureAt = none ∧ ValidProjection start source result.accepted then
    some result.accepted
  else none

theorem project_sound [DecidableEq Selector] [DecidableEq Payload]
    {start : Nat} {source : List (View Selector Payload)}
    {output : List (Occurrence Selector Payload)}
    (accepted : project start source = some output) : ValidProjection start source output := by
  unfold project at accepted
  dsimp only at accepted
  split at accepted
  · rename_i valid
    cases Option.some.inj accepted
    exact valid.2
  · contradiction

theorem project_complete [DecidableEq Selector] [DecidableEq Payload]
    (start : Nat) (blocks : List (Block Selector Payload)) :
    project start (events blocks) = some (positioned start blocks) := by
  simp [project, scan_complete, ValidProjection, positioned_blocks]

/-- Concatenation keeps all occurrences, and offsets the right trace by the
left trace's actual event count rather than restarting occurrence numbering. -/
theorem project_append [DecidableEq Selector] [DecidableEq Payload]
    {start : Nat} {left right : List (View Selector Payload)}
    {leftOutput rightOutput : List (Occurrence Selector Payload)}
    (leftAccepted : project start left = some leftOutput)
    (rightAccepted : project (start + left.length) right = some rightOutput) :
    project start (left ++ right) = some (leftOutput ++ rightOutput) := by
  obtain ⟨leftEvents, leftPositions⟩ := project_sound leftAccepted
  obtain ⟨rightEvents, rightPositions⟩ := project_sound rightAccepted
  have leftLength : left.length = 3 * leftOutput.length := by
    rw [leftEvents, events_length, List.length_map]
  rw [leftEvents, rightEvents, ← events_append, project_complete, positioned_append,
    ← leftPositions, List.length_map, ← leftLength, ← rightPositions]

/-- No address-based deduplication: a successful projection retains one output
per complete selector/EA/data triple. -/
theorem project_count [DecidableEq Selector] [DecidableEq Payload]
    {start : Nat} {source : List (View Selector Payload)}
    {output : List (Occurrence Selector Payload)}
    (accepted : project start source = some output) : source.length = 3 * output.length := by
  rw [(project_sound accepted).1, events_length, List.length_map]

theorem project_position [DecidableEq Selector] [DecidableEq Payload]
    {start index : Nat} {source : List (View Selector Payload)}
    {output : List (Occurrence Selector Payload)} {occurrence : Occurrence Selector Payload}
    (accepted : project start source = some output) (atIndex : output[index]? = some occurrence) :
    occurrence.readPosition = start + 3 * index := by
  have positions := (project_sound accepted).2
  have observed := congrArg (fun entries => entries[index]?) positions
  rw [atIndex, positioned_at, List.getElem?_map, atIndex] at observed
  exact congrArg Occurrence.readPosition (Option.some.inj observed)

theorem distinct_positions [DecidableEq Selector] [DecidableEq Payload]
    {start i j : Nat} {source : List (View Selector Payload)}
    {output : List (Occurrence Selector Payload)} {first second : Occurrence Selector Payload}
    (accepted : project start source = some output)
    (atFirst : output[i]? = some first) (atSecond : output[j]? = some second) (ordered : i < j) :
    first.readPosition < second.readPosition ∧ first ≠ second := by
  have firstPosition := project_position accepted atFirst
  have secondPosition := project_position accepted atSecond
  constructor
  · omega
  · intro same
    cases same
    omega

/-- Every matched triple stays ordered, and even the first data request
precedes the next occurrence's selector read. PA equality is irrelevant. -/
theorem request_order [DecidableEq Selector] [DecidableEq Payload]
    {start i j : Nat} {source : List (View Selector Payload)}
    {output : List (Occurrence Selector Payload)} {first second : Occurrence Selector Payload}
    (accepted : project start source = some output)
    (atFirst : output[i]? = some first) (atSecond : output[j]? = some second) (ordered : i < j) :
    first.readPosition < first.eaPosition ∧ first.eaPosition < first.dataPosition ∧
      first.dataPosition < second.readPosition := by
  have firstPosition := project_position accepted atFirst
  have secondPosition := project_position accepted atSecond
  simp only [Occurrence.eaPosition, Occurrence.dataPosition]
  omega

/-- Exact reconstruction exposes the matched read/EA/data triple at every
supplied list split, preserving data, sizes, selector responses, and ack bits. -/
theorem project_split [DecidableEq Selector] [DecidableEq Payload]
    {start : Nat} {source : List (View Selector Payload)}
    {output before after : List (Occurrence Selector Payload)} {occurrence : Occurrence Selector Payload}
    (accepted : project start source = some output)
    (splitOutput : output = before ++ occurrence :: after) :
    source = events (before.map Occurrence.block) ++ occurrence.block.events ++
      events (after.map Occurrence.block) := by
  rw [(project_sound accepted).1, splitOutput]
  simp [events, List.append_assoc]

/-- The expected calls are external input, not a list recovered from the
projection. Payload equality distinguishes same-PA calls with different data.
Identical call swaps are unobservable without additional external identities;
this check does not compare selectors or acknowledgements. -/
structure Call (Payload : Type) where
  address : Nat
  size : Nat
  payload : Payload
  deriving DecidableEq

def Block.call (block : Block Selector Payload) : Call Payload :=
  ⟨block.address, block.size, block.payload⟩

def matchesCalls (expected : List (Call Payload))
    (output : List (Occurrence Selector Payload)) : Prop :=
  output.map (fun occurrence => occurrence.block.call) = expected

instance [DecidableEq Payload] (expected : List (Call Payload))
    (output : List (Occurrence Selector Payload)) : Decidable (matchesCalls expected output) :=
  inferInstanceAs (Decidable (_ = _))

def projectCalls [DecidableEq Selector] [DecidableEq Payload]
    (expected : List (Call Payload)) (start : Nat) (source : List (View Selector Payload)) :
    Option (List (Occurrence Selector Payload)) :=
  match project start source with
  | none => none
  | some output => if matchesCalls expected output then some output else none

theorem projectCalls_sound [DecidableEq Selector] [DecidableEq Payload]
    {expected : List (Call Payload)} {start : Nat} {source : List (View Selector Payload)}
    {output : List (Occurrence Selector Payload)}
    (accepted : projectCalls expected start source = some output) :
    project start source = some output ∧ matchesCalls expected output := by
  unfold projectCalls at accepted
  split at accepted
  · contradiction
  · rename_i actual projected
    split at accepted
    · rename_i matched
      cases Option.some.inj accepted
      exact ⟨projected, matched⟩
    · contradiction

theorem positioned_calls (start : Nat) (blocks : List (Block Selector Payload)) :
    (positioned start blocks).map (fun occurrence => occurrence.block.call) =
      blocks.map Block.call := by
  have h := congrArg (List.map (fun block : Block Selector Payload => block.call))
    (positioned_blocks start blocks)
  simpa only [List.map_map, Function.comp_def] using h

theorem mismatched_calls_rejected [DecidableEq Selector] [DecidableEq Payload]
    (expected : List (Call Payload)) (start : Nat) (blocks : List (Block Selector Payload))
    (mismatch : blocks.map Block.call ≠ expected) :
    projectCalls expected start (events blocks) = none := by
  simp [projectCalls, project_complete, matchesCalls, positioned_calls, mismatch]

theorem projectCalls_count [DecidableEq Selector] [DecidableEq Payload]
    {expected : List (Call Payload)} {start : Nat} {source : List (View Selector Payload)}
    {output : List (Occurrence Selector Payload)}
    (accepted : projectCalls expected start source = some output) :
    source.length = 3 * expected.length := by
  obtain ⟨projected, matched⟩ := projectCalls_sound accepted
  have lengths := congrArg List.length matched
  simp only [List.length_map] at lengths
  rw [project_count projected, lengths]

/-- Supplying raw trace provenance cannot be inferred from projection. Even
this equality says nothing about producing `raw` by the actual Arm model. -/
def SuppliedView (observe : Raw → View Selector Payload) (raw : List Raw)
    (source : List (View Selector Payload)) : Prop := source = raw.map observe

/-- The external audit is carried, not proved. This theorem cannot construct
evidence of original-model trace production or of a sound observation adapter. -/
theorem supplied_trace_projection [DecidableEq Selector] [DecidableEq Payload]
    (audit : List Raw → Prop) (observe : Raw → View Selector Payload)
    (raw : List Raw) (source : List (View Selector Payload))
    (start : Nat) (output : List (Occurrence Selector Payload))
    (audited : audit raw) (supplied : SuppliedView observe raw source)
    (accepted : project start source = some output) :
    audit raw ∧ raw.map observe = events (output.map Occurrence.block) ∧
      output = positioned start (output.map Occurrence.block) := by
  obtain ⟨reconstructed, ordered⟩ := project_sound accepted
  exact ⟨audited, supplied.symm.trans reconstructed, ordered⟩

/-- A successful replay contract adds an externally supplied state relation.
The true acknowledgements here are NOT a consequence of prompt completion. -/
def SuccessfulReplay (start : Nat)
    (replays : List (View Selector Payload) → State → State → Prop)
    (source : List (View Selector Payload)) (before after : State)
    (output : List (Occurrence Selector Payload)) : Prop :=
  ValidProjection start source output ∧ replays source before after ∧
    ∀ occurrence ∈ output, occurrence.block.acknowledged = true

theorem false_ack_excludes_successful_replay
    {start : Nat} {replays : List (View Selector Payload) → State → State → Prop}
    {source : List (View Selector Payload)} {before after : State}
    {output : List (Occurrence Selector Payload)} {occurrence : Occurrence Selector Payload}
    (present : occurrence ∈ output) (acknowledged : occurrence.block.acknowledged = false) :
    ¬ SuccessfulReplay start replays source before after output := by
  intro success
  have h := success.2.2 occurrence present
  rw [acknowledged] at h
  cases h

namespace Examples

-- Abstract test observations, NOT generated Arm event values. Their short
-- selector/payload lists deliberately carry no width/byte-count guarantee.
private def first : Block (List Nat) (List Nat) := ⟨[2], 4096, 8, [0], true⟩
private def second : Block (List Nat) (List Nat) := ⟨[], 4096, 8, [1], false⟩

theorem same_address_occurrences :
    project 0 (events [first, second]) = some [⟨0, first⟩, ⟨3, second⟩] := by
  exact project_complete 0 [first, second]

theorem identical_repeated_requests :
    project 7 (events [first, first]) = some [⟨7, first⟩, ⟨10, first⟩] ∧
      (⟨7, first⟩ : Occurrence (List Nat) (List Nat)) ≠ ⟨10, first⟩ := by
  constructor
  · exact project_complete 7 [first, first]
  · decide

theorem false_ack_is_structurally_accepted :
    project 0 second.events = some [⟨0, second⟩] := by
  exact project_complete 0 [second]

theorem false_ack_is_not_successful_replay :
    ¬ SuccessfulReplay 0 (fun _ (_ _ : Unit) => True)
      second.events () () [⟨0, second⟩] := by
  apply false_ack_excludes_successful_replay (occurrence := ⟨0, second⟩)
  · simp
  · rfl

theorem dropped_call_rejected :
    projectCalls [first.call, second.call] 0 second.events = none := by decide

theorem reordered_calls_rejected :
    projectCalls [first.call, second.call] 0 (events [second, first]) = none := by decide

theorem missing_selector_rejected :
    project 0 (first.events.drop 1) = none := by decide

theorem data_before_ea_rejected :
    project (Selector := List Nat) (Payload := List Nat) 0
      [.readReg "__defaultRAM" [2], .writeMem 4096 8 [0] true, .writeEA 4096 8] = none := by decide

theorem wrong_register_rejected :
    project (Selector := List Nat) (Payload := List Nat) 0
      [.readReg "__otherRAM" [2], .writeEA 4096 8, .writeMem 4096 8 [0] true] = none := by decide

theorem mismatched_address_rejected :
    project (Selector := List Nat) (Payload := List Nat) 0
      [.readReg "__defaultRAM" [2], .writeEA 4096 8, .writeMem 4097 8 [0] true] = none := by decide

theorem mismatched_size_rejected :
    project (Selector := List Nat) (Payload := List Nat) 0
      [.readReg "__defaultRAM" [2], .writeEA 4096 8, .writeMem 4096 4 [0] true] = none := by decide

theorem mismatched_payload_rejected :
    projectCalls [first.call] 0 second.events = none := by decide

theorem nonplain_or_unhandled_event_rejected :
    project (Selector := List Nat) (Payload := List Nat) 0
      [.readReg "__defaultRAM" [2], .writeEA 4096 8, .other] = none := by decide

/-- A pending/failed suffix cannot retroactively erase the earlier matched
request. Neither this parser failure nor its prefix is an architectural commit. -/
theorem incomplete_suffix_keeps_prefix :
    scan 10 (first.events ++ [.readReg "__defaultRAM" [], .writeEA 4096 8]) =
      ⟨[⟨10, first⟩], some 13⟩ := by decide

theorem unmatched_suffix_keeps_prefix :
    scan 0 (first.events ++ [.other]) = ⟨[⟨0, first⟩], some 3⟩ := by decide

theorem unmatched_pair_is_not_completed :
    scan 0 (first.events ++ [.readReg "__defaultRAM" [], .writeEA 4096 8,
      .writeMem 4097 8 [1] true]) = ⟨[⟨0, first⟩], some 3⟩ := by decide

theorem reset_suffix_positions_invalid :
    ¬ ValidProjection 0 (events [first, second]) [⟨0, first⟩, ⟨0, second⟩] := by decide

theorem unrelated_output_invalid :
    ¬ ValidProjection 0 ([] : List (View (List Nat) (List Nat))) [⟨0, first⟩] := by decide

end Examples

/-- info: 'Oak.MemoryEventProjection.project_sound' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms project_sound
/-- info: 'Oak.MemoryEventProjection.scan_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms scan_prefix
/-- info: 'Oak.MemoryEventProjection.project_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms project_complete
/-- info: 'Oak.MemoryEventProjection.project_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms project_append
/-- info: 'Oak.MemoryEventProjection.project_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms project_count
/-- info: 'Oak.MemoryEventProjection.project_position' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms project_position
/-- info: 'Oak.MemoryEventProjection.distinct_positions' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms distinct_positions
/-- info: 'Oak.MemoryEventProjection.request_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms request_order
/-- info: 'Oak.MemoryEventProjection.project_split' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms project_split
/-- info: 'Oak.MemoryEventProjection.projectCalls_sound' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms projectCalls_sound
/-- info: 'Oak.MemoryEventProjection.projectCalls_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms projectCalls_count
/-- info: 'Oak.MemoryEventProjection.mismatched_calls_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mismatched_calls_rejected
/-- info: 'Oak.MemoryEventProjection.supplied_trace_projection' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms supplied_trace_projection
/-- info: 'Oak.MemoryEventProjection.false_ack_excludes_successful_replay' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms false_ack_excludes_successful_replay
/-- info: 'Oak.MemoryEventProjection.Examples.same_address_occurrences' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Examples.same_address_occurrences
/-- info: 'Oak.MemoryEventProjection.Examples.incomplete_suffix_keeps_prefix' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Examples.incomplete_suffix_keeps_prefix
/-- info: 'Oak.MemoryEventProjection.Examples.reordered_calls_rejected' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Examples.reordered_calls_rejected
/-- info: 'Oak.MemoryEventProjection.Examples.false_ack_is_not_successful_replay' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Examples.false_ack_is_not_successful_replay

end Oak.MemoryEventProjection
