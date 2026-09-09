import SegmentPublication

set_option autoImplicit false
namespace OakVerification.CommandAssembly
open Packed Scanner Ranges SegmentPublication

/-! Command assembly from published clause and hint ranges.

The decoder reads one command per proof line: an identifier word, then either
a clause segment and a hint segment, or the word `d` and a deletion segment.
This module models that assembly on top of the proved segment publication state
and shows that the assembled layout decodes to exactly the published clauses
and instructions. Splitting a line into its words is the byte adapter's job and
is not modeled here. -/

-- The decoder accepts an ID or deletion stamp when the word is one numeric
-- token whose sign is valid and either nonnegative or a spelling of zero.
def identifier (word : String) : Option Nat :=
  let bytes := word.toUTF8.toList.map UInt8.toNat
  let t := scan bytes 0
  if t.kind = 2 ∧ t.sign ≠ 0 ∧ (t.sign = 1 ∨ t.magnitude = 0) ∧ (scan bytes t.next).kind = 0
  then some t.magnitude else none

structure Assembly where
  literals : State
  references : State
  initial : List (Nat × Nat)
  commands : List Command
  deriving Repr

-- The proof phase begins after the initial clauses are published.
def start (literals : State) (capacity : Nat) : Assembly :=
  ⟨literals, emptyState capacity, literals.ranges, []⟩

def addition (variables : Nat) (a : Assembly) (id clause hints : String) : Option Assembly :=
  match identifier id, publish .literal variables a.literals clause,
      publish .hint variables a.references hints with
  | some stamp, some literals, some references =>
    some ⟨literals, references, a.initial, a.commands ++
      [⟨true, stamp, a.literals.buffer.pool.length,
        literals.buffer.pool.length - a.literals.buffer.pool.length,
        a.references.buffer.pool.length,
        references.buffer.pool.length - a.references.buffer.pool.length⟩]⟩
  | _, _, _ => none

-- A deletion records the current literal offset with an empty clause range.
def deletion (variables : Nat) (a : Assembly) (id ids : String) : Option Assembly :=
  match identifier id, publish .deletion variables a.references ids with
  | some stamp, some references =>
    some ⟨a.literals, references, a.initial, a.commands ++
      [⟨false, stamp, a.literals.buffer.pool.length, 0,
        a.references.buffer.pool.length,
        references.buffer.pool.length - a.references.buffer.pool.length⟩]⟩
  | _, _ => none

inductive Line where
  | add (id clause hints : String)
  | delete (id ids : String)
  deriving Repr

def step (variables : Nat) (a : Assembly) : Line → Option Assembly
  | .add id clause hints => addition variables a id clause hints
  | .delete id ids => deletion variables a id ids

def assemble (variables : Nat) (a : Assembly) : List Line → Option Assembly
  | [] => some a
  | line :: rest => (step variables a line).bind fun next => assemble variables next rest

def toLayout (variables : Nat) (a : Assembly) : Layout :=
  ⟨variables, a.literals.buffer.pool, a.initial.map Prod.fst, a.initial.map Prod.snd,
    a.references.buffer.pool, a.commands⟩

-- The decoder's command metadata. Deletions carry the current literal offset
-- rather than the packer's zero; the range decoder ignores both.
def assembled (offset refsOffset : Nat) : List Instruction → List Command
  | [] => []
  | .add id clause hints :: rest =>
    ⟨true, id, offset, clause.length, refsOffset, hints.length⟩ ::
      assembled (offset + clause.length) (refsOffset + hints.length) rest
  | .delete stamp ids :: rest =>
    ⟨false, stamp, offset, 0, refsOffset, ids.length⟩ ::
      assembled offset (refsOffset + ids.length) rest

def PositiveAddition : Instruction → Prop
  | .add _ clause _ => ProofPacking.Positive clause
  | .delete _ _ => True

structure Represents (a : Assembly) (clauses : List Clause) (instructions : List Instruction) : Prop where
  literals : Valid a.literals
  references : Valid a.references
  pool : a.literals.buffer.pool =
    (clauses.map ProofPacking.encodeClause).flatten ++ (instructions.map ProofPacking.literals).flatten
  refs : a.references.buffer.closed = instructions.map ProofPacking.references
  initial : a.initial = ProofPacking.segments 0 (clauses.map ProofPacking.encodeClause)
  commands : a.commands = assembled (clauses.map ProofPacking.encodeClause).flatten.length 0 instructions
  positive : ∀ c ∈ clauses, ProofPacking.Positive c
  additions : ∀ i ∈ instructions, PositiveAddition i

theorem encode_decoded (items : List Nat) :
    ProofPacking.encodeClause (items.map decodeLiteral) = items := by
  induction items with
  | nil => rfl
  | cons n rest ih =>
    change encodeLiteral (decodeLiteral n) :: ProofPacking.encodeClause (rest.map decodeLiteral) = n :: rest
    rw [encode_decode n, ih]

theorem encode_decoded_map (segments : List (List Nat)) :
    (segments.map (List.map decodeLiteral)).map ProofPacking.encodeClause = segments := by
  induction segments with
  | nil => rfl
  | cons items rest ih => simp [encode_decoded, ih]

theorem positive_decoded (items : List Nat) : ProofPacking.Positive (items.map decodeLiteral) := by
  intro l member
  obtain ⟨n, _, rfl⟩ := List.mem_map.1 member
  simp [decodeLiteral]

theorem valid_pool (s : State) (valid : Valid s) :
    s.buffer.pool = s.buffer.closed.flatten := by
  have layout := valid.1.1
  rwa [valid.2.1, List.append_nil] at layout

theorem assembled_append (offset refsOffset : Nat) (before after : List Instruction) :
    assembled offset refsOffset (before ++ after) =
      assembled offset refsOffset before ++
        assembled (offset + (before.map ProofPacking.literals).flatten.length)
          (refsOffset + (before.map ProofPacking.references).flatten.length) after := by
  induction before generalizing offset refsOffset with
  | nil => simp [assembled]
  | cons c rest ih =>
    cases c with
    | add id clause hints =>
      simp [assembled, ProofPacking.literals, ProofPacking.references, ih, ProofPacking.encodeClause,
        Nat.add_assoc]
    | delete stamp ids =>
      simp [assembled, ProofPacking.literals, ProofPacking.references, ih, Nat.add_assoc]

theorem assembled_length (offset refsOffset : Nat) (instructions : List Instruction) :
    (assembled offset refsOffset instructions).length = instructions.length := by
  induction instructions generalizing offset refsOffset with
  | nil => rfl
  | cons c rest ih => cases c <;> simp [assembled, ih]

theorem commands_length (offset refsOffset : Nat) (instructions : List Instruction) :
    (ProofPacking.commands offset refsOffset instructions).length = instructions.length := by
  induction instructions generalizing offset refsOffset with
  | nil => rfl
  | cons c rest ih => cases c <;> simp [ProofPacking.commands, ih]

theorem start_represents (literals : State) (capacity : Nat) (valid : Valid literals) :
    Represents (start literals capacity)
      (literals.buffer.closed.map (List.map decodeLiteral)) [] := by
  refine ⟨valid, empty_valid capacity, ?_, rfl, ?_, rfl, ?_, by simp⟩
  · show literals.buffer.pool =
      ((literals.buffer.closed.map (List.map decodeLiteral)).map ProofPacking.encodeClause).flatten ++ [].flatten
    rw [encode_decoded_map, List.flatten_nil, List.append_nil]
    exact valid_pool literals valid
  · show literals.ranges =
      ProofPacking.segments 0 ((literals.buffer.closed.map (List.map decodeLiteral)).map ProofPacking.encodeClause)
    rw [encode_decoded_map]
    exact valid.2.2
  · intro c member
    obtain ⟨items, _, rfl⟩ := List.mem_map.1 member
    exact positive_decoded items

theorem addition_represents (variables : Nat) (a after : Assembly)
    (clauses : List Clause) (instructions : List Instruction) (id clause hints : String)
    (rep : Represents a clauses instructions)
    (stepped : addition variables a id clause hints = some after) :
    ∃ (stamp : Nat) (items refs : List Nat), identifier id = some stamp ∧
      Represents after clauses (instructions ++ [.add stamp (items.map decodeLiteral) refs]) := by
  unfold addition at stepped
  cases scanned : identifier id with
  | none => simp [scanned] at stepped
  | some stamp =>
    cases literalsPublished : publish .literal variables a.literals clause with
    | none => simp [scanned, literalsPublished] at stepped
    | some literals =>
      cases refsPublished : publish .hint variables a.references hints with
      | none => simp [scanned, literalsPublished, refsPublished] at stepped
      | some references =>
        simp only [scanned, literalsPublished, refsPublished, Option.some.injEq] at stepped
        subst after
        obtain ⟨items, litPool, litClosed, _, _⟩ :=
          publish_layout .literal variables a.literals literals clause rep.literals literalsPublished
        obtain ⟨refs, refPool, refClosed, _, _⟩ :=
          publish_layout .hint variables a.references references hints rep.references refsPublished
        refine ⟨stamp, items, refs, rfl, ?_⟩
        have litValid := publish_valid .literal variables a.literals literals clause rep.literals literalsPublished
        have refValid := publish_valid .hint variables a.references references hints rep.references refsPublished
        have litLength : a.literals.buffer.pool.length =
            (clauses.map ProofPacking.encodeClause).flatten.length +
              (instructions.map ProofPacking.literals).flatten.length := by
          rw [rep.pool, List.length_append]
        have refLength : a.references.buffer.pool.length =
            (instructions.map ProofPacking.references).flatten.length := by
          rw [valid_pool a.references rep.references, rep.refs]
        refine ⟨litValid, refValid, ?_, ?_, rep.initial, ?_, rep.positive, ?_⟩
        · simp [litPool, rep.pool, ProofPacking.literals, encode_decoded]
        · simp [refClosed, rep.refs, ProofPacking.references]
        · simp only [rep.commands, assembled_append, assembled, litPool, refPool, List.length_append,
            List.length_map, Nat.add_sub_cancel_left, Nat.zero_add, litLength, refLength]
        · intro i member
          simp only [List.mem_append, List.mem_singleton] at member
          cases member with
          | inl earlier => exact rep.additions i earlier
          | inr new => subst new; exact positive_decoded items

theorem deletion_represents (variables : Nat) (a after : Assembly)
    (clauses : List Clause) (instructions : List Instruction) (id ids : String)
    (rep : Represents a clauses instructions)
    (stepped : deletion variables a id ids = some after) :
    ∃ (stamp : Nat) (refs : List Nat), identifier id = some stamp ∧
      Represents after clauses (instructions ++ [.delete stamp refs]) := by
  unfold deletion at stepped
  cases scanned : identifier id with
  | none => simp [scanned] at stepped
  | some stamp =>
    cases refsPublished : publish .deletion variables a.references ids with
    | none => simp [scanned, refsPublished] at stepped
    | some references =>
      simp only [scanned, refsPublished, Option.some.injEq] at stepped
      subst after
      obtain ⟨refs, refPool, refClosed, _, _⟩ :=
        publish_layout .deletion variables a.references references ids rep.references refsPublished
      refine ⟨stamp, refs, rfl, ?_⟩
      have refValid := publish_valid .deletion variables a.references references ids rep.references refsPublished
      have litLength : a.literals.buffer.pool.length =
          (clauses.map ProofPacking.encodeClause).flatten.length +
            (instructions.map ProofPacking.literals).flatten.length := by
        rw [rep.pool, List.length_append]
      have refLength : a.references.buffer.pool.length =
          (instructions.map ProofPacking.references).flatten.length := by
        rw [valid_pool a.references rep.references, rep.refs]
      refine ⟨rep.literals, refValid, ?_, ?_, rep.initial, ?_, rep.positive, ?_⟩
      · simp [rep.pool, ProofPacking.literals]
      · simp [refClosed, rep.refs, ProofPacking.references]
      · simp only [rep.commands, assembled_append, assembled, refPool, List.length_append,
          Nat.add_sub_cancel_left, Nat.zero_add, litLength, refLength]
      · intro i member
        simp only [List.mem_append, List.mem_singleton] at member
        cases member with
        | inl earlier => exact rep.additions i earlier
        | inr new => subst new; trivial

theorem step_represents (variables : Nat) (a after : Assembly)
    (clauses : List Clause) (instructions : List Instruction) (line : Line)
    (rep : Represents a clauses instructions) (stepped : step variables a line = some after) :
    ∃ instruction, Represents after clauses (instructions ++ [instruction]) := by
  cases line with
  | add id clause hints =>
    obtain ⟨stamp, items, refs, _, next⟩ :=
      addition_represents variables a after clauses instructions id clause hints rep stepped
    exact ⟨_, next⟩
  | delete id ids =>
    obtain ⟨stamp, refs, _, next⟩ :=
      deletion_represents variables a after clauses instructions id ids rep stepped
    exact ⟨_, next⟩

theorem assemble_represents (variables : Nat) (lines : List Line) (a after : Assembly)
    (clauses : List Clause) (instructions : List Instruction)
    (rep : Represents a clauses instructions)
    (assembled : assemble variables a lines = some after) :
    ∃ appended : List Instruction, Represents after clauses (instructions ++ appended) := by
  induction lines generalizing a instructions with
  | nil =>
    simp only [assemble, Option.some.injEq] at assembled
    subst after
    exact ⟨[], by simpa using rep⟩
  | cons line rest ih =>
    simp only [assemble] at assembled
    cases stepped : step variables a line with
    | none => simp [stepped] at assembled
    | some next =>
      simp only [stepped, Option.bind_some] at assembled
      obtain ⟨instruction, nextRep⟩ := step_represents variables a next clauses instructions line rep stepped
      obtain ⟨appended, finalRep⟩ := ih next (instructions ++ [instruction]) nextRep assembled
      exact ⟨instruction :: appended, by simpa [List.append_assoc] using finalRep⟩

-- The range decoder never reads a deletion's clause range.
theorem decodeCommand_deletion (pool refs : List Nat) (id start count refsStart refsCount : Nat) :
    decodeCommand pool refs ⟨false, id, start, count, refsStart, refsCount⟩ =
      decodeCommand pool refs ⟨false, id, 0, 0, refsStart, refsCount⟩ := rfl

theorem assembled_decodes (pool refs : List Nat) (offset refsOffset : Nat)
    (instructions : List Instruction) :
    (assembled offset refsOffset instructions).mapM (decodeCommand pool refs) =
      (ProofPacking.commands offset refsOffset instructions).mapM (decodeCommand pool refs) := by
  induction instructions generalizing offset refsOffset with
  | nil => rfl
  | cons c rest ih =>
    cases c with
    | add id clause hints =>
      simp only [assembled, ProofPacking.commands, List.mapM_cons]
      rw [ih]
    | delete stamp ids =>
      simp only [assembled, ProofPacking.commands, List.mapM_cons]
      rw [decodeCommand_deletion, ih]

theorem toLayout_fields (variables : Nat) (a : Assembly)
    (clauses : List Clause) (instructions : List Instruction) (rep : Represents a clauses instructions) :
    toLayout variables a =
      ⟨variables, (ProofPacking.pack variables clauses instructions).pool,
        (ProofPacking.pack variables clauses instructions).starts,
        (ProofPacking.pack variables clauses instructions).sizes,
        (ProofPacking.pack variables clauses instructions).refs,
        assembled (clauses.map ProofPacking.encodeClause).flatten.length 0 instructions⟩ := by
  simp only [toLayout, ProofPacking.pack, rep.initial, rep.commands,
    valid_pool a.references rep.references, rep.pool, rep.refs]

theorem assembled_resources (variables : Nat) (a : Assembly)
    (clauses : List Clause) (instructions : List Instruction) (rep : Represents a clauses instructions)
    (resources : ProofPacking.Resources (toLayout variables a)) :
    ProofPacking.Resources (ProofPacking.pack variables clauses instructions) := by
  rw [toLayout_fields variables a clauses instructions rep] at resources
  unfold ProofPacking.Resources at resources ⊢
  simp only [assembled_length] at resources
  simpa [ProofPacking.pack, commands_length] using resources

theorem assembled_decoded (variables : Nat) (a : Assembly)
    (clauses : List Clause) (instructions : List Instruction) (rep : Represents a clauses instructions)
    (supported : ∀ c ∈ instructions, ProofPacking.CommandSupported c)
    (resources : ProofPacking.Resources (toLayout variables a)) :
    decodeLayout (toLayout variables a) = some ⟨clauses, instructions⟩ := by
  have packed := ProofPacking.roundtrip variables clauses instructions
    ⟨assembled_resources variables a clauses instructions rep resources, rep.positive, supported⟩
  rw [toLayout_fields variables a clauses instructions rep]
  unfold decodeLayout at packed ⊢
  simp only [assembled_length, assembled_decodes]
  simpa [ProofPacking.pack, commands_length] using packed

-- Acceptance of the assembled layout refutes exactly the published initial clauses.
theorem assembled_sound (variables : Nat) (a : Assembly)
    (clauses : List Clause) (instructions : List Instruction) (rep : Represents a clauses instructions)
    (supported : ∀ c ∈ instructions, ProofPacking.CommandSupported c)
    (resources : ProofPacking.Resources (toLayout variables a))
    (accepted : CertifiedStream.check (toLayout variables a) = true) :
    Unsatisfiable (initialDatabase clauses) :=
  InitialDecoder.decoded_sound _ _
    (assembled_decoded variables a clauses instructions rep supported resources) accepted

theorem zip_projections (ranges : List (Nat × Nat)) :
    (ranges.map Prod.fst).zip (ranges.map Prod.snd) = ranges := by
  induction ranges with
  | nil => rfl
  | cons r rest ih => simp [ih]

-- Whatever the commands decode to, the decoded initial clauses are the published ones.
theorem assembled_clauses (variables : Nat) (a : Assembly)
    (clauses : List Clause) (instructions : List Instruction) (rep : Represents a clauses instructions)
    (d : Decoded) (decoded : decodeLayout (toLayout variables a) = some d) : d.clauses = clauses := by
  have traversal := InitialDecoder.clauses_decoded _ d decoded
  rw [toLayout_fields variables a clauses instructions rep] at traversal
  simp only [ProofPacking.pack, zip_projections] at traversal
  have expected := ProofPacking.initial_ranges [] (instructions.map ProofPacking.literals).flatten clauses rep.positive
  simp only [List.nil_append, List.length_nil] at expected
  rw [expected] at traversal
  exact (Option.some.inj traversal).symm

-- Composition from the published initial clauses through the whole proof phase.
-- The executable decoder and certified stream supply every support condition.
theorem assemble_sound (variables capacity : Nat) (initial : State) (lines : List Line)
    (a : Assembly) (valid : Valid initial)
    (built : assemble variables (start initial capacity) lines = some a)
    (accepted : InitialDecoder.check (toLayout variables a) = true) :
    Unsatisfiable (initialDatabase (initial.buffer.closed.map (List.map decodeLiteral))) := by
  obtain ⟨instructions, rep⟩ := assemble_represents variables lines (start initial capacity) a _ []
    (start_represents initial capacity valid) built
  obtain ⟨d, decoded, unsatisfiable⟩ := InitialDecoder.check_sound _ accepted
  rw [← assembled_clauses variables a _ instructions rep d decoded]
  exact unsatisfiable

-- The certified stream's live table starts from exactly the published clauses,
-- whatever the command metadata later decodes to.
theorem represented_origin (variables : Nat) (a : Assembly)
    (clauses : List Clause) (instructions : List Instruction) (rep : Represents a clauses instructions) :
    CertifiedStream.origin (toLayout variables a) = initialDatabase clauses := by
  have expected := ProofPacking.initial_ranges [] (instructions.map ProofPacking.literals).flatten clauses rep.positive
  simp only [List.nil_append, List.length_nil] at expected
  rw [toLayout_fields variables a clauses instructions rep]
  unfold CertifiedStream.origin
  simp only [ProofPacking.pack, zip_projections]
  exact LiveTable.initialize_refines _ _ clauses (InitialDecoder.mapM_lookup _ _ _ expected)

-- Acceptance by the certified stream alone refutes the published clauses.
theorem represented_sound (variables : Nat) (a : Assembly)
    (clauses : List Clause) (instructions : List Instruction) (rep : Represents a clauses instructions)
    (accepted : CertifiedStream.check (toLayout variables a) = true) :
    Unsatisfiable (initialDatabase clauses) := by
  rw [← represented_origin variables a clauses instructions rep]
  exact CertifiedStream.check_sound _ accepted

theorem assemble_certified_sound (variables capacity : Nat) (initial : State) (lines : List Line)
    (a : Assembly) (valid : Valid initial)
    (built : assemble variables (start initial capacity) lines = some a)
    (accepted : CertifiedStream.check (toLayout variables a) = true) :
    Unsatisfiable (initialDatabase (initial.buffer.closed.map (List.map decodeLiteral))) := by
  obtain ⟨instructions, rep⟩ := assemble_represents variables lines (start initial capacity) a _ []
    (start_represents initial capacity valid) built
  exact represented_sound variables a _ instructions rep accepted

#print axioms identifier
#print axioms encode_decoded
#print axioms positive_decoded
#print axioms assembled_append
#print axioms start_represents
#print axioms addition_represents
#print axioms deletion_represents
#print axioms step_represents
#print axioms assemble_represents
#print axioms decodeCommand_deletion
#print axioms assembled_decodes
#print axioms toLayout_fields
#print axioms assembled_resources
#print axioms assembled_decoded
#print axioms assembled_sound
#print axioms zip_projections
#print axioms assembled_clauses
#print axioms assemble_sound
#print axioms represented_origin
#print axioms represented_sound
#print axioms assemble_certified_sound
end OakVerification.CommandAssembly
