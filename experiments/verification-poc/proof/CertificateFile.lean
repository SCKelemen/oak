import CommandAssembly

set_option autoImplicit false
namespace OakVerification.CertificateFile
open Packed Scanner Ranges SegmentPublication CommandAssembly

/-! The complete certificate-file state machine.

This module reads whole DIMACS and LRAT texts byte by byte with the proved
scanner, exactly as the Oak decoder does: entry guards, comment and blank
lines, the `p cnf` header with its variable and clause-count domains, clause
segments that may span lines, and proof lines made of an identifier, an
optional deletion marker, and zero-terminated segments. It composes the
segment publication state, the command assembly invariant, and the certified
stream checker into one executable check with a soundness theorem. -/

def bytesOf (text : String) : List Nat := text.toUTF8.toList.map UInt8.toNat

-- The decoder's entry guards: at most 65536 bytes, every byte ASCII.
def ascii (bytes : List Nat) : Bool :=
  decide (bytes.length ≤ 65536) && bytes.all (fun b => decide (b ≤ 127))

-- A token spelled as exactly one given byte, as `rup_word` tests.
def Word (bytes : List Nat) (t : Token) (ch : Nat) : Prop :=
  t.stop = t.start + 1 ∧ bytes[t.start]? = some ch
instance (bytes : List Nat) (t : Token) (ch : Nat) : Decidable (Word bytes t ch) := by
  unfold Word; infer_instance

-- One zero-terminated segment starting at a byte position. Unlike the
-- single-segment adapter, a newline or end of input inside a segment rejects,
-- and the position after the terminator is returned for the next reader.
def segmentAt (mode : Mode) (variables : Nat) (bytes : List Nat) (pos : Nat) (b : Buffer) :
    Nat → Option (Buffer × Nat)
  | 0 => none
  | fuel + 1 =>
    let t := scan bytes pos
    if t.kind ≠ 2 then none
    else if mode = .deletion ∧ t.magnitude = 0 ∧ ¬ Word bytes t 48 then none
    else (tokenStep mode variables b t).bind fun after =>
      if t.magnitude = 0 then some (after, t.next)
      else segmentAt mode variables bytes t.next after fuel

theorem segmentAt_completes (mode : Mode) (variables : Nat) (bytes : List Nat)
    (fuel pos : Nat) (before after : Buffer) (next : Nat)
    (decoded : segmentAt mode variables bytes pos before fuel = some (after, next)) :
    Completes before after := by
  induction fuel generalizing pos before with
  | zero => simp [segmentAt] at decoded
  | succ fuel ih =>
    simp only [segmentAt] at decoded
    split at decoded
    · simp at decoded
    · split at decoded
      · simp at decoded
      · cases stepped : tokenStep mode variables before (scan bytes pos) with
        | none => simp [stepped] at decoded
        | some middle =>
          simp only [stepped, Option.bind] at decoded
          split at decoded
          · rename_i zero
            simp only [Option.some.injEq, Prod.mk.injEq] at decoded
            obtain ⟨same, _⟩ := decoded
            subst same
            rw [zero_closes mode variables before middle (scan bytes pos) zero stepped]
            exact close_completes before
          · rename_i nonzero
            obtain ⟨item, pushed⟩ := nonzero_push mode variables before middle (scan bytes pos) nonzero stepped
            exact push_completion before middle after item pushed (ih _ middle decoded)

theorem segmentAt_preserves (mode : Mode) (variables : Nat) (bytes : List Nat)
    (fuel pos : Nat) (before after : Buffer) (next : Nat) (wellFormed : WellFormed before)
    (decoded : segmentAt mode variables bytes pos before fuel = some (after, next)) :
    WellFormed after := by
  induction fuel generalizing pos before with
  | zero => simp [segmentAt] at decoded
  | succ fuel ih =>
    simp only [segmentAt] at decoded
    split at decoded
    · simp at decoded
    · split at decoded
      · simp at decoded
      · cases stepped : tokenStep mode variables before (scan bytes pos) with
        | none => simp [stepped] at decoded
        | some middle =>
          simp only [stepped, Option.bind] at decoded
          have middleWellFormed := tokenStep_preserves wellFormed stepped
          split at decoded
          · simp only [Option.some.injEq, Prod.mk.injEq] at decoded
            obtain ⟨same, _⟩ := decoded
            subst same
            exact middleWellFormed
          · exact ih _ middle middleWellFormed decoded

-- Literal-mode steps keep every pool item inside the declared variable domain.
def Domain (variables : Nat) (b : Buffer) : Prop := ∀ n ∈ b.pool, n / 2 < variables

theorem tokenStep_domain (variables : Nat) (b after : Buffer) (t : Token)
    (domain : Domain variables b) (stepped : tokenStep .literal variables b t = some after) :
    Domain variables after := by
  unfold tokenStep at stepped
  split at stepped
  · split at stepped
    · cases Option.some.inj stepped
      simpa [Domain, closeSegment] using domain
    · split at stepped
      · split at stepped
        · rename_i _ nonzero _ bound
          obtain ⟨pool, _, _, _, _⟩ := push_layout stepped
          intro n member
          rw [pool, List.mem_append, List.mem_singleton] at member
          cases member with
          | inl earlier => exact domain n earlier
          | inr item =>
            subst item
            split <;> omega
        · simp at stepped
      · rename_i notLiteral
        exact absurd rfl notLiteral
  · simp at stepped

theorem segmentAt_domain (variables : Nat) (bytes : List Nat)
    (fuel pos : Nat) (before after : Buffer) (next : Nat) (domain : Domain variables before)
    (decoded : segmentAt .literal variables bytes pos before fuel = some (after, next)) :
    Domain variables after := by
  induction fuel generalizing pos before with
  | zero => simp [segmentAt] at decoded
  | succ fuel ih =>
    simp only [segmentAt] at decoded
    split at decoded
    · simp at decoded
    · split at decoded
      · simp at decoded
      · cases stepped : tokenStep .literal variables before (scan bytes pos) with
        | none => simp [stepped] at decoded
        | some middle =>
          simp only [stepped, Option.bind] at decoded
          have middleDomain := tokenStep_domain variables before middle (scan bytes pos) domain stepped
          split at decoded
          · simp only [Option.some.injEq, Prod.mk.injEq] at decoded
            obtain ⟨same, _⟩ := decoded
            subst same
            exact middleDomain
          · exact ih _ middle middleDomain decoded

-- Position-based publication with the same metadata as `publish`.
def publishAt (mode : Mode) (variables : Nat) (s : State) (bytes : List Nat) (pos : Nat) :
    Option (State × Nat) :=
  match segmentAt mode variables bytes pos s.buffer (bytes.length + 1) with
  | none => none
  | some (after, next) =>
    some (⟨after, s.ranges ++ [(s.buffer.pool.length, after.pool.length - s.buffer.pool.length)]⟩, next)

theorem publishAt_layout (mode : Mode) (variables : Nat) (s after : State) (bytes : List Nat)
    (pos next : Nat) (valid : Valid s) (published : publishAt mode variables s bytes pos = some (after, next)) :
    ∃ items : List Nat,
      after.buffer.pool = s.buffer.pool ++ items ∧
      after.buffer.closed = s.buffer.closed ++ [items] ∧ after.buffer.pending = [] ∧
      after.ranges = s.ranges ++ [(s.buffer.pool.length, items.length)] ∧
      Packed.WellFormed after.buffer := by
  unfold publishAt at published
  cases decoded : segmentAt mode variables bytes pos s.buffer (bytes.length + 1) with
  | none => simp [decoded] at published
  | some result =>
    obtain ⟨buffer, stop⟩ := result
    simp only [decoded, Option.some.injEq, Prod.mk.injEq] at published
    obtain ⟨same, _⟩ := published
    subst same
    obtain ⟨items, pool, closed, pending, _⟩ :=
      segmentAt_completes mode variables bytes _ pos s.buffer buffer stop decoded
    refine ⟨items, pool, ?_, pending, ?_, ?_⟩
    · simpa [valid.2.1] using closed
    · simp [pool]
    · exact segmentAt_preserves mode variables bytes _ pos s.buffer buffer stop valid.1 decoded

theorem publishAt_valid (mode : Mode) (variables : Nat) (s after : State) (bytes : List Nat)
    (pos next : Nat) (valid : Valid s) (published : publishAt mode variables s bytes pos = some (after, next)) :
    Valid after := by
  obtain ⟨items, pool, closed, pending, ranges, wellFormed⟩ :=
    publishAt_layout mode variables s after bytes pos next valid published
  refine ⟨wellFormed, pending, ?_⟩
  have initialPool : s.buffer.pool = s.buffer.closed.flatten := by simpa [valid.2.1] using valid.1.1
  rw [ranges, closed, segments_append, valid.2.2]
  simp [ProofPacking.segments, initialPool]

-- Identifier and deletion-stamp tokens: `scan[4] != 0 && (scan[4] == 1 || scan[3] == 0)`.
def identifierToken (t : Token) : Option Nat :=
  if t.kind = 2 ∧ t.sign ≠ 0 ∧ (t.sign = 1 ∨ t.magnitude = 0) then some t.magnitude else none

-- The single-word identifier rule is this token rule plus end of input.
def identifierWord (bytes : List Nat) : Option Nat :=
  let t := scan bytes 0
  if t.kind = 2 ∧ t.sign ≠ 0 ∧ (t.sign = 1 ∨ t.magnitude = 0) ∧ (scan bytes t.next).kind = 0
  then some t.magnitude else none

theorem identifier_word (word : String) : identifier word = identifierWord (bytesOf word) := rfl

theorem identifier_token (bytes : List Nat) (n : Nat) :
    identifierWord bytes = some n ↔
      identifierToken (scan bytes 0) = some n ∧ (scan bytes (scan bytes 0).next).kind = 0 := by
  simp only [identifierWord, identifierToken]
  generalize scan bytes 0 = t
  generalize (scan bytes t.next).kind = k
  by_cases eof : k = 0 <;> by_cases cond : t.kind = 2 ∧ t.sign ≠ 0 ∧ (t.sign = 1 ∨ t.magnitude = 0) <;>
    simp [eof, cond]

-- A command line ends at a newline or the end of input; any further word rejects.
def lineEnd (bytes : List Nat) (pos : Nat) : Option Nat :=
  let t := scan bytes pos
  if t.kind = 2 then none else some t.next

def skipLine (bytes : List Nat) (pos : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    let t := scan bytes pos
    if t.kind = 2 then skipLine bytes t.next fuel else some t.next

-- Command metadata as the decoder records it: the literal offset at the start
-- of the line and the counts published on this line.
def command (addition : Bool) (stamp : Nat) (a : Assembly) (literals references : State) : Command :=
  ⟨addition, stamp, a.literals.buffer.pool.length,
    literals.buffer.pool.length - a.literals.buffer.pool.length,
    a.references.buffer.pool.length,
    references.buffer.pool.length - a.references.buffer.pool.length⟩

def store (a : Assembly) (literals references : State) (c : Command) : Option Assembly :=
  if a.commands.length < 256 then some ⟨literals, references, a.initial, a.commands ++ [c]⟩ else none

def readCommand (variables : Nat) (bytes : List Nat) (pos : Nat) (a : Assembly) :
    Option (Assembly × Nat) :=
  let t := scan bytes pos
  match identifierToken t with
  | none => none
  | some stamp =>
    let marker := scan bytes t.next
    if marker.kind = 2 ∧ Word bytes marker 100 then
      match publishAt .deletion variables a.references bytes marker.next with
      | none => none
      | some (references, next) =>
        match lineEnd bytes next with
        | none => none
        | some after =>
          (store a a.literals references (command false stamp a a.literals references)).map (·, after)
    else
      match publishAt .literal variables a.literals bytes t.next with
      | none => none
      | some (literals, next) =>
        match publishAt .hint variables a.references bytes next with
        | none => none
        | some (references, last) =>
          match lineEnd bytes last with
          | none => none
          | some after =>
            (store a literals references (command true stamp a literals references)).map (·, after)

theorem pool_length (s : State) (clauses : List Clause) (instructions : List Instruction)
    (pool : s.buffer.pool = (clauses.map ProofPacking.encodeClause).flatten ++ (instructions.map ProofPacking.literals).flatten) :
    s.buffer.pool.length =
      (clauses.map ProofPacking.encodeClause).flatten.length + (instructions.map ProofPacking.literals).flatten.length := by
  rw [pool, List.length_append]

theorem addition_step (stamp : Nat) (a : Assembly) (clauses : List Clause) (instructions : List Instruction)
    (literals references : State) (items refs : List Nat)
    (rep : Represents a clauses instructions) (litValid : Valid literals) (refValid : Valid references)
    (litPool : literals.buffer.pool = a.literals.buffer.pool ++ items)
    (refPool : references.buffer.pool = a.references.buffer.pool ++ refs)
    (refClosed : references.buffer.closed = a.references.buffer.closed ++ [refs]) :
    Represents ⟨literals, references, a.initial, a.commands ++ [command true stamp a literals references]⟩
      clauses (instructions ++ [.add stamp (items.map decodeLiteral) refs]) := by
  have litLength := pool_length a.literals clauses instructions rep.pool
  have refLength : a.references.buffer.pool.length =
      (instructions.map ProofPacking.references).flatten.length := by
    rw [valid_pool a.references rep.references, rep.refs]
  refine ⟨litValid, refValid, ?_, ?_, rep.initial, ?_, rep.positive, ?_⟩
  · simp [litPool, rep.pool, ProofPacking.literals, encode_decoded]
  · simp [refClosed, rep.refs, ProofPacking.references]
  · simp only [rep.commands, assembled_append, assembled, command, litPool, refPool, List.length_append,
      List.length_map, Nat.add_sub_cancel_left, Nat.zero_add, litLength, refLength]
  · intro i member
    simp only [List.mem_append, List.mem_singleton] at member
    cases member with
    | inl earlier => exact rep.additions i earlier
    | inr new => subst new; exact positive_decoded items

theorem deletion_step (stamp : Nat) (a : Assembly) (clauses : List Clause) (instructions : List Instruction)
    (references : State) (refs : List Nat)
    (rep : Represents a clauses instructions) (refValid : Valid references)
    (refPool : references.buffer.pool = a.references.buffer.pool ++ refs)
    (refClosed : references.buffer.closed = a.references.buffer.closed ++ [refs]) :
    Represents ⟨a.literals, references, a.initial, a.commands ++ [command false stamp a a.literals references]⟩
      clauses (instructions ++ [.delete stamp refs]) := by
  have litLength := pool_length a.literals clauses instructions rep.pool
  have refLength : a.references.buffer.pool.length =
      (instructions.map ProofPacking.references).flatten.length := by
    rw [valid_pool a.references rep.references, rep.refs]
  refine ⟨rep.literals, refValid, ?_, ?_, rep.initial, ?_, rep.positive, ?_⟩
  · simp [rep.pool, ProofPacking.literals]
  · simp [refClosed, rep.refs, ProofPacking.references]
  · simp only [rep.commands, assembled_append, assembled, command, refPool, List.length_append,
      Nat.add_sub_cancel_left, Nat.sub_self, Nat.zero_add, litLength, refLength]
  · intro i member
    simp only [List.mem_append, List.mem_singleton] at member
    cases member with
    | inl earlier => exact rep.additions i earlier
    | inr new => subst new; trivial

theorem store_represents (a after : Assembly) (literals references : State) (c : Command)
    (stored : store a literals references c = some after) :
    after = ⟨literals, references, a.initial, a.commands ++ [c]⟩ := by
  unfold store at stored
  split at stored
  · exact (Option.some.inj stored).symm
  · simp at stored

theorem readCommand_represents (variables : Nat) (bytes : List Nat) (pos next : Nat)
    (a after : Assembly) (clauses : List Clause) (instructions : List Instruction)
    (rep : Represents a clauses instructions)
    (read : readCommand variables bytes pos a = some (after, next)) :
    ∃ instruction : Instruction, Represents after clauses (instructions ++ [instruction]) := by
  unfold readCommand at read
  cases scanned : identifierToken (scan bytes pos) with
  | none => simp [scanned] at read
  | some stamp =>
    simp only [scanned] at read
    split at read
    · cases refsPublished : publishAt .deletion variables a.references bytes (scan bytes (scan bytes pos).next).next with
      | none => simp [refsPublished] at read
      | some result =>
        obtain ⟨references, stop⟩ := result
        simp only [refsPublished] at read
        cases ended : lineEnd bytes stop with
        | none => simp [ended] at read
        | some last =>
          simp only [ended] at read
          cases stored : store a a.literals references (command false stamp a a.literals references) with
          | none => simp [stored] at read
          | some assembled =>
            simp only [stored, Option.map_some, Option.some.injEq, Prod.mk.injEq] at read
            obtain ⟨same, _⟩ := read
            subst same
            rw [store_represents a assembled a.literals references _ stored]
            obtain ⟨refs, refPool, refClosed, _, _, _⟩ :=
              publishAt_layout .deletion variables a.references references bytes _ stop rep.references refsPublished
            exact ⟨_, deletion_step stamp a clauses instructions references refs rep
              (publishAt_valid .deletion variables a.references references bytes _ stop rep.references refsPublished)
              refPool refClosed⟩
    · cases litsPublished : publishAt .literal variables a.literals bytes (scan bytes pos).next with
      | none => simp [litsPublished] at read
      | some litResult =>
        obtain ⟨literals, middle⟩ := litResult
        simp only [litsPublished] at read
        cases refsPublished : publishAt .hint variables a.references bytes middle with
        | none => simp [refsPublished] at read
        | some refResult =>
          obtain ⟨references, stop⟩ := refResult
          simp only [refsPublished] at read
          cases ended : lineEnd bytes stop with
          | none => simp [ended] at read
          | some last =>
            simp only [ended] at read
            cases stored : store a literals references (command true stamp a literals references) with
            | none => simp [stored] at read
            | some assembled =>
              simp only [stored, Option.map_some, Option.some.injEq, Prod.mk.injEq] at read
              obtain ⟨same, _⟩ := read
              subst same
              rw [store_represents a assembled literals references _ stored]
              obtain ⟨items, litPool, _, _, _, _⟩ :=
                publishAt_layout .literal variables a.literals literals bytes _ middle rep.literals litsPublished
              obtain ⟨refs, refPool, refClosed, _, _, _⟩ :=
                publishAt_layout .hint variables a.references references bytes _ stop rep.references refsPublished
              exact ⟨_, addition_step stamp a clauses instructions literals references items refs rep
                (publishAt_valid .literal variables a.literals literals bytes _ middle rep.literals litsPublished)
                (publishAt_valid .hint variables a.references references bytes _ stop rep.references refsPublished)
                litPool refPool refClosed⟩

-- The proof phase: blank lines, comment lines, and one command per other line.
def proofLines (variables : Nat) (bytes : List Nat) : Nat → Assembly → Nat → Option Assembly
  | _, _, 0 => none
  | pos, a, fuel + 1 =>
    let t := scan bytes pos
    if t.kind = 0 then some a
    else if t.kind = 1 then proofLines variables bytes t.next a fuel
    else if Word bytes t 99 then
      match skipLine bytes t.next fuel with
      | none => none
      | some next => proofLines variables bytes next a fuel
    else
      match readCommand variables bytes pos a with
      | none => none
      | some (after, next) => proofLines variables bytes next after fuel

theorem proofLines_represents (variables : Nat) (bytes : List Nat) (fuel pos : Nat)
    (a after : Assembly) (clauses : List Clause) (instructions : List Instruction)
    (rep : Represents a clauses instructions)
    (decoded : proofLines variables bytes pos a fuel = some after) :
    ∃ appended : List Instruction, Represents after clauses (instructions ++ appended) := by
  induction fuel generalizing pos a instructions with
  | zero => simp [proofLines] at decoded
  | succ fuel ih =>
    simp only [proofLines] at decoded
    split at decoded
    · cases Option.some.inj decoded
      exact ⟨[], by simpa using rep⟩
    · split at decoded
      · exact ih _ a instructions rep decoded
      · split at decoded
        · cases skipped : skipLine bytes (scan bytes pos).next fuel with
          | none => simp [skipped] at decoded
          | some next =>
            simp only [skipped] at decoded
            exact ih _ a instructions rep decoded
        · cases read : readCommand variables bytes pos a with
          | none => simp [read] at decoded
          | some result =>
            obtain ⟨middle, next⟩ := result
            simp only [read] at decoded
            obtain ⟨instruction, middleRep⟩ :=
              readCommand_represents variables bytes pos next a middle clauses instructions rep read
            obtain ⟨appended, finalRep⟩ := ih _ middle (instructions ++ [instruction]) middleRep decoded
            exact ⟨instruction :: appended, by simpa [List.append_assoc] using finalRep⟩

-- The DIMACS phase. Comment and blank lines may precede the header.
def preamble (bytes : List Nat) : Nat → Nat → Option Nat
  | _, 0 => none
  | pos, fuel + 1 =>
    let t := scan bytes pos
    if t.kind = 0 then none
    else if t.kind = 1 then preamble bytes t.next fuel
    else if Word bytes t 99 then
      match skipLine bytes t.next fuel with
      | none => none
      | some next => preamble bytes next fuel
    else some pos

structure Header where
  variables : Nat
  count : Nat
  deriving Repr

def header (bytes : List Nat) (pos : Nat) : Option (Header × Nat) :=
  let p := scan bytes pos
  let cnf := scan bytes p.next
  let v := scan bytes cnf.next
  let n := scan bytes v.next
  if p.kind = 2 ∧ Word bytes p 112 ∧
      cnf.kind = 2 ∧ cnf.stop = cnf.start + 3 ∧ bytes[cnf.start]? = some 99 ∧
        bytes[cnf.start + 1]? = some 110 ∧ bytes[cnf.start + 2]? = some 102 ∧
      v.kind = 2 ∧ v.sign = 1 ∧ 0 < v.magnitude ∧ v.magnitude ≤ 64 ∧
      n.kind = 2 ∧ n.sign ≠ 0 ∧ (n.sign = 1 ∨ n.magnitude = 0) ∧ n.magnitude ≤ 256 then
    match lineEnd bytes n.next with
    | none => none
    | some next => some (⟨v.magnitude, n.magnitude⟩, next)
  else none

theorem header_bounds (bytes : List Nat) (pos next : Nat) (h : Header)
    (parsed : header bytes pos = some (h, next)) :
    0 < h.variables ∧ h.variables ≤ 64 ∧ h.count ≤ 256 := by
  simp only [header] at parsed
  split at parsed
  · rename_i cond
    obtain ⟨_, _, _, _, _, _, _, _, _, lower, upper, _, _, _, bound⟩ := cond
    split at parsed
    · simp at parsed
    · simp only [Option.some.injEq, Prod.mk.injEq] at parsed
      obtain ⟨same, _⟩ := parsed
      subst same
      exact ⟨lower, upper, bound⟩
  · simp at parsed

-- Between clause terminators the pending literals stay in the pool; the
-- published ranges still describe exactly the closed clauses.
def Partial (variables : Nat) (s : State) : Prop :=
  WellFormed s.buffer ∧ s.ranges = ProofPacking.segments 0 s.buffer.closed ∧ Domain variables s.buffer

def clauses (variables count : Nat) (bytes : List Nat) : Nat → State → Bool → Nat → Option State
  | _, _, _, 0 => none
  | pos, s, first, fuel + 1 =>
    let t := scan bytes pos
    if t.kind = 0 then
      if s.buffer.pending = [] ∧ s.buffer.closed.length = count then some s else none
    else if t.kind = 1 then clauses variables count bytes t.next s true fuel
    else if first ∧ Word bytes t 99 then
      match skipLine bytes t.next fuel with
      | none => none
      | some next => clauses variables count bytes next s true fuel
    else
      match tokenStep .literal variables s.buffer t with
      | none => none
      | some after =>
        if t.magnitude = 0 then
          if s.buffer.closed.length < count then
            clauses variables count bytes t.next
              ⟨after, s.ranges ++ [(Packed.start s.buffer, s.buffer.pending.length)]⟩ false fuel
          else none
        else clauses variables count bytes t.next ⟨after, s.ranges⟩ false fuel

theorem close_partial (variables : Nat) (s : State) (part : Partial variables s) :
    Partial variables ⟨closeSegment s.buffer, s.ranges ++ [(Packed.start s.buffer, s.buffer.pending.length)]⟩ := by
  obtain ⟨wellFormed, ranges, domain⟩ := part
  refine ⟨seal_preserves s.buffer wellFormed, ?_, ?_⟩
  · show s.ranges ++ [(Packed.start s.buffer, s.buffer.pending.length)] =
      ProofPacking.segments 0 (s.buffer.closed ++ [s.buffer.pending])
    rw [segments_append, ranges, (pending_range s.buffer wellFormed).1]
    simp [ProofPacking.segments]
  · simpa [Domain, closeSegment] using domain

theorem push_partial (variables : Nat) (s : State) (after : Buffer) (t : Token)
    (part : Partial variables s) (nonzero : t.magnitude ≠ 0)
    (stepped : tokenStep .literal variables s.buffer t = some after) :
    Partial variables ⟨after, s.ranges⟩ := by
  obtain ⟨wellFormed, ranges, domain⟩ := part
  obtain ⟨item, pushed⟩ := nonzero_push .literal variables s.buffer after t nonzero stepped
  obtain ⟨_, _, closed, _, _⟩ := push_layout pushed
  exact ⟨tokenStep_preserves wellFormed stepped, by simpa [closed] using ranges,
    tokenStep_domain variables s.buffer after t domain stepped⟩

theorem clauses_valid (variables count : Nat) (bytes : List Nat) (fuel pos : Nat) (first : Bool)
    (s out : State) (part : Partial variables s)
    (decoded : clauses variables count bytes pos s first fuel = some out) :
    Valid out ∧ Domain variables out.buffer ∧ out.buffer.closed.length = count := by
  induction fuel generalizing pos s first with
  | zero => simp [clauses] at decoded
  | succ fuel ih =>
    simp only [clauses] at decoded
    split at decoded
    · split at decoded
      · rename_i finished
        cases Option.some.inj decoded
        exact ⟨⟨part.1, finished.1, part.2.1⟩, part.2.2, finished.2⟩
      · simp at decoded
    · split at decoded
      · exact ih _ true s part decoded
      · split at decoded
        · cases skipped : skipLine bytes (scan bytes pos).next fuel with
          | none => simp [skipped] at decoded
          | some next =>
            simp only [skipped] at decoded
            exact ih _ true s part decoded
        · cases stepped : tokenStep .literal variables s.buffer (scan bytes pos) with
          | none => simp [stepped] at decoded
          | some after =>
            simp only [stepped] at decoded
            split at decoded
            · rename_i zero
              split at decoded
              · rw [zero_closes .literal variables s.buffer after (scan bytes pos) zero stepped] at decoded
                exact ih _ false _ (close_partial variables s part) decoded
              · simp at decoded
            · rename_i nonzero
              exact ih _ false _ (push_partial variables s after (scan bytes pos) part nonzero stepped) decoded

def formula (cnf : String) : Option (Header × State) :=
  if !ascii (bytesOf cnf) then none else
  match preamble (bytesOf cnf) 0 ((bytesOf cnf).length + 1) with
  | none => none
  | some pos =>
    match header (bytesOf cnf) pos with
    | none => none
    | some (h, next) =>
      match clauses h.variables h.count (bytesOf cnf) next (emptyState 4096) true ((bytesOf cnf).length + 1) with
      | none => none
      | some s => some (h, s)

theorem empty_partial (variables capacity : Nat) : Partial variables (emptyState capacity) := by
  refine ⟨empty_wellFormed capacity, rfl, ?_⟩
  intro n member
  simp [emptyState, empty] at member

-- The parsed formula is a valid publication state within the declared domains
-- with exactly the declared number of clauses.
theorem formula_valid (cnf : String) (h : Header) (s : State) (parsed : formula cnf = some (h, s)) :
    Valid s ∧ Domain h.variables s.buffer ∧ s.buffer.closed.length = h.count ∧
      0 < h.variables ∧ h.variables ≤ 64 ∧ h.count ≤ 256 := by
  unfold formula at parsed
  split at parsed
  · simp at parsed
  · cases prefixed : preamble (bytesOf cnf) 0 ((bytesOf cnf).length + 1) with
    | none => simp [prefixed] at parsed
    | some pos =>
      simp only [prefixed] at parsed
      cases headed : header (bytesOf cnf) pos with
      | none => simp [headed] at parsed
      | some result =>
        obtain ⟨found, next⟩ := result
        simp only [headed] at parsed
        cases decoded : clauses found.variables found.count (bytesOf cnf) next (emptyState 4096) true ((bytesOf cnf).length + 1) with
        | none => simp [decoded] at parsed
        | some out =>
          simp only [decoded, Option.some.injEq, Prod.mk.injEq] at parsed
          obtain ⟨sameHeader, sameState⟩ := parsed
          subst sameHeader
          subst sameState
          obtain ⟨valid, domain, counted⟩ :=
            clauses_valid found.variables found.count (bytesOf cnf) _ next true (emptyState 4096) out
              (empty_partial found.variables 4096) decoded
          obtain ⟨lower, upper, bound⟩ := header_bounds (bytesOf cnf) pos next found headed
          exact ⟨valid, domain, counted, lower, upper, bound⟩

-- The whole file check: both texts pass the entry guards, the DIMACS phase
-- publishes the initial clauses, the proof phase assembles every command, and
-- the certified stream refutes the published clauses.
def check (cnf proof : String) : Bool :=
  match formula cnf with
  | none => false
  | some (h, literals) =>
    if !ascii (bytesOf proof) then false else
    match proofLines h.variables (bytesOf proof) 0 (CommandAssembly.start literals 4096) ((bytesOf proof).length + 1) with
    | none => false
    | some a => CertifiedStream.check (toLayout h.variables a)

theorem check_sound (cnf proof : String) (accepted : check cnf proof = true) :
    ∃ (h : Header) (s : State), formula cnf = some (h, s) ∧
      s.buffer.closed.length = h.count ∧
      Unsatisfiable (initialDatabase (s.buffer.closed.map (List.map decodeLiteral))) := by
  unfold check at accepted
  cases parsed : formula cnf with
  | none => simp [parsed] at accepted
  | some result =>
    obtain ⟨h, s⟩ := result
    simp only [parsed] at accepted
    split at accepted
    · simp at accepted
    · cases assembled : proofLines h.variables (bytesOf proof) 0 (CommandAssembly.start s 4096) ((bytesOf proof).length + 1) with
      | none => simp [assembled] at accepted
      | some a =>
        simp only [assembled] at accepted
        obtain ⟨valid, _, counted, _⟩ := formula_valid cnf h s parsed
        obtain ⟨instructions, rep⟩ := proofLines_represents h.variables (bytesOf proof) _ 0
          (CommandAssembly.start s 4096) a _ [] (start_represents s 4096 valid) assembled
        simp only [List.nil_append] at rep
        exact ⟨h, s, rfl, counted, represented_sound h.variables a _ instructions rep accepted⟩

#print axioms segmentAt_completes
#print axioms segmentAt_preserves
#print axioms tokenStep_domain
#print axioms segmentAt_domain
#print axioms publishAt_layout
#print axioms publishAt_valid
#print axioms identifier_word
#print axioms identifier_token
#print axioms addition_step
#print axioms deletion_step
#print axioms readCommand_represents
#print axioms proofLines_represents
#print axioms header_bounds
#print axioms close_partial
#print axioms push_partial
#print axioms clauses_valid
#print axioms formula_valid
#print axioms check
#print axioms check_sound
end OakVerification.CertificateFile
