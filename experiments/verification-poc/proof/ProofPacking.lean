import InitialDecoder

set_option autoImplicit false
namespace OakVerification.ProofPacking
open Ranges

def encodeClause (c : Clause) : List Nat := c.map encodeLiteral

def segments (offset : Nat) : List (List Nat) → List (Nat × Nat)
  | [] => []
  | xs :: rest => (offset, xs.length) :: segments (offset + xs.length) rest

def literals : Instruction → List Nat
  | .add _ clause _ => encodeClause clause
  | .delete _ _ => []
def references : Instruction → List Nat
  | .add _ _ hints => hints
  | .delete _ ids => ids

def commands (offset refsOffset : Nat) : List Instruction → List Command
  | [] => []
  | .add id clause hints :: rest =>
    ⟨true, id, offset, clause.length, refsOffset, hints.length⟩ ::
      commands (offset + clause.length) (refsOffset + hints.length) rest
  | .delete stamp ids :: rest =>
    ⟨false, stamp, 0, 0, refsOffset, ids.length⟩ ::
      commands offset (refsOffset + ids.length) rest

def pack (variables : Nat) (clauses : List Clause) (instructions : List Instruction) : Layout :=
  let initial := clauses.map encodeClause
  let ranges := segments 0 initial
  ⟨variables, initial.flatten ++ (instructions.map literals).flatten,
    ranges.map Prod.fst, ranges.map Prod.snd, (instructions.map references).flatten,
    commands initial.flatten.length 0 instructions⟩

def Positive (clause : Clause) : Prop := ∀ l ∈ clause, 0 < l.index

def CommandSupported : Instruction → Prop
  | .add id clause hints => id ≤ 256 ∧ hints.length ≤ 256 ∧ Positive clause ∧
      ∀ id ∈ hints, 0 < id ∧ id ≤ 256
  | .delete stamp ids => stamp ≤ 2147483647 ∧ ∀ id ∈ ids, 0 < id ∧ id ≤ 256

-- Exactly the executable range decoder's shape and variable-domain guards.
-- These are resource/representation conditions, never proof validity premises.
def Resources (raw : Layout) : Prop :=
  (raw.variables = 0 || raw.variables > 64 || raw.pool.length > 4096 ||
    raw.refs.length > 4096 || raw.starts.length != raw.sizes.length ||
    raw.starts.length > 256 || raw.commands.length > 256) = false ∧
  raw.pool.all (fun n => decide (n / 2 < raw.variables)) = true

def Supported (variables : Nat) (clauses : List Clause) (instructions : List Instruction) : Prop :=
  Resources (pack variables clauses instructions) ∧
  (∀ clause ∈ clauses, Positive clause) ∧ (∀ c ∈ instructions, CommandSupported c)

theorem clause_roundtrip (clause : Clause) (positive : Positive clause) :
    (encodeClause clause).map decodeLiteral = clause := by
  induction clause with
  | nil => rfl
  | cons l ls ih =>
    change decodeLiteral (encodeLiteral l) :: (encodeClause ls).map decodeLiteral = l :: ls
    rw [decode_encode l (positive l (by simp)), ih (fun x member => positive x (by simp [member]))]

theorem read_encoded (before : List Nat) (clause : Clause) (after : List Nat)
    (positive : Positive clause) :
    readClause (before ++ encodeClause clause ++ after) before.length clause.length = some clause := by
  have decoded := clause_contents before (encodeClause clause) after
  have size : (encodeClause clause).length = clause.length := by simp [encodeClause]
  rw [size, clause_roundtrip clause positive] at decoded
  exact decoded

theorem initial_ranges (before after : List Nat) (clauses : List Clause)
    (positive : ∀ c ∈ clauses, Positive c) :
    (segments before.length (clauses.map encodeClause)).mapM
      (fun r => readClause (before ++ (clauses.map encodeClause).flatten ++ after) r.1 r.2) = some clauses := by
  induction clauses generalizing before with
  | nil => simp [segments]
  | cons c cs ih =>
    have head := read_encoded before c ((cs.map encodeClause).flatten ++ after)
      (positive c (by simp))
    have tail := ih (before ++ encodeClause c) (fun x member => positive x (by simp [member]))
    simpa [segments, encodeClause, List.append_assoc] using
      (show (do
        let first ← readClause (before ++ encodeClause c ++ ((cs.map encodeClause).flatten ++ after)) before.length c.length
        let rest ← (segments (before ++ encodeClause c).length (cs.map encodeClause)).mapM
          (fun r => readClause ((before ++ encodeClause c) ++ (cs.map encodeClause).flatten ++ after) r.1 r.2)
        pure (first :: rest)) = some (c :: cs) by rw [head, tail]; rfl)

theorem command_ranges (before refsBefore after refsAfter : List Nat)
    (instructions : List Instruction) (supported : ∀ c ∈ instructions, CommandSupported c) :
    (commands before.length refsBefore.length instructions).mapM
      (decodeCommand (before ++ (instructions.map literals).flatten ++ after)
        (refsBefore ++ (instructions.map references).flatten ++ refsAfter)) = some instructions := by
  induction instructions generalizing before refsBefore with
  | nil => simp [commands]
  | cons c cs ih =>
    have tailOK : ∀ x ∈ cs, CommandSupported x := fun x member => supported x (by simp [member])
    have headOK := supported c (by simp)
    cases c with
    | add id clause hints =>
      obtain ⟨idBound, hintsBound, positive, ids⟩ := headOK
      have stampBound : ¬ id > 2147483647 := by omega
      have idGuard : ¬ id > 256 := by omega
      have hintsGuard : ¬ hints.length > 256 := by omega
      have idsGuard : hints.all (fun id => decide (0 < id ∧ id ≤ 256)) = true := by simpa using ids
      have clauseRead := read_encoded before clause ((cs.map literals).flatten ++ after) positive
      have refsRead := range_contents refsBefore hints ((cs.map references).flatten ++ refsAfter)
      have tail := ih (before ++ encodeClause clause) (refsBefore ++ hints) tailOK
      simp only [commands, List.map_cons, literals, references, List.flatten_cons, List.mapM_cons]
      have head : decodeCommand (before ++ (encodeClause clause ++ (cs.map literals).flatten) ++ after)
          (refsBefore ++ (hints ++ (cs.map references).flatten) ++ refsAfter)
          ⟨true, id, before.length, clause.length, refsBefore.length, hints.length⟩ =
          some (.add id clause hints) := by
        simp [decodeCommand, stampBound, idGuard, hintsGuard, List.append_assoc,
          refsRead, idsGuard, clauseRead]
      rw [head]
      simpa [encodeClause, List.append_assoc] using congrArg (Option.map (Instruction.add id clause hints :: ·)) tail
    | delete stamp ids =>
      obtain ⟨stampBound, refsOK⟩ := headOK
      have stampGuard : ¬ stamp > 2147483647 := by omega
      have idsGuard : ids.all (fun id => decide (0 < id ∧ id ≤ 256)) = true := by simpa using refsOK
      have refsRead := range_contents refsBefore ids ((cs.map references).flatten ++ refsAfter)
      have tail := ih before (refsBefore ++ ids) tailOK
      simp only [commands, List.map_cons, literals, references, List.flatten_cons, List.nil_append, List.mapM_cons]
      have head : decodeCommand (before ++ (cs.map literals).flatten ++ after)
          (refsBefore ++ (ids ++ (cs.map references).flatten) ++ refsAfter)
          ⟨false, stamp, 0, 0, refsBefore.length, ids.length⟩ = some (.delete stamp ids) := by
        simp [decodeCommand, stampGuard, List.append_assoc, refsRead, idsGuard]
      rw [head]
      simpa [List.append_assoc] using congrArg (Option.map (Instruction.delete stamp ids :: ·)) tail

theorem roundtrip (variables : Nat) (clauses : List Clause) (instructions : List Instruction)
    (supported : Supported variables clauses instructions) :
    decodeLayout (pack variables clauses instructions) = some ⟨clauses, instructions⟩ := by
  obtain ⟨resources, positive, supported⟩ := supported
  have initial := initial_ranges [] (instructions.map literals).flatten clauses positive
  have cmds := command_ranges (clauses.map encodeClause).flatten [] [] [] instructions supported
  have zipped : (pack variables clauses instructions).starts.zip (pack variables clauses instructions).sizes =
      segments 0 (clauses.map encodeClause) := by
    change ((segments 0 (clauses.map encodeClause)).map Prod.fst).zip
      ((segments 0 (clauses.map encodeClause)).map Prod.snd) = _
    have projections : ∀ xs : List (Nat × Nat), (xs.map Prod.fst).zip (xs.map Prod.snd) = xs := by
      intro xs
      induction xs with
      | nil => rfl
      | cons x xs ih => simp [ih]
    exact projections _
  simp only [decodeLayout, resources.1, Bool.false_eq_true, ↓reduceIte, resources.2, Bool.not_true]
  rw [zipped]
  have initial' : (segments 0 (clauses.map encodeClause)).mapM
      (fun r => readClause (pack variables clauses instructions).pool r.1 r.2) = some clauses := by
    simpa [pack] using initial
  have cmds' : (pack variables clauses instructions).commands.mapM
      (decodeCommand (pack variables clauses instructions).pool (pack variables clauses instructions).refs) = some instructions := by
    simpa [pack] using cmds
  simp [initial', cmds']

instance (clause : Clause) : Decidable (Positive clause) := by
  unfold Positive
  infer_instance
instance (instruction : Instruction) : Decidable (CommandSupported instruction) := by
  cases instruction <;> unfold CommandSupported <;> infer_instance
instance (raw : Layout) : Decidable (Resources raw) := by
  unfold Resources
  infer_instance
instance (variables : Nat) (clauses : List Clause) (instructions : List Instruction) :
    Decidable (Supported variables clauses instructions) := by
  unfold Supported
  infer_instance

theorem packed_sound (variables : Nat) (clauses : List Clause) (instructions : List Instruction)
    (supported : Supported variables clauses instructions)
    (accepted : CertifiedStream.check (pack variables clauses instructions) = true) :
    Unsatisfiable (initialDatabase clauses) :=
  InitialDecoder.decoded_sound _ _ (roundtrip variables clauses instructions supported) accepted

def check (variables : Nat) (clauses : List Clause) (instructions : List Instruction) : Bool :=
  if Supported variables clauses instructions then CertifiedStream.check (pack variables clauses instructions)
  else false

theorem check_sound (variables : Nat) (clauses : List Clause) (instructions : List Instruction)
    (accepted : check variables clauses instructions = true) : Unsatisfiable (initialDatabase clauses) := by
  unfold check at accepted
  split at accepted
  next supported => exact packed_sound variables clauses instructions supported accepted
  next => contradiction

#print axioms check
#print axioms check_sound
#print axioms clause_roundtrip
#print axioms read_encoded
#print axioms initial_ranges
#print axioms command_ranges
#print axioms roundtrip
#print axioms packed_sound
end OakVerification.ProofPacking
