import OakText

set_option autoImplicit false
namespace OakVerification.OakText
open Scanner Ranges Packed SegmentPublication CommandAssembly CertificateFile

/-! Roadmap step 2, second increment: the transliterated Oak decoder refines the
proved file model. `check_refines` states that every acceptance by
`OakText.check` is an acceptance by `CertificateFile.check`, and
`check_refutes` transfers the file model's soundness theorem to the Oak
decoder's stage machines: an acceptance refutes the formula the DIMACS text
defines. What remains between the compiled program and these theorems is the
transliteration's fidelity to `self_hosted_text.oak`, checked on every corpus
case by `OakTextCompare` and stated as the assumption it is.

The proof follows the decoder's structure. The LRAT phase is handled line by
line: a stage-0 state at a line start corresponds to a command assembly, each
literal, hint, or deletion segment the Oak loop consumes is one `segmentAt`
run of the model, and storing the command at the end of the line is
`readCommand`. The DIMACS phase is handled token by token against `clauses`
once the header has been matched against `preamble` and `header`. -/

-- Every scanned token's sign tag is 0, 1, or 2.
theorem sign_cases (bytes : List Nat) (pos : Nat) :
    (scan bytes pos).sign = 0 ∨ (scan bytes pos).sign = 1 ∨ (scan bytes pos).sign = 2 := by
  unfold scan scanTail tokenAt
  split
  · simp
  · split
    · simp
    · simp only [numeric]
      split
      · rename_i tag ds _
        split
        · simp
        · split <;> simp_all
      · rename_i tag ds _
        split
        · simp
        · split <;> simp_all
      · rename_i tag ds _
        split
        · simp
        · split <;> simp_all

-- Every scanned token's kind is 0 (end of input), 1 (newline), or 2 (word).
theorem kind_cases (bytes : List Nat) (pos : Nat) :
    (scan bytes pos).kind = 0 ∨ (scan bytes pos).kind = 1 ∨ (scan bytes pos).kind = 2 := by
  unfold scan scanTail tokenAt
  split
  · simp
  · split <;> simp

-- Fuel monotonicity of the model's readers: more fuel never changes a
-- successful result.
theorem segmentAt_mono (mode : Mode) (variables : Nat) (bytes : List Nat) :
    ∀ (fuel fuel' pos : Nat) (b : Buffer) (r : Buffer × Nat),
      segmentAt mode variables bytes pos b fuel = some r → fuel ≤ fuel' →
      segmentAt mode variables bytes pos b fuel' = some r := by
  intro fuel
  induction fuel with
  | zero => intro fuel' pos b r h; simp [segmentAt] at h
  | succ fuel ih =>
    intro fuel' pos b r h le
    obtain ⟨fuel'', rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    simp only [segmentAt] at h ⊢
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i notEnd notMarker
        simp only [notEnd, notMarker, if_false]
        cases stepped : tokenStep mode variables b (scan bytes pos) with
        | none => simp [stepped] at h
        | some after =>
          simp only [stepped, Option.bind] at h ⊢
          split at h
          · rename_i zero
            simpa [zero] using h
          · rename_i nonzero
            simp only [nonzero, if_false]
            exact ih fuel'' _ after r h (by omega)

theorem skipLine_mono (bytes : List Nat) :
    ∀ (fuel fuel' pos : Nat) (r : Nat),
      skipLine bytes pos fuel = some r → fuel ≤ fuel' → skipLine bytes pos fuel' = some r := by
  intro fuel
  induction fuel with
  | zero => intro fuel' pos r h; simp [skipLine] at h
  | succ fuel ih =>
    intro fuel' pos r h le
    obtain ⟨fuel'', rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    simp only [skipLine] at h ⊢
    split at h
    · rename_i word
      simp only [word, if_true]
      exact ih fuel'' _ r h (by omega)
    · rename_i notWord
      simpa [notWord] using h

theorem proofLines_mono (variables : Nat) (bytes : List Nat) :
    ∀ (fuel fuel' pos : Nat) (a r : Assembly),
      proofLines variables bytes pos a fuel = some r → fuel ≤ fuel' →
      proofLines variables bytes pos a fuel' = some r := by
  intro fuel
  induction fuel with
  | zero => intro fuel' pos a r h; simp [proofLines] at h
  | succ fuel ih =>
    intro fuel' pos a r h le
    obtain ⟨fuel'', rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    simp only [proofLines] at h ⊢
    split at h
    · rename_i eof; simpa [eof] using h
    · rename_i notEof
      simp only [notEof, if_false]
      split at h
      · rename_i newline
        simp only [newline, if_true]
        exact ih fuel'' _ a r h (by omega)
      · rename_i notNewline
        simp only [notNewline, if_false]
        split at h
        · rename_i comment
          simp only [comment, if_true]
          cases skipped : skipLine bytes (scan bytes pos).next fuel with
          | none => simp [skipped] at h
          | some next =>
            simp only [skipped] at h
            rw [skipLine_mono bytes fuel fuel'' _ next skipped (by omega)]
            exact ih fuel'' _ a r h (by omega)
        · rename_i notComment
          simp only [notComment, if_false]
          cases read : readCommand variables bytes pos a with
          | none => simp [read] at h
          | some result =>
            obtain ⟨after, next⟩ := result
            simp only [read] at h ⊢
            exact ih fuel'' _ after r h (by omega)

theorem preamble_mono (bytes : List Nat) :
    ∀ (fuel fuel' pos : Nat) (r : Nat),
      preamble bytes pos fuel = some r → fuel ≤ fuel' → preamble bytes pos fuel' = some r := by
  intro fuel
  induction fuel with
  | zero => intro fuel' pos r h; simp [preamble] at h
  | succ fuel ih =>
    intro fuel' pos r h le
    obtain ⟨fuel'', rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    simp only [preamble] at h ⊢
    split at h
    · simp at h
    · rename_i notEof
      simp only [notEof, if_false]
      split at h
      · rename_i newline
        simp only [newline, if_true]
        exact ih fuel'' _ r h (by omega)
      · rename_i notNewline
        simp only [notNewline, if_false]
        split at h
        · rename_i comment
          simp only [comment, if_true]
          cases skipped : skipLine bytes (scan bytes pos).next fuel with
          | none => simp [skipped] at h
          | some next =>
            simp only [skipped] at h
            rw [skipLine_mono bytes fuel fuel'' _ next skipped (by omega)]
            exact ih fuel'' _ r h (by omega)
        · rename_i notComment
          simpa [notComment] using h

theorem clauses_mono (variables count : Nat) (bytes : List Nat) :
    ∀ (fuel fuel' pos : Nat) (s r : State) (first : Bool),
      clauses variables count bytes pos s first fuel = some r → fuel ≤ fuel' →
      clauses variables count bytes pos s first fuel' = some r := by
  intro fuel
  induction fuel with
  | zero => intro fuel' pos s r first h; simp [clauses] at h
  | succ fuel ih =>
    intro fuel' pos s r first h le
    obtain ⟨fuel'', rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    simp only [clauses] at h ⊢
    split at h
    · rename_i eof; simpa [eof] using h
    · rename_i notEof
      simp only [notEof, if_false]
      split at h
      · rename_i newline
        simp only [newline, if_true]
        exact ih fuel'' _ s r true h (by omega)
      · rename_i notNewline
        simp only [notNewline, if_false]
        split at h
        · rename_i comment
          simp only [comment]
          cases skipped : skipLine bytes (scan bytes pos).next fuel with
          | none => simp [skipped] at h
          | some next =>
            simp only [skipped] at h
            rw [skipLine_mono bytes fuel fuel'' _ next skipped (by omega)]
            exact ih fuel'' _ s r true h (by omega)
        · rename_i notComment
          simp only [notComment, if_false]
          cases stepped : tokenStep .literal variables s.buffer (scan bytes pos) with
          | none => simp [stepped] at h
          | some after =>
            simp only [stepped] at h ⊢
            split at h
            · rename_i zero
              simp only [zero, if_true]
              split at h
              · rename_i room
                simp only [room, if_true]
                exact ih fuel'' _ _ r false h (by omega)
              · simp at h
            · rename_i nonzero
              simp only [nonzero, if_false]
              exact ih fuel'' _ _ r false h (by omega)

-- ---- The Oak proof loop

theorem proofLoop_stop (bytes : List Nat) (pos : Nat) (p : Proof) (fuel : Nat)
    (invalid : p.valid = false) : proofLoop bytes pos p (fuel + 1) = some p := by
  simp [proofLoop, invalid]

-- An accepted run started from a valid state.
theorem proofLoop_accepted_valid (bytes : List Nat) (fuel pos : Nat) (p q : Proof)
    (h : proofLoop bytes pos p fuel = some q) (hq : q.valid = true) : p.valid = true := by
  cases fuel with
  | zero => simp [proofLoop] at h
  | succ fuel =>
    by_cases valid : p.valid = true
    · exact valid
    · have invalid : p.valid = false := by simpa using valid
      rw [proofLoop_stop bytes pos p fuel invalid] at h
      cases Option.some.inj h
      rw [invalid] at hq
      cases hq

theorem proofStep_variables (bytes : List Nat) (t : Token) (p : Proof) :
    (proofStep bytes t p).1.variables = p.variables := by
  unfold proofStep
  simp only
  repeat' split
  all_goals rfl

theorem proofLoop_variables (bytes : List Nat) :
    ∀ (fuel pos : Nat) (p q : Proof), proofLoop bytes pos p fuel = some q → q.variables = p.variables := by
  intro fuel
  induction fuel with
  | zero => intro pos p q h; simp [proofLoop] at h
  | succ fuel ih =>
    intro pos p q h
    simp only [proofLoop] at h
    split at h
    · cases Option.some.inj h; rfl
    · split at h
      · cases Option.some.inj h; exact proofStep_variables bytes _ p
      · rw [ih _ _ _ h]; exact proofStep_variables bytes _ p

-- The buffer a segment leaves behind: the items appended to the pool, the
-- pending data and the items closed as one segment, nothing pending.
def afterSegment (b : Buffer) (items : List Nat) : Buffer :=
  ⟨b.capacity, b.pool ++ items, b.closed ++ [b.pending ++ items], []⟩

theorem afterSegment_cons (b : Buffer) (item : Nat) (items : List Nat) (room : b.pool.length < b.capacity) :
    push b item = some { b with pool := b.pool ++ [item], pending := b.pending ++ [item] } ∧
      afterSegment { b with pool := b.pool ++ [item], pending := b.pending ++ [item] } items =
        afterSegment b (item :: items) := by
  exact ⟨by simp [push, room], by simp [afterSegment]⟩

-- A word token's sign is nonzero exactly when it is 1 or 2.
theorem sign_nonzero (bytes : List Nat) (pos : Nat) :
    (scan bytes pos).sign ≠ 0 ↔ (scan bytes pos).sign = 1 ∨ (scan bytes pos).sign = 2 := by
  rcases sign_cases bytes pos with h | h | h <;> simp [h]

-- Oak's stage 2 consumes one literal segment: the items it pushes are the
-- items the model's literal `segmentAt` pushes, and the loop resumes at
-- stage 3 right after the terminator with the same pool and command.
theorem literal_segment (bytes : List Nat) :
    ∀ (fuel pos : Nat) (p q : Proof) (b : Buffer),
      p.valid = true → p.first = false → p.comment = false → p.stage = 2 →
      b.pool = p.pool → b.capacity = 4096 →
      proofLoop bytes pos p fuel = some q → q.valid = true →
      ∃ (items : List Nat) (next fuel' : Nat) (p' : Proof), fuel' ≤ fuel ∧
        segmentAt .literal p.variables bytes pos b fuel = some (afterSegment b items, next) ∧
        proofLoop bytes next p' fuel' = some q ∧
        p'.valid = true ∧ p'.first = false ∧ p'.comment = false ∧ p'.stage = 3 ∧
        p'.variables = p.variables ∧ p'.pool = p.pool ++ items ∧ p'.refs = p.refs ∧
        p'.commands = p.commands ∧
        p'.command = { p.command with count := p.command.count + items.length } := by
  intro fuel
  induction fuel with
  | zero => intro pos p q b _ _ _ _ _ _ h; simp [proofLoop] at h
  | succ fuel ih =>
    intro pos p q b valid first comment stage pool cap h hq
    rw [proofLoop, if_neg (by simp [valid])] at h
    by_cases kind : (scan bytes pos).kind = 2
    · -- A word token in stage 2: a literal or the terminator.
      have step : proofStep bytes (scan bytes pos) p =
          if (scan bytes pos).magnitude = 0 then
            ({ p with valid := decide ((scan bytes pos).sign ≠ 0), stage := 3, first := false, comment := false }, false)
          else if decide ((scan bytes pos).sign ≠ 0) && decide ((scan bytes pos).magnitude ≤ p.variables ∧ p.pool.length < 4096) then
            ({ p with
                valid := true
                stage := 2
                pool := p.pool ++ [encoded (scan bytes pos).magnitude (scan bytes pos).sign]
                command := { p.command with count := p.command.count + 1 }
                first := false
                comment := false }, false)
          else ({ p with valid := false, stage := 2, first := false, comment := false }, false) := by
        unfold proofStep
        simp [kind, first, comment, stage]
      rw [step] at h
      by_cases zero : (scan bytes pos).magnitude = 0
      · -- The terminator: the segment closes, the loop continues in stage 3.
        rw [if_pos zero] at h
        simp only [Bool.false_eq_true, if_false] at h
        have sign : (scan bytes pos).sign ≠ 0 := by
          intro none
          have := proofLoop_accepted_valid bytes fuel _ _ q h hq
          simp [none] at this
        refine ⟨[], (scan bytes pos).next, fuel, _, Nat.le_succ fuel, ?_, h, by simp [sign], rfl, rfl, rfl, rfl, by simp, rfl, rfl, by simp⟩
        rw [segmentAt]
        have signs := (sign_nonzero bytes pos).1 sign
        simp [kind, tokenStep, zero, signs, closeSegment, afterSegment]
      · -- A literal: pushed on both sides, then the rest of the segment.
        rw [if_neg zero] at h
        by_cases ok : (decide ((scan bytes pos).sign ≠ 0) && decide ((scan bytes pos).magnitude ≤ p.variables ∧ p.pool.length < 4096)) = true
        · rw [if_pos ok] at h
          simp only [Bool.false_eq_true, if_false] at h
          have sign : (scan bytes pos).sign ≠ 0 := by simpa using (Bool.and_eq_true_iff.1 ok).1
          have bounds : (scan bytes pos).magnitude ≤ p.variables ∧ p.pool.length < 4096 := by
            simpa using (Bool.and_eq_true_iff.1 ok).2
          have room : b.pool.length < b.capacity := by
            rw [pool, cap]; exact bounds.2
          obtain ⟨pushed, _⟩ := afterSegment_cons b (encoded (scan bytes pos).magnitude (scan bytes pos).sign) [] room
          obtain ⟨items, next, fuel', p', le, decoded, rest, v', f', c', s', vars, pool', refs', cmds', cmd'⟩ :=
            ih (scan bytes pos).next _ q { b with pool := b.pool ++ [encoded (scan bytes pos).magnitude (scan bytes pos).sign], pending := b.pending ++ [encoded (scan bytes pos).magnitude (scan bytes pos).sign] }
              rfl rfl rfl rfl (by simp [pool]) cap h hq
          refine ⟨encoded (scan bytes pos).magnitude (scan bytes pos).sign :: items, next, fuel', p', Nat.le_succ_of_le le, ?_, rest, v', f', c', s', vars, ?_, refs', cmds', ?_⟩
          · rw [segmentAt]
            have signs := (sign_nonzero bytes pos).1 sign
            have stepped : tokenStep .literal p.variables b (scan bytes pos) =
                some { b with pool := b.pool ++ [encoded (scan bytes pos).magnitude (scan bytes pos).sign], pending := b.pending ++ [encoded (scan bytes pos).magnitude (scan bytes pos).sign] } := by
              simp only [tokenStep, kind, signs, zero, bounds.1]
              simpa [encoded] using pushed
            simp only [kind, ne_eq, not_true_eq_false, if_false, stepped, Option.bind, zero]
            obtain ⟨_, same⟩ := afterSegment_cons b (encoded (scan bytes pos).magnitude (scan bytes pos).sign) items room
            rw [← same]
            simpa [Mode.literal] using decoded
          · simp [pool', List.append_assoc]
          · rw [cmd']
            simp only [List.length_cons]
            congr 1
            omega
        · rw [if_neg ok] at h
          simp only [Bool.false_eq_true, if_false] at h
          have := proofLoop_accepted_valid bytes fuel _ _ q h hq
          simp at this
    · -- A newline or the end of input inside a segment rejects.
      have step : (proofStep bytes (scan bytes pos) p).1.valid = false := by
        unfold proofStep
        simp [kind, stage]
      exfalso
      split at h
      · cases Option.some.inj h; rw [step] at hq; cases hq
      · have := proofLoop_accepted_valid bytes fuel _ _ q h hq
        rw [step] at this; cases this

-- Oak's stages 3 (hints) and 4 (deletion ids) consume one reference segment
-- in the model's hint or deletion mode: nonzero words must be positive and
-- go to the reference pool, the terminator of a deletion must be spelled `0`,
-- and the loop resumes at stage 5 right after the terminator.
theorem reference_segment (bytes : List Nat) (mode : Mode) (s : Nat)
    (shape : (s = 3 ∧ mode = .hint) ∨ (s = 4 ∧ mode = .deletion)) :
    ∀ (fuel pos : Nat) (p q : Proof) (b : Buffer),
      p.valid = true → p.first = false → p.comment = false → p.stage = s →
      b.pool = p.refs → b.capacity = 4096 →
      proofLoop bytes pos p fuel = some q → q.valid = true →
      ∃ (items : List Nat) (next fuel' : Nat) (p' : Proof), fuel' ≤ fuel ∧
        segmentAt mode p.variables bytes pos b fuel = some (afterSegment b items, next) ∧
        proofLoop bytes next p' fuel' = some q ∧
        p'.valid = true ∧ p'.first = false ∧ p'.comment = false ∧ p'.stage = 5 ∧
        p'.variables = p.variables ∧ p'.pool = p.pool ∧ p'.refs = p.refs ++ items ∧
        p'.commands = p.commands ∧
        p'.command = { p.command with refsCount := p.command.refsCount + items.length } := by
  have s0 : s ≠ 0 := by rcases shape with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have s1 : s ≠ 1 := by rcases shape with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have s2 : s ≠ 2 := by rcases shape with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have s5 : s ≠ 5 := by rcases shape with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have notLiteral : mode ≠ .literal := by rcases shape with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  intro fuel
  induction fuel with
  | zero => intro pos p q b _ _ _ _ _ _ h; simp [proofLoop] at h
  | succ fuel ih =>
    intro pos p q b valid first comment stage pool cap h hq
    rw [proofLoop, if_neg (by simp [valid])] at h
    by_cases kind : (scan bytes pos).kind = 2
    · have step : proofStep bytes (scan bytes pos) p =
          if (scan bytes pos).magnitude = 0 then
            ({ p with
                valid := decide ((scan bytes pos).sign ≠ 0 ∧ s ≠ 5) && (if s = 4 then decide (Word bytes (scan bytes pos) 48) else true)
                stage := 5
                first := false
                comment := false }, false)
          else if decide ((scan bytes pos).sign ≠ 0 ∧ s ≠ 5) && decide ((scan bytes pos).sign = 1 ∧ p.refs.length < 4096) then
            ({ p with
                valid := true
                stage := s
                refs := p.refs ++ [(scan bytes pos).magnitude]
                command := { p.command with refsCount := p.command.refsCount + 1 }
                first := false
                comment := false }, false)
          else ({ p with valid := false, stage := s, first := false, comment := false }, false) := by
        unfold proofStep
        simp [kind, first, comment, stage, s0, s1, s2]
      rw [step] at h
      by_cases zero : (scan bytes pos).magnitude = 0
      · rw [if_pos zero] at h
        simp only [Bool.false_eq_true, if_false] at h
        have accepted := proofLoop_accepted_valid bytes fuel _ _ q h hq
        simp only [Bool.and_eq_true_iff] at accepted
        have sign : (scan bytes pos).sign ≠ 0 := (decide_eq_true_iff.1 accepted.1).1
        have marker : ¬ (mode = .deletion ∧ (scan bytes pos).magnitude = 0 ∧ ¬ Word bytes (scan bytes pos) 48) := by
          rcases shape with ⟨hs, hm⟩ | ⟨hs, hm⟩
          · simp [hm]
          · have word : Word bytes (scan bytes pos) 48 := by
              have := accepted.2
              simp [hs] at this
              exact this
            simp [word]
        refine ⟨[], (scan bytes pos).next, fuel, _, Nat.le_succ fuel, ?_, h, ?_, rfl, rfl, rfl, rfl, rfl, by simp, rfl, by simp⟩
        · rw [segmentAt]
          have signs := (sign_nonzero bytes pos).1 sign
          have closed : tokenStep mode p.variables b (scan bytes pos) = some (closeSegment b) := by
            simp [tokenStep, kind, signs, zero]
          rw [if_neg (by simp [kind]), if_neg marker, closed]
          simp [Option.bind, zero, closeSegment, afterSegment]
        · simp only [Bool.and_eq_true_iff]
          exact accepted
      · rw [if_neg zero] at h
        by_cases ok : (decide ((scan bytes pos).sign ≠ 0 ∧ s ≠ 5) && decide ((scan bytes pos).sign = 1 ∧ p.refs.length < 4096)) = true
        · rw [if_pos ok] at h
          simp only [Bool.false_eq_true, if_false] at h
          have positive : (scan bytes pos).sign = 1 ∧ p.refs.length < 4096 := decide_eq_true_iff.1 (Bool.and_eq_true_iff.1 ok).2
          have room : b.pool.length < b.capacity := by
            rw [pool, cap]; exact positive.2
          obtain ⟨pushed, _⟩ := afterSegment_cons b (scan bytes pos).magnitude [] room
          obtain ⟨items, next, fuel', p', le, decoded, rest, v', f', c', s', vars, pool', refs', cmds', cmd'⟩ :=
            ih (scan bytes pos).next _ q { b with pool := b.pool ++ [(scan bytes pos).magnitude], pending := b.pending ++ [(scan bytes pos).magnitude] }
              rfl rfl rfl rfl (by simp [pool]) cap h hq
          refine ⟨(scan bytes pos).magnitude :: items, next, fuel', p', Nat.le_succ_of_le le, ?_, rest, v', f', c', s', vars, pool', ?_, cmds', ?_⟩
          · rw [segmentAt]
            have stepped : tokenStep mode p.variables b (scan bytes pos) =
                some { b with pool := b.pool ++ [(scan bytes pos).magnitude], pending := b.pending ++ [(scan bytes pos).magnitude] } := by
              simp only [tokenStep, kind, positive.1, zero, notLiteral]
              simpa using pushed
            simp only [kind, ne_eq, not_true_eq_false, if_false, zero, and_false, false_and, stepped, Option.bind]
            obtain ⟨_, same⟩ := afterSegment_cons b (scan bytes pos).magnitude items room
            rw [← same]
            exact decoded
          · simp [refs', List.append_assoc]
          · rw [cmd']
            simp only [List.length_cons]
            congr 1
            omega
        · rw [if_neg ok] at h
          simp only [Bool.false_eq_true, if_false] at h
          have := proofLoop_accepted_valid bytes fuel _ _ q h hq
          simp at this
    · have step : (proofStep bytes (scan bytes pos) p).1.valid = false := by
        unfold proofStep
        simp [kind, stage, s0, s5]
      exfalso
      split at h
      · cases Option.some.inj h; rw [step] at hq; cases hq
      · have := proofLoop_accepted_valid bytes fuel _ _ q h hq
        rw [step] at this; cases this

-- Past the end of input the scanner stays at the end.
theorem scan_eof_next (bytes : List Nat) (pos : Nat) (eof : (scan bytes pos).kind = 0) :
    (scan bytes (scan bytes pos).next).kind = 0 := by
  unfold scan scanTail at eof ⊢
  generalize hc : countWhile space (bytes.drop pos) = c at eof ⊢
  cases tail : (bytes.drop pos).drop c with
  | nil =>
    simp only [tokenAt]
    have : bytes.drop (pos + c) = [] := by rw [← List.drop_drop]; simpa using tail
    simp [this]
  | cons b bs =>
    simp only [tail, tokenAt] at eof
    split at eof <;> simp at eof

-- A line start: stage 0, the first-word flag set, no comment pending, valid.
def LineStart (p : Proof) : Prop :=
  p.valid = true ∧ p.stage = 0 ∧ p.first = true ∧ p.comment = false

-- The fields a line preserves: variables, pools, and stored commands.
def SameData (p p' : Proof) : Prop :=
  p'.variables = p.variables ∧ p'.pool = p.pool ∧ p'.refs = p.refs ∧ p'.commands = p.commands

-- A comment line: Oak ignores words until the line ends, as `skipLine` does,
-- and resumes at a line start with nothing changed.
theorem comment_line (bytes : List Nat) :
    ∀ (fuel pos : Nat) (p q : Proof),
      p.valid = true → p.stage = 0 → p.comment = true →
      proofLoop bytes pos p fuel = some q → q.valid = true →
      ∃ (next : Nat) (p' : Proof), skipLine bytes pos fuel = some next ∧ LineStart p' ∧ SameData p p' ∧
        ((∃ fuel', fuel' < fuel ∧ proofLoop bytes next p' fuel' = some q) ∨
          (0 < fuel ∧ (scan bytes next).kind = 0 ∧ q = p')) := by
  intro fuel
  induction fuel with
  | zero => intro pos p q _ _ _ h; simp [proofLoop] at h
  | succ fuel ih =>
    intro pos p q valid stage comment h hq
    rw [proofLoop, if_neg (by simp [valid])] at h
    by_cases kind : (scan bytes pos).kind = 2
    · have step : proofStep bytes (scan bytes pos) p = ({ p with first := false, comment := true }, false) := by
        unfold proofStep
        simp [kind, comment]
      rw [step] at h
      simp only [Bool.false_eq_true, if_false] at h
      obtain ⟨next, p', skipped, start, same, rest⟩ :=
        ih (scan bytes pos).next { p with first := false, comment := true } q valid stage rfl h hq
      refine ⟨next, p', ?_, start, same, ?_⟩
      · rw [skipLine, if_pos kind]; exact skipped
      · rcases rest with ⟨fuel', lt, run⟩ | ⟨_, eof, same⟩
        · exact Or.inl ⟨fuel', Nat.lt_succ_of_lt lt, run⟩
        · exact Or.inr ⟨Nat.succ_pos fuel, eof, same⟩
    · have step : proofStep bytes (scan bytes pos) p =
          ({ p with valid := true, stage := 0, first := true, comment := false }, decide ((scan bytes pos).kind = 0)) := by
        unfold proofStep
        simp [kind, stage]
      rw [step] at h
      refine ⟨(scan bytes pos).next, { p with valid := true, stage := 0, first := true, comment := false },
        ?_, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
      · rw [skipLine, if_neg kind]
      · by_cases eof : (scan bytes pos).kind = 0
        · simp only [eof, decide_true, if_true] at h
          exact Or.inr ⟨Nat.succ_pos fuel, scan_eof_next bytes pos eof, (Option.some.inj h).symm⟩
        · simp only [eof, decide_false, Bool.false_eq_true, if_false] at h
          exact Or.inl ⟨fuel, Nat.lt_succ_self fuel, h⟩

-- The end of a command line: after the final terminator (stage 5) only a
-- newline or the end of input is accepted, and the command is stored when
-- fewer than 256 are held.
theorem line_end (bytes : List Nat) (fuel pos : Nat) (p q : Proof)
    (valid : p.valid = true) (first : p.first = false) (comment : p.comment = false) (stage : p.stage = 5)
    (h : proofLoop bytes pos p fuel = some q) (hq : q.valid = true) :
    (scan bytes pos).kind ≠ 2 ∧ p.commands.length < 256 ∧
      ∃ p' : Proof, LineStart p' ∧ p'.variables = p.variables ∧ p'.pool = p.pool ∧ p'.refs = p.refs ∧
        p'.commands = p.commands ++ [p.command] ∧
        ((∃ fuel', fuel' < fuel ∧ proofLoop bytes (scan bytes pos).next p' fuel' = some q) ∨
          (0 < fuel ∧ (scan bytes pos).kind = 0 ∧ q = p')) := by
  cases fuel with
  | zero => simp [proofLoop] at h
  | succ fuel =>
    rw [proofLoop, if_neg (by simp [valid])] at h
    by_cases kind : (scan bytes pos).kind = 2
    · exfalso
      have step : (proofStep bytes (scan bytes pos) p).1.valid = false := by
        unfold proofStep
        simp [kind, first, comment, stage]
      split at h
      · cases Option.some.inj h; rw [step] at hq; cases hq
      · have := proofLoop_accepted_valid bytes fuel _ _ q h hq
        rw [step] at this; cases this
    · by_cases room : p.commands.length < 256
      · have step : proofStep bytes (scan bytes pos) p =
            ({ p with valid := true, commands := p.commands ++ [p.command], stage := 0, first := true, comment := false },
              decide ((scan bytes pos).kind = 0)) := by
          unfold proofStep
          simp [kind, stage, room]
        rw [step] at h
        refine ⟨kind, room, { p with valid := true, commands := p.commands ++ [p.command], stage := 0, first := true, comment := false },
          ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, ?_⟩
        by_cases eof : (scan bytes pos).kind = 0
        · simp only [eof, decide_true, if_true] at h
          exact Or.inr ⟨Nat.succ_pos fuel, eof, (Option.some.inj h).symm⟩
        · simp only [eof, decide_false, Bool.false_eq_true, if_false] at h
          exact Or.inl ⟨fuel, Nat.lt_succ_self fuel, h⟩
      · exfalso
        have step : (proofStep bytes (scan bytes pos) p).1.valid = false := by
          unfold proofStep
          simp [kind, stage, room]
        split at h
        · cases Option.some.inj h; rw [step] at hq; cases hq
        · have := proofLoop_accepted_valid bytes fuel _ _ q h hq
          rw [step] at this; cases this

-- In stage 1 a word other than `d` is the first literal: Oak moves to stage 2
-- and treats the same token there.
theorem stage1_as_stage2 (bytes : List Nat) (t : Token) (p : Proof)
    (kind : t.kind = 2) (notMarker : ¬ Word bytes t 100)
    (first : p.first = false) (comment : p.comment = false) (stage : p.stage = 1) :
    proofStep bytes t p = proofStep bytes t { p with stage := 2 } := by
  unfold proofStep
  simp [kind, notMarker, first, comment, stage]

theorem proofLoop_stage1 (bytes : List Nat) (fuel pos : Nat) (p : Proof)
    (kind : (scan bytes pos).kind = 2) (notMarker : ¬ Word bytes (scan bytes pos) 100)
    (valid : p.valid = true) (first : p.first = false) (comment : p.comment = false) (stage : p.stage = 1) :
    proofLoop bytes pos p fuel = proofLoop bytes pos { p with stage := 2 } fuel := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    simp only [proofLoop]
    rw [stage1_as_stage2 bytes (scan bytes pos) p kind notMarker first comment stage]
    simp [valid]

-- The Oak state and a command assembly describe the same data.
def Rel (p : Proof) (a : Assembly) : Prop :=
  a.literals.buffer.pool = p.pool ∧ a.literals.buffer.pending = [] ∧ a.literals.buffer.capacity = 4096 ∧
  a.references.buffer.pool = p.refs ∧ a.references.buffer.pending = [] ∧ a.references.buffer.capacity = 4096 ∧
  a.commands = p.commands

-- A publication over a related buffer, from a segment run the Oak loop
-- established with its own fuel.
theorem publishAt_of_segment (mode : Mode) (variables : Nat) (bytes : List Nat) (s : State)
    (pos next fuel : Nat) (items : List Nat) (bound : fuel ≤ bytes.length + 1)
    (decoded : segmentAt mode variables bytes pos s.buffer fuel = some (afterSegment s.buffer items, next)) :
    publishAt mode variables s bytes pos =
      some (⟨afterSegment s.buffer items, s.ranges ++ [(s.buffer.pool.length, items.length)]⟩, next) := by
  unfold publishAt
  rw [segmentAt_mono mode variables bytes fuel (bytes.length + 1) pos s.buffer _ decoded bound]
  simp [afterSegment]

-- One command line: Oak's identifier, optional marker, segments, and line
-- end are the model's `readCommand`, and the two sides store the same
-- command over the same pools.
theorem command_line (bytes : List Nat) (fuel pos : Nat) (p q : Proof) (a : Assembly)
    (bound : fuel ≤ bytes.length + 1) (start : LineStart p) (rel : Rel p a)
    (kind : (scan bytes pos).kind = 2) (notComment : ¬ Word bytes (scan bytes pos) 99)
    (h : proofLoop bytes pos p fuel = some q) (hq : q.valid = true) :
    ∃ (a' : Assembly) (after : Nat) (p' : Proof),
      readCommand p.variables bytes pos a = some (a', after) ∧ LineStart p' ∧
      p'.variables = p.variables ∧ Rel p' a' ∧
      ((∃ fuel', fuel' < fuel ∧ proofLoop bytes after p' fuel' = some q) ∨
        (1 < fuel ∧ (scan bytes after).kind = 0 ∧ q = p')) := by
  obtain ⟨valid, stage, first, comment⟩ := start
  obtain ⟨litPool, litPending, litCap, refPool, refPending, refCap, cmds⟩ := rel
  cases fuel with
  | zero => simp [proofLoop] at h
  | succ fuel =>
  rw [proofLoop, if_neg (by simp [valid])] at h
  -- The identifier.
  have step : proofStep bytes (scan bytes pos) p =
      ({ p with
          valid := decide ((scan bytes pos).sign ≠ 0 ∧ ((scan bytes pos).sign = 1 ∨ (scan bytes pos).magnitude = 0))
          stage := 1
          command := ⟨true, (scan bytes pos).magnitude, p.pool.length, 0, p.refs.length, 0⟩
          first := false
          comment := false }, false) := by
    unfold proofStep
    simp [kind, stage, first, comment, notComment]
  rw [step] at h
  simp only [Bool.false_eq_true, if_false] at h
  have ident : (scan bytes pos).sign ≠ 0 ∧ ((scan bytes pos).sign = 1 ∨ (scan bytes pos).magnitude = 0) := by
    have := proofLoop_accepted_valid bytes fuel _ _ q h hq
    simpa using this
  have identifier : identifierToken (scan bytes pos) = some (scan bytes pos).magnitude := by
    simp [identifierToken, kind, ident]
  -- The marker position.
  have fuelBound : fuel ≤ bytes.length + 1 := Nat.le_of_succ_le bound
  by_cases markerKind : (scan bytes (scan bytes pos).next).kind = 2
  · by_cases marker : Word bytes (scan bytes (scan bytes pos).next) 100
    · -- A deletion line.
      cases fuel with
      | zero => simp [proofLoop] at h
      | succ fuel =>
      rw [proofLoop, if_neg (by simp [decide_eq_true ident])] at h
      have step2 : proofStep bytes (scan bytes (scan bytes pos).next)
          { p with
            valid := decide ((scan bytes pos).sign ≠ 0 ∧ ((scan bytes pos).sign = 1 ∨ (scan bytes pos).magnitude = 0))
            stage := 1
            command := ⟨true, (scan bytes pos).magnitude, p.pool.length, 0, p.refs.length, 0⟩
            first := false
            comment := false } =
          ({ p with
              valid := decide ((scan bytes pos).sign ≠ 0 ∧ ((scan bytes pos).sign = 1 ∨ (scan bytes pos).magnitude = 0))
              stage := 4
              command := ⟨false, (scan bytes pos).magnitude, p.pool.length, 0, p.refs.length, 0⟩
              first := false
              comment := false }, false) := by
        unfold proofStep
        simp [markerKind, marker]
      rw [step2] at h
      simp only [Bool.false_eq_true, if_false] at h
      obtain ⟨items, next, fuel', p3, le, decoded, rest, v3, f3, c3, s3, vars3, pool3, refs3, cmds3, cmd3⟩ :=
        reference_segment bytes .deletion 4 (Or.inr ⟨rfl, rfl⟩) fuel _ _ q a.references.buffer
          (decide_eq_true ident) rfl rfl rfl (by simpa using refPool) refCap h hq
      have published := publishAt_of_segment .deletion p.variables bytes a.references _ next fuel items
        (by omega) (by simpa using decoded)
      obtain ⟨endKind, room, p4, start4, vars4, pool4, refs4, cmds4, rest4⟩ :=
        line_end bytes fuel' next p3 q v3 f3 c3 s3 rest hq
      have lineEndAt : lineEnd bytes next = some (scan bytes next).next := by
        simp [lineEnd, endKind]
      have stored : store a a.literals ⟨afterSegment a.references.buffer items,
          a.references.ranges ++ [(a.references.buffer.pool.length, items.length)]⟩
          (command false (scan bytes pos).magnitude a a.literals
            ⟨afterSegment a.references.buffer items, a.references.ranges ++ [(a.references.buffer.pool.length, items.length)]⟩) =
          some ⟨a.literals, ⟨afterSegment a.references.buffer items, a.references.ranges ++ [(a.references.buffer.pool.length, items.length)]⟩,
            a.initial, a.commands ++ [command false (scan bytes pos).magnitude a a.literals
              ⟨afterSegment a.references.buffer items, a.references.ranges ++ [(a.references.buffer.pool.length, items.length)]⟩]⟩ := by
        have : a.commands.length < 256 := by rw [cmds, ← cmds3]; simpa using room
        simp [store, this]
      refine ⟨⟨a.literals, ⟨afterSegment a.references.buffer items, a.references.ranges ++ [(a.references.buffer.pool.length, items.length)]⟩,
          a.initial, a.commands ++ [command false (scan bytes pos).magnitude a a.literals
            ⟨afterSegment a.references.buffer items, a.references.ranges ++ [(a.references.buffer.pool.length, items.length)]⟩]⟩,
        (scan bytes next).next, p4, ?_, start4, by rw [vars4, vars3], ?_, ?_⟩
      · rw [readCommand]
        simp only [identifier, markerKind, marker, and_self, if_true, published, lineEndAt, stored, Option.map]
      · refine ⟨by simpa [pool4, pool3] using litPool, litPending, litCap, ?_, rfl, by simpa [afterSegment] using refCap, ?_⟩
        · simp [afterSegment, refPool, refs4, refs3]
        · rw [cmds4, cmds3, cmd3, cmds]
          simp [command, afterSegment, refPool, litPool]
      · rcases rest4 with ⟨fuel'', lt, run⟩ | ⟨_, eof, same⟩
        · exact Or.inl ⟨fuel'', by omega, run⟩
        · exact Or.inr ⟨by omega, scan_eof_next bytes next eof, same⟩
    · -- An addition line: literals, then hints.
      rw [proofLoop_stage1 bytes fuel _ _ markerKind marker (decide_eq_true ident) rfl rfl rfl] at h
      obtain ⟨items, next1, fuel1, p3, le1, decoded1, rest1, v3, f3, c3, s3, vars3, pool3, refs3, cmds3, cmd3⟩ :=
        literal_segment bytes fuel _ _ q a.literals.buffer (decide_eq_true ident) rfl rfl rfl (by simpa using litPool) litCap h hq
      have published1 := publishAt_of_segment .literal p.variables bytes a.literals _ next1 fuel items
        fuelBound (by simpa using decoded1)
      obtain ⟨hints, next2, fuel2, p4, le2, decoded2, rest2, v4, f4, c4, s4, vars4, pool4, refs4, cmds4, cmd4⟩ :=
        reference_segment bytes .hint 3 (Or.inl ⟨rfl, rfl⟩) fuel1 next1 p3 q a.references.buffer v3 f3 c3 s3
          (by rw [refs3]; simpa using refPool) refCap rest1 hq
      have published2 := publishAt_of_segment .hint p.variables bytes a.references next1 next2 fuel1 hints
        (by omega) (by rw [← vars3]; exact decoded2)
      obtain ⟨endKind, room, p5, start5, vars5, pool5, refs5, cmds5, rest5⟩ :=
        line_end bytes fuel2 next2 p4 q v4 f4 c4 s4 rest2 hq
      have lineEndAt : lineEnd bytes next2 = some (scan bytes next2).next := by
        simp [lineEnd, endKind]
      have roomA : a.commands.length < 256 := by rw [cmds, ← cmds3, ← cmds4]; simpa using room
      refine ⟨⟨⟨afterSegment a.literals.buffer items, a.literals.ranges ++ [(a.literals.buffer.pool.length, items.length)]⟩,
          ⟨afterSegment a.references.buffer hints, a.references.ranges ++ [(a.references.buffer.pool.length, hints.length)]⟩,
          a.initial, a.commands ++ [command true (scan bytes pos).magnitude a
            ⟨afterSegment a.literals.buffer items, a.literals.ranges ++ [(a.literals.buffer.pool.length, items.length)]⟩
            ⟨afterSegment a.references.buffer hints, a.references.ranges ++ [(a.references.buffer.pool.length, hints.length)]⟩]⟩,
        (scan bytes next2).next, p5, ?_, start5, by rw [vars5, vars4, vars3], ?_, ?_⟩
      · rw [readCommand]
        simp only [identifier, markerKind, marker, and_false, if_false, published1, published2, lineEndAt, store, roomA, if_true, Option.map]
      · refine ⟨?_, rfl, by simpa [afterSegment] using litCap, ?_, rfl, by simpa [afterSegment] using refCap, ?_⟩
        · simp [afterSegment, litPool, pool5, pool4, pool3]
        · simp [afterSegment, refPool, refs5, refs4, refs3]
        · rw [cmds5, cmds4, cmds3, cmd4, cmd3, cmds]
          simp [command, afterSegment, refPool, litPool]
      · rcases rest5 with ⟨fuel'', lt, run⟩ | ⟨pos2, eof, same⟩
        · exact Or.inl ⟨fuel'', by omega, run⟩
        · exact Or.inr ⟨by omega, scan_eof_next bytes next2 eof, same⟩
  · -- A newline or the end of input right after the identifier rejects.
    exfalso
    cases fuel with
    | zero => simp [proofLoop] at h
    | succ fuel =>
    rw [proofLoop, if_neg (by simp [decide_eq_true ident])] at h
    have step2 : (proofStep bytes (scan bytes (scan bytes pos).next)
        { p with
          valid := decide ((scan bytes pos).sign ≠ 0 ∧ ((scan bytes pos).sign = 1 ∨ (scan bytes pos).magnitude = 0))
          stage := 1
          command := ⟨true, (scan bytes pos).magnitude, p.pool.length, 0, p.refs.length, 0⟩
          first := false
          comment := false }).1.valid = false := by
      unfold proofStep
      simp [markerKind]
    split at h
    · cases Option.some.inj h; rw [step2] at hq; cases hq
    · have := proofLoop_accepted_valid bytes fuel _ _ q h hq
      rw [step2] at this; cases this

-- Related data survives a line that changes only the control fields.
theorem rel_same (p p' : Proof) (a : Assembly) (rel : Rel p a) (same : SameData p p') : Rel p' a := by
  obtain ⟨_, pool, refs, cmds⟩ := same
  obtain ⟨litPool, litPending, litCap, refPool, refPending, refCap, commands⟩ := rel
  exact ⟨by rw [litPool, pool], litPending, litCap, by rw [refPool, refs], refPending, refCap, by rw [commands, cmds]⟩

-- The LRAT phase: from a line start, every accepted Oak run is a `proofLines`
-- run of the model over a related assembly, and the results are related.
theorem proof_refines (bytes : List Nat) :
    ∀ (fuel : Nat), fuel ≤ bytes.length + 1 → ∀ (pos : Nat) (p q : Proof) (a : Assembly),
      LineStart p → Rel p a → proofLoop bytes pos p fuel = some q → q.valid = true →
      ∃ a' : Assembly, proofLines p.variables bytes pos a fuel = some a' ∧ Rel q a' := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
  intro bound pos p q a start rel h hq
  cases fuel with
  | zero => simp [proofLoop] at h
  | succ fuel =>
  have ⟨valid, stage, first, comment⟩ := start
  by_cases kind : (scan bytes pos).kind = 2
  · by_cases isComment : Word bytes (scan bytes pos) 99
    · -- A comment line.
      rw [proofLoop, if_neg (by simp [valid])] at h
      have step : proofStep bytes (scan bytes pos) p = ({ p with first := false, comment := true }, false) := by
        unfold proofStep
        simp [kind, first, comment, isComment]
      rw [step] at h
      simp only [Bool.false_eq_true, if_false] at h
      obtain ⟨next, p', skipped, start', same, rest⟩ :=
        comment_line bytes fuel (scan bytes pos).next { p with first := false, comment := true } q valid stage rfl h hq
      rw [proofLines, if_neg (by simp [kind]), if_neg (by simp [kind]), if_pos isComment, skipped]
      have rel' : Rel p' a := rel_same _ p' a rel same
      rcases rest with ⟨fuel', lt, run⟩ | ⟨positive, eof, same'⟩
      · obtain ⟨a', model, rel''⟩ := ih fuel' (by omega) (by omega) next p' q a start' rel' run hq
        refine ⟨a', ?_, rel''⟩
        rw [← same.1]
        exact proofLines_mono p'.variables bytes fuel' fuel next a a' model (by omega)
      · obtain ⟨fuel, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
        refine ⟨a, ?_, same' ▸ rel'⟩
        simp [proofLines, eof]
    · -- A command line.
      obtain ⟨a', after, p', read, start', vars, rel', rest⟩ :=
        command_line bytes (fuel + 1) pos p q a bound start rel kind isComment h hq
      rw [proofLines, if_neg (by simp [kind]), if_neg (by simp [kind]), if_neg isComment, read]
      rcases rest with ⟨fuel', lt, run⟩ | ⟨two, eof, same'⟩
      · obtain ⟨a'', model, rel''⟩ := ih fuel' (by omega) (by omega) after p' q a' start' rel' run hq
        refine ⟨a'', ?_, rel''⟩
        rw [← vars]
        exact proofLines_mono p'.variables bytes fuel' fuel after a' a'' model (by omega)
      · obtain ⟨fuel, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
        refine ⟨a', ?_, same' ▸ rel'⟩
        simp [proofLines, eof]
  · -- A blank line or the end of input.
    rw [proofLoop, if_neg (by simp [valid])] at h
    have step : proofStep bytes (scan bytes pos) p =
        ({ p with valid := true, stage := 0, first := true, comment := false }, decide ((scan bytes pos).kind = 0)) := by
      unfold proofStep
      simp [kind, stage]
    rw [step] at h
    by_cases eof : (scan bytes pos).kind = 0
    · simp only [eof, decide_true, if_true] at h
      refine ⟨a, ?_, ?_⟩
      · rw [proofLines, if_pos eof]
      · rw [← Option.some.inj h]; exact rel
    · simp only [eof, decide_false, Bool.false_eq_true, if_false] at h
      have newline : (scan bytes pos).kind = 1 := by
        rcases kind_cases bytes pos with h0 | h1 | h2
        · exact absurd h0 eof
        · exact h1
        · exact absurd h2 kind
      obtain ⟨a', model, rel'⟩ := ih fuel (Nat.lt_succ_self fuel) (by omega) (scan bytes pos).next
        { p with valid := true, stage := 0, first := true, comment := false } q a ⟨rfl, rfl, rfl, rfl⟩ rel h hq
      refine ⟨a', ?_, rel'⟩
      rw [proofLines, if_neg eof, if_pos newline]
      exact model

-- ---- The Oak DIMACS loop

theorem cnfLoop_stop (bytes : List Nat) (pos : Nat) (c : Cnf) (fuel : Nat)
    (invalid : c.valid = false) : cnfLoop bytes pos c (fuel + 1) = some c := by
  simp [cnfLoop, invalid]

theorem cnfLoop_accepted_valid (bytes : List Nat) (fuel pos : Nat) (c q : Cnf)
    (h : cnfLoop bytes pos c fuel = some q) (hq : q.valid = true) : c.valid = true := by
  cases fuel with
  | zero => simp [cnfLoop] at h
  | succ fuel =>
    by_cases valid : c.valid = true
    · exact valid
    · have invalid : c.valid = false := by simpa using valid
      rw [cnfLoop_stop bytes pos c fuel invalid] at h
      cases Option.some.inj h
      rw [invalid] at hq
      cases hq

-- The Oak DIMACS state and the model's publication state describe the same
-- clauses: the pool, the pending suffix (from Oak's `pending` index), the
-- closed count, and the published ranges as Oak's start/size arrays.
def CnfRel (c : Cnf) (s : State) : Prop :=
  s.buffer.pool = c.pool ∧ s.buffer.capacity = 4096 ∧
  s.buffer.pending = c.pool.drop c.pending ∧ c.pending ≤ c.pool.length ∧
  s.buffer.closed.length = c.clauses ∧
  s.ranges.map Prod.fst = c.initial ∧ s.ranges.map Prod.snd = c.sizes

-- The fields a DIMACS line preserves.
def SameCnf (c c' : Cnf) : Prop :=
  c'.variables = c.variables ∧ c'.expected = c.expected ∧ c'.clauses = c.clauses ∧
  c'.pool = c.pool ∧ c'.initial = c.initial ∧ c'.sizes = c.sizes ∧ c'.pending = c.pending

theorem cnfRel_same (c c' : Cnf) (s : State) (rel : CnfRel c s) (same : SameCnf c c') : CnfRel c' s := by
  obtain ⟨_, _, clauses, pool, initial, sizes, pending⟩ := same
  obtain ⟨p, cap, pend, le, closed, fst, snd⟩ := rel
  exact ⟨by rw [p, pool], cap, by rw [pend, pool, pending], by rw [pending, pool]; exact le,
    by rw [closed, clauses], by rw [fst, initial], by rw [snd, sizes]⟩

-- A comment line in the DIMACS text (stage 0 or 5): words are ignored until
-- the line ends, as `skipLine`, and the loop resumes at a line start.
theorem cnf_comment_line (bytes : List Nat) (s : Nat) (shape : s = 0 ∨ s = 5) :
    ∀ (fuel pos : Nat) (c q : Cnf),
      c.valid = true → c.stage = s → c.comment = true →
      cnfLoop bytes pos c fuel = some q → q.valid = true →
      ∃ (next : Nat) (c' : Cnf), skipLine bytes pos fuel = some next ∧
        c'.valid = true ∧ c'.stage = s ∧ c'.first = true ∧ c'.comment = false ∧ SameCnf c c' ∧
        ((∃ fuel', fuel' < fuel ∧ cnfLoop bytes next c' fuel' = some q) ∨
          (0 < fuel ∧ (scan bytes next).kind = 0 ∧ q = c')) := by
  intro fuel
  induction fuel with
  | zero => intro pos c q _ _ _ h; simp [cnfLoop] at h
  | succ fuel ih =>
    intro pos c q valid stage comment h hq
    rw [cnfLoop, if_neg (by simp [valid])] at h
    by_cases kind : (scan bytes pos).kind = 2
    · have step : cnfStep bytes (scan bytes pos) c = ({ c with first := false, comment := true }, false) := by
        unfold cnfStep
        simp [kind, comment]
      rw [step] at h
      simp only [Bool.false_eq_true, if_false] at h
      obtain ⟨next, c', skipped, v', s', f', cm', same, rest⟩ :=
        ih (scan bytes pos).next { c with first := false, comment := true } q valid stage rfl h hq
      refine ⟨next, c', ?_, v', s', f', cm', same, ?_⟩
      · rw [skipLine, if_pos kind]; exact skipped
      · rcases rest with ⟨fuel', lt, run⟩ | ⟨_, eof, same'⟩
        · exact Or.inl ⟨fuel', Nat.lt_succ_of_lt lt, run⟩
        · exact Or.inr ⟨Nat.succ_pos fuel, eof, same'⟩
    · have step : cnfStep bytes (scan bytes pos) c =
          ({ c with valid := true, stage := s, first := true, comment := false }, decide ((scan bytes pos).kind = 0)) := by
        unfold cnfStep
        rcases shape with rfl | rfl <;> simp [kind, stage]
      rw [step] at h
      refine ⟨(scan bytes pos).next, { c with valid := true, stage := s, first := true, comment := false },
        ?_, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
      · rw [skipLine, if_neg kind]
      · by_cases eof : (scan bytes pos).kind = 0
        · simp only [eof, decide_true, if_true] at h
          exact Or.inr ⟨Nat.succ_pos fuel, scan_eof_next bytes pos eof, (Option.some.inj h).symm⟩
        · simp only [eof, decide_false, Bool.false_eq_true, if_false] at h
          exact Or.inl ⟨fuel, Nat.lt_succ_self fuel, h⟩

-- At the end of input the model accepts a state with nothing pending and
-- the declared number of clauses.
theorem clauses_eof (variables count : Nat) (bytes : List Nat) (pos fuel : Nat) (s : State) (first : Bool)
    (eof : (scan bytes pos).kind = 0) (pending : s.buffer.pending = []) (closed : s.buffer.closed.length = count) :
    clauses variables count bytes pos s first (fuel + 1) = some s := by
  rw [clauses]
  simp [eof, pending, closed]

-- The clause phase: from stage 5, every accepted Oak run whose final state
-- passes the decoder's closing check (every clause closed, the declared
-- count reached) is a `clauses` run of the model over a related state.
theorem clause_phase (bytes : List Nat) :
    ∀ (fuel pos : Nat) (c q : Cnf) (s : State),
      c.valid = true → c.stage = 5 → c.comment = false → CnfRel c s →
      cnfLoop bytes pos c fuel = some q → q.valid = true →
      q.clauses = q.expected → q.pending = q.pool.length →
      ∃ s' : State, clauses c.variables c.expected bytes pos s c.first fuel = some s' ∧
        CnfRel q s' ∧ q.variables = c.variables ∧ q.expected = c.expected := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
  intro pos c q s valid stage comment rel h hq closedAll counted
  cases fuel with
  | zero => simp [cnfLoop] at h
  | succ fuel =>
  rw [cnfLoop, if_neg (by simp [valid])] at h
  by_cases kind : (scan bytes pos).kind = 2
  · by_cases isComment : (c.first && decide (Word bytes (scan bytes pos) 99)) = true
    · -- A comment line.
      have first : c.first = true := (Bool.and_eq_true_iff.1 isComment).1
      have word : Word bytes (scan bytes pos) 99 := decide_eq_true_iff.1 (Bool.and_eq_true_iff.1 isComment).2
      have step : cnfStep bytes (scan bytes pos) c = ({ c with first := false, comment := true }, false) := by
        unfold cnfStep
        simp [kind, comment, isComment]
      rw [step] at h
      simp only [Bool.false_eq_true, if_false] at h
      obtain ⟨next, c', skipped, v', s', f', cm', same, rest⟩ :=
        cnf_comment_line bytes 5 (Or.inr rfl) fuel (scan bytes pos).next { c with first := false, comment := true } q valid stage rfl h hq
      have rel' : CnfRel c' s := cnfRel_same _ c' s rel same
      rw [clauses, if_neg (by simp [kind]), if_neg (by simp [kind]), if_pos ⟨by simp [first], word⟩, skipped]
      rcases rest with ⟨fuel', lt, run⟩ | ⟨positive, eof, same'⟩
      · obtain ⟨s'', model, rel'', vars, expected⟩ := ih fuel' (by omega) next c' q s v' s' cm' rel' run hq closedAll counted
        refine ⟨s'', ?_, rel'', by rw [vars, same.1], by rw [expected, same.2.1]⟩
        rw [← same.1, ← same.2.1, ← f']
        exact clauses_mono c'.variables c'.expected bytes fuel' fuel next s s'' c'.first model (by omega)
      · subst same'
        refine ⟨s, ?_, rel', same.1, same.2.1⟩
        obtain ⟨_, _, pend, _, closed, _, _⟩ := rel'
        cases fuel with
        | zero => omega
        | succ fuel =>
          have expected := same.2.1
          have clausesSame := same.2.2.1
          simp only at expected clausesSame
          apply clauses_eof _ _ bytes next fuel s true eof
          · rw [pend, counted]; simp
          · rw [closed, closedAll, expected]
    · -- A clause token.
      have notComment : ¬ (c.first = true ∧ Word bytes (scan bytes pos) 99) := by
        intro ⟨f, w⟩; simp [f, w] at isComment
      have signs := sign_nonzero bytes pos
      obtain ⟨pool, cap, pend, le, closed, fst, snd⟩ := rel
      by_cases zero : (scan bytes pos).magnitude = 0
      · have step : cnfStep bytes (scan bytes pos) c =
            if (decide ((scan bytes pos).sign ≠ 0) && decide (c.stage = 5) && decide (c.clauses < c.expected)) = true then
              ({ c with
                  valid := true
                  initial := c.initial ++ [c.pending]
                  sizes := c.sizes ++ [c.pool.length - c.pending]
                  clauses := c.clauses + 1
                  pending := c.pool.length
                  first := false
                  comment := c.first && decide (Word bytes (scan bytes pos) 99) }, false)
            else ({ c with valid := false, first := false, comment := c.first && decide (Word bytes (scan bytes pos) 99) }, false) := by
          unfold cnfStep
          simp [kind, comment, isComment, stage, zero]
        rw [step] at h
        by_cases ok : (decide ((scan bytes pos).sign ≠ 0) && decide (c.stage = 5) && decide (c.clauses < c.expected)) = true
        · rw [if_pos ok] at h
          simp only [Bool.false_eq_true, if_false] at h
          have sign : (scan bytes pos).sign ≠ 0 := decide_eq_true_iff.1 (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 ok).1).1
          have room : c.clauses < c.expected := decide_eq_true_iff.1 (Bool.and_eq_true_iff.1 ok).2
          have closedStep : tokenStep .literal c.variables s.buffer (scan bytes pos) = some (closeSegment s.buffer) := by
            simp [tokenStep, kind, signs.1 sign, zero]
          have relStep : CnfRel
              { c with
                  valid := true
                  initial := c.initial ++ [c.pending]
                  sizes := c.sizes ++ [c.pool.length - c.pending]
                  clauses := c.clauses + 1
                  pending := c.pool.length
                  first := false
                  comment := c.first && decide (Word bytes (scan bytes pos) 99) }
              ⟨closeSegment s.buffer, s.ranges ++ [(Packed.start s.buffer, s.buffer.pending.length)]⟩ := by
            refine ⟨by simp [closeSegment, pool], by simp [closeSegment, cap], by simp [closeSegment], Nat.le_refl _, by simp [closeSegment, closed], ?_, ?_⟩
            · simp [List.map_append, fst, Packed.start, pool, pend, List.length_drop]
              omega
            · simp [List.map_append, snd, pend, List.length_drop]
          obtain ⟨s'', model, rel'', vars, expected⟩ := ih fuel (Nat.lt_succ_self fuel) (scan bytes pos).next
            { c with
                valid := true
                initial := c.initial ++ [c.pending]
                sizes := c.sizes ++ [c.pool.length - c.pending]
                clauses := c.clauses + 1
                pending := c.pool.length
                first := false
                comment := c.first && decide (Word bytes (scan bytes pos) 99) } q _
            rfl stage (by simpa using isComment) relStep h hq closedAll counted
          refine ⟨s'', ?_, rel'', vars, expected⟩
          rw [clauses, if_neg (by simp [kind]), if_neg (by simp [kind]), if_neg notComment, closedStep]
          simp only [zero, if_true]
          rw [if_pos (by rw [closed]; exact room)]
          exact model
        · rw [if_neg ok] at h
          simp only [Bool.false_eq_true, if_false] at h
          have := cnfLoop_accepted_valid bytes fuel _ _ q h hq
          simp at this
      · have step : cnfStep bytes (scan bytes pos) c =
            if (decide ((scan bytes pos).sign ≠ 0) && decide (c.stage = 5) && decide ((scan bytes pos).magnitude ≤ c.variables ∧ c.pool.length < 4096)) = true then
              ({ c with
                  valid := true
                  pool := c.pool ++ [encoded (scan bytes pos).magnitude (scan bytes pos).sign]
                  first := false
                  comment := c.first && decide (Word bytes (scan bytes pos) 99) }, false)
            else ({ c with valid := false, first := false, comment := c.first && decide (Word bytes (scan bytes pos) 99) }, false) := by
          unfold cnfStep
          simp [kind, comment, isComment, stage, zero]
        rw [step] at h
        by_cases ok : (decide ((scan bytes pos).sign ≠ 0) && decide (c.stage = 5) && decide ((scan bytes pos).magnitude ≤ c.variables ∧ c.pool.length < 4096)) = true
        · rw [if_pos ok] at h
          simp only [Bool.false_eq_true, if_false] at h
          have sign : (scan bytes pos).sign ≠ 0 := decide_eq_true_iff.1 (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 ok).1).1
          have bounds : (scan bytes pos).magnitude ≤ c.variables ∧ c.pool.length < 4096 := decide_eq_true_iff.1 (Bool.and_eq_true_iff.1 ok).2
          have pushed : tokenStep .literal c.variables s.buffer (scan bytes pos) =
              some { s.buffer with
                pool := s.buffer.pool ++ [encoded (scan bytes pos).magnitude (scan bytes pos).sign]
                pending := s.buffer.pending ++ [encoded (scan bytes pos).magnitude (scan bytes pos).sign] } := by
            have room : s.buffer.pool.length < s.buffer.capacity := by rw [pool, cap]; exact bounds.2
            simp [tokenStep, kind, signs.1 sign, zero, bounds.1, push, room, encoded]
          have relStep : CnfRel
              { c with
                  valid := true
                  pool := c.pool ++ [encoded (scan bytes pos).magnitude (scan bytes pos).sign]
                  first := false
                  comment := c.first && decide (Word bytes (scan bytes pos) 99) }
              ⟨{ s.buffer with
                  pool := s.buffer.pool ++ [encoded (scan bytes pos).magnitude (scan bytes pos).sign]
                  pending := s.buffer.pending ++ [encoded (scan bytes pos).magnitude (scan bytes pos).sign] }, s.ranges⟩ := by
            refine ⟨by simp [pool], by simp [cap], ?_, by simp; omega, by simp [closed], by simp [fst], by simp [snd]⟩
            simp only [pend]
            rw [List.drop_append_of_le_length le]
          obtain ⟨s'', model, rel'', vars, expected⟩ := ih fuel (Nat.lt_succ_self fuel) (scan bytes pos).next
            { c with
                valid := true
                pool := c.pool ++ [encoded (scan bytes pos).magnitude (scan bytes pos).sign]
                first := false
                comment := c.first && decide (Word bytes (scan bytes pos) 99) } q _
            rfl stage (by simpa using isComment) relStep h hq closedAll counted
          refine ⟨s'', ?_, rel'', vars, expected⟩
          rw [clauses, if_neg (by simp [kind]), if_neg (by simp [kind]), if_neg notComment, pushed]
          simp only [zero, if_false]
          exact model
        · rw [if_neg ok] at h
          simp only [Bool.false_eq_true, if_false] at h
          have := cnfLoop_accepted_valid bytes fuel _ _ q h hq
          simp at this
  · -- A blank line or the end of input.
    have step : cnfStep bytes (scan bytes pos) c =
        ({ c with valid := true, stage := 5, first := true, comment := false }, decide ((scan bytes pos).kind = 0)) := by
      unfold cnfStep
      simp [kind, stage]
    rw [step] at h
    by_cases eof : (scan bytes pos).kind = 0
    · simp only [eof, decide_true, if_true] at h
      have same : q = { c with valid := true, stage := 5, first := true, comment := false } := (Option.some.inj h).symm
      subst same
      obtain ⟨pool, cap, pend, le, closed, fst, snd⟩ := rel
      refine ⟨s, ?_, ⟨pool, cap, pend, le, closed, fst, snd⟩, rfl, rfl⟩
      apply clauses_eof _ _ bytes pos fuel s c.first eof
      · simp only at counted
        rw [pend, counted]; simp
      · simp only at closedAll
        rw [closed]; exact closedAll
    · simp only [eof, decide_false, Bool.false_eq_true, if_false] at h
      have newline : (scan bytes pos).kind = 1 := by
        rcases kind_cases bytes pos with h0 | h1 | h2
        · exact absurd h0 eof
        · exact h1
        · exact absurd h2 kind
      obtain ⟨s', model, rel', vars, expected⟩ := ih fuel (Nat.lt_succ_self fuel) (scan bytes pos).next
        { c with valid := true, stage := 5, first := true, comment := false } q s rfl rfl rfl rel h hq closedAll counted
      refine ⟨s', ?_, rel', vars, expected⟩
      rw [clauses, if_neg eof, if_pos newline]
      exact model

-- Stage 0 skips blank and comment lines to the first word, as `preamble`
-- does; an accepted run that reaches stage 5 must have found that word.
theorem preamble_phase (bytes : List Nat) :
    ∀ (fuel pos : Nat) (c q : Cnf),
      c.valid = true → c.stage = 0 → c.first = true → c.comment = false →
      cnfLoop bytes pos c fuel = some q → q.valid = true → q.stage = 5 →
      ∃ (posP fuel' : Nat) (c' : Cnf), fuel' ≤ fuel ∧ preamble bytes pos fuel = some posP ∧
        (scan bytes posP).kind = 2 ∧ ¬ Word bytes (scan bytes posP) 99 ∧
        cnfLoop bytes posP c' fuel' = some q ∧
        c'.valid = true ∧ c'.stage = 0 ∧ c'.first = true ∧ c'.comment = false ∧ SameCnf c c' := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
  intro pos c q valid stage first comment h hq stage5
  cases fuel with
  | zero => simp [cnfLoop] at h
  | succ fuel =>
  rw [cnfLoop, if_neg (by simp [valid])] at h
  by_cases kind : (scan bytes pos).kind = 2
  · by_cases isComment : Word bytes (scan bytes pos) 99
    · have step : cnfStep bytes (scan bytes pos) c = ({ c with first := false, comment := true }, false) := by
        unfold cnfStep
        simp [kind, first, comment, isComment]
      rw [step] at h
      simp only [Bool.false_eq_true, if_false] at h
      obtain ⟨next, c', skipped, v', s', f', cm', same, rest⟩ :=
        cnf_comment_line bytes 0 (Or.inl rfl) fuel (scan bytes pos).next { c with first := false, comment := true } q valid stage rfl h hq
      rcases rest with ⟨fuel', lt, run⟩ | ⟨_, _, same'⟩
      · obtain ⟨posP, fuel'', c'', le, pre, kindP, wordP, run'', v'', s'', f'', cm'', same''⟩ :=
          ih fuel' (by omega) next c' q v' s' f' cm' run hq stage5
        refine ⟨posP, fuel'', c'', by omega, ?_, kindP, wordP, run'', v'', s'', f'', cm'', ?_⟩
        · rw [preamble, if_neg (by simp [kind]), if_neg (by simp [kind]), if_pos isComment, skipped]
          exact preamble_mono bytes fuel' fuel next posP pre (by omega)
        · obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := same
          obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := same''
          exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6, b7.trans a7⟩
      · exfalso
        subst same'
        rw [s'] at stage5
        cases stage5
    · refine ⟨pos, fuel + 1, c, Nat.le_refl _, ?_, kind, isComment, ?_, valid, stage, first, comment, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
      · rw [preamble, if_neg (by simp [kind]), if_neg (by simp [kind]), if_neg isComment]
      · rw [cnfLoop, if_neg (by simp [valid])]
        exact h
  · have step : cnfStep bytes (scan bytes pos) c =
        ({ c with valid := true, stage := 0, first := true, comment := false }, decide ((scan bytes pos).kind = 0)) := by
      unfold cnfStep
      simp [kind, stage]
    rw [step] at h
    by_cases eof : (scan bytes pos).kind = 0
    · exfalso
      simp only [eof, decide_true, if_true] at h
      have same : q = { c with valid := true, stage := 0, first := true, comment := false } := (Option.some.inj h).symm
      subst same
      simp at stage5
    · simp only [eof, decide_false, Bool.false_eq_true, if_false] at h
      have newline : (scan bytes pos).kind = 1 := by
        rcases kind_cases bytes pos with h0 | h1 | h2
        · exact absurd h0 eof
        · exact h1
        · exact absurd h2 kind
      obtain ⟨posP, fuel', c', le, pre, kindP, wordP, run, v', s', f', cm', same⟩ :=
        ih fuel (Nat.lt_succ_self fuel) (scan bytes pos).next { c with valid := true, stage := 0, first := true, comment := false } q
          rfl rfl rfl rfl h hq stage5
      refine ⟨posP, fuel', c', Nat.le_succ_of_le le, ?_, kindP, wordP, run, v', s', f', cm', same⟩
      rw [preamble, if_neg eof, if_pos newline]
      exact pre

-- The header line: `p cnf V N` and the line end, token by token, as the
-- model's `header`; Oak resumes at stage 5 with the declared domains.
theorem header_line (bytes : List Nat) (fuel pos : Nat) (c q : Cnf)
    (valid : c.valid = true) (stage : c.stage = 0) (first : c.first = true) (comment : c.comment = false)
    (kind : (scan bytes pos).kind = 2) (notComment : ¬ Word bytes (scan bytes pos) 99)
    (h : cnfLoop bytes pos c fuel = some q) (hq : q.valid = true) :
    ∃ (hd : Header) (next : Nat) (c5 : Cnf), header bytes pos = some (hd, next) ∧
      c5.valid = true ∧ c5.stage = 5 ∧ c5.first = true ∧ c5.comment = false ∧
      c5.variables = hd.variables ∧ c5.expected = hd.count ∧
      c5.pool = c.pool ∧ c5.initial = c.initial ∧ c5.sizes = c.sizes ∧ c5.clauses = c.clauses ∧ c5.pending = c.pending ∧
      ((∃ fuel', fuel' < fuel ∧ cnfLoop bytes next c5 fuel' = some q) ∨
        (0 < fuel ∧ (scan bytes next).kind = 0 ∧ q = c5)) := by
  -- p
  cases fuel with
  | zero => simp [cnfLoop] at h
  | succ fuel =>
  rw [cnfLoop, if_neg (by simp [valid])] at h
  have step0 : cnfStep bytes (scan bytes pos) c =
      ({ c with valid := decide (Word bytes (scan bytes pos) 112), stage := 1, first := false, comment := false }, false) := by
    unfold cnfStep
    simp [kind, stage, first, comment, notComment]
  rw [step0] at h
  simp only [Bool.false_eq_true, if_false] at h
  have wordP : Word bytes (scan bytes pos) 112 := by
    have := cnfLoop_accepted_valid bytes fuel _ _ q h hq
    simpa using this
  -- cnf
  cases fuel with
  | zero => simp [cnfLoop] at h
  | succ fuel =>
  rw [cnfLoop, if_neg (by simp [wordP])] at h
  have kind1 : (scan bytes (scan bytes pos).next).kind = 2 := by
    apply Decidable.byContradiction
    intro other
    have step : (cnfStep bytes (scan bytes (scan bytes pos).next)
        { c with valid := decide (Word bytes (scan bytes pos) 112), stage := 1, first := false, comment := false }).1.valid = false := by
      unfold cnfStep
      simp [other]
    split at h
    · cases Option.some.inj h; rw [step] at hq; cases hq
    · have := cnfLoop_accepted_valid bytes fuel _ _ q h hq
      rw [step] at this; cases this
  have step1 : cnfStep bytes (scan bytes (scan bytes pos).next)
      { c with valid := decide (Word bytes (scan bytes pos) 112), stage := 1, first := false, comment := false } =
      ({ c with
          valid := decide ((scan bytes (scan bytes pos).next).stop - (scan bytes (scan bytes pos).next).start = 3) &&
            decide (bytes[(scan bytes (scan bytes pos).next).start]? = some 99 ∧
              bytes[(scan bytes (scan bytes pos).next).start + 1]? = some 110 ∧
              bytes[(scan bytes (scan bytes pos).next).start + 2]? = some 102)
          stage := 2
          first := false
          comment := false }, false) := by
    unfold cnfStep
    simp [kind1]
  rw [step1] at h
  simp only [Bool.false_eq_true, if_false] at h
  have spelledCnf : (scan bytes (scan bytes pos).next).stop - (scan bytes (scan bytes pos).next).start = 3 ∧
      bytes[(scan bytes (scan bytes pos).next).start]? = some 99 ∧
      bytes[(scan bytes (scan bytes pos).next).start + 1]? = some 110 ∧
      bytes[(scan bytes (scan bytes pos).next).start + 2]? = some 102 := by
    have := cnfLoop_accepted_valid bytes fuel _ _ q h hq
    simpa using this
  -- V
  cases fuel with
  | zero => simp [cnfLoop] at h
  | succ fuel =>
  rw [cnfLoop, if_neg (by simp [spelledCnf])] at h
  have kind2 : (scan bytes (scan bytes (scan bytes pos).next).next).kind = 2 := by
    apply Decidable.byContradiction
    intro other
    have step : (cnfStep bytes (scan bytes (scan bytes (scan bytes pos).next).next)
        { c with
            valid := decide ((scan bytes (scan bytes pos).next).stop - (scan bytes (scan bytes pos).next).start = 3) &&
              decide (bytes[(scan bytes (scan bytes pos).next).start]? = some 99 ∧
                bytes[(scan bytes (scan bytes pos).next).start + 1]? = some 110 ∧
                bytes[(scan bytes (scan bytes pos).next).start + 2]? = some 102)
            stage := 2
            first := false
            comment := false }).1.valid = false := by
      unfold cnfStep
      simp [other]
    split at h
    · cases Option.some.inj h; rw [step] at hq; cases hq
    · have := cnfLoop_accepted_valid bytes fuel _ _ q h hq
      rw [step] at this; cases this
  have step2 : cnfStep bytes (scan bytes (scan bytes (scan bytes pos).next).next)
      { c with
          valid := decide ((scan bytes (scan bytes pos).next).stop - (scan bytes (scan bytes pos).next).start = 3) &&
            decide (bytes[(scan bytes (scan bytes pos).next).start]? = some 99 ∧
              bytes[(scan bytes (scan bytes pos).next).start + 1]? = some 110 ∧
              bytes[(scan bytes (scan bytes pos).next).start + 2]? = some 102)
          stage := 2
          first := false
          comment := false } =
      ({ c with
          valid := decide ((scan bytes (scan bytes (scan bytes pos).next).next).sign ≠ 0) &&
            decide ((scan bytes (scan bytes (scan bytes pos).next).next).sign = 1 ∧
              (scan bytes (scan bytes (scan bytes pos).next).next).magnitude > 0 ∧
              (scan bytes (scan bytes (scan bytes pos).next).next).magnitude ≤ 64)
          variables := (scan bytes (scan bytes (scan bytes pos).next).next).magnitude
          stage := 3
          first := false
          comment := false }, false) := by
    unfold cnfStep
    simp [kind2]
  rw [step2] at h
  simp only [Bool.false_eq_true, if_false] at h
  have domainV : (scan bytes (scan bytes (scan bytes pos).next).next).sign = 1 ∧
      (scan bytes (scan bytes (scan bytes pos).next).next).magnitude > 0 ∧
      (scan bytes (scan bytes (scan bytes pos).next).next).magnitude ≤ 64 := by
    have := cnfLoop_accepted_valid bytes fuel _ _ q h hq
    simp at this
    exact this.2
  -- N
  cases fuel with
  | zero => simp [cnfLoop] at h
  | succ fuel =>
  rw [cnfLoop, if_neg (by simp [domainV])] at h
  have kind3 : (scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).kind = 2 := by
    apply Decidable.byContradiction
    intro other
    have step : (cnfStep bytes (scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next)
        { c with
            valid := decide ((scan bytes (scan bytes (scan bytes pos).next).next).sign ≠ 0) &&
              decide ((scan bytes (scan bytes (scan bytes pos).next).next).sign = 1 ∧
                (scan bytes (scan bytes (scan bytes pos).next).next).magnitude > 0 ∧
                (scan bytes (scan bytes (scan bytes pos).next).next).magnitude ≤ 64)
            variables := (scan bytes (scan bytes (scan bytes pos).next).next).magnitude
            stage := 3
            first := false
            comment := false }).1.valid = false := by
      unfold cnfStep
      simp [other]
    split at h
    · cases Option.some.inj h; rw [step] at hq; cases hq
    · have := cnfLoop_accepted_valid bytes fuel _ _ q h hq
      rw [step] at this; cases this
  have step3 : cnfStep bytes (scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next)
      { c with
          valid := decide ((scan bytes (scan bytes (scan bytes pos).next).next).sign ≠ 0) &&
            decide ((scan bytes (scan bytes (scan bytes pos).next).next).sign = 1 ∧
              (scan bytes (scan bytes (scan bytes pos).next).next).magnitude > 0 ∧
              (scan bytes (scan bytes (scan bytes pos).next).next).magnitude ≤ 64)
          variables := (scan bytes (scan bytes (scan bytes pos).next).next).magnitude
          stage := 3
          first := false
          comment := false } =
      ({ c with
          valid := decide ((scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).sign ≠ 0) &&
            decide (((scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).sign = 1 ∨
                (scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).magnitude = 0) ∧
              (scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).magnitude ≤ 256)
          variables := (scan bytes (scan bytes (scan bytes pos).next).next).magnitude
          expected := (scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).magnitude
          stage := 4
          first := false
          comment := false }, false) := by
    unfold cnfStep
    simp [kind3]
  rw [step3] at h
  simp only [Bool.false_eq_true, if_false] at h
  have domainN : (scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).sign ≠ 0 ∧
      ((scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).sign = 1 ∨
        (scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).magnitude = 0) ∧
      (scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).magnitude ≤ 256 := by
    have := cnfLoop_accepted_valid bytes fuel _ _ q h hq
    simp only [Bool.and_eq_true_iff, decide_eq_true_iff] at this
    exact ⟨this.1, this.2.1, this.2.2⟩
  -- The line end.
  cases fuel with
  | zero => simp [cnfLoop] at h
  | succ fuel =>
  rw [cnfLoop, if_neg (by simp [domainN])] at h
  have kind4 : (scan bytes (scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).next).kind ≠ 2 := by
    intro word
    have step : (cnfStep bytes (scan bytes (scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).next)
        { c with
            valid := decide ((scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).sign ≠ 0) &&
              decide (((scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).sign = 1 ∨
                  (scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).magnitude = 0) ∧
                (scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).magnitude ≤ 256)
            variables := (scan bytes (scan bytes (scan bytes pos).next).next).magnitude
            expected := (scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).magnitude
            stage := 4
            first := false
            comment := false }).1.valid = false := by
      unfold cnfStep
      simp [word]
    split at h
    · cases Option.some.inj h; rw [step] at hq; cases hq
    · have := cnfLoop_accepted_valid bytes fuel _ _ q h hq
      rw [step] at this; cases this
  have step4 : cnfStep bytes (scan bytes (scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).next)
      { c with
          valid := decide ((scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).sign ≠ 0) &&
            decide (((scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).sign = 1 ∨
                (scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).magnitude = 0) ∧
              (scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).magnitude ≤ 256)
          variables := (scan bytes (scan bytes (scan bytes pos).next).next).magnitude
          expected := (scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).magnitude
          stage := 4
          first := false
          comment := false } =
      ({ c with
          valid := true
          variables := (scan bytes (scan bytes (scan bytes pos).next).next).magnitude
          expected := (scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).magnitude
          stage := 5
          first := true
          comment := false },
        decide ((scan bytes (scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).next).kind = 0)) := by
    unfold cnfStep
    simp [kind4]
  rw [step4] at h
  have parsed : header bytes pos = some (⟨(scan bytes (scan bytes (scan bytes pos).next).next).magnitude,
      (scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).magnitude⟩,
      (scan bytes (scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).next).next) := by
    unfold header
    rw [if_pos ⟨kind, wordP, kind1, by omega, spelledCnf.2.1, spelledCnf.2.2.1, spelledCnf.2.2.2, kind2, domainV.1, domainV.2.1, domainV.2.2, kind3, domainN.1, domainN.2.1, domainN.2.2⟩]
    simp [lineEnd, kind4]
  refine ⟨⟨(scan bytes (scan bytes (scan bytes pos).next).next).magnitude,
      (scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).magnitude⟩,
    (scan bytes (scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).next).next,
    { c with
        valid := true
        variables := (scan bytes (scan bytes (scan bytes pos).next).next).magnitude
        expected := (scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).magnitude
        stage := 5
        first := true
        comment := false },
    parsed, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  by_cases eof : (scan bytes (scan bytes (scan bytes (scan bytes (scan bytes pos).next).next).next).next).kind = 0
  · simp only [eof, decide_true, if_true] at h
    exact Or.inr ⟨Nat.succ_pos _, scan_eof_next bytes _ eof, (Option.some.inj h).symm⟩
  · simp only [eof, decide_false, Bool.false_eq_true, if_false] at h
    exact Or.inl ⟨fuel, by omega, h⟩

-- ---- Composition

theorem store_initial (a : Assembly) (literals references : State) (c : Command) (a' : Assembly)
    (h : store a literals references c = some a') : a'.initial = a.initial := by
  unfold store at h
  split at h
  · cases Option.some.inj h; rfl
  · simp at h

theorem map_pair_some {α β : Type} (f : α → β) (o : Option α) (b : β) (h : Option.map f o = some b) :
    ∃ x, o = some x ∧ f x = b := by
  cases o with
  | none => simp at h
  | some x => exact ⟨x, rfl, Option.some.inj h⟩

theorem readCommand_initial (variables : Nat) (bytes : List Nat) (pos : Nat) (a a' : Assembly) (next : Nat)
    (h : readCommand variables bytes pos a = some (a', next)) : a'.initial = a.initial := by
  unfold readCommand at h
  simp only at h
  split at h
  · simp at h
  · split at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · obtain ⟨a'', stored, eq⟩ := map_pair_some _ _ _ h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
          exact store_initial _ _ _ _ _ stored
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · obtain ⟨a'', stored, eq⟩ := map_pair_some _ _ _ h
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
            exact store_initial _ _ _ _ _ stored

-- The published initial ranges survive the proof phase.
theorem proofLines_initial (variables : Nat) (bytes : List Nat) :
    ∀ (fuel pos : Nat) (a a' : Assembly),
      proofLines variables bytes pos a fuel = some a' → a'.initial = a.initial := by
  intro fuel
  induction fuel with
  | zero => intro pos a a' h; simp [proofLines] at h
  | succ fuel ih =>
    intro pos a a' h
    simp only [proofLines] at h
    split at h
    · cases Option.some.inj h; rfl
    · split at h
      · exact ih _ a a' h
      · split at h
        · cases skipped : skipLine bytes (scan bytes pos).next fuel with
          | none => simp [skipped] at h
          | some next =>
            simp only [skipped] at h
            exact ih _ a a' h
        · cases read : readCommand variables bytes pos a with
          | none => simp [read] at h
          | some result =>
            obtain ⟨middle, next⟩ := result
            simp only [read] at h
            rw [ih _ middle a' h]
            exact readCommand_initial variables bytes pos a middle next read

-- The DIMACS phase: from the initial state, every accepted run that passes
-- the closing check is the model's preamble, header, and clauses.
theorem cnf_refines (bytes : List Nat) (fuel : Nat) (bound : fuel ≤ bytes.length + 1) (c q : Cnf)
    (valid : c.valid = true) (stage : c.stage = 0) (first : c.first = true) (comment : c.comment = false)
    (pool : c.pool = []) (initial : c.initial = []) (sizes : c.sizes = []) (clauses : c.clauses = 0)
    (pending : c.pending = 0)
    (h : cnfLoop bytes 0 c fuel = some q) (hq : q.valid = true) (stage5 : q.stage = 5)
    (closedAll : q.clauses = q.expected) (counted : q.pending = q.pool.length) :
    ∃ (posP next : Nat) (hd : Header) (s : State),
      preamble bytes 0 (bytes.length + 1) = some posP ∧ header bytes posP = some (hd, next) ∧
      CertificateFile.clauses hd.variables hd.count bytes next (emptyState 4096) true (bytes.length + 1) = some s ∧
      CnfRel q s ∧ q.variables = hd.variables ∧ q.expected = hd.count := by
  obtain ⟨posP, fuel', c', le, pre, kindP, wordP, run, v', s', f', cm', same⟩ :=
    preamble_phase bytes fuel 0 c q valid stage first comment h hq stage5
  obtain ⟨hd, next, c5, hdr, v5, s5, f5, cm5, vars5, expected5, pool5, initial5, sizes5, clauses5, pending5, rest⟩ :=
    header_line bytes fuel' posP c' q v' s' f' cm' kindP wordP run hq
  obtain ⟨_, _, sameClauses, samePool, sameInitial, sameSizes, samePending⟩ := same
  have emptyRel : CnfRel c5 (emptyState 4096) := by
    refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [emptyState, empty, pool5, initial5, sizes5, clauses5, pending5, samePool, sameInitial, sameSizes, sameClauses, samePending, pool, initial, sizes, clauses, pending]
  have pre' := preamble_mono bytes fuel (bytes.length + 1) 0 posP pre bound
  rcases rest with ⟨fuel'', lt, run5⟩ | ⟨_, eof, same'⟩
  · obtain ⟨s, model, rel, vars, expected⟩ :=
      clause_phase bytes fuel'' next c5 q (emptyState 4096) v5 s5 cm5 emptyRel run5 hq closedAll counted
    refine ⟨posP, next, hd, s, pre', hdr, ?_, rel, by rw [vars, vars5], by rw [expected, expected5]⟩
    rw [← vars5, ← expected5, ← f5]
    exact clauses_mono _ _ bytes fuel'' (bytes.length + 1) next _ s _ model (by omega)
  · subst same'
    refine ⟨posP, next, hd, emptyState 4096, pre', hdr, ?_, emptyRel, vars5, expected5⟩
    apply clauses_eof hd.variables hd.count bytes next bytes.length (emptyState 4096) true eof
    · rfl
    · simp only [emptyState, empty, List.length_nil]
      rw [← expected5, ← closedAll, clauses5, sameClauses, clauses]

theorem guard_ascii (bytes : List Nat) : guard bytes = ascii bytes := rfl

-- Every acceptance by the transliterated Oak decoder is an acceptance by the
-- proved file model: the Oak checker implements the model.
theorem check_refines (cnf proof : String) (accepted : check cnf proof = true) :
    CertificateFile.check cnf proof = true := by
  unfold check at accepted
  cases built : layout cnf proof with
  | none => simp [built] at accepted
  | some raw =>
  simp only [built] at accepted
  unfold layout at built
  cases phase : cnfPhase (bytesOf cnf) (bytesOf proof) with
  | none => simp [phase] at built
  | some c =>
  simp only [phase] at built
  cases run : proofLoop (bytesOf proof) 0 (proofStart c) ((bytesOf proof).length + 1) with
  | none => simp [run] at built
  | some p =>
  simp only [run] at built
  split at built
  · rename_i pvalid
    cases Option.some.inj built
    have closing : closingCheck c = true := proofLoop_accepted_valid _ _ _ _ _ run pvalid
    have closingFacts := closing
    simp only [closingCheck, Bool.and_eq_true_iff, decide_eq_true_iff] at closingFacts
    obtain ⟨cvalid, stage5, closedAll, counted⟩ := closingFacts
    have guards : (guard (bytesOf cnf) && guard (bytesOf proof)) = true :=
      cnfLoop_accepted_valid _ _ _ _ _ phase cvalid
    obtain ⟨gc, gp⟩ := Bool.and_eq_true_iff.1 guards
    obtain ⟨posP, next, hd, s, pre, hdr, cls, rel, vars, expected⟩ :=
      cnf_refines (bytesOf cnf) _ (Nat.le_refl _) _ c guards rfl rfl rfl rfl rfl rfl rfl rfl phase cvalid stage5 closedAll counted
    obtain ⟨sPool, sCap, sPending, _, _, sFst, sSnd⟩ := rel
    have relStart : Rel (proofStart c) (CommandAssembly.start s 4096) := by
      refine ⟨sPool, ?_, sCap, rfl, rfl, rfl, rfl⟩
      show s.buffer.pending = []
      rw [sPending, counted]; simp
    obtain ⟨a, lines, relEnd⟩ :=
      proof_refines (bytesOf proof) _ (Nat.le_refl _) 0 (proofStart c) p (CommandAssembly.start s 4096)
        ⟨closing, rfl, rfl, rfl⟩ relStart run pvalid
    have init := proofLines_initial _ _ _ _ _ _ lines
    have pvars := proofLoop_variables _ _ _ _ _ run
    obtain ⟨litPool, _, _, refPool, _, _, cmds⟩ := relEnd
    rw [guard_ascii] at gc gp
    unfold CertificateFile.check formula
    simp only [gc, gp, Bool.not_true, Bool.false_eq_true, if_false, pre, hdr, cls]
    have linesAt : proofLines hd.variables (bytesOf proof) 0 (CommandAssembly.start s 4096) ((bytesOf proof).length + 1) = some a := by
      rw [← vars]; exact lines
    rw [linesAt]
    simp only
    have same : toLayout hd.variables a = ⟨p.variables, p.pool, c.initial, c.sizes, p.refs, p.commands⟩ := by
      simp only [toLayout, litPool, refPool, cmds, init, CommandAssembly.start, sFst, sSnd]
      rw [pvars]
      simp [proofStart, vars]
    rw [same]
    exact accepted
  · simp at built

-- With the file model's soundness theorem: an acceptance by the Oak decoder
-- refutes the formula the DIMACS text defines, with the declared clause count.
theorem check_refutes (cnf proof : String) (accepted : check cnf proof = true) :
    ∃ (h : Header) (s : State), formula cnf = some (h, s) ∧
      s.buffer.closed.length = h.count ∧
      Unsatisfiable (initialDatabase (s.buffer.closed.map (List.map decodeLiteral))) :=
  CertificateFile.check_sound cnf proof (check_refines cnf proof accepted)

#print axioms check_refines
#print axioms check_refutes

end OakVerification.OakText
