import CertificateFile

set_option autoImplicit false
namespace OakVerification.OakText
open Scanner Ranges CertificateFile

/-! A transliteration of the Oak decoder `rup_text_check`
(`self_hosted_text.oak`), the executable reference for roadmap step 2: prove
that the Oak checker implements the proved file model.

The Oak program is two stage machines over the scanner, one for the DIMACS
text and one for the LRAT text, accumulating the literal pool, the initial
clause ranges, the reference pool, and the commands in bounded storage, then
handing that layout to the bounded stream checker. This module restates them
structure for structure: every Oak local is a field, every stage test a
branch, every assignment an assignment, in the order the Oak source writes
them. Bounded arrays become lists whose length is the Oak counter; the scanner
is the proved `scan`, whose agreement with `rup_token` the Go/Oak/Lean scanner
gate compares token by token; the stream checker is `CertifiedStream.check`,
whose agreement with `rup_stream_check` the stream gate compares layout by
layout.

What this buys: `OakTextCompare` checks the transliteration against compiled
Oak and against the proved file model on every corpus case, so the remaining
assumption between the compiled program and this module is transliteration
fidelity, stated here rather than left implicit. `OakTextRefinement.lean`
proves the refinement: every acceptance of `check` below is an acceptance of
`CertificateFile.check` (`check_refines`), so the file model's soundness
transfers to the Oak decoder (`check_refutes`). `check_sound` below is what
this module establishes on its own: an acceptance refutes the initial
clauses of the layout it hands to the certified stream. -/

-- `rup_encoded`: the packed literal.
def encoded (magnitude sign : Nat) : Nat :=
  (magnitude - 1) * 2 + if sign = 1 then 1 else 0

-- The DIMACS phase locals of `rup_text_check`.
structure Cnf where
  valid : Bool
  stage : Nat
  variables : Nat
  expected : Nat
  clauses : Nat
  pool : List Nat
  initial : List Nat
  sizes : List Nat
  pending : Nat
  first : Bool
  comment : Bool
  deriving Repr

-- One iteration of the DIMACS loop body, given the scanned token. Every
-- branch is one update of the incoming state, so a proof about a branch is a
-- proof about one record.
def cnfStep (bytes : List Nat) (t : Token) (c : Cnf) : Cnf × Bool :=
  if t.kind ≠ 2 then
    ({ c with
        valid := decide (c.stage = 0 ∨ c.stage ≥ 4)
        stage := if c.stage = 4 then 5 else c.stage
        first := true
        comment := false }, decide (t.kind = 0))
  else
    let comment := c.comment || (c.first && decide (Word bytes t 99))
    if comment then ({ c with first := false, comment := comment }, false)
    else if c.stage = 0 then
      ({ c with valid := decide (Word bytes t 112), stage := 1, first := false, comment := comment }, false)
    else if c.stage = 1 then
      ({ c with
          valid := decide (t.stop - t.start = 3) && decide (bytes[t.start]? = some 99 ∧
            bytes[t.start + 1]? = some 110 ∧ bytes[t.start + 2]? = some 102)
          stage := 2
          first := false
          comment := comment }, false)
    else if c.stage = 2 then
      ({ c with
          valid := decide (t.sign ≠ 0) && decide (t.sign = 1 ∧ t.magnitude > 0 ∧ t.magnitude ≤ 64)
          variables := t.magnitude
          stage := 3
          first := false
          comment := comment }, false)
    else if c.stage = 3 then
      ({ c with
          valid := decide (t.sign ≠ 0) && decide ((t.sign = 1 ∨ t.magnitude = 0) ∧ t.magnitude ≤ 256)
          expected := t.magnitude
          stage := 4
          first := false
          comment := comment }, false)
    else if t.magnitude = 0 then
      if decide (t.sign ≠ 0) && decide (c.stage = 5) && decide (c.clauses < c.expected) then
        ({ c with
            valid := true
            initial := c.initial ++ [c.pending]
            sizes := c.sizes ++ [c.pool.length - c.pending]
            clauses := c.clauses + 1
            pending := c.pool.length
            first := false
            comment := comment }, false)
      else ({ c with valid := false, first := false, comment := comment }, false)
    else
      if decide (t.sign ≠ 0) && decide (c.stage = 5) && decide (t.magnitude ≤ c.variables ∧ c.pool.length < 4096) then
        ({ c with
            valid := true
            pool := c.pool ++ [encoded t.magnitude t.sign]
            first := false
            comment := comment }, false)
      else ({ c with valid := false, first := false, comment := comment }, false)

-- `while !done && valid`, with fuel standing in for the scanner's progress.
def cnfLoop (bytes : List Nat) : Nat → Cnf → Nat → Option Cnf
  | _, _, 0 => none
  | pos, c, fuel + 1 =>
    if !c.valid then some c else
    if (cnfStep bytes (scan bytes pos) c).2 then some (cnfStep bytes (scan bytes pos) c).1
    else cnfLoop bytes (scan bytes pos).next (cnfStep bytes (scan bytes pos) c).1 fuel

-- The LRAT phase locals of `rup_text_check`.
structure Proof where
  valid : Bool
  stage : Nat
  variables : Nat
  pool : List Nat
  refs : List Nat
  commands : List Command
  command : Command
  first : Bool
  comment : Bool
  deriving Repr

def proofStep (bytes : List Nat) (t : Token) (p : Proof) : Proof × Bool :=
  if t.kind ≠ 2 then
    if p.stage = 5 then
      if p.commands.length < 256 then
        ({ p with
            valid := true
            commands := p.commands ++ [p.command]
            stage := 0
            first := true
            comment := false }, decide (t.kind = 0))
      else ({ p with valid := false, stage := 0, first := true, comment := false }, decide (t.kind = 0))
    else
      ({ p with valid := decide (p.stage = 0), stage := 0, first := true, comment := false },
        decide (t.kind = 0))
  else
    let comment := p.comment || (p.first && decide (Word bytes t 99))
    if comment then ({ p with first := false, comment := comment }, false)
    else if p.stage = 0 then
      ({ p with
          valid := decide (t.sign ≠ 0 ∧ (t.sign = 1 ∨ t.magnitude = 0))
          stage := 1
          command := ⟨true, t.magnitude, p.pool.length, 0, p.refs.length, 0⟩
          first := false
          comment := comment }, false)
    else if p.stage = 1 ∧ Word bytes t 100 then
      ({ p with
          command := { p.command with addition := false }
          stage := 4
          first := false
          comment := comment }, false)
    else
      let stage := if p.stage = 1 then 2 else p.stage
      if stage = 2 then
        if t.magnitude = 0 then
          ({ p with valid := decide (t.sign ≠ 0), stage := 3, first := false, comment := comment }, false)
        else if decide (t.sign ≠ 0) && decide (t.magnitude ≤ p.variables ∧ p.pool.length < 4096) then
          ({ p with
              valid := true
              stage := stage
              pool := p.pool ++ [encoded t.magnitude t.sign]
              command := { p.command with count := p.command.count + 1 }
              first := false
              comment := comment }, false)
        else ({ p with valid := false, stage := stage, first := false, comment := comment }, false)
      else if t.magnitude = 0 then
        ({ p with
            valid := decide (t.sign ≠ 0 ∧ stage ≠ 5) && (if stage = 4 then decide (Word bytes t 48) else true)
            stage := 5
            first := false
            comment := comment }, false)
      else if decide (t.sign ≠ 0 ∧ stage ≠ 5) && decide (t.sign = 1 ∧ p.refs.length < 4096) then
        ({ p with
            valid := true
            stage := stage
            refs := p.refs ++ [t.magnitude]
            command := { p.command with refsCount := p.command.refsCount + 1 }
            first := false
            comment := comment }, false)
      else ({ p with valid := false, stage := stage, first := false, comment := comment }, false)

def proofLoop (bytes : List Nat) : Nat → Proof → Nat → Option Proof
  | _, _, 0 => none
  | pos, p, fuel + 1 =>
    if !p.valid then some p else
    if (proofStep bytes (scan bytes pos) p).2 then some (proofStep bytes (scan bytes pos) p).1
    else proofLoop bytes (scan bytes pos).next (proofStep bytes (scan bytes pos) p).1 fuel

-- The entry guards: at most 65536 bytes, every byte ASCII.
def guard (bytes : List Nat) : Bool :=
  decide (bytes.length ≤ 65536) && bytes.all (fun b => decide (b ≤ 127))

def initialCnf : Cnf :=
  ⟨true, 0, 0, 0, 0, [], [], [], 0, true, false⟩

-- The DIMACS phase of `rup_text_check`: the entry guards, then the loop
-- over the cnf bytes from the initial state.
def cnfPhase (cnfBytes proofBytes : List Nat) : Option Cnf :=
  cnfLoop cnfBytes 0 { initialCnf with valid := guard cnfBytes && guard proofBytes } (cnfBytes.length + 1)

-- The check between the phases: every clause closed, the declared count met.
def closingCheck (c : Cnf) : Bool :=
  c.valid && decide (c.stage = 5 ∧ c.clauses = c.expected ∧ c.pending = c.pool.length)

-- The LRAT phase's initial state: the decoder's `scan[0] = 0; stage = 0`
-- reset, carrying the variable domain and the literal pool forward.
def proofStart (c : Cnf) : Proof :=
  ⟨closingCheck c, 0, c.variables, c.pool, [], [], ⟨true, 0, 0, 0, 0, 0⟩, true, false⟩

-- `rup_text_check` up to its final call: the layout the Oak decoder hands to
-- `rup_stream_check` when both phases accept — the DIMACS phase's clauses and
-- the proof phase's pool, references, and commands — and `none` otherwise.
def layout (cnf proof : String) : Option Layout :=
  match cnfPhase (bytesOf cnf) (bytesOf proof) with
  | none => none
  | some c =>
    match proofLoop (bytesOf proof) 0 (proofStart c) ((bytesOf proof).length + 1) with
    | none => none
    | some p => if p.valid then some ⟨p.variables, p.pool, c.initial, c.sizes, p.refs, p.commands⟩ else none

-- `rup_text_check`: `accepted = valid ? rup_stream_check(...) | false`.
def check (cnf proof : String) : Bool :=
  match layout cnf proof with
  | none => false
  | some raw => CertifiedStream.check raw

-- Acceptance by the transliterated Oak checker refutes the initial clauses
-- of the layout it built: the certified stream's soundness, through the
-- decoder's own construction.
theorem check_sound (cnf proof : String) (accepted : check cnf proof = true) :
    ∃ raw : Layout, layout cnf proof = some raw ∧ Unsatisfiable (CertifiedStream.origin raw) := by
  unfold check at accepted
  cases built : layout cnf proof with
  | none => simp [built] at accepted
  | some raw =>
    simp only [built] at accepted
    exact ⟨raw, rfl, CertifiedStream.check_sound raw accepted⟩

#print axioms check_sound

end OakVerification.OakText
