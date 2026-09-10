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
fidelity, stated here rather than left implicit. The refinement theorem —
every acceptance of `check` below is an acceptance of
`CertificateFile.check` — is the next increment of roadmap step 2; until it
lands, the corpus agreement is the evidence and `check_sound` below is what
is proved about this module on its own: an acceptance refutes the initial
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

def Cnf.literals (c : Cnf) : Nat := c.pool.length

-- One iteration of the DIMACS loop body, given the scanned token.
def cnfStep (bytes : List Nat) (t : Token) (c : Cnf) : Cnf × Bool :=
  if t.kind ≠ 2 then
    let valid := decide (c.stage = 0 ∨ c.stage ≥ 4)
    let stage := if c.stage = 4 then 5 else c.stage
    ({ c with valid := valid, stage := stage, first := true, comment := false }, decide (t.kind = 0))
  else
    let comment := c.comment || (c.first && decide (Word bytes t 99))
    let c := { c with first := false, comment := comment }
    if comment then (c, false)
    else if c.stage = 0 then
      ({ c with valid := decide (Word bytes t 112), stage := 1 }, false)
    else if c.stage = 1 then
      let valid := decide (t.stop - t.start = 3)
      let valid := valid && decide (bytes[t.start]? = some 99 ∧ bytes[t.start + 1]? = some 110 ∧
        bytes[t.start + 2]? = some 102)
      ({ c with valid := valid, stage := 2 }, false)
    else
      let valid := decide (t.sign ≠ 0)
      if c.stage = 2 then
        let variables := t.magnitude
        let valid := valid && decide (t.sign = 1 ∧ variables > 0 ∧ variables ≤ 64)
        ({ c with valid := valid, variables := variables, stage := 3 }, false)
      else if c.stage = 3 then
        let expected := t.magnitude
        let valid := valid && decide ((t.sign = 1 ∨ expected = 0) ∧ expected ≤ 256)
        ({ c with valid := valid, expected := expected, stage := 4 }, false)
      else
        let valid := valid && decide (c.stage = 5)
        if t.magnitude = 0 then
          let valid := valid && decide (c.clauses < c.expected)
          if valid then
            ({ c with
                valid := valid
                initial := c.initial ++ [c.pending]
                sizes := c.sizes ++ [c.literals - c.pending]
                clauses := c.clauses + 1
                pending := c.literals }, false)
          else ({ c with valid := valid }, false)
        else
          let valid := valid && decide (t.magnitude ≤ c.variables ∧ c.literals < 4096)
          if valid then
            ({ c with valid := valid, pool := c.pool ++ [encoded t.magnitude t.sign] }, false)
          else ({ c with valid := valid }, false)

-- `while !done && valid`, with fuel standing in for the scanner's progress.
def cnfLoop (bytes : List Nat) : Nat → Cnf → Nat → Option Cnf
  | _, _, 0 => none
  | pos, c, fuel + 1 =>
    if !c.valid then some c else
    let t := scan bytes pos
    let (after, done) := cnfStep bytes t c
    if done then some after else cnfLoop bytes t.next after fuel

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

def Proof.literals (p : Proof) : Nat := p.pool.length
def Proof.references (p : Proof) : Nat := p.refs.length
def Proof.count (p : Proof) : Nat := p.commands.length

def proofStep (bytes : List Nat) (t : Token) (p : Proof) : Proof × Bool :=
  if t.kind ≠ 2 then
    let valid := decide (p.stage = 0 ∨ p.stage = 5)
    let (valid, commands) :=
      if p.stage = 5 then
        let valid := valid && decide (p.count < 256)
        (valid, if valid then p.commands ++ [p.command] else p.commands)
      else (valid, p.commands)
    ({ p with
        valid := valid
        commands := commands
        stage := 0
        first := true
        comment := false }, decide (t.kind = 0))
  else
    let comment := p.comment || (p.first && decide (Word bytes t 99))
    let p := { p with first := false, comment := comment }
    if comment then (p, false)
    else if p.stage = 0 then
      let valid := decide (t.sign ≠ 0 ∧ (t.sign = 1 ∨ t.magnitude = 0))
      ({ p with
          valid := valid
          stage := 1
          command := ⟨true, t.magnitude, p.literals, 0, p.references, 0⟩ }, false)
    else if p.stage = 1 ∧ Word bytes t 100 then
      ({ p with command := { p.command with addition := false }, stage := 4 }, false)
    else
      let stage := if p.stage = 1 then 2 else p.stage
      let valid := decide (t.sign ≠ 0 ∧ stage ≠ 5)
      if stage = 2 then
        if t.magnitude = 0 then ({ p with valid := valid, stage := 3 }, false)
        else
          let valid := valid && decide (t.magnitude ≤ p.variables ∧ p.literals < 4096)
          if valid then
            ({ p with
                valid := valid
                stage := stage
                pool := p.pool ++ [encoded t.magnitude t.sign]
                command := { p.command with count := p.command.count + 1 } }, false)
          else ({ p with valid := valid, stage := stage }, false)
      else
        if t.magnitude = 0 then
          let valid := if stage = 4 then valid && decide (Word bytes t 48) else valid
          ({ p with valid := valid, stage := 5 }, false)
        else
          let valid := valid && decide (t.sign = 1 ∧ p.references < 4096)
          if valid then
            ({ p with
                valid := valid
                stage := stage
                refs := p.refs ++ [t.magnitude]
                command := { p.command with refsCount := p.command.refsCount + 1 } }, false)
          else ({ p with valid := valid, stage := stage }, false)

def proofLoop (bytes : List Nat) : Nat → Proof → Nat → Option Proof
  | _, _, 0 => none
  | pos, p, fuel + 1 =>
    if !p.valid then some p else
    let t := scan bytes pos
    let (after, done) := proofStep bytes t p
    if done then some after else proofLoop bytes t.next after fuel

-- The entry guards: at most 65536 bytes, every byte ASCII.
def guard (bytes : List Nat) : Bool :=
  decide (bytes.length ≤ 65536) && bytes.all (fun b => decide (b ≤ 127))

def initialCnf : Cnf :=
  ⟨true, 0, 0, 0, 0, [], [], [], 0, true, false⟩

-- `rup_text_check` up to its final call: the layout the Oak decoder hands to
-- `rup_stream_check` when both phases accept — the DIMACS phase's clauses and
-- the proof phase's pool, references, and commands — and `none` otherwise.
def layout (cnf proof : String) : Option Layout :=
  let cnfBytes := bytesOf cnf
  let proofBytes := bytesOf proof
  let valid := guard cnfBytes && guard proofBytes
  match cnfLoop cnfBytes 0 { initialCnf with valid := valid } (cnfBytes.length + 1) with
  | none => none
  | some c =>
    let valid := c.valid && decide (c.stage = 5 ∧ c.clauses = c.expected ∧ c.pending = c.literals)
    let p : Proof := ⟨valid, 0, c.variables, c.pool, [], [], ⟨true, 0, 0, 0, 0, 0⟩, true, false⟩
    match proofLoop proofBytes 0 p (proofBytes.length + 1) with
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
