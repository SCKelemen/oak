import RUPExecutable

/-!
Strict ASCII DIMACS/LRAT adapter. Parsing is executable but its correspondence
with the external file formats is not formally proved. The wrapper theorem
refers explicitly to the clause database returned by this parser.
-/
set_option autoImplicit false
namespace OakVerification.Text

structure Formula where
  variables : Nat
  clauses : List Clause
  deriving Repr

def fields (line : String) : List String :=
  let normalized := String.ofList (line.toList.map fun c =>
    if c == '\t' || c == '\r' || c.toNat == 11 || c.toNat == 12 then ' ' else c)
  (normalized.splitOn " ").filter (· != "")

def decimal (word : String) : Except String Nat := do
  if word.isEmpty then throw "empty integer"
  let mut n := 0
  for c in word.toList do
    if c < '0' ∨ '9' < c then throw "non-decimal integer"
    n := n * 10 + (c.toNat - '0'.toNat)
    if 2147483647 < n then throw "integer outside supported 31-bit magnitude"
  return n

def integer (word : String) : Except String Int := do
  match word.toList with
  | '+' :: rest => return Int.ofNat (← decimal (String.ofList rest))
  | '-' :: rest => return -(Int.ofNat (← decimal (String.ofList rest)))
  | _ => return Int.ofNat (← decimal word)

def natural (word : String) : Except String Nat := do
  let n ← integer word
  if n < 0 then throw "negative count or identifier"
  return n.toNat

def literal (n : Int) : Literal := ⟨n.natAbs, decide (0 < n)⟩

def parseDIMACS (text : String) : Except String Formula := do
  if text.utf8ByteSize > 20000000 then throw "CNF input limit"
  let mut header : Option (Nat × Nat) := none
  let mut clauses : Array Clause := #[]
  let mut pending : Clause := []
  for line in text.splitOn "\n" do
    match fields line with
    | [] => pure ()
    | "c" :: _ => pure ()
    | ["p", "cnf", variables, count] =>
      if header.isSome then throw "duplicate DIMACS header"
      header := some (← natural variables, ← natural count)
    | "p" :: _ => throw "invalid DIMACS header"
    | words =>
      let some (variables, _) := header | throw "missing DIMACS header"
      for word in words do
        let n ← integer word
        if n = 0 then
          clauses := clauses.push pending.reverse
          pending := []
        else
          if n.natAbs > variables then throw "literal outside variable domain"
          pending := literal n :: pending
  let some (variables, count) := header | throw "missing DIMACS header"
  if !pending.isEmpty || clauses.size != count then throw "unterminated clause or count mismatch"
  return ⟨variables, clauses.toList⟩

-- Tail recursion avoids recursion depth proportional to a clause's width.
def terminated (numbers : List Int) : Except String (List Int × List Int) :=
  go numbers []
where
  go : List Int → List Int → Except String (List Int × List Int)
    | [], _ => .error "missing zero terminator"
    | n :: rest, acc =>
      if n = 0 then .ok (acc.reverse, rest) else go rest (n :: acc)

def positiveIDs (numbers : List Int) : Except String (List Nat) :=
  numbers.mapM fun n => do
    if n ≤ 0 then throw "nonpositive identifier or unsupported RAT hint"
    return n.toNat

def parseLRAT (text : String) : Except String (List Instruction) := do
  if text.utf8ByteSize > 50000000 then throw "proof input limit"
  let mut commands : Array Instruction := #[]
  for line in text.splitOn "\n" do
    match fields line with
    | [] => pure ()
    | "c" :: _ => pure ()
    | id :: "d" :: words =>
      if words.reverse.head? != some "0" then throw "deletion requires literal zero terminator"
      let stamp ← natural id
      let (ids, rest) ← terminated (← words.mapM integer)
      if !rest.isEmpty then throw "tokens after deletion terminator"
      commands := commands.push (.delete stamp (← positiveIDs ids))
    | id :: words =>
      let index ← natural id
      let (clause, tail) ← terminated (← words.mapM integer)
      let (hints, rest) ← terminated tail
      if !rest.isEmpty then throw "tokens after addition terminator"
      commands := commands.push (.add index (clause.map literal) (← positiveIDs hints))
  return commands.toList

def checkText (cnf proof : String) : Except String Bool :=
  match parseDIMACS cnf with
  | .error reason => .error reason
  | .ok formula =>
    match parseLRAT proof with
    | .error reason => .error reason
    | .ok commands => .ok (checkProof formula.variables formula.clauses commands)

theorem checkText_sound {cnf proof : String}
    (accepted : checkText cnf proof = .ok true) :
    ∃ formula, parseDIMACS cnf = .ok formula ∧
      Unsatisfiable (initialDatabase formula.clauses) := by
  unfold checkText at accepted
  cases parsed : parseDIMACS cnf with
  | error reason => simp [parsed] at accepted
  | ok formula =>
    cases decoded : parseLRAT proof with
    | error reason => simp [parsed, decoded] at accepted
    | ok commands =>
      refine ⟨formula, rfl, checkProof_sound (variables := formula.variables) (commands := commands) ?_⟩
      simpa [parsed, decoded] using accepted

#print axioms checkText_sound
end OakVerification.Text
