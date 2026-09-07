import BooleanCNF
import Lean

open Lean
open OakVerification.BooleanCNF

structure ProgramNode where
  op : String
  value : Bool
  index : Nat
  left : Nat
  right : Nat
  deriving FromJson
structure ValuationRow where
  x : Bool
  y : Bool
  value : Bool
  go_sat : Bool
  deriving FromJson
structure EncodingCase where
  name : String
  program : Array ProgramNode
  rows : Array ValuationRow
  deriving FromJson

def decodeNode (built : Array OakVerification.BooleanCNF.Expr) (n : ProgramNode) :
    Except String OakVerification.BooleanCNF.Expr := do
  let child := fun index => match built[index]? with
    | some e => Except.ok e
    | none => Except.error "non-backward child reference"
  match n.op with
  | "bool" => return .constant n.value
  | "var" =>
    if n.index < 2 then return .input n.index else throw "input outside corpus domain"
  | "!" => return .neg (← child n.left)
  | "&&" => return .conj (← child n.left) (← child n.right)
  | "||" => return .disj (← child n.left) (← child n.right)
  | _ => throw "unsupported Boolean operator"

def decodeProgram (program : Array ProgramNode) : Except String OakVerification.BooleanCNF.Expr := do
  let mut built : Array OakVerification.BooleanCNF.Expr := #[]
  for n in program do
    let e ← decodeNode built n
    built := built.push e
  match built.back? with
  | some e => return e
  | none => throw "empty expression program"

-- These kernel-evaluated regressions catch returning after the first operator
-- instead of reconstructing the final root, and accepting forward references.
private def doubleNegationProgram : Array ProgramNode := #[
  ⟨"bool", false, 0, 0, 0⟩, ⟨"!", false, 0, 0, 0⟩, ⟨"!", false, 0, 1, 0⟩]
example : (match decodeProgram doubleNegationProgram with
    | .ok e => e == .neg (.neg (.constant false))
    | .error _ => false) = true := by decide
example : (match decodeProgram #[⟨"!", false, 0, 0, 0⟩] with
    | .ok _ => false
    | .error _ => true) = true := by decide

-- The symbolic specification has different auxiliary names and may retain
-- gates that Go simplifies away. Compare existential satisfiability, not IDs.
def auxiliaries (f : CNF) : List Atom :=
  ((f.flatMap (fun c => c.map Lit.atom)).filter (fun a =>
    match a with | .gate _ => true | _ => false)).eraseDups

def auxiliaryValuations : List Atom → List (List (Atom × Bool))
  | [] => [[]]
  | a :: rest => (auxiliaryValuations rest).flatMap (fun tail => [(a, false) :: tail, (a, true) :: tail])

def extension (input : Nat → Bool) (values : List (Atom × Bool)) : Assignment
  | .one => true
  | .input n => input n
  | .gate e => ((values.find? (fun pair => pair.1 == .gate e)).map Prod.snd).getD false

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: BooleanCNFCompare CASES.json")
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let testCases ← IO.ofExcept (fromJson? json : Except String (Array EncodingCase))
  if testCases.isEmpty then throw (IO.userError "empty Boolean CNF corpus")
  let mut count := 0
  for c in testCases do
    let e ← IO.ofExcept (decodeProgram c.program)
    let f := encode e
    let names := auxiliaries f
    if names.length > 10 then throw (IO.userError "auxiliary enumeration bound exceeded")
    if c.rows.size != 4 then throw (IO.userError "expected all four input valuations")
    let mut seen : List (Bool × Bool) := []
    for row in c.rows do
      if seen.contains (row.x, row.y) then throw (IO.userError "duplicate input valuation")
      seen := (row.x, row.y) :: seen
      let input := fun n => if n == 0 then row.x else row.y
      let value := eval input e
      let sat := (auxiliaryValuations names).any (fun values => cnfSat (extension input values) f)
      if value != row.value || sat != value || sat != row.go_sat then
        throw (IO.userError s!"{c.name}: Lean expression={value}, Lean CNF={sat}, Go expression={row.value}, Go CNF={row.go_sat}")
      count := count + 1
  IO.println s!"Boolean CNF agreement: {testCases.size} expressions, {count} input valuations"
