import RUPExecutable
import Lean

/-! Test adapter only: JSON decoding and signed-integer conversion are outside
    the checker theorem. The Go harness supplies expected decisions. -/
open Lean OakVerification

structure CommandCase where
  kind : String
  id : Nat
  clause : Array Int
  hints : Array Int
  ids : Array Nat
  deriving FromJson

structure TestCase where
  name : String
  kind : String
  variables : Nat
  database : Array (Array Int)
  clause : Array Int
  hints : Array Int
  commands : Array CommandCase
  expected : Bool
  deriving FromJson

def decodeLiteral (n : Int) : OakVerification.Literal := ⟨n.natAbs, decide (0 < n)⟩
def decodeClause (c : Array Int) : Clause := c.toList.map decodeLiteral
-- Negative/RAT hints become ID zero, which checkRUP always rejects.
def decodeHints (h : Array Int) : List Nat := h.toList.map Int.toNat

def decodeCommand (c : CommandCase) : Except String Instruction :=
  match c.kind with
  | "add" => .ok (.add c.id (decodeClause c.clause) (decodeHints c.hints))
  | "delete" => .ok (.delete c.id c.ids.toList)
  | _ => .error s!"unknown instruction kind: {c.kind}"

def evaluate (c : TestCase) : Except String Bool := do
  let clauses := c.database.toList.map decodeClause
  match c.kind with
  | "rup" => return (checkRUP (initialDatabase clauses) (decodeClause c.clause)
      (decodeHints c.hints)).isSome
  | "proof" =>
    let commands ← c.commands.toList.mapM decodeCommand
    return checkProof c.variables clauses commands
  | _ => .error s!"unknown case kind: {c.kind}"

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: RUPCompare CASES.json")
  let text ← IO.FS.readFile path
  let json ← IO.ofExcept (Json.parse text)
  let testCases ← IO.ofExcept (fromJson? json : Except String (Array TestCase))
  if testCases.isEmpty then throw (IO.userError "empty differential corpus")
  let mut accepted := 0
  for c in testCases do
    let actual ← IO.ofExcept (evaluate c)
    if actual != c.expected then
      throw (IO.userError s!"{c.name}: Lean={actual}, Go={c.expected}")
    if actual then accepted := accepted + 1
  IO.println s!"Go/Lean agreement: {testCases.size} cases ({accepted} accepted, {testCases.size - accepted} rejected)"
