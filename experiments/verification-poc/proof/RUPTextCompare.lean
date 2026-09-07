import RUPText
import Lean

open Lean

structure TextCase where
  name : String
  cnf : String
  proof : String
  expected : Bool
  deriving FromJson

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: RUPTextCompare CASES.json")
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let testCases ← IO.ofExcept (fromJson? json : Except String (Array TextCase))
  if testCases.isEmpty then throw (IO.userError "empty text corpus")
  let mut accepted := 0
  for c in testCases do
    let result := OakVerification.Text.checkText c.cnf c.proof
    let actual := match result with | .ok true => true | _ => false
    if actual != c.expected then
      throw (IO.userError s!"{c.name}: Lean={actual}, expected Go={c.expected}")
    if actual then accepted := accepted + 1
  IO.println s!"Go/Lean text agreement: {testCases.size} cases ({accepted} accepted, {testCases.size - accepted} rejected)"
