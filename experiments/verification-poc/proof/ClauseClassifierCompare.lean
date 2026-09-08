import ClauseClassifier
import Lean

open Lean OakVerification OakVerification.ClauseClassifier
structure ClassifierCase where
  clause : Array Nat
  cells : Array Nat
  expected : Array Nat
  deriving FromJson

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: ClauseClassifierCompare CASES.json")
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let cases ← IO.ofExcept (fromJson? json : Except String (Array ClassifierCase))
  if cases.isEmpty then throw (IO.userError "empty classifier corpus")
  let mut index := 0
  for c in cases do
    if c.cells.isEmpty || c.cells.size > 64 || c.cells.any (· > 2) ||
        c.clause.any (fun n => n / 2 ≥ c.cells.size) then
      throw (IO.userError s!"case {index}: corpus outside classifier domain")
    let s : PropagationState.Scratch := fun slot => PropagationState.decode (c.cells[slot]?.getD 0)
    let result := classify s (c.clause.toList.map Ranges.decodeLiteral)
    if (wire result).toArray != c.expected then throw (IO.userError s!"case {index}: classification differs")
    index := index + 1
  IO.println s!"Oak/Go/Lean clause classifier: {cases.size} cases agree"
