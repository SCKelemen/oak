import PropagationState
import Lean

open Lean OakVerification.PropagationState
structure PropagationCase where
  variables : Nat
  clauses : Array (Array Int)
  target : Array Int
  hints : Array Nat
  trace : Array Nat
  deriving FromJson

def literalCode (n : Int) : Nat := (n.natAbs - 1) * 2 + if n > 0 then 1 else 0

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: PropagationStateCompare CASES.json")
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let cases ← IO.ofExcept (fromJson? json : Except String (Array PropagationCase))
  if cases.isEmpty then throw (IO.userError "empty propagation corpus")
  let mut snapshots := 0
  let mut index := 0
  for c in cases do
    let input : Input := ⟨c.variables, c.clauses.toList.map (fun xs => xs.toList.map literalCode),
      c.target.toList.map literalCode, c.hints.toList⟩
    let actual := (trace input).toArray
    if actual != c.trace then throw (IO.userError s!"case {index}: propagation trace differs")
    snapshots := snapshots + actual.size / 67
    index := index + 1
  IO.println s!"Oak/Go/Lean propagation state: {cases.size} cases, {snapshots} complete 64-cell snapshots agree"
