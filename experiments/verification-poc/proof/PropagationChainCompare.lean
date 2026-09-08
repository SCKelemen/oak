import PropagationChain
import Lean

open Lean OakVerification
structure ChainCase where
  name : String
  variables : Nat
  clauses : Array (Array Int)
  target : Array Int
  hints : Array Int
  accepted : Bool
  deriving FromJson

def logicalLiteral (n : Int) : OakVerification.Literal := ⟨n.natAbs, decide (0 < n)⟩
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: PropagationChainCompare CASES.json")
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let cases ← IO.ofExcept (fromJson? json : Except String (Array ChainCase))
  if cases.isEmpty then throw (IO.userError "empty propagation-chain corpus")
  let mut accepted := 0
  for c in cases do
    let clauses := c.clauses.toList.map (fun xs => xs.toList.map logicalLiteral)
    let target := c.target.toList.map logicalLiteral
    let hints := c.hints.toList.map Int.toNat
    let db := initialDatabase clauses
    let result := (PropagationChain.check c.variables db target hints).isSome
    if result != c.accepted then throw (IO.userError s!"{c.name}: classifier-based chain differs")
    let bounded := decide (0 < c.variables ∧ c.variables ≤ 64) &&
      (target ++ clauses.flatten).all (fun l => decide (0 < l.index ∧ l.index ≤ c.variables))
    let original := bounded && (checkRUP db target hints).isSome
    if original != result then throw (IO.userError s!"{c.name}: original Lean checker differs")
    if result then accepted := accepted + 1
  IO.println s!"Oak/Go/Lean propagation chain: {cases.size} cases ({accepted} accepted, {cases.size - accepted} rejected); both Lean checkers agree"
