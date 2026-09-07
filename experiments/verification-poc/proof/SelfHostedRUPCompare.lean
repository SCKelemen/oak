import RUPExecutable
import Lean

open Lean
open OakVerification

structure Case where
  variables : Nat
  clauses : Array (Array Int)
  target : Array Int
  hints : Array Nat
  accepted : Bool
  deriving FromJson

def literal (x : Int) : Except String Literal := do
  if x = 0 then throw "zero is not a literal"
  return ⟨x.natAbs, x > 0⟩

def clause (xs : Array Int) : Except String Clause := do
  let mut result := []
  for x in xs do result := (← literal x) :: result
  return result.reverse

def checkCase (c : Case) : Except String Bool := do
  let mut clauses := []
  for xs in c.clauses do clauses := (← clause xs) :: clauses
  let target ← clause c.target
  return (checkRUP (initialDatabase clauses.reverse) target c.hints.toList).isSome

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: SelfHostedRUPCompare CASES.json")
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let cases ← IO.ofExcept (fromJson? json : Except String (Array Case))
  if cases.isEmpty then throw (IO.userError "empty self-hosted RUP corpus")
  let mut accepted := 0
  for c in cases do
    let actual ← IO.ofExcept (checkCase c)
    if actual != c.accepted then throw (IO.userError "Lean and reference decision differ")
    if actual then accepted := accepted + 1
  IO.println s!"Oak/Go/Lean RUP-step agreement: {cases.size} cases ({accepted} accepted, {cases.size-accepted} rejected)"
