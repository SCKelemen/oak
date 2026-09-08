import BoundedDecimal
import Lean

open Lean OakVerification.Decimal

structure DecimalCase where
  name : String
  bytes : Array Nat
  accepted : Bool
  negative : Bool
  magnitude : Nat
  deriving FromJson

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: BoundedDecimalCompare CASES.json")
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let cases ← IO.ofExcept (fromJson? json : Except String (Array DecimalCase))
  if cases.isEmpty then throw (IO.userError "empty decimal corpus")
  let mut accepted := 0
  for c in cases do
    let actual := parseSigned c.bytes.toList
    let expected := if c.accepted then some (Signed.mk c.negative c.magnitude) else none
    if actual != expected then throw (IO.userError s!"{c.name}: Lean={repr actual}, Go={repr expected}")
    if c.accepted then accepted := accepted + 1
  IO.println s!"Oak/Go/Lean decimal agreement: {cases.size} cases ({accepted} accepted, {cases.size - accepted} rejected)"
