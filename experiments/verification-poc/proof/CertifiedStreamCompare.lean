import InitialDecoder
import Lean

open Lean OakVerification OakVerification.Ranges
structure StreamCommand where
  addition : Bool
  id : Nat
  start : Nat
  count : Nat
  refsStart : Nat
  refsCount : Nat
  deriving FromJson
structure StreamCase where
  name : String
  variables : Nat
  pool : Array Nat
  starts : Array Nat
  sizes : Array Nat
  refs : Array Nat
  commands : Array StreamCommand
  accepted : Bool
  deriving FromJson

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: CertifiedStreamCompare CASES.json")
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let cases ← IO.ofExcept (fromJson? json : Except String (Array StreamCase))
  if cases.isEmpty then throw (IO.userError "empty certified-stream corpus")
  let mut accepted := 0
  for c in cases do
    let cmds := c.commands.toList.map fun r => Command.mk r.addition r.id r.start r.count r.refsStart r.refsCount
    let raw : Layout := ⟨c.variables, c.pool.toList, c.starts.toList, c.sizes.toList, c.refs.toList, cmds⟩
    let result := CertifiedStream.check raw
    if result != c.accepted then throw (IO.userError s!"{c.name}: certified stream differs")
    if InitialDecoder.check raw != result then throw (IO.userError s!"{c.name}: decoder composition differs")
    if checkLayout raw != result then throw (IO.userError s!"{c.name}: original Lean stream differs")
    if result then accepted := accepted + 1
  IO.println s!"Oak/Go/Lean certified stream: {cases.size} layouts ({accepted} accepted, {cases.size - accepted} rejected); both Lean streams agree"
