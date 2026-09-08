import LiveTable
import Lean

open Lean OakVerification OakVerification.Ranges

structure TableCommand where
  addition : Bool
  id : Nat
  start : Nat
  count : Nat
  refsStart : Nat
  refsCount : Nat
  deriving FromJson
structure TableCase where
  name : String
  variables : Nat
  pool : Array Nat
  starts : Array Nat
  sizes : Array Nat
  refs : Array Nat
  commands : Array TableCommand
  trace : Array Nat
  deriving FromJson

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: LiveTableCompare CASES.json")
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let cases ← IO.ofExcept (fromJson? json : Except String (Array TableCase))
  if cases.isEmpty then throw (IO.userError "empty live-table corpus")
  let mut snapshots := 0
  for c in cases do
    let commands := c.commands.toList.map fun r => Command.mk r.addition r.id r.start r.count r.refsStart r.refsCount
    let raw : Layout := ⟨c.variables, c.pool.toList, c.starts.toList, c.sizes.toList, c.refs.toList, commands⟩
    let actual := (LiveTable.trace raw).toArray
    if actual != c.trace then throw (IO.userError s!"{c.name}: live-table trace differs")
    snapshots := snapshots + actual.size / 771
  IO.println s!"Oak/Go/Lean live table: {cases.size} layouts, {snapshots} complete 256-slot snapshots agree"
