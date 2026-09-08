import CommandAssembly
import Lean

/-! Test adapter only. The Go harness supplies the compiled Oak observations and
    its own oracle; this replays the same texts through the proved assembly. -/
open Lean OakVerification.SegmentPublication OakVerification.CommandAssembly

structure AssemblyCommand where
  id : String
  deletion : Bool
  clause : String
  hints : String
  deriving FromJson
structure AssemblyCase where
  name : String
  variables : Nat
  initial : Array String
  commands : Array AssemblyCommand
  accepted : Bool
  layout : Array Nat
  deriving FromJson

def line (c : AssemblyCommand) : Line :=
  if c.deletion then .delete c.id c.hints else .add c.id c.clause c.hints

def flatten (raw : OakVerification.Ranges.Layout) : Array Nat :=
  ([raw.variables, raw.pool.length, raw.starts.length, raw.refs.length, raw.commands.length] ++
    raw.pool ++ raw.starts ++ raw.sizes ++ raw.refs ++
    raw.commands.flatMap fun c =>
      [if c.addition then 1 else 0, c.id, c.start, c.count, c.refsStart, c.refsCount]).toArray

def layout (c : AssemblyCase) : Option (Array Nat) := do
  if c.variables = 0 || c.variables > 64 || c.initial.size > 256 || c.commands.size > 256 then none else do
    let mut literals := emptyState 4096
    for body in c.initial do
      literals ← publish .literal c.variables literals body
    let a ← assemble c.variables (start literals 4096) (c.commands.toList.map line)
    return flatten (toLayout c.variables a)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: CommandAssemblyCompare CASES.json")
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let cases ← IO.ofExcept (fromJson? json : Except String (Array AssemblyCase))
  if cases.isEmpty then throw (IO.userError "empty assembly corpus")
  let mut accepted := 0
  for c in cases do
    let actual := layout c
    let expected := if c.accepted then some c.layout else none
    if actual != expected then throw (IO.userError s!"{c.name}: assembled layout mismatch (Lean decoded={actual.isSome}, Go decoded={c.accepted})")
    if c.accepted then accepted := accepted + 1
  IO.println s!"Oak/Go/Lean command assembly: {cases.size} cases ({accepted} decoded, {cases.size - accepted} rejected)"
