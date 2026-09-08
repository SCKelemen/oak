import PackedBuffers
import Lean

open Lean OakVerification.Packed

structure BufferCommand where
  deletion : Bool
  clause : String
  hints : String
  deriving FromJson
structure BufferCase where
  name : String
  variables : Nat
  initial : Array String
  commands : Array BufferCommand
  accepted : Bool
  layout : Array Nat
  deriving FromJson

def layout (c : BufferCase) : Option (Array Nat) := do
  if c.variables = 0 || c.variables > 64 || c.initial.size > 256 || c.commands.size > 256 then none else do
    let mut literals := empty 4096
    let mut references := empty 4096
    let mut starts : List Nat := []
    let mut sizes : List Nat := []
    let mut commands : List Nat := []
    for body in c.initial do
      let old := literals.pool.length
      literals ← segment .literal c.variables literals body
      starts := starts ++ [old]
      sizes := sizes ++ [literals.pool.length - old]
    let mut id := c.initial.size
    for cmd in c.commands do
      id := id + 1
      let old := literals.pool.length
      if !cmd.deletion then literals ← segment .literal c.variables literals cmd.clause
      let refStart := references.pool.length
      references ← segment (if cmd.deletion then .deletion else .hint) c.variables references cmd.hints
      commands := commands ++ [if cmd.deletion then 0 else 1, id,
        old, literals.pool.length - old, refStart, references.pool.length - refStart]
    return ([c.variables, literals.pool.length, starts.length, references.pool.length, c.commands.size] ++
      literals.pool ++ starts ++ sizes ++ references.pool ++ commands).toArray

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: PackedBuffersCompare CASES.json")
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let cases ← IO.ofExcept (fromJson? json : Except String (Array BufferCase))
  if cases.isEmpty then throw (IO.userError "empty buffer corpus")
  let mut accepted := 0
  for c in cases do
    let actual := layout c
    let expected := if c.accepted then some c.layout else none
    if actual != expected then throw (IO.userError s!"{c.name}: buffer layout mismatch (Lean decoded={actual.isSome}, Go decoded={c.accepted})")
    if c.accepted then accepted := accepted + 1
  IO.println s!"Oak/Go/Lean buffer layouts: {cases.size} cases ({accepted} decoded, {cases.size - accepted} rejected)"
