import SegmentPublication
import Lean

open Lean OakVerification.Packed OakVerification.SegmentPublication

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
    let mut literals := emptyState 4096
    let mut references := emptyState 4096
    let mut commands : List Nat := []
    for body in c.initial do
      literals ← publish .literal c.variables literals body
    let starts := literals.ranges.map Prod.fst
    let sizes := literals.ranges.map Prod.snd
    let mut id := c.initial.size
    for cmd in c.commands do
      id := id + 1
      let old := literals.buffer.pool.length
      if !cmd.deletion then literals ← publish .literal c.variables literals cmd.clause
      references ← publish (if cmd.deletion then .deletion else .hint) c.variables references cmd.hints
      let litRange ← if cmd.deletion then some (old, 0) else literals.ranges.getLast?
      let refRange ← references.ranges.getLast?
      commands := commands ++ [if cmd.deletion then 0 else 1, id,
        litRange.1, litRange.2, refRange.1, refRange.2]
    return ([c.variables, literals.buffer.pool.length, starts.length, references.buffer.pool.length, c.commands.size] ++
      literals.buffer.pool ++ starts ++ sizes ++ references.buffer.pool ++ commands).toArray

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: SegmentPublicationCompare CASES.json")
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let cases ← IO.ofExcept (fromJson? json : Except String (Array BufferCase))
  if cases.isEmpty then throw (IO.userError "empty buffer corpus")
  let mut accepted := 0
  for c in cases do
    let actual := layout c
    let expected := if c.accepted then some c.layout else none
    if actual != expected then throw (IO.userError s!"{c.name}: buffer layout mismatch (Lean decoded={actual.isSome}, Go decoded={c.accepted})")
    if c.accepted then accepted := accepted + 1
  IO.println s!"Oak/Go/Lean segment publication: {cases.size} cases ({accepted} decoded, {cases.size - accepted} rejected)"
