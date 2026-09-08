import ScannerState
import Lean

open Lean OakVerification.Scanner

structure ScannerExpected where
  kind : Nat
  next : Nat
  start : Nat
  stop : Nat
  magnitude : Nat
  sign : Nat
  deriving FromJson
structure ScannerCase where
  name : String
  bytes : Array Nat
  cursor : Nat
  tokens : Array ScannerExpected
  deriving FromJson

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: ScannerStateCompare CASES.json")
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let cases ← IO.ofExcept (fromJson? json : Except String (Array ScannerCase))
  if cases.isEmpty then throw (IO.userError "empty scanner corpus")
  let mut transitions := 0
  for c in cases do
    if c.cursor > c.bytes.size || c.bytes.size > 65536 || c.tokens.isEmpty ||
        c.bytes.any (fun b => b > 255) then
      throw (IO.userError s!"{c.name}: invalid corpus preconditions")
    let mut cursor := c.cursor
    for r in c.tokens do
      let actual := scan c.bytes.toList cursor
      let expected : Token := ⟨r.kind, r.next, r.start, r.stop, r.magnitude, r.sign⟩
      if actual != expected then
        throw (IO.userError s!"{c.name} @ {cursor}: Lean={repr actual}, Go={repr expected}")
      cursor := actual.next
      transitions := transitions + 1
  IO.println s!"Oak/Go/Lean scanner agreement: {cases.size} cases, {transitions} transitions"
