import RangeBridge
import Lean

open Lean OakVerification OakVerification.Ranges

structure RawCommand where
  addition : Bool
  id : Nat
  start : Nat
  count : Nat
  refsStart : Nat
  refsCount : Nat
  deriving FromJson
structure RangeCase where
  name : String
  variables : Nat
  pool : Array Nat
  starts : Array Nat
  sizes : Array Nat
  refs : Array Nat
  commands : Array RawCommand
  decoded : Bool
  meaning : Array Int
  accepted : Bool
  deriving FromJson

def signedLiteral (l : OakVerification.Literal) : Int := if l.positive then Int.ofNat l.index else -(Int.ofNat l.index)
def meaning (variables : Nat) (d : Decoded) : Array Int := Id.run do
  let mut out : List Int := [Int.ofNat variables, Int.ofNat d.clauses.length]
  for c in d.clauses do out := out ++ [Int.ofNat c.length] ++ c.map signedLiteral
  out := out ++ [Int.ofNat d.commands.length]
  for cmd in d.commands do
    match cmd with
    | .add id clause hints =>
      out := out ++ [1, Int.ofNat id, Int.ofNat clause.length] ++ clause.map signedLiteral ++
        [Int.ofNat hints.length] ++ hints.map Int.ofNat
    | .delete stamp ids => out := out ++ [0, Int.ofNat stamp, Int.ofNat ids.length] ++ ids.map Int.ofNat
  return out.toArray

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: RangeBridgeCompare CASES.json")
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let cases ← IO.ofExcept (fromJson? json : Except String (Array RangeCase))
  if cases.isEmpty then throw (IO.userError "empty range corpus")
  let mut decoded := 0
  let mut accepted := 0
  for c in cases do
    let commands := c.commands.toList.map fun r => Command.mk r.addition r.id r.start r.count r.refsStart r.refsCount
    let raw : Layout := ⟨c.variables, c.pool.toList, c.starts.toList, c.sizes.toList, c.refs.toList, commands⟩
    let d := decodeLayout raw
    if d.isSome != c.decoded then throw (IO.userError s!"{c.name}: representation decoding differs")
    if let some value := d then
      decoded := decoded + 1
      if meaning c.variables value != c.meaning then throw (IO.userError s!"{c.name}: literal/reference meaning differs")
    let result := checkLayout raw
    if result != c.accepted then throw (IO.userError s!"{c.name}: checker decision differs")
    if result then accepted := accepted + 1
  IO.println s!"Oak/Go/Lean range bridge: {cases.size} layouts ({decoded} decoded, {accepted} accepted, {cases.size - accepted} rejected)"
