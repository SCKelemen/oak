import PackedText
import Lean

open Lean OakVerification OakVerification.Ranges
namespace CertificateReplay

deriving instance DecidableEq for Instruction

structure Input where
  cnf : String
  proof : String
  deriving FromJson

-- Test adapter only: preserve literal order, command IDs, and deletion stamps.
def pack (formula : Text.Formula) (instructions : List Instruction) : Layout := Id.run do
  let mut pool := []
  let mut starts := []
  let mut sizes := []
  let mut refs := []
  let mut commands := []
  for clause in formula.clauses do
    starts := starts ++ [pool.length]
    sizes := sizes ++ [clause.length]
    pool := pool ++ clause.map encodeLiteral
  for instruction in instructions do
    match instruction with
    | .add id clause hints =>
      commands := commands ++ [⟨true, id, pool.length, clause.length, refs.length, hints.length⟩]
      pool := pool ++ clause.map encodeLiteral
      refs := refs ++ hints
    | .delete stamp ids =>
      commands := commands ++ [⟨false, stamp, 0, 0, refs.length, ids.length⟩]
      refs := refs ++ ids
  return ⟨formula.variables, pool, starts, sizes, refs, commands⟩

def pack (formula : Text.Formula) (instructions : List Instruction) : Layout :=
  ProofPacking.pack formula.variables formula.clauses instructions

deriving instance DecidableEq for Command
deriving instance DecidableEq for Layout

def layoutJSON (name : String) (raw : Layout) (accepted : Bool) : Json :=
  Json.mkObj [
    ("name", toJson name), ("variables", toJson raw.variables),
    ("pool", toJson raw.pool), ("starts", toJson raw.starts), ("sizes", toJson raw.sizes),
    ("refs", toJson raw.refs), ("accepted", toJson accepted),
    ("commands", toJson (raw.commands.map fun c => Json.mkObj [
      ("addition", toJson c.addition), ("id", toJson c.id), ("start", toJson c.start),
      ("count", toJson c.count), ("refsStart", toJson c.refsStart), ("refsCount", toJson c.refsCount)]))]

def checkCase (name : String) (raw : Layout) (expected : Bool) : IO Json := do
  if CertifiedStream.check raw != expected then
    throw (IO.userError s!"{name}: certified stream differs from expected {expected}")
  if InitialDecoder.check raw != expected then
    throw (IO.userError s!"{name}: decoder composition differs")
  if checkLayout raw != expected then
    throw (IO.userError s!"{name}: original stream differs")
  return layoutJSON name raw expected

end CertificateReplay
open CertificateReplay

def main (args : List String) : IO Unit := do
  let [manifest, output, report] := args |
    throw (IO.userError "usage: CertificateReplay MANIFEST.json CASES.json REPORT.json")
  -- A failure cannot leave a previous success report behind.
  IO.FS.writeFile report "{\"format\":\"oak-certified-replay-1\",\"passed\":false}\n"
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile manifest))
  let inputs ← IO.ofExcept (fromJson? json : Except String (Array Input))
  if inputs.isEmpty then throw (IO.userError "empty certificate manifest")
  let mut cases : Array Json := #[]
  let mut results : Array Json := #[]
  let mut accepted := 0
  for input in inputs do
    let cnfText ← IO.FS.readFile input.cnf
    let proofText ← IO.FS.readFile input.proof
    let formula ← IO.ofExcept (Text.parseDIMACS cnfText)
    let instructions ← IO.ofExcept (Text.parseLRAT proofText)
    let raw := pack formula instructions
    if !(decide (raw = packReference formula instructions)) then
      throw (IO.userError s!"{input.cnf}: proved and reference packing differ")
    match decodeLayout raw with
    | none =>
      results := results.push (Json.mkObj [
        ("cnf", toJson input.cnf), ("proof", toJson input.proof),
        ("status", toJson "outside-bounded-profile"), ("layout", layoutJSON "excluded" raw false)])
    | some decoded =>
      if !(decide (decoded.clauses = formula.clauses ∧ decoded.commands = instructions)) then
        throw (IO.userError s!"{input.cnf}: packing changed decoded formula or commands")
      if !(ProofPacking.check formula.variables formula.clauses instructions) then
        throw (IO.userError s!"{input.cnf}: certified packing composition rejected")
      if (PackedText.check cnfText proofText) != .ok true then
        throw (IO.userError s!"{input.cnf}: packed text composition rejected")
      if (PackedText.check s!"p cnf {formula.variables} 1\n1 0\n" proofText) != .ok false then
        throw (IO.userError s!"{input.cnf}: packed text accepted wrong formula")
      if (PackedText.check cnfText (proofText ++ "\n1 0 0\n")) != .ok false then
        throw (IO.userError s!"{input.cnf}: packed text accepted invalid suffix")
      cases := cases.push (← checkCase input.cnf raw true)
      -- Keep the variable domain while replacing the database by a SAT unit.
      let wrong := pack ⟨formula.variables, [[⟨1, true⟩]]⟩ instructions
      cases := cases.push (← checkCase (input.cnf ++ "-wrong-formula") wrong false)
      -- Always within the ID profile: reusing an initial ID must reject even
      -- after a refutation. No resource guard can explain this rejection.
      let suffix := pack formula (instructions ++ [.add 1 [] []])
      if (decodeLayout suffix).isNone then
        throw (IO.userError s!"{input.cnf}: suffix mutation exceeds profile")
      cases := cases.push (← checkCase (input.cnf ++ "-invalid-suffix") suffix false)
      accepted := accepted + 1
      results := results.push (Json.mkObj [
        ("cnf", toJson input.cnf), ("proof", toJson input.proof), ("status", toJson "replayed"),
        ("accepted", toJson true), ("wrong_formula_rejected", toJson true),
        ("invalid_suffix_rejected", toJson true), ("packing_roundtrip", toJson true)])
  if accepted = 0 then throw (IO.userError "no actual certificates fit the bounded profile")
  IO.FS.writeFile output ((toJson cases).pretty ++ "\n")
  IO.FS.writeFile report ((Json.mkObj [
    ("format", toJson "oak-certified-replay-1"), ("passed", toJson true),
    ("certificates", toJson accepted), ("rejection_checks", toJson (accepted * 2)),
    ("outside_profile", toJson (inputs.size - accepted)), ("results", toJson results)]).pretty ++ "\n")
  IO.println s!"Certified real-certificate replay: {accepted} accepted, {accepted * 2} rejected corruptions, {inputs.size - accepted} outside profile"
