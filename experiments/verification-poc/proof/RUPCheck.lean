import RUPText
import Lean

open Lean

def main (args : List String) : IO UInt32 := do
  let [cnfPath, proofPath] := args | do
    IO.eprintln "usage: RUPCheck FORMULA.cnf PROOF.lrat"
    return 2
  let cnf ← IO.FS.readFile cnfPath
  let proof ← IO.FS.readFile proofPath
  let (accepted, stage, message) := match OakVerification.Text.checkText cnf proof with
    | .error reason => (false, "parse", reason)
    | .ok false => (false, "check", "no valid refutation")
    | .ok true => (true, "check", "decoded formula is unsatisfiable")
  IO.println (Json.mkObj [
    ("format", toJson "oak-lean-text-check-1"),
    ("accepted", toJson accepted), ("stage", toJson stage), ("message", toJson message)]).compress
  return if accepted then 0 else 1
