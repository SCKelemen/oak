import NumberedCNF
import RUPText
import Lean

/-! Isolated fixture runner. Checking reconstructs the target CNF from the
expression; it never trusts a solver-supplied DIMACS formula or SAT status. -/
open Lean
open OakVerification.BooleanCNF
open OakVerification.NumberedCNF
abbrev BExpr := OakVerification.BooleanCNF.Expr

structure ProofExample where
  name : String
  expression : BExpr
  validity : Bool
  expectedRefutation : Bool

def equivalent (a b : BExpr) : BExpr := .disj (.conj a b) (.conj (.neg a) (.neg b))
def examples : List ProofExample :=
  let x : BExpr := .input 0
  let y : BExpr := .input 1
  let z : BExpr := .input 2
  let shared : BExpr := .disj x y
  [⟨"false", .constant false, false, true⟩,
   ⟨"contradiction", .conj x (.neg x), false, true⟩,
   ⟨"excluded-middle", .disj x (.neg x), true, true⟩,
   ⟨"de-morgan", equivalent (.neg (.conj x y)) (.disj (.neg x) (.neg y)), true, true⟩,
   ⟨"distributivity", equivalent (.conj x (.disj y z)) (.disj (.conj x y) (.conj x z)), true, true⟩,
   ⟨"shared-contradiction", .conj shared (.neg shared), false, true⟩,
   ⟨"true", .constant true, false, false⟩,
   ⟨"input", x, false, false⟩,
   ⟨"non-tautology", .conj x y, true, false⟩]

def target (fixture : ProofExample) : BExpr :=
  if fixture.validity then .neg fixture.expression else fixture.expression

def dimacs (e : BExpr) : String :=
  let f := encode e
  let table := atoms f
  let clauses := numberCNF table f
  let line := fun c : OakVerification.Clause =>
    String.intercalate " " (c.map (fun l =>
      (if l.positive then "" else "-") ++ toString l.index)) ++ " 0\n"
  s!"p cnf {table.length} {clauses.length}\n" ++ String.join (clauses.map line)

def getExample (name : String) : IO ProofExample :=
  match examples.find? (fun e => e.name == name) with
  | some e => pure e
  | none => throw (IO.userError s!"unknown fixture: {name}")

def checkExample (fixture : ProofExample) (proof : String) : Except String Bool := do
  let commands ← OakVerification.Text.parseLRAT proof
  if fixture.validity then
    return checkValid fixture.expression commands
  else return checkEncoded fixture.expression commands

def main (args : List String) : IO UInt32 := do
  match args with
  | ["list"] =>
    for fixture in examples do
      IO.println s!"{fixture.name}\t{if fixture.expectedRefutation then 20 else 10}"
    return 0
  | ["emit", name, path] =>
    let fixture ← getExample name
    IO.FS.writeFile path (dimacs (target fixture))
    return 0
  | ["check", name, path] =>
    let fixture ← getExample name
    let text ← IO.FS.readFile path
    let (accepted, stage) := match checkExample fixture text with
      | .error _ => (false, "parse")
      | .ok accepted => (accepted, "check")
    IO.println (Json.mkObj [
      ("format", toJson "oak-boolean-proof-1"), ("example", toJson name),
      ("accepted", toJson accepted), ("stage", toJson stage),
      ("claim", toJson (if fixture.validity then "valid" else "unsatisfiable"))]).compress
    return if accepted then 0 else 1
  | _ =>
    IO.eprintln "usage: BooleanProof list | emit NAME CNF | check NAME LRAT"
    return 2
