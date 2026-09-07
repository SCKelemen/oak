import BooleanSafety
import RUPText
import Lean

/-! Strict, bounded interchange adapter. Its decoded model is the theorem's source. -/
open Lean
namespace OakVerification.BooleanModel
open BooleanCNF BooleanSafety

structure Node where
  op : String
  value : Bool
  index : Nat
  left : Nat
  right : Nat
  deriving FromJson
structure Bundle where
  format : String
  source_sha256 : String
  semantic_digest : String
  fields : Array String
  initial : Array Node
  step : Array Node
  invariant : Array Node
  deriving FromJson

def decodeNode (bound : Nat) (built : Array BooleanCNF.Expr) (n : Node) :
    Except String BooleanCNF.Expr := do
  let child := fun i => match built[i]? with
    | some e => Except.ok e
    | none => Except.error "non-backward child reference"
  match n.op with
  | "bool" => return .constant n.value
  | "var" =>
    if n.index < bound then return .input n.index else throw "input outside field domain"
  | "!" => return .neg (← child n.left)
  | "&&" => return .conj (← child n.left) (← child n.right)
  | "||" => return .disj (← child n.left) (← child n.right)
  | _ => throw "unsupported Boolean operator"

def decodeProgram (bound : Nat) (nodes : Array Node) : Except String BooleanCNF.Expr := do
  if nodes.isEmpty || nodes.size > 4096 then throw "program needs 1..4096 nodes"
  let mut built : Array BooleanCNF.Expr := #[]
  let mut sizes : Array Nat := #[]
  for node in nodes do
    let e ← decodeNode bound built node
    let size := match node.op with
      | "!" => 1 + sizes[node.left]!
      | "&&" | "||" => 1 + sizes[node.left]! + sizes[node.right]!
      | _ => 1
    if size > 4096 then throw "expanded expression exceeds 4096 nodes"
    sizes := sizes.push size
    built := built.push e
  match built.back? with
  | some e => return e
  | none => throw "empty program"

def decodeBundle (b : Bundle) : Except String Model := do
  if b.format != "oak-boolean-model-1" then throw "unsupported bundle format"
  if b.fields.isEmpty || b.fields.size > 6 then throw "model needs 1..6 fields"
  if b.fields.toList.eraseDups.length != b.fields.size then throw "duplicate field"
  if b.fields.any String.isEmpty then throw "empty field name"
  return ⟨← decodeProgram b.fields.size b.initial,
    ← decodeProgram (2*b.fields.size) b.step,
    ← decodeProgram b.fields.size b.invariant⟩

def query (m : Model) (name : String) : Except String BooleanCNF.Expr :=
  match name with
  | "initial" => .ok m.initial
  | "base" => .ok (base m)
  | "step" => .ok (preservation m)
  | _ => .error "query must be initial, base, or step"

def dimacs (e : BooleanCNF.Expr) : String :=
  let f := encode e
  let table := NumberedCNF.atoms f
  let clauses := NumberedCNF.numberCNF table f
  let line := fun c : OakVerification.Clause =>
    String.intercalate " " (c.map (fun l =>
      (if l.positive then "" else "-") ++ toString l.index)) ++ " 0\n"
  s!"p cnf {table.length} {clauses.length}\n" ++ String.join (clauses.map line)

def checkTexts (m : Model) (baseText stepText : String) : Except String Bool := do
  let bp ← Text.parseLRAT baseText
  let sp ← Text.parseLRAT stepText
  return checkSafety m bp sp

theorem checkTexts_sound (m : Model) (bp sp : String)
    (accepted : checkTexts m bp sp = .ok true) :
    ∀ s, Reachable m s → eval s m.invariant = true := by
  unfold checkTexts at accepted
  cases hb : Text.parseLRAT bp with
  | error e => simp [hb] at accepted
  | ok b =>
    cases hs : Text.parseLRAT sp with
    | error e => simp [hb, hs] at accepted
    | ok s =>
      have h : checkSafety m b s = true := by simpa [hb, hs] using accepted
      exact checkSafety_sound m b s h


#print axioms checkTexts_sound
end OakVerification.BooleanModel

open OakVerification.BooleanModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", bundlePath, role, output] =>
    let json ← IO.ofExcept (Json.parse (← IO.FS.readFile bundlePath))
    let b ← IO.ofExcept (fromJson? json : Except String Bundle)
    let m ← IO.ofExcept (decodeBundle b)
    let e ← IO.ofExcept (query m role)
    IO.FS.writeFile output (dimacs e)
    return 0
  | ["check", bundlePath, basePath, stepPath] =>
    let json ← IO.ofExcept (Json.parse (← IO.FS.readFile bundlePath))
    let b ← IO.ofExcept (fromJson? json : Except String Bundle)
    let m ← IO.ofExcept (decodeBundle b)
    let result := checkTexts m (← IO.FS.readFile basePath) (← IO.FS.readFile stepPath)
    let (accepted, stage) := match result with
      | .error _ => (false, "parse")
      | .ok ok => (ok, "check")
    IO.println (Json.mkObj [
      ("format", toJson "oak-boolean-safety-1"), ("accepted", toJson accepted),
      ("scope", toJson "decoded-boolean-model"), ("stage", toJson stage),
      ("source_sha256", toJson b.source_sha256), ("semantic_digest", toJson b.semantic_digest)]).compress
    return if accepted then 0 else 1
  | _ =>
    IO.eprintln "usage: BooleanModel emit BUNDLE initial|base|step CNF | check BUNDLE BASE_LRAT STEP_LRAT"
    return 2
