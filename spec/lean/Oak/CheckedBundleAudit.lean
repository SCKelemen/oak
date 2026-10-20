import Oak.BitwiseSourceObjectParity
import Lean

/-!
# Fixed audit for the narrow source / Wasm / ARM64 / RV64 bundle

This command is trusted checker code, not a caller-supplied audit script. The
caller supplies only bounded numeric byte lists through the fixed request
renderer. The three theorem types are constructed here from the fixed model,
never from caller text or a caller-provided expected type. This module does not
change a production API or verdict.

`toKernelEnv` waits for asynchronous kernel checking. Root bodies are checked
again with the kernel, not merely found in the elaborator's provisional map.
`collectAxioms` uses imported closure metadata in Lean 4.33.1. Therefore the
compiler, this module, the model, all imported .olean files and their metadata
must come from the controlled installation. `--trust=0` does NOT authenticate or
recheck imported .olean files. Import/source/toolchain custody remains a separate
prerequisite, not something proved by this record or by self-declared hashes.

Exactly one compact JSON record is printed only after every check succeeds.
Diagnostics are never authority: the consumer must additionally require process
exit zero, the exact schema/inventory, and all four byte arrays byte-for-byte.
-/
set_option autoImplicit false
namespace Oak.CheckedBundleAudit
open Lean Elab Command

private def request (field : String) : Name :=
  Name.str `Oak.CheckedBundleRequest field

private def reject {α : Type} (message : String) : CommandElabM α :=
  throwError "checked bundle refused: {message}"

private def closed (name : Name) (e : Expr) : CommandElabM Unit := do
  if e.hasFVar || e.hasMVar || e.hasLooseBVars || e.hasLevelParam then
    reject s!"{name} contains free variables, metavariables, or universe parameters"

private def kernelType (env : Environment) (e : Expr) : CommandElabM Expr := do
  match Kernel.check env {} e with
  | .ok type => pure type
  | .error _ => reject "kernel expression check failed"

private def sameType (env : Environment) (name : Name) (actual expected : Expr) :
    CommandElabM Unit := do
  closed name actual
  closed name expected
  match Kernel.isDefEq env {} actual expected with
  | .ok true => pure ()
  | _ => reject s!"{name} has the wrong exact type or value"

private def requireDefinition (env : Environment) (name : Name) (expected : Expr) :
    CommandElabM DefinitionVal := do
  if (env.getModuleIdxFor? name).isSome then
    reject s!"{name} must be a current-request definition"
  let some (.defnInfo info) := env.toKernelEnv.find? name
    | reject s!"missing definition {name}"
  unless info.levelParams.isEmpty && info.safety == .safe do
    reject s!"{name} must be a safe monomorphic definition"
  closed name info.value
  sameType env name info.type expected
  sameType env name (← kernelType env info.value) expected
  return info

private def requireTheorem (env : Environment) (name : Name) (expected : Expr) :
    CommandElabM Json := do
  if (env.getModuleIdxFor? name).isSome then
    reject s!"{name} must be a current-request theorem"
  let some (.thmInfo info) := env.toKernelEnv.find? name
    | reject s!"missing theorem root {name}"
  unless info.levelParams.isEmpty do
    reject s!"{name} has unexpected universe parameters"
  closed name info.value
  sameType env name info.type expected
  sameType env name (← kernelType env info.value) expected
  let axioms ← collectAxioms name
  for axiomName in axioms do
    unless [``propext, ``Quot.sound, ``Classical.choice].contains axiomName do
      reject s!"{name} depends on forbidden axiom {axiomName}"
  return Json.mkObj [
    ("name", toJson name.toString),
    ("axioms", toJson (axioms.map Name.toString))]

private def reduce (env : Environment) (e : Expr) : CommandElabM Expr := do
  match Kernel.whnf env {} e with
  | .ok value => pure value
  | .error _ => reject "kernel byte reduction failed"

/-- Decode the exact kernel value; no evaluator, native_decide or unsafe cast. -/
private def readBytes (env : Environment) (name : Name) (native : Bool) (limit : Nat) (input : Option Expr := none) :
    CommandElabM Json := do
  let mut rest := input.getD (mkConst name)
  let mut bytes : Array Json := #[]
  for _ in [:limit + 1] do
    let value ← reduce env rest
    if value.isAppOfArity ``List.nil 1 then
      unless !bytes.isEmpty do reject s!"{name} is empty"
      return .arr bytes
    unless value.isAppOfArity ``List.cons 3 do
      reject s!"{name} is not a closed byte list"
    if bytes.size == limit then reject s!"{name} exceeds its byte limit"
    let args := value.getAppArgs
    let byte := args[1]!
    let asNat := if native then
      mkApp2 (mkConst ``BitVec.toNat) (mkNatLit 8) byte
    else mkApp (mkConst ``UInt8.toNat) byte
    let .lit (.natVal n) ← reduce env asNat
      | reject s!"{name} contains a non-numeric byte"
    unless n < 256 do reject s!"{name} contains an out-of-range byte"
    bytes := bytes.push (toJson n)
    rest := args[2]!
  reject s!"{name} exceeds its byte limit"

private def audit : CommandElabM Unit := do
  unless Lean.versionString == "4.33.1" do reject "Lean version must be 4.33.1"
  let env ← getEnv
  unless env.header.trustLevel == 0 do reject "Lean trust level must be zero"
  if debug.skipKernelTC.get (← getOptions) then reject "kernel checking is disabled"
  -- Forces all checking tasks before looking up roots or serializing anything.
  let checked := env.toKernelEnv
  let env := Environment.ofKernelEnv checked
  let uint8 := mkConst ``UInt8
  let bytes := mkApp (mkConst ``List [0]) uint8
  let nativeBytes := mkApp (mkConst ``List [0])
    (mkApp (mkConst ``BitVec) (mkNatLit 8))
  let decl := mkConst ``Oak.BitwiseSource.Decl
  for field in ["source", "wasm"] do
    let _ ← requireDefinition env (request field) bytes
  for field in ["arm", "rv"] do
    let _ ← requireDefinition env (request field) nativeBytes
  let declaration ← requireDefinition env (request "declaration") decl
  let source := mkConst (request "source")
  let wasm := mkConst (request "wasm")
  let arm := mkConst (request "arm")
  let rv := mkConst (request "rv")
  let d := mkConst (request "declaration")
  let emptyBytes := mkApp (mkConst ``List.nil [0]) uint8
  let fallback := mkAppN (mkConst ``Oak.BitwiseSource.Decl.mk)
    #[emptyBytes, emptyBytes, emptyBytes, mkConst ``Oak.BitwiseFunction.Op.and]
  let parsed := mkApp (mkConst ``Oak.BitwiseSource.parse) source
  let expectedDeclaration := mkAppN (mkConst ``Option.getD [0]) #[decl, parsed, fallback]
  sameType env (request "declaration") declaration.value expectedDeclaration
  let check := mkAppN (mkConst ``Oak.BitwiseSourceObjectParity.check)
    #[source, wasm, arm, rv]
  let someD := mkApp2 (mkConst ``Option.some [0]) decl d
  let expectedAdmission := mkApp3 (mkConst ``Eq [1])
    (mkApp (mkConst ``Option [0]) decl) check someD
  let admitted ← requireTheorem env (request "admitted") expectedAdmission
  let arguments := #[source, wasm, arm, rv, d, mkConst (request "admitted")]
  let expectedBinding ← kernelType env <|
    mkAppN (mkConst ``Oak.BitwiseSourceObjectParity.accepted_source_object_binding) arguments
  let binding ← requireTheorem env (request "binding") expectedBinding
  let expectedAllInputs ← kernelType env <|
    mkAppN (mkConst ``Oak.BitwiseSourceObjectParity.accepted_all_input_success) arguments
  let allInputs ← requireTheorem env (request "all_inputs") expectedAllInputs
  let op ← reduce env (mkApp (mkConst ``Oak.BitwiseSource.Decl.op) d)
  let opName ← if op.isConstOf ``Oak.BitwiseFunction.Op.and then pure "and"
    else if op.isConstOf ``Oak.BitwiseFunction.Op.or then pure "or"
    else if op.isConstOf ``Oak.BitwiseFunction.Op.xor then pure "xor"
    else reject "unsupported parsed operation"
  let declarationRecord := Json.mkObj [
    ("name", ← readBytes env (request "declaration") false 2048
      (some (mkApp (mkConst ``Oak.BitwiseSource.Decl.name) d))),
    ("first", ← readBytes env (request "declaration") false 2048
      (some (mkApp (mkConst ``Oak.BitwiseSource.Decl.first) d))),
    ("second", ← readBytes env (request "declaration") false 2048
      (some (mkApp (mkConst ``Oak.BitwiseSource.Decl.second) d))),
    ("op", toJson opName)]
  let record := Json.mkObj [
    ("schema", toJson "oak.checked-bundle.v1"),
    ("profile", toJson "bitwise-source-wasm-arm64-rv64-v1"),
    ("proof_package", toJson "698f6a7b013df508a831d391fe425f4f27cf4581"),
    ("lean_version", toJson Lean.versionString),
    ("source", ← readBytes env (request "source") false 2048),
    ("wasm", ← readBytes env (request "wasm") false 1024),
    ("arm", ← readBytes env (request "arm") true 2048),
    ("rv", ← readBytes env (request "rv") true 2048),
    ("declaration", declarationRecord),
    ("roots", Json.arr #[admitted, binding, allInputs])]
  liftIO <| IO.println record.compress

elab "#oak_checked_bundle_audit" : command => audit
end Oak.CheckedBundleAudit
