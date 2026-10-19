/- Source-only proposed audit driver. It has not been elaborated or executed.
   Candidate modules are imported from the fresh gate output only. -/
import Oak.Stdlib.BoundedReaderModel
import Oak.Stdlib.APDULengthModel
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Data.Json

set_option autoImplicit false
open Lean Elab Command

namespace APDUGateAudit

def targetModules : Array Name := #[`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.APDULengthModel]
def allowedAxioms : Array Name := #[`propext, `Quot.sound, `Classical.choice]
def forbiddenOracleNames : Array Name := #[`sorryAx, `Lean.trustCompiler,
  `Lean.ofReduceBool, `Lean.ofReduceNat, `Lean.reduceBool, `Lean.reduceNat]

def expected : Array (Name × Name × Bool) := #[
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.data_window_take_iff, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.short_response_bounds, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.extended_response_bounds, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.short_zero_sentinel, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.extended_zero_sentinel, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.shape_unique, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.shape_frame_bound, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.shape_payload_bounds, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.shape_payload_sum_no_u32_wrap, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.layout_consumed, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.layout_response_bounds, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.short_data_sound, true),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.extended_data_sound, true),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.decode_sound, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.decode_of_shape, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.decode_success_iff, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.decode_payload_safe, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.positions_in_bounds, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.positions_count, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.reject_too_long, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.reject_header, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.reject_six_byte_marker, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.reject_extended_zero_lc, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.reject_short_data, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.reject_short_trailing, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.reject_extended_data, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.reject_one_byte_extended_le, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.reject_extended_trailing, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.frame_unchanged, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.rejection_returns_no_command, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.range_fits_iff, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.range_fits_empty_at_end, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.range_fits_offset_past_end, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.range_fits_sum_fits_u32, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.window_ok_iff, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.window_invalid_iff, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.window_ok_bounds, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.remaining_valid, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.remaining_invalid, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.remaining_ok_iff, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.take_ok_iff, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.take_invalid_precedence, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.take_insufficient_iff, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.take_ok_bounds, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.take_ok_fits_u32, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.take_failure_no_rest, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.take_frame_unchanged, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.take_failure_keeps_committed_cursor, false)
]

def jnames (ns : Array Name) : Json := Json.arr (ns.map fun n => Json.str n.toString)

def owner? (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.allImportedModuleNames[idx.toNat]?

def directRefs (ci : ConstantInfo) : Array Name := Id.run do
  let mut refs := ci.type.getUsedConstants
  if let some value := ci.value? (allowOpaque := true) then
    refs := refs ++ value.getUsedConstants
  if let .inductInfo val := ci then
    refs := refs ++ val.ctors.toArray
  return refs.toList.mergeSort Name.lt |>.toArray

def kind (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def emit (value : Json) : CommandElabM Unit :=
  logInfo m!"OAK_APDU_AUDIT {value.compress}"

/-- Independent bounded dependency traversal, in addition to collectAxioms. -/
def reachableAxioms (env : Environment) (root : Name) : CommandElabM (Array Name) := do
  let mut todo := #[root]
  let mut seen : NameSet := {}
  let mut axioms : NameSet := {}
  let mut count := 0
  let mut edges := 0
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    unless seen.contains n do
      count := count + 1
      if count > 10000 then throwError "dependency traversal node cap"
      seen := seen.insert n
      if forbiddenOracleNames.contains n then throwError "forbidden proof oracle: {n}"
      let some ci := env.checked.get.find? n
        | throwError "unresolved checked dependency: {n}"
      if ci.isUnsafe then throwError "unsafe proof dependency: {n}"
      if let .axiomInfo _ := ci then
        unless allowedAxioms.contains n do throwError "unapproved axiom: {n}"
        axioms := axioms.insert n
      let deps := directRefs ci
      edges := edges + deps.size
      if edges > 100000 || todo.size + deps.size > 100000 then
        throwError "per-root dependency edge/pending cap"
      todo := todo ++ deps
  return axioms.toArray.qsort Name.lt

run_cmd do
  let env := (← getEnv).setExporting false
  let imports := env.allImportedModuleNames
  emit <| Json.mkObj [("record", Json.str "imports"), ("modules", jnames imports)]
  let constants := env.checked.get.constants.toList.toArray
  let candidates := constants.filter fun pair =>
    (owner? env pair.1).any (fun m => targetModules.contains m)
  if candidates.isEmpty || candidates.size > 2000 then
    throwError "empty or oversized candidate-owned declaration inventory"
  unless expected.size == 48 do throwError "wrong expected theorem count"
  let mut resolved : Array Name := #[]
  for (moduleName, userName, isPrivate) in expected do
    let theoremMatches := candidates.filter fun pair =>
      privateToUserName pair.1 == userName && owner? env pair.1 == some moduleName
    unless theoremMatches.size == 1 do throwError "missing or duplicate expected theorem: {userName}"
    let (actualName, ci) := theoremMatches[0]!
    unless ci.isTheorem do throwError "expected theorem has another declaration kind: {actualName}"
    unless isPrivateName actualName == isPrivate do throwError "private/public mismatch: {actualName}"
    if resolved.contains actualName then throwError "duplicate theorem resolution: {actualName}"
    resolved := resolved.push actualName
    let builtin ← collectAxioms actualName
    let walked ← reachableAxioms env actualName
    unless builtin.qsort Name.lt == walked do
      throwError "builtin/traversed axiom disagreement: {actualName}"
    emit <| Json.mkObj [("record", Json.str "expected_theorem"),
      ("owner", Json.str moduleName.toString), ("user_name", Json.str userName.toString),
      ("actual_name", Json.str actualName.toString), ("private", Json.bool isPrivate),
      ("axioms", jnames walked), ("direct_dependencies", jnames (directRefs ci))]
  for (n, ci) in candidates do
    if ci.isUnsafe || ci.isPartial then throwError "unsafe/partial candidate declaration: {n}"
    if let .axiomInfo _ := ci then throwError "candidate-owned axiom: {n}"
    let axs ← collectAxioms n
    for ax in axs do
      unless allowedAxioms.contains ax do throwError "unapproved candidate axiom: {n}: {ax}"
    emit <| Json.mkObj [("record", Json.str "candidate_declaration"),
      ("actual_name", Json.str n.toString), ("user_name", Json.str (privateToUserName n).toString),
      ("owner", Json.str ((owner? env n).getD .anonymous).toString),
      ("kind", Json.str (kind ci)), ("axioms", jnames axs),
      ("direct_dependencies", jnames (directRefs ci))]
  let mut todo := candidates.map (·.1)
  let mut seen : NameSet := {}
  let mut nodes := 0
  let mut edges := 0
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    unless seen.contains n do
      nodes := nodes + 1
      if nodes > 10000 then throwError "combined graph node cap"
      seen := seen.insert n
      if forbiddenOracleNames.contains n then throwError "forbidden dependency: {n}"
      let some ci := env.checked.get.find? n | throwError "missing graph dependency: {n}"
      if ci.isUnsafe then throwError "unsafe dependency: {n}"
      if let .axiomInfo _ := ci then
        unless allowedAxioms.contains n do throwError "unapproved graph axiom: {n}"
      let deps := directRefs ci
      edges := edges + deps.size
      if edges > 100000 || todo.size + deps.size > 100000 then
        throwError "combined graph edge/pending cap"
      emit <| Json.mkObj [("record", Json.str "dependency"),
        ("actual_name", Json.str n.toString), ("kind", Json.str (kind ci)),
        ("direct_dependencies", jnames deps)]
      todo := todo ++ deps
  emit <| Json.mkObj [("record", Json.str "complete"),
    ("expected_theorems", toJson resolved.size), ("candidate_declarations", toJson candidates.size),
    ("dependency_nodes", toJson nodes), ("dependency_edges", toJson edges),
    ("anonymous_examples_persisted", Json.bool false),
    ("anonymous_examples_accounted_by_exact_source_compile", toJson (15 : Nat))]

end APDUGateAudit
