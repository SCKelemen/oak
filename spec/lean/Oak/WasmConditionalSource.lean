import Oak.BitwiseSourceLowering
import Oak.WasmConditionalExecution

/-! A canonical, independently checked original-source conditional slice.
The byte grammar and typed-expression bridge do not verify the Go parser or
compiler, the full Core specification, or an engine implementation. -/
set_option autoImplicit false
namespace Oak.WasmConditionalSource
open WasmExecution
abbrev Bytes := BitwiseSource.Bytes
open BitwiseSource (ascii identifier)

structure Decl where
  name : Bytes
  first : Bytes
  second : Bytes
  deriving DecidableEq, Repr

/-- Reuse the existing restricted identifier policy, with small explicit name
bounds and no parameter duplicates or function/parameter shadowing. -/
def valid (d : Decl) : Bool :=
  identifier d.name && identifier d.first && identifier d.second &&
    decide (d.first ≠ d.second ∧ d.name ≠ d.first ∧ d.name ≠ d.second ∧
      d.name.length ≤ 64 ∧ d.first.length ≤ 64 ∧ d.second.length ≤ 64)

def render (d : Decl) : Bytes :=
  d.name ++ ascii ": (" ++ d.first ++ ascii ": u32, " ++ d.second ++
  ascii ": u32): u32 = (" ++ d.first ++ ascii " < " ++ d.second ++
  ascii ") ? (" ++ d.first ++ ascii " - " ++ d.second ++
  ascii ") | (" ++ d.second ++ ascii " - " ++ d.first ++ ascii ")\n"

/-- A declarative complete byte grammar, independent of field discovery. -/
inductive Grammar : Bytes → Decl → Prop where
  | function (d : Decl) : valid d = true → Grammar (render d) d

def candidate (source : Bytes) : Option Decl :=
  match ByteFields.splitOn source.dropLast 32 with
  | name :: first :: _ :: second :: _ =>
      some ⟨name.dropLast, (first.drop 1).dropLast, second.dropLast⟩
  | _ => none

/-- Every original byte must equal the independently reconstructed grammar.
Only candidate discovery is allowed to ignore untrusted fields. -/
def parse (source : Bytes) : Option Decl := do
  if source.length > 1024 then none else do
    let d ← candidate source
    if valid d && decide (source = render d) then some d else none

theorem parse_sound {source : Bytes} {d : Decl} (h : parse source = some d) :
    Grammar source d := by
  unfold parse at h
  split at h
  · contradiction
  · cases hc : candidate source with
    | none => simp [hc] at h
    | some parsed =>
      rw [hc] at h
      change (if valid parsed && decide (source = render parsed) then some parsed else none) = some d at h
      split at h
      · rename_i good
        have he : parsed = d := Option.some.inj h
        subst parsed
        have both : valid d = true ∧ source = render d := by simpa using good
        rw [both.2]
        exact .function d both.1
      · contradiction

theorem parse_exact {source : Bytes} {d : Decl} (h : parse source = some d) :
    source = render d := by cases parse_sound h; rfl

open WasmConditionalExecution (result)

def environment (d : Decl) (a b : BitVec 32) (name : Bytes) : Option (BitVec 32) :=
  if name = d.first then some a else if name = d.second then some b else none

def evaluate (d : Decl) (a b : BitVec 32) : Option (BitVec 32) := do
  let x ← environment d a b d.first
  let y ← environment d a b d.second
  some (result x y)

theorem grammar_evaluation {source : Bytes} {d : Decl} (h : Grammar source d)
    (a b : BitVec 32) : evaluate d a b = some (result a b) := by
  cases h with
  | function d good =>
    have distinct : d.first ≠ d.second := (of_decide_eq_true (Bool.and_eq_true_iff.mp good).2).1
    simp [evaluate, environment, Ne.symm distinct]

open LoweringRefinement
open BitwiseSourceLowering (parameters noSpans noLocals inputs)

def arg0 : Expr parameters noSpans noLocals .u32 :=
  .var .u32 "arg0" (by simp [resolve, parameters, noLocals])
def arg1 : Expr parameters noSpans noLocals .u32 :=
  .var .u32 "arg1" (by simp [resolve, parameters, noLocals])

/-- Alpha-renaming follows the two resolved declaration positions. The source
conditional uses existing typed comparison, subtraction and ite constructors. -/
def toExpr (_d : Decl) : Expr parameters noSpans noLocals .u32 :=
  .ite (.cmp .lt arg0 arg1) (.arith .sub arg0 arg1) (.arith .sub arg1 arg0)

theorem typed_meaning (d : Decl) (a b : BitVec 32) (fuel : Nat) :
    evalX (toExpr d) (inputs a b) (fun _ => 0) fuel = some (result a b) := by
  by_cases h : a.toNat < b.toNat <;>
    simp [toExpr, arg0, arg1, evalX, inputs, noLocals, varX, cmpX, arithX, Ty.signed, Ty.width, result, BitVec.ult, h] <;> rfl

theorem grammar_to_existing {source : Bytes} {d : Decl} (h : Grammar source d)
    (a b : BitVec 32) (fuel : Nat) :
    evaluate d a b = evalX (toExpr d) (inputs a b) (fun _ => 0) fuel := by
  rw [grammar_evaluation h a b, typed_meaning]


/-- The export name comes from the checked source declaration; the complete
function table, signature, phi local and all body tokens are checked together. -/
def module (d : Decl) : WasmModule.Module :=
  ⟨WasmConditionalExecution.functions,[⟨d.name,0⟩]⟩

def accepts (source : Bytes) (claim : Decl) (bytes : Bytes) : Bool :=
  parse source == some claim && WasmModule.decode bytes == some (module claim)

/-- Replaying any changed original source against the same claim fails,
including changes that happen to preserve mathematical behavior. -/
theorem refuses_source_replay (source : Bytes) (claim : Decl) (bytes : Bytes)
    (changed : source ≠ render claim) : accepts source claim bytes = false := by
  have refused : parse source ≠ some claim := fun h => changed (parse_exact h)
  simp [accepts, refused]

/-- Source grammar, named source evaluation, the existing typed expression
meaning and complete decoded named-export execution agree for every input.
The original bytes and executable success are checked/derived, not premises. -/
theorem accepted_source_to_export {source bytes : Bytes} {claim : Decl}
    (h : accepts source claim bytes = true) (a b : BitVec 32) (sourceFuel extra : Nat) :
    Grammar source claim ∧
    evaluate claim a b = some (result a b) ∧
    evalX (toExpr claim) (inputs a b) (fun _ => 0) sourceFuel = some (result a b) ∧
    WasmModule.decode bytes = some (module claim) ∧
    WasmModule.invokeExport bytes claim.name (16+extra) [.i32 a,.i32 b] =
      some (.ok ⟨[.i32 (result a b)],#[.i32 a,.i32 b,.i32 (result a b)]⟩) := by
  obtain ⟨hs,hd⟩ := Bool.and_eq_true_iff.mp h
  have parsed : parse source = some claim := by simpa using hs
  have decoded : WasmModule.decode bytes = some (module claim) := by simpa using hd
  have grammar := parse_sound parsed
  refine ⟨grammar,grammar_evaluation grammar a b,typed_meaning claim a b sourceFuel,decoded,?_⟩
  rw [WasmModule.invoke_decoded decoded (e := ⟨claim.name,0⟩) (by simp [module])]
  exact congrArg some (WasmConditionalExecution.invocation_more a b extra)

end Oak.WasmConditionalSource
