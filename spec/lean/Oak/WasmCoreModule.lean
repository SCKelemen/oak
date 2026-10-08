import Oak.WasmCoreBitwiseProjection

/-! Source-pinned, hand-transcribed closed-i32 Core module rules.
The external transcription boundary remains; see spec/wasm-core/README.md.
Unlike the earlier singleton projection, validity below checks an AST with
independent type, function, export, and omitted-section fields. -/
set_option autoImplicit false
namespace Oak.WasmCoreModule
open Oak.BitwiseFunction
open Oak.WasmCoreBitwiseProjection (Instr Typed Step Steps body binop numeric)

/-- Only i32 occurs in this closed type fragment. A list of units represents
an explicit list of i32 value types, not an arbitrary unconstrained type. -/
structure FuncType where
  parameters : List Unit
  results : List Unit
  deriving DecidableEq, Repr

/-- One final, parentless subtype in a singleton recursive group, with a
closed function composite. No reference types or type variables can occur;
roll/closure/substitution therefore leave the represented signature unchanged. -/
inductive ClosedType where
  | recFinalFunc (signature : FuncType)
  deriving DecidableEq, Repr

def expand : ClosedType → FuncType
  | .recFinalFunc signature => signature

/-- Resulttype_ok uses Valtype_ok/num, Numtype_ok/i32 at every position. -/
inductive I32TypesOk : List Unit → Prop where
  | nil : I32TypesOk []
  | cons {rest : List Unit} : I32TypesOk rest → I32TypesOk (()::rest)

inductive FuncTypeOk : FuncType → Prop where
  | intro (parameters results : List Unit) : I32TypesOk parameters → I32TypesOk results →
      FuncTypeOk ⟨parameters,results⟩

/-- Comptype_ok/func, Subtype_ok with no supertype, Rectype_ok singleton,
and Type_ok with a closed roll. Each premise is constructively discharged. -/
inductive ClosedTypeOk : ClosedType → Prop where
  | finalFunc {signature : FuncType} : FuncTypeOk signature →
      ClosedTypeOk (.recFinalFunc signature)

inductive TypesOk : List ClosedType → Prop where
  | nil : TypesOk []
  | cons {dt : ClosedType} {rest : List ClosedType} :
      ClosedTypeOk dt → TypesOk rest → TypesOk (dt::rest)

/-- No type-index occurrences exist inside this closed i32-only type syntax.
This is why rolling/substitution during type allocation is identity here. -/
def freeTypeIndices : ClosedType → List Nat
  | .recFinalFunc _ => []

def substituteTypes (_context : List ClosedType) : ClosedType → ClosedType
  | .recFinalFunc signature => .recFinalFunc signature

theorem closed_type_substitution (context : List ClosedType) (dt : ClosedType) :
    freeTypeIndices dt = [] ∧ substituteTypes context dt = dt := by cases dt <;> exact ⟨rfl,rfl⟩

structure Function where
  typeIndex : Nat
  locals : List Unit
  code : List Instr
  deriving Repr

structure Export where
  name : List UInt8
  functionIndex : Nat
  deriving DecidableEq, Repr

structure Module where
  types : List ClosedType
  functions : List Function
  exports : List Export
  imports : List Nat := []
  tags : List Nat := []
  globals : List Nat := []
  memories : List Nat := []
  tables : List Nat := []
  dataSegments : List Nat := []
  elements : List Nat := []
  start : Option Nat := none

/-- `Func_ok`: type lookup/expansion, initialized i32 parameters/defaultable
locals, empty input stack, and the declared result stack. `Typed` is the
restricted InstrSeq/Expr typing derivation, not equality with the desired body. -/
inductive FunctionOk (types : List ClosedType) : Function → ClosedType → Prop where
  | intro (f : Function) (dt : ClosedType) :
      types[f.typeIndex]? = some dt →
      Typed ((expand dt).parameters.length + f.locals.length) f.code 0
        (expand dt).results.length → FunctionOk types f dt

/-- `Export_ok` and `Externidx_ok/func`, with the actual function index. -/
inductive ExportOk (functionTypes : List ClosedType) : Export → ClosedType → Prop where
  | intro (e : Export) (dt : ClosedType) :
      functionTypes[e.functionIndex]? = some dt → ExportOk functionTypes e dt

inductive Each₂ {A B : Type} (R : A → B → Prop) : List A → List B → Prop where
  | nil : Each₂ R [] []
  | cons {a : A} {b : B} {as : List A} {bs : List B} :
      R a b → Each₂ R as bs → Each₂ R (a::as) (b::bs)

theorem Each₂.length_eq {A B : Type} {R : A → B → Prop} {as : List A} {bs : List B}
    (h : Each₂ R as bs) : as.length = bs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem function_index_valid {types : List ClosedType} {f : Function} {dt : ClosedType}
    (h : FunctionOk types f dt) : f.typeIndex < types.length := by
  cases h with
  | intro lookup _ => exact (List.getElem?_eq_some_iff.mp lookup).1

theorem export_index_valid {types : List ClosedType} {e : Export} {dt : ClosedType}
    (h : ExportOk types e dt) : e.functionIndex < types.length := by
  cases h with
  | intro lookup => exact (List.getElem?_eq_some_iff.mp lookup).1

/-- `Module_ok` specialized to closed function types and absent non-function
sections. Function/export types are derived independently via indexed contexts.
The two Each₂ premises require cardinality matching as well as per-item proofs.
The Ref context consists of the function indices occurring in exports; no other
fragment construct uses references. -/
inductive ModuleOk : Module → List ClosedType → Prop where
  | intro (m : Module) (functionTypes exportTypes : List ClosedType) :
      TypesOk m.types →
      m.imports = [] → m.tags = [] → m.globals = [] → m.memories = [] →
      m.tables = [] → m.dataSegments = [] → m.elements = [] → m.start = none →
      Each₂ (FunctionOk m.types) m.functions functionTypes →
      Each₂ (ExportOk functionTypes) m.exports exportTypes →
      (m.exports.map Export.name).Nodup → ModuleOk m exportTypes

def signature : FuncType := ⟨[(),()], [()]⟩
def closedType : ClosedType := .recFinalFunc signature

theorem closed_type_ok : ClosedTypeOk closedType :=
  .finalFunc (.intro _ _ (.cons (.cons .nil)) (.cons .nil))

def function (op : Op) : Function := ⟨0, [], body op⟩
def module (name : List UInt8) (op : Op) : Module :=
  {types := [closedType], functions := [function op], exports := [⟨name,0⟩]}

theorem function_ok (op : Op) : FunctionOk [closedType] (function op) closedType :=
  .intro _ _ rfl (Oak.WasmCoreBitwiseProjection.body_typed op)

theorem module_ok (name : List UInt8) (op : Op) :
    ModuleOk (module name op) [closedType] := by
  apply ModuleOk.intro (module name op) [closedType] [closedType]
    (.cons closed_type_ok .nil) rfl rfl rfl rfl rfl rfl rfl rfl
  · exact .cons (function_ok op) .nil
  · exact .cons (.intro _ _ rfl) .nil
  · simp [module]

theorem module_cardinality {m : Module} {exportTypes : List ClosedType}
    (h : ModuleOk m exportTypes) :
    ∃ functionTypes : List ClosedType, m.functions.length = functionTypes.length ∧
      m.exports.length = exportTypes.length ∧ (m.exports.map Export.name).Nodup := by
  cases h with
  | intro functionTypes _ _ _ _ _ _ _ _ _ _ funcs exports names =>
    exact ⟨functionTypes, funcs.length_eq, exports.length_eq, names⟩

example (op : Op) (dt : ClosedType) :
    ¬ FunctionOk [closedType] {function op with typeIndex := 1} dt := by
  intro h
  have bound := function_index_valid h
  simp at bound

example (name : List UInt8) (dt : ClosedType) :
    ¬ ExportOk [closedType] ⟨name,1⟩ dt := by
  intro h
  have bound := export_index_valid h
  simp at bound

/-- Instances contain allocated function addresses; source indices are not
silently treated as store addresses. All other module-instance vectors are empty. -/
structure ModuleInstance where
  types : List ClosedType
  functionAddresses : List Nat
  exports : List (List UInt8 × Nat)
  deriving DecidableEq, Repr

structure FunctionInstance where
  type : ClosedType
  moduleInstance : ModuleInstance
  code : Function
  deriving Repr

structure Store where
  functions : List FunctionInstance
  other : List Nat
  deriving Repr

def allocatedInstance (s : Store) (name : List UInt8) : ModuleInstance :=
  ⟨[closedType], [s.functions.length], [(name, s.functions.length)]⟩

def allocatedFunction (s : Store) (name : List UInt8) (op : Op) : FunctionInstance :=
  ⟨closedType, allocatedInstance s name, function op⟩

def allocate (s : Store) (name : List UInt8) (op : Op) : Store :=
  ⟨s.functions ++ [allocatedFunction s name op], s.other⟩

theorem allocated_code_type (s : Store) (name : List UInt8) (op : Op) :
    (allocatedFunction s name op).moduleInstance.types[(allocatedFunction s name op).code.typeIndex]? =
      some (allocatedFunction s name op).type := rfl

/-- `allocexport`/`allocexternidx`: resolve the module's function index through
its address vector. Invalid indices cannot be allocated by this relation. -/
inductive ExportAllocated (inst : ModuleInstance) : Export → (List UInt8 × Nat) → Prop where
  | intro (e : Export) (address : Nat) :
      inst.functionAddresses[e.functionIndex]? = some address →
      ExportAllocated inst e (e.name,address)

/-- Specialization of allocfunc/allocmodule, after the empty allocation vectors
and closed-type substitution have reduced. Records all observable output fields;
the code instance points back to the allocated module, not a dummy instance. -/
inductive Allocation (s : Store) (m : Module) : Store → ModuleInstance → Prop where
  | intro (out : Store) (inst : ModuleInstance) (f : Function) (dt : ClosedType) :
      m.types = [dt] → m.functions = [f] → m.types[f.typeIndex]? = some dt →
      m.imports = [] → m.tags = [] → m.globals = [] → m.memories = [] →
      m.tables = [] → m.dataSegments = [] → m.elements = [] →
      inst.types = m.types → inst.functionAddresses = [s.functions.length] →
      Each₂ (ExportAllocated inst) m.exports inst.exports →
      out.functions = s.functions ++ [⟨dt, inst, f⟩] → out.other = s.other →
      Allocation s m out inst

/-- The no-import/start/data/element fragment instantiates without a pending
initialization instruction. The ModuleOk premise is a derivation, not an axiom. -/
inductive Instantiation (s : Store) (m : Module) : Store → ModuleInstance → List Instr → Prop where
  | intro {out : Store} {inst : ModuleInstance} {exportTypes : List ClosedType} :
      ModuleOk m exportTypes → Allocation s m out inst → m.start = none →
      m.dataSegments = [] → m.elements = [] → Instantiation s m out inst []

theorem instantiate (s : Store) (name : List UInt8) (op : Op) :
    Instantiation s (module name op) (allocate s name op) (allocatedInstance s name) [] := by
  apply Instantiation.intro (module_ok name op)
  · apply Allocation.intro _ _ _ _
    all_goals first | rfl | exact .cons (.intro _ _ rfl) .nil
  all_goals rfl

theorem fresh_function (s : Store) (name : List UInt8) (op : Op) :
    (allocate s name op).functions[s.functions.length]? = some (allocatedFunction s name op) := by
  simp [allocate]

theorem fresh_before (s : Store) : s.functions[s.functions.length]? = none := by simp

theorem preserves_function (s : Store) (name : List UInt8) (op : Op) (i : Nat)
    (h : i < s.functions.length) :
    (allocate s name op).functions[i]? = s.functions[i]? := by
  simp [allocate, List.getElem?_append, h]

theorem preserves_other (s : Store) (name : List UInt8) (op : Op) :
    (allocate s name op).other = s.other := rfl

def exportAddress (inst : ModuleInstance) (name : List UInt8) : Option Nat :=
  (inst.exports.find? (fun e => e.1 = name)).map Prod.snd

theorem export_resolves (s : Store) (name : List UInt8) :
    exportAddress (allocatedInstance s name) name = some s.functions.length := by
  simp [exportAddress, allocatedInstance]

/-- The reference is explicitly non-null. The Null alternative cannot use the
call-ref-func rule. Type matching is an equality of the closed signatures. -/
inductive Reference where
  | null | function (address : Nat)
  deriving DecidableEq, Repr

inductive Configuration where
  | call (arguments : List (BitVec 32)) (reference : Reference) (expected : ClosedType)
  | activation (arity : Nat) (moduleInstance : ModuleInstance)
      (locals : List (BitVec 32)) (instructions : List Instr)
  | result (values : List (BitVec 32))
  deriving Repr

/-- `$invoke`: store lookup, expansion, and exactly one i32 value per parameter.
All arguments have type i32 by construction; no opaque type-check hypothesis. -/
inductive Invoke (s : Store) : Nat → List (BitVec 32) → Configuration → Prop where
  | intro (address : Nat) (args : List (BitVec 32)) (fi : FunctionInstance) :
      s.functions[address]? = some fi →
      args.length = (expand fi.type).parameters.length →
      Invoke s address args (.call args (.function address) fi.type)

/-- `Step/call_ref-func` with its lookup/type/arity premises and initialized
locals, and closure under the previously source-pinned administrative rules.
The store is immutable because this fragment contains no mutating instruction. -/
inductive CallStep (s : Store) : Configuration → Configuration → Prop where
  | callRef (address : Nat) (args : List (BitVec 32)) (expected : ClosedType)
      (fi : FunctionInstance) :
      s.functions[address]? = some fi → fi.type = expected →
      args.length = (expand fi.type).parameters.length →
      CallStep s (.call args (.function address) expected)
        (.activation (expand fi.type).results.length fi.moduleInstance
          (args ++ List.replicate fi.code.locals.length (0#32))
          [.label (expand fi.type).results.length fi.code.code])
  | body {n : Nat} {inst : ModuleInstance} {locals : List (BitVec 32)} {before after : List Instr} :
      Step locals before after →
      CallStep s (.activation n inst locals before) (.activation n inst locals after)
  | frameValues (n : Nat) (inst : ModuleInstance) (locals values : List (BitVec 32)) :
      values.length = n →
      CallStep s (.activation n inst locals (values.map Instr.const)) (.result values)

inductive CallSteps (s : Store) : Configuration → Configuration → Prop where
  | refl (c : Configuration) : CallSteps s c c
  | trans {a b c : Configuration} : CallStep s a b → CallSteps s b c → CallSteps s a c

theorem lift_steps (s : Store) (n : Nat) (inst : ModuleInstance) (locals : List (BitVec 32))
    {before after : List Instr} (h : Steps locals before after) :
    CallSteps s (.activation n inst locals before) (.activation n inst locals after) := by
  induction h with
  | refl _ => exact .refl _
  | trans h _ ih => exact .trans (.body h) ih

theorem CallSteps.append {s : Store} {a b c : Configuration}
    (h : CallSteps s a b) (h' : CallSteps s b c) : CallSteps s a c := by
  induction h with
  | refl _ => exact h'
  | trans step _ ih => exact .trans step (ih h')

/-- External invoke, checked non-null call-ref entry, and complete administrative
return, for every input and every pre-existing store. Only the fresh function is
read, so old store well-formedness is not needed for this restricted derivation. -/
theorem invocation_success (s : Store) (name : List UInt8) (op : Op) (a b : BitVec 32) :
    Invoke (allocate s name op) s.functions.length [a,b]
      (.call [a,b] (.function s.functions.length) closedType) ∧
    CallSteps (allocate s name op)
      (.call [a,b] (.function s.functions.length) closedType)
      (.result [eval op a b]) := by
  constructor
  · exact .intro _ _ _ (fresh_function s name op) rfl
  · apply CallSteps.trans (.callRef _ _ _ _ (fresh_function s name op) rfl rfl)
    have labelSteps := (Oak.WasmCoreBitwiseProjection.body_steps op a b).label 1
    have returned : Steps [a,b] [.label 1 (body op)] [.const (eval op a b)] :=
      labelSteps.append (.trans (.labelValues 1 [eval op a b]) (.refl _))
    exact (lift_steps _ 1 (allocatedInstance s name) [a,b] returned).append
      (.trans (.frameValues 1 _ [a,b] [eval op a b] rfl) (.refl _))

end Oak.WasmCoreModule
