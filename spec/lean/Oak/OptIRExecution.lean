import Oak.StatefulCopy

/-!
# Execution of the closed raw OptIR vocabulary

These records retain the production CFG fields, not a replacement copy IR.
`step` fetches ordinary operations and CFG edges from the supplied program;
`call` enters the named graph with a separate SSA environment and shared byte
memory. Unknown instructions, bad arities/types, invalid accesses and inactive
payload projections fault. Exhaustion is distinct from both a fault and the
ordinary `DestinationTooSmall` value.

Effects, facts and source identities are retained but have no dynamic meaning.
A separate closed profile and exact snapshot transport check must admit them.
No optimizer, frontend, serialization, target ABI or instruction-set theorem is
implied by the execution definitions.
-/
namespace Oak.OptIRExecution

open Oak.StatefulCopy Oak.Stdlib.Bytes

structure Source where
  context : String := ""
  line : Nat := 0
  column : Nat := 0
  deriving DecidableEq, Repr
structure ValueDef where
  id : Nat
  ty : String
  name : String := ""
  source : Source := {}
  deriving DecidableEq, Repr
structure Attribute where
  name : String
  value : String
  deriving DecidableEq, Repr
structure Fact where
  id : String
  name : String
  values : List Nat
  provenance : String
  witness : String
  scope : String
  dependencies : List String
  deriving DecidableEq, Repr
structure Operation where
  code : String
  results : List ValueDef := []
  operands : List Nat := []
  effects : List String := []
  attributes : List Attribute := []
  facts : List Fact := []
  source : Source := {}
  memoryAccessID : String := ""
  memoryCallID : String := ""
  deriving DecidableEq, Repr
structure Edge where
  target : Nat := 0
  arguments : List Nat := []
  deriving DecidableEq, Repr
structure Terminator where
  kind : String
  condition : Nat := 0
  trueEdge : Edge := {}
  falseEdge : Edge := {}
  values : List Nat := []
  deriving DecidableEq, Repr
structure Block where
  id : Nat
  parameters : List ValueDef := []
  operations : List Operation := []
  terminator : Terminator
  deriving DecidableEq, Repr
structure CFG where
  name : String
  entry : Nat
  results : List String
  blocks : List Block
  facts : List Fact := []
  deriving DecidableEq, Repr
abbrev Program := List CFG

inductive Value where
  | u8 (value : UInt8)
  | u32 (value : UInt32)
  | bool (value : Bool)
  | unit
  | view (value : ByteView)
  | span (value : ByteView)
  | copyError (value : CopyError)
  | result (value : Result_u32_CopyError)
  deriving DecidableEq, Repr

def Value.type : Value → String
  | .u8 _ => "u8"
  | .u32 _ => "u32"
  | .bool _ => "Bool"
  | .unit => "()"
  | .view _ => "[]u8"
  | .span _ => "[*]u8"
  | .copyError _ => "bytes__CopyError"
  | .result _ => "Result_u32_bytes__CopyError"

abbrev Env := Nat → Option Value

def emptyEnv : Env := fun _ => none

def Env.set (env : Env) (id : Nat) (value : Value) : Env :=
  fun other => if other = id then some value else env other

@[simp] theorem Env.set_same (env : Env) (id : Nat) (value : Value) :
    (env.set id value) id = some value := by simp [Env.set]
@[simp] theorem Env.set_other (env : Env) (id other : Nat) (value : Value)
    (h : other ≠ id) : (env.set id value) other = env other := by simp [Env.set, h]

def readValues (env : Env) : List Nat → Option (List Value)
  | [] => some []
  | id :: ids => do
    let v ← env id
    let vs ← readValues env ids
    pure (v :: vs)

def bindValues (env : Env) : List ValueDef → List Value → Option Env
  | [], [] => some env
  | d :: ds, v :: vs =>
    if d.ty = v.type then bindValues (env.set d.id v) ds vs else none
  | _, _ => none

structure World where
  allocs : Allocations
  bits : Nat
  permissions : Permissions

/-- Dynamic descriptor validity retains owner identity, not only a raw base. -/
def Live (world : World) (v : ByteView) : Prop :=
  ∃ a, world.allocs v.owner = some a ∧ a.base = v.ownerBase ∧
    v.window.start + v.window.len ≤ a.size ∧ v.window.len < 2 ^ 32 ∧
    v.ownerBase + a.size < 2 ^ world.bits

noncomputable def loadByte (world : World) (mem : Memory) (v : ByteView)
    (index : UInt32) : Option UInt8 := by
  classical
  exact if Live world v ∧ index.toNat < v.window.len ∧
      world.permissions.readable (v.base + index.toNat)
    then mem (v.base + index.toNat) else none

/-- One-byte update, independent of every copy algorithm. -/
def writeByte (mem : Memory) (address : Nat) (byte : UInt8) : Memory :=
  fun other => if other = address then some byte else mem other

noncomputable def storeByte (world : World) (mem : Memory) (v : ByteView)
    (index : UInt32) (byte : UInt8) : Option Memory := by
  classical
  exact if Live world v ∧ index.toNat < v.window.len ∧
      world.permissions.exclusiveWrite (v.base + index.toNat) ∧
      (mem (v.base + index.toNat)).isSome
    then some (writeByte mem (v.base + index.toNat) byte) else none

@[simp] theorem writeByte_same (mem : Memory) (a : Nat) (byte : UInt8) :
    writeByte mem a byte a = some byte := by simp [writeByte]

theorem writeByte_other (mem : Memory) (a other : Nat) (byte : UInt8)
    (h : other ≠ a) : writeByte mem a byte other = mem other := by
  simp [writeByte, h]

theorem represented_live {allocs : Allocations} {bits : Nat} {permissions : Permissions}
    {mem : Memory} {v : ByteView} {backing : Array UInt8}
    (h : RepresentsWindow allocs bits mem v backing) :
    Live ⟨allocs, bits, permissions⟩ v :=
  ⟨⟨v.ownerBase, backing.size⟩, h.live, rfl, h.bounds, h.length, h.endpoint⟩

/-- Reading a represented window agrees with the existing logical projection. -/
theorem byte_read_refines {allocs : Allocations} {bits : Nat} {permissions : Permissions}
    {mem : Memory} {v : ByteView} {backing : Array UInt8}
    (h : RepresentsWindow allocs bits mem v backing) (index : UInt32)
    (hi : index.toNat < v.window.len)
    (hp : permissions.readable (v.base + index.toNat)) :
    loadByte ⟨allocs,bits,permissions⟩ mem v index =
      some ((logical backing v).getD index.toNat 0) := by
  classical
  simp only [loadByte, represented_live h, hi, hp, and_self, ↓reduceIte]
  exact represented_read h index.toNat hi

/-- Checked byte stores never rely on a total-memory default. -/
theorem byte_store_refines {allocs : Allocations} {bits : Nat} {permissions : Permissions}
    {mem : Memory} {v : ByteView} {backing : Array UInt8}
    (h : RepresentsWindow allocs bits mem v backing) (index : UInt32) (byte : UInt8)
    (hi : index.toNat < v.window.len)
    (hp : permissions.exclusiveWrite (v.base + index.toNat)) :
    storeByte ⟨allocs,bits,permissions⟩ mem v index byte =
      some (writeByte mem (v.base + index.toNat) byte) := by
  classical
  simp [storeByte, represented_live h, hi, hp, represented_read h index.toNat hi]

/-- Constructor-wise logical Result transport is exact; this is not the
physical ABI's still-open decode premise. -/
theorem result_value_exact (r : Result_u32_CopyError) :
    decodeResult (encodeResult r) = some r := decode_encode r

/-- Canonical nonnegative integer attribute interpretation. This small total
reader avoids relying on any external/native evaluation oracle in proofs. -/
def decimalDigits : List Char → Nat → Option Nat
  | [], n => some n
  | c::cs, n =>
    if '0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat then
      decimalDigits cs (10*n + (c.toNat-'0'.toNat)) else none

def decimal (text : String) : Option Nat :=
  if text.toList.isEmpty then none else decimalDigits text.toList 0

/-- Non-call operations. Calls are dispatched by `step` to the actual graph. -/
noncomputable def evalOperation (world : World) (mem : Memory)
    (op : Operation) (args : List Value) : Option (List Value × Memory) := do
  match op.code, args, op.attributes, op.results with
  | "const.integer", [], [⟨"value", text⟩], [r] =>
    let n ← decimal text
    if r.ty = "u32" ∧ n < 2^32 then pure ([.u32 n.toUInt32],mem)
    else if r.ty = "u8" ∧ n < 256 then pure ([.u8 n.toUInt8],mem) else none
  | "const.bool", [], [⟨"value", "true"⟩], [_] => pure ([.bool true],mem)
  | "const.bool", [], [⟨"value", "false"⟩], [_] => pure ([.bool false],mem)
  | "const.unit", [], [], [_] => pure ([.unit],mem)
  | "descriptor.length", [.view v], [], [_]
  | "descriptor.length", [.span v], [], [_] =>
    if v.window.len < 2^32 then pure ([.u32 v.window.len.toUInt32],mem) else none
  | "integer.add", [.u32 a,.u32 b], [], [_] => pure ([.u32 (a+b)],mem)
  | "compare.less", [.u32 a,.u32 b], [], [_] => pure ([.bool (decide (a<b))],mem)
  | "compare.equal", [.u32 a,.u32 b], [], [_] => pure ([.bool (decide (a=b))],mem)
  | "memory.byte-load", [.view v,.u32 index], [], [_]
  | "memory.byte-load", [.span v,.u32 index], [], [_] =>
    let byte ← loadByte world mem v index
    pure ([.u8 byte],mem)
  | "memory.byte-store", [.span v,.u32 index,.u8 byte], [], [] =>
    let mem ← storeByte world mem v index byte
    pure ([],mem)
  | "adt.construct", [], [⟨"variant", "bytes__CopyError.DestinationTooSmall"⟩], [_] =>
    pure ([.copyError .DestinationTooSmall],mem)
  | "adt.construct", [.u32 count], [⟨"variant", "Result_u32_bytes__CopyError.Ok"⟩], [_] =>
    pure ([.result (.Ok count)],mem)
  | "adt.construct", [.copyError error], [⟨"variant", "Result_u32_bytes__CopyError.Err"⟩], [_] =>
    pure ([.result (.Err error)],mem)
  | "adt.is-variant", [.result (.Ok _)], [⟨"variant", "Result_u32_bytes__CopyError.Ok"⟩], [_]
  | "adt.is-variant", [.result (.Err _)], [⟨"variant", "Result_u32_bytes__CopyError.Err"⟩], [_] =>
    pure ([.bool true],mem)
  | "adt.is-variant", [.result (.Err _)], [⟨"variant", "Result_u32_bytes__CopyError.Ok"⟩], [_]
  | "adt.is-variant", [.result (.Ok _)], [⟨"variant", "Result_u32_bytes__CopyError.Err"⟩], [_] =>
    pure ([.bool false],mem)
  | "adt.payload", [.result (.Ok count)], [⟨"variant", "Result_u32_bytes__CopyError.Ok"⟩], [_] =>
    pure ([.u32 count],mem)
  | "adt.payload", [.result (.Err error)], [⟨"variant", "Result_u32_bytes__CopyError.Err"⟩], [_] =>
    pure ([.copyError error],mem)
  | _, _, _, _ => none

structure Frame where
  function : CFG
  block : Nat
  pc : Nat
  env : Env
structure Continuation where
  caller : Frame
  results : List ValueDef
structure State where
  mem : Memory
  frame : Frame
  stack : List Continuation

inductive StepResult where
  | next (state : State)
  | returned (values : List Value) (mem : Memory)
  | fault

inductive Outcome where
  | returned (values : List Value) (mem : Memory)
  | fault
  | exhausted

def findFunction (program : Program) (name : String) : Option CFG :=
  program.find? (fun cfg => cfg.name == name)
def findBlock (cfg : CFG) (id : Nat) : Option Block :=
  cfg.blocks.find? (fun block => block.id == id)

def enter (cfg : CFG) (args : List Value) : Option Frame := do
  let block ← findBlock cfg cfg.entry
  let env ← bindValues emptyEnv block.parameters args
  pure ⟨cfg,cfg.entry,0,env⟩

def branch (frame : Frame) (edge : Edge) : Option Frame := do
  let block ← findBlock frame.function edge.target
  let args ← readValues frame.env edge.arguments
  let env ← bindValues frame.env block.parameters args
  pure ⟨frame.function,edge.target,0,env⟩

noncomputable def step (world : World) (program : Program) (state : State) : StepResult :=
  match findBlock state.frame.function state.frame.block with
  | none => .fault
  | some block =>
    match block.operations[state.frame.pc]? with
    | some op =>
      match readValues state.frame.env op.operands with
      | none => .fault
      | some args =>
        if op.code = "call" then
          match op.attributes with
          | [⟨"callee",name⟩] =>
            match findFunction program name with
            | none => .fault
            | some cfg =>
              match enter cfg args with
              | none => .fault
              | some frame => .next ⟨state.mem,frame,
                  ⟨{state.frame with pc := state.frame.pc+1},op.results⟩::state.stack⟩
          | _ => .fault
        else
          match evalOperation world state.mem op args with
          | none => .fault
          | some (values,mem) =>
            match bindValues state.frame.env op.results values with
            | none => .fault
            | some env => .next ⟨mem,{state.frame with pc:=state.frame.pc+1,env:=env},state.stack⟩
    | none =>
      if state.frame.pc ≠ block.operations.length then .fault else
      match block.terminator.kind with
      | "return" =>
        match readValues state.frame.env block.terminator.values with
        | none => .fault
        | some values =>
          match state.stack with
          | [] => .returned values state.mem
          | continuation::stack =>
            match bindValues continuation.caller.env continuation.results values with
            | none => .fault
            | some env => .next ⟨state.mem,{continuation.caller with env:=env},stack⟩
      | "branch" =>
        match branch state.frame block.terminator.trueEdge with
        | none => .fault
        | some frame => .next ⟨state.mem,frame,state.stack⟩
      | "cond-branch" =>
        match state.frame.env block.terminator.condition with
        | some (.bool condition) =>
          match branch state.frame (if condition then block.terminator.trueEdge else block.terminator.falseEdge) with
          | none => .fault
          | some frame => .next ⟨state.mem,frame,state.stack⟩
        | _ => .fault
      | _ => .fault

noncomputable def run (world : World) (program : Program) : Nat → State → Outcome
  | 0, _ => .exhausted
  | fuel+1, state => match step world program state with
    | .next state => run world program fuel state
    | .returned values mem => .returned values mem
    | .fault => .fault

noncomputable def execute (world : World) (program : Program) (root : String)
    (args : List Value) (mem : Memory) (fuel : Nat) : Outcome :=
  match findFunction program root with
  | none => .fault
  | some cfg => match enter cfg args with
    | none => .fault
    | some frame => run world program fuel ⟨mem,frame,[]⟩

/-- Every successful path persists under larger IR fuel. -/
theorem run_more (world : World) (program : Program) (fuel : Nat) :
    ∀ state values mem extra,
      run world program fuel state = .returned values mem →
      run world program (fuel+extra) state = .returned values mem := by
  induction fuel with
  | zero => intro state values mem extra h; cases h
  | succ fuel ih =>
    intro state values mem extra h
    simp only [run] at h
    cases hs : step world program state with
    | next next =>
      simp only [hs] at h
      simpa only [Nat.succ_add,run,hs] using ih next values mem extra h
    | returned vs memory =>
      simpa only [Nat.succ_add,run,hs] using h
    | fault => simp only [hs] at h; cases h

end Oak.OptIRExecution

namespace Oak.OptIRExecution

/-- Exactly `steps` ordinary machine transitions, stopping before any final
return. This is a generic CFG execution prefix, not a copy evaluator. -/
noncomputable def advance (world : World) (program : Program) : Nat → State → Option State
  | 0, state => some state
  | n+1, state => match step world program state with
    | .next next => advance world program n next
    | _ => none

theorem advance_run (world : World) (program : Program) (n : Nat) :
    ∀ before after fuel, advance world program n before = some after →
      run world program (n+fuel) before = run world program fuel after := by
  induction n with
  | zero => intro before after fuel h; cases h; simp
  | succ n ih =>
    intro before after fuel h
    simp only [advance] at h
    cases hs : step world program before with
    | next next =>
      simp only [hs] at h
      simpa only [Nat.succ_add,run,hs] using ih next after fuel h
    | returned _ _ => simp only [hs] at h; cases h
    | fault => simp only [hs] at h; cases h

theorem advance_add (world : World) (program : Program) (n : Nat) :
    ∀ state m, advance world program (n+m) state =
      (advance world program n state).bind (advance world program m) := by
  induction n with
  | zero => intro state m; simp [advance]
  | succ n ih =>
    intro state m
    simp only [Nat.succ_add, advance]
    cases step world program state <;> simp [ih]

end Oak.OptIRExecution
