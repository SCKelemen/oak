import Oak.WasmControl

/-! Direct calls in a closed table of defined scalar functions. Parameters and
results use declaration order; operand stacks use top-first order. Imports,
module instantiation and validator soundness remain outside this model. -/
namespace Oak.WasmCalls
open WasmExecution

structure Function where
  params : List Width := []
  results : List Width := []
  locals : List Width := []
  body : List WasmControl.Token := []
  deriving DecidableEq, Repr

structure Machine where
  active : WasmControl.Machine
  callers : List WasmControl.Machine := []
  deriving DecidableEq, Repr

inductive Error where
  | control (reason : WasmControl.Error)
  | functionOutOfBounds
  deriving DecidableEq, Repr

def zero : Width → Value | .w32 => .i32 0 | .w64 => .i64 0

/-- Pop arguments in reverse declaration order and initialize fresh locals.
The callee cannot see caller operands, labels, or locals. -/
def activate (f : Function) (stack : List Value) : Except Error WasmControl.Machine := do
  let args ← (WasmControl.takeResults f.params.reverse stack).mapError Error.control
  if (WasmInstruction.assemble f.body).isNone then .error (.control (.scalar .malformed))
  else if !WasmControl.nested f.body [] then .error (.control .malformedControl)
  else .ok ⟨⟨[], (args.reverse ++ f.locals.map zero).toArray⟩, f.body,
    [⟨.function, f.results.reverse, [], [], []⟩]⟩

/-- Save the caller after consuming arguments; its code is already past call. -/
def call (functions : Array Function) (index : Nat) (m : Machine) : Except Error Machine := do
  let some f := functions[index]? | .error .functionOutOfBounds
  let callee ← activate f m.active.state.stack
  let caller := {m.active with state := {m.active.state with stack := m.active.state.stack.drop f.params.length}}
  .ok ⟨callee, caller :: m.callers⟩

/-- Return values precede suspended operands; caller locals and labels are
restored exactly. The active control machine has checked the result signature. -/
def resume (m : Machine) : Machine :=
  match m.callers with
  | [] => m
  | caller :: outer =>
    ⟨{caller with state := {caller.state with stack := m.active.state.stack ++ caller.state.stack}}, outer⟩

def done (m : Machine) : Bool := WasmControl.done m.active && m.callers.isEmpty

def tick (functions : Array Function) (m : Machine) : Except Error Machine :=
  if WasmControl.done m.active then .ok (resume m)
  else match m.active.code with
    | (16, index) :: rest =>
      if (WasmInstruction.encode 16 index).isNone then .error (.control (.scalar .malformed))
      else call functions index.toNat {m with active := {m.active with code := rest}}
    | _ => do
      let next ← (WasmControl.tick m.active).mapError Error.control
      .ok {m with active := next}

def run (functions : Array Function) : Nat → Machine → Except Error State
  | 0, m => if done m then .ok m.active.state else .error (.control .exhausted)
  | n+1, m => if done m then .ok m.active.state else do run functions n (← tick functions m)

/-- External arguments are in declaration order and must match exactly. -/
def invoke (functions : Array Function) (index fuel : Nat) (args : List Value) : Except Error State := do
  let some f := functions[index]? | .error .functionOutOfBounds
  if args.map Value.width ≠ f.params then .error (.control (.scalar .typeMismatch))
  else
    let active ← activate f args.reverse
    run functions fuel ⟨active, []⟩

/-- Decode a body, retaining its caller-supplied signature/local metadata. -/
def decodeFunction (metadata : Function) (count : Nat) (bytes : List UInt8) :
    Option (Function × List UInt8) := do
  let (body, suffix) ← WasmInstruction.decodeMany count bytes
  some ({metadata with body := body}, suffix)

theorem decodeFunction_assemble (f : Function) {bytes}
    (h : WasmInstruction.assemble f.body = some bytes) (suffix : List UInt8) :
    decodeFunction f f.body.length (bytes ++ suffix) = some (f, suffix) := by
  simp [decodeFunction, WasmInstruction.decode_assemble h suffix]

/-- Decoding assembled body bytes preserves whole-table invocation, including
nested calls and recursion at any runtime fuel. -/
theorem decoded_invocation (functions : Array Function) (slot entry fuel : Nat)
    (f : Function) (args : List Value) {bytes} (suffix : List UInt8)
    (h : WasmInstruction.assemble f.body = some bytes) (_hslot : slot < functions.size) :
    (decodeFunction f f.body.length (bytes ++ suffix)).map (fun decoded =>
      invoke (functions.setIfInBounds slot decoded.1) entry fuel args) =
      some (invoke (functions.setIfInBounds slot f) entry fuel args) := by
  rw [decodeFunction_assemble f h suffix]; rfl

/-- Actual extracted assembler output decodes to the intended function body.
Metadata is supplied separately; this is not module parser/instantiator proof. -/
theorem assembled_function (dst out : Array UInt8) (offset : UInt32)
    (plan : Array WasmAssembler.WasmInstruction) (bytes : List UInt8) (asmFuel : Nat)
    (result : WasmAssembler.WasmAssembly) (metadata : Function)
    (hp : plan.size < 2^32) (hd : dst.size < 2^32)
    (he : WasmAssembler.instructionSequence plan.toList = some bytes)
    (hfit : offset.toNat + bytes.length ≤ dst.size) (hf : plan.size + 11 ≤ asmFuel)
    (hw : WasmAssembler.wasm_assemble dst offset plan asmFuel = some (result, out)) :
    decodeFunction metadata plan.size (out.toList.drop offset.toNat) =
      some ({metadata with body := plan.toList.map fun ins => (ins.opcode.toUInt8, ins.immediate.toInt)},
        dst.toList.drop (offset.toNat + bytes.length)) := by
  rw [WasmAssembler.assemble_admitted_exact _ _ _ _ _ hp hd he hfit hf] at hw
  cases hw
  rw [WasmAssembler.writeBytes_suffix _ _ _ hfit]
  have h := WasmInstruction.decode_assemble (WasmAssembler.instructionSequence_model he)
    (dst.toList.drop (offset.toNat + bytes.length))
  simp only [List.length_map, Array.length_toList] at h
  unfold decodeFunction
  rw [h]
  rfl

/-- Correct argument order, fresh zero locals and an isolated function label. -/
theorem activate_arguments (f : Function) (args junk : List Value)
    (ht : args.map Value.width = f.params)
    (he : (WasmInstruction.assemble f.body).isNone = false)
    (hn : WasmControl.nested f.body [] = true) :
    activate f (args.reverse ++ junk) = .ok
      ⟨⟨[], (args ++ f.locals.map zero).toArray⟩, f.body,
        [⟨.function, f.results.reverse, [], [], []⟩]⟩ := by
  have ht' : f.params.reverse = args.reverse.map Value.width := by simp [← ht]
  have ha : WasmControl.takeResults f.params.reverse (args.reverse ++ junk) = .ok args.reverse := by
    rw [ht']
    exact WasmControl.takeResults_prefix _ _
  simp [activate, ha, he, hn, bind, Except.bind, Except.mapError]

/-- Calls consume precisely the parameter prefix and suspend the remaining
caller state, independently of callee body, inner labels, and outer callers. -/
theorem call_arguments (functions : Array Function) (index : Nat) (f : Function)
    (caller : WasmControl.Machine) (outer : List WasmControl.Machine)
    (args junk : List Value) (hl : functions[index]? = some f)
    (hs : caller.state.stack = args.reverse ++ junk)
    (ht : args.map Value.width = f.params)
    (he : (WasmInstruction.assemble f.body).isNone = false)
    (hn : WasmControl.nested f.body [] = true) :
    call functions index ⟨caller, outer⟩ = .ok
      ⟨⟨⟨[], (args ++ f.locals.map zero).toArray⟩, f.body,
          [⟨.function, f.results.reverse, [], [], []⟩]⟩,
        {caller with state := {caller.state with stack := junk}} :: outer⟩ := by
  have ha := activate_arguments f args junk ht he hn
  have hlen : f.params.length = args.reverse.length := by simp [← ht]
  simp [call, hl, hs, ha, hlen, bind, Except.bind]

/-- Callee-local writes and labels cannot leak into the resumed caller. -/
theorem resume_caller (callee caller : WasmControl.Machine) (outer : List WasmControl.Machine) :
    resume ⟨callee, caller :: outer⟩ =
      ⟨{caller with state := {caller.state with stack := callee.state.stack ++ caller.state.stack}}, outer⟩ := rfl

theorem run_more (functions : Array Function) {n m s}
    (h : run functions n m = .ok s) (extra : Nat) : run functions (n+extra) m = .ok s := by
  induction n generalizing m with
  | zero =>
    simp only [run] at h
    split at h
    · rename_i hd; cases extra <;> simpa [run, hd] using h
    · contradiction
  | succ n ih =>
    simp only [run] at h
    split at h
    · rename_i hd; simpa [Nat.succ_add, run, hd] using h
    · rename_i hd
      cases ht : tick functions m with
      | error e => simp [ht, bind, Except.bind] at h
      | ok next =>
        simp [ht, bind, Except.bind] at h
        simpa [Nat.succ_add, run, hd, ht, bind, Except.bind] using ih h

end Oak.WasmCalls
