import Oak.WasmExecution

/-! Structured control for the assembler's zero-parameter scalar block profile.
The function body excludes its final end byte. Calls and module validation are
not modeled. Fuel exhaustion is a model limit, never a Core runtime trap. -/
namespace Oak.WasmControl
open WasmExecution
abbrev Token := UInt8 × Int

inductive Error where
  | scalar (fault : Fault)
  | malformedControl | labelOutOfBounds | resultMismatch | exhausted
  deriving DecidableEq, Repr

inductive LabelKind where
  | block | loop | function
  deriving DecidableEq, Repr

structure Frame where
  kind : LabelKind
  results : List Width
  saved : List Value
  next : List Token
  restart : List Token := []
  deriving DecidableEq, Repr

structure Machine where
  state : State
  code : List Token
  frames : List Frame
  deriving DecidableEq, Repr

/-- Check all delimiters, including unreachable arms, before executing. -/
def nested : List Token → List (UInt8 × Bool) → Bool
  | [], frames => frames.isEmpty
  | (op, _) :: rest, frames =>
    if op = 2 ∨ op = 3 ∨ op = 4 then nested rest ((op, false) :: frames)
    else if op = 5 then match frames with
      | (4, false) :: outer => nested rest ((4, true) :: outer)
      | _ => false
    else if op = 11 then match frames with
      | _ :: outer => nested rest outer
      | [] => false
    else nested rest frames

structure Parts where
  yes : List Token
  no : List Token
  next : List Token
  deriving DecidableEq, Repr

/-- Split the next matching end and optional outer else. Nested delimiters are
retained in their arms. `nested` checks the complete body's delimiter grammar. -/
def splitBody : List Token → Nat → Bool → List Token → List Token → Option Parts
  | [], _, _, _, _ => none
  | ins@(op, _) :: rest, depth, inElse, yes, no =>
    if op = 11 ∧ depth = 0 then some ⟨yes.reverse, no.reverse, rest⟩
    else if op = 5 ∧ depth = 0 then splitBody rest depth true yes no
    else
      let depth' := if op = 2 ∨ op = 3 ∨ op = 4 then depth + 1
        else if op = 11 then depth - 1 else depth
      if inElse then splitBody rest depth' inElse yes (ins :: no)
      else splitBody rest depth' inElse (ins :: yes) no

def resultTypes (v : Int) : List Width :=
  if v = 127 then [.w32] else if v = 126 then [.w64] else []

/-- A branch carries a typed prefix and discards extra intermediate operands. -/
def takeResults (types : List Width) (stack : List Value) : Except Error (List Value) :=
  if types.length > stack.length then .error (.scalar .stackUnderflow)
  else if (stack.take types.length).map Value.width = types then .ok (stack.take types.length)
  else .error (.scalar .typeMismatch)

def Frame.branchTypes (f : Frame) : List Width := if f.kind = .loop then [] else f.results

/-- A loop branch retains its target frame and restarts its body. Other branches
remove the target as well as all inner labels and resume after its end. -/
def jump (depth : Nat) (m : Machine) : Except Error Machine := do
  let f :: outer := m.frames.drop depth | .error .labelOutOfBounds
  let values ← takeResults f.branchTypes m.state.stack
  if f.kind = .loop then
    .ok ⟨{m.state with stack := values}, f.restart, f :: outer⟩
  else
    .ok ⟨{m.state with stack := values ++ f.saved}, f.next, outer⟩

/-- Normal fallthrough requires exactly the declared results; unlike a branch,
it cannot discard surplus values. Loop fallthrough exits rather than repeats. -/
def leave (m : Machine) : Except Error Machine := do
  let f :: outer := m.frames | .error .malformedControl
  if m.state.stack.length ≠ f.results.length then .error .resultMismatch
  else
    let values ← takeResults f.results m.state.stack
    .ok ⟨{m.state with stack := values ++ f.saved}, f.next, outer⟩

def condition (s : State) : Except Error (Bool × State) :=
  match s.stack with
  | [] => .error (.scalar .stackUnderflow)
  | .i32 v :: rest => .ok (v ≠ 0, {s with stack := rest})
  | _ => .error (.scalar .typeMismatch)

def enter (op : UInt8) (imm : Int) (m : Machine) : Except Error Machine := do
  let some parts := splitBody m.code 0 false [] [] | .error .malformedControl
  let (yes, state) ← if op = 4 then condition m.state else .ok (true, m.state)
  let body := if yes then parts.yes else parts.no
  let f : Frame := ⟨(if op = 3 then .loop else .block), resultTypes imm,
    state.stack, parts.next, parts.yes⟩
  .ok ⟨{state with stack := []}, body, f :: m.frames⟩

/-- One machine transition. The public entry checks all token encodings too. -/
def tick (m : Machine) : Except Error Machine :=
  match m.code with
  | [] => leave m
  | ins@(op, imm) :: rest => do
    if (WasmInstruction.encode op imm).isNone then .error (.scalar .malformed)
    else
      let next := {m with code := rest}
      if op = 2 ∨ op = 3 ∨ op = 4 then enter op imm next
      else if op = 12 then jump imm.toNat next
      else if op = 13 then
        let (yes, state) ← condition m.state
        if yes then jump imm.toNat {next with state := state}
        else .ok {next with state := state}
      else if op = 15 then
        jump (m.frames.findIdx (fun f => f.kind = .function)) next
      else
        let state ← (WasmExecution.step ins m.state).mapError Error.scalar
        .ok {next with state := state}

def done (m : Machine) : Bool := m.code.isEmpty && m.frames.isEmpty

def run : Nat → Machine → Except Error State
  | 0, m => if done m then .ok m.state else .error .exhausted
  | n + 1, m => if done m then .ok m.state else do run n (← tick m)

/-- Execute a body inside an implicit function label. The caller supplies the
initial locals and function result types; no module instantiation is claimed. -/
def execute (fuel : Nat) (code : List Token) (results : List Width)
    (locals : Array Value) : Except Error State :=
  if (WasmInstruction.assemble code).isNone then .error (.scalar .malformed)
  else if !nested code [] then .error .malformedControl
  else run fuel ⟨⟨[], locals⟩, code, [⟨.function, results, [], [], []⟩]⟩

/-- Syntactic decode count and runtime fuel are deliberately separate. Decode
checks the entire selected body; success leaves any external suffix untouched. -/
def executeBytes (count fuel : Nat) (bytes : List UInt8) (results : List Width)
    (locals : Array Value) : Except Error (State × List UInt8) :=
  match WasmInstruction.decodeMany count bytes with
  | none => .error (.scalar .malformed)
  | some (code, suffix) => (execute fuel code results locals).map (fun s => (s, suffix))

theorem executeBytes_assemble {code bytes} (h : WasmInstruction.assemble code = some bytes)
    (fuel : Nat) (suffix : List UInt8) (results : List Width) (locals : Array Value) :
    executeBytes code.length fuel (bytes ++ suffix) results locals =
      (execute fuel code results locals).map (fun s => (s, suffix)) := by
  simp [executeBytes, WasmInstruction.decode_assemble h suffix]

/-- Actual extracted assembler bytes execute as their input tokens, for every
runtime fuel, local array, function result signature and untouched suffix. -/
theorem assembled_execution (dst out : Array UInt8) (offset : UInt32)
    (plan : Array WasmAssembler.WasmInstruction) (bytes : List UInt8) (asmFuel fuel : Nat)
    (result : WasmAssembler.WasmAssembly) (results : List Width) (locals : Array Value)
    (hp : plan.size < 2^32) (hd : dst.size < 2^32)
    (he : WasmAssembler.instructionSequence plan.toList = some bytes)
    (hfit : offset.toNat + bytes.length ≤ dst.size) (hf : plan.size + 11 ≤ asmFuel)
    (hw : WasmAssembler.wasm_assemble dst offset plan asmFuel = some (result, out)) :
    executeBytes plan.size fuel (out.toList.drop offset.toNat) results locals =
      (execute fuel (plan.toList.map fun ins => (ins.opcode.toUInt8, ins.immediate.toInt)) results locals).map
        (fun s => (s, dst.toList.drop (offset.toNat + bytes.length))) := by
  rw [WasmAssembler.assemble_admitted_exact _ _ _ _ _ hp hd he hfit hf] at hw
  cases hw
  rw [WasmAssembler.writeBytes_suffix _ _ _ hfit]
  simpa using executeBytes_assemble (WasmAssembler.instructionSequence_model he) fuel
    (dst.toList.drop (offset.toNat + bytes.length)) results locals

/-- A successful carried prefix has exactly the requested types and arity. -/
theorem takeResults_typed {types stack values} (h : takeResults types stack = .ok values) :
    values.map Value.width = types ∧ values.length = types.length := by
  unfold takeResults at h
  split at h
  · contradiction
  · split at h
    · rename_i ht
      cases h
      exact ⟨ht, by simpa using congrArg List.length ht⟩
    · contradiction

/-- Intermediate values can be discarded, but the typed result prefix cannot. -/
theorem takeResults_prefix (values junk : List Value) :
    takeResults (values.map Value.width) (values ++ junk) = .ok values := by
  simp [takeResults]

/-- Successful execution is stable under additional runtime fuel. -/
theorem run_more {n m s} (h : run n m = .ok s) (extra : Nat) : run (n + extra) m = .ok s := by
  induction n generalizing m with
  | zero =>
    simp only [run] at h
    split at h
    · rename_i hd
      cases extra <;> simpa [run, hd] using h
    · contradiction
  | succ n ih =>
    simp only [run] at h
    split at h
    · rename_i hd
      simpa [Nat.succ_add, run, hd] using h
    · rename_i hd
      cases ht : tick m with
      | error e => simp [ht, bind, Except.bind] at h
      | ok next =>
        simp [ht, bind, Except.bind] at h
        simpa [Nat.succ_add, run, hd, ht, bind, Except.bind] using ih h

/-- Loop branch arity is zero even when normal loop completion returns a value. -/
theorem loop_branch (s : State) (f : Frame) (outer : List Frame) (code : List Token)
    (hk : f.kind = .loop) :
    jump 0 ⟨s, code, f :: outer⟩ = .ok ⟨{s with stack := []}, f.restart, f :: outer⟩ := by
  simp [jump, Frame.branchTypes, hk, takeResults, bind, Except.bind]

/-- Exiting a non-loop preserves the target's outer stack and every local,
while discarding intermediate operands and all labels through the target. -/
theorem branch_exit (inner outer : List Frame) (f : Frame) (values junk : List Value)
    (locals : Array Value) (code : List Token) (hk : f.kind ≠ .loop)
    (ht : values.map Value.width = f.results) :
    jump inner.length ⟨⟨values ++ junk, locals⟩, code, inner ++ f :: outer⟩ =
      .ok ⟨⟨values ++ f.saved, locals⟩, f.next, outer⟩ := by
  simp [jump, Frame.branchTypes, hk, ← ht, takeResults_prefix, bind, Except.bind]

/-- Normal block or loop completion restores the saved outer operands without
changing locals, and always removes the completed frame. -/
theorem leave_results (f : Frame) (outer : List Frame) (values : List Value)
    (locals : Array Value) (code : List Token) (ht : values.map Value.width = f.results) :
    leave ⟨⟨values, locals⟩, code, f :: outer⟩ =
      .ok ⟨⟨values ++ f.saved, locals⟩, f.next, outer⟩ := by
  simp [leave, ← ht, takeResults, bind, Except.bind]

/-- A false conditional branch pops only its condition. Its carried operands,
locals, continuation and all labels remain unchanged. -/
theorem br_if_zero (imm : Int) (rest : List Value) (locals : Array Value)
    (code : List Token) (frames : List Frame)
    (he : (WasmInstruction.encode 13 imm).isNone = false) :
    tick ⟨⟨.i32 0 :: rest, locals⟩, (13, imm) :: code, frames⟩ =
      .ok ⟨⟨rest, locals⟩, code, frames⟩ := by
  simp [tick, he, condition, bind, Except.bind]

/-- Every nonzero i32 condition, not only one, takes the same indexed branch. -/
theorem br_if_nonzero (imm : Int) (v : BitVec 32) (rest : List Value)
    (locals : Array Value) (code : List Token) (frames : List Frame)
    (he : (WasmInstruction.encode 13 imm).isNone = false) (hv : v ≠ 0) :
    tick ⟨⟨.i32 v :: rest, locals⟩, (13, imm) :: code, frames⟩ =
      jump imm.toNat ⟨⟨rest, locals⟩, code, frames⟩ := by
  have hv' : v ≠ 0#32 := hv
  simp [tick, he, condition, hv', bind, Except.bind]

end Oak.WasmControl
