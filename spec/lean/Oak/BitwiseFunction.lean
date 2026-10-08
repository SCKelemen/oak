import Oak.WasmExecution

/-!
# First successful u32 bitwise function slice

The supported expression is exactly `op(parameter 0, parameter 1)`, with two
u32 parameters and one u32 result, for AND/OR/XOR. This is not an arbitrary
expression-tree compiler. Bytes are the instruction body followed by its
function-end opcode, excluding the module and code-entry/local declarations.

The end boundary below is a deliberately restricted function-body model.
It requires an otherwise empty operand stack and a single i32 result, consumes
the final end, and rejects trailing bytes. It does not reinterpret unsupported
control flow as successful execution. Parser, Go compiler, module validation,
instantiation, native ABIs, and external ISA semantics are not proved here.
No production verdict or TranslationVerified flag consumes this module.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Oak.BitwiseFunction

open Oak.WasmExecution

inductive Op where
  | and | or | xor
  deriving DecidableEq, Repr

/-- Common 32-bit mathematical meaning, independent of instruction decoding. -/
def eval (op : Op) (left right : BitVec 32) : BitVec 32 :=
  match op with
  | .and => left &&& right
  | .or => left ||| right
  | .xor => left ^^^ right

def opcode : Op → UInt8
  | .and => 113 | .or => 114 | .xor => 115

def instructions (op : Op) : List (UInt8 × Int) :=
  [(32, 0), (32, 1), (opcode op, 0)]

def bodyBytes (op : Op) : List UInt8 := [32, 0, 32, 1, opcode op]

def functionBytes (op : Op) : List UInt8 := bodyBytes op ++ [11]

/-- Check the function delimiter, exhaustion, and exact single-result shape. -/
def finish (state : State) (remaining : List UInt8) : Except Fault (BitVec 32) :=
  match WasmInstruction.decode remaining with
  | some ((11, 0), []) =>
      match state.stack with
      | [.i32 value] => .ok value
      | _ => .error .typeMismatch
  | _ => .error .malformed

/-- Locals have already been supplied by the caller. Count is a syntactic
body-instruction count; it is not a control-flow fuel or a module decoder. -/
def invoke (count : Nat) (bytes : List UInt8) (locals : Array Value) :
    Except Fault (BitVec 32) := do
  let (state, remaining) ← runBytes count bytes ⟨[], locals⟩
  finish state remaining

/-- Compose exact assembled-byte execution with a successful, typed body
result and the checked terminal boundary. Fault agreement alone is insufficient. -/
theorem assembled_function {code : List (UInt8 × Int)} {bytes : List UInt8}
    {locals : Array Value} {value : BitVec 32}
    (encoded : WasmInstruction.assemble code = some bytes)
    (executed : run code ⟨[], locals⟩ = .ok ⟨[.i32 value], locals⟩) :
    invoke code.length (bytes ++ [11]) locals = .ok value := by
  unfold invoke
  rw [runBytes_assemble encoded [11], executed]
  rfl

theorem exact_encoding (op : Op) :
    WasmInstruction.assemble (instructions op) = some (bodyBytes op) := by
  cases op <;> decide +kernel

/-- Total success, not merely preservation conditional on a successful run. -/
theorem body_success (op : Op) (left right : BitVec 32) :
    run (instructions op) ⟨[], #[.i32 left, .i32 right]⟩ =
      .ok ⟨[.i32 (eval op left right)], #[.i32 left, .i32 right]⟩ := by
  cases op <;> rfl

/-- Every pair of 32-bit inputs returns the common word result from the exact
decoded bytes, including final end consumption and single-result validation. -/
theorem function_success (op : Op) (left right : BitVec 32) :
    invoke 3 (functionBytes op) #[.i32 left, .i32 right] =
      .ok (eval op left right) := by
  exact assembled_function (exact_encoding op) (body_success op left right)

/-- Concrete instruction plan for the mechanically extracted Oak assembler,
including the function-end byte. Its span starts at the first instruction. -/
def assemblyPlan (op : Op) : Array WasmAssembler.WasmInstruction :=
  #[⟨32, 0⟩, ⟨32, 1⟩, ⟨UInt32.ofNat (opcode op).toNat, 0⟩, ⟨11, 0⟩]

theorem assemblyPlan_encoding (op : Op) :
    WasmAssembler.instructionSequence (assemblyPlan op).toList =
      some (functionBytes op) := by
  cases op <;> decide +kernel

/-- The extracted assembler terminates successfully and its actual six-byte
output span returns the shared word result for all inputs. The destination may
have arbitrary prefix/suffix bytes, which are outside the emitted function.
This uses the existing disjoint-array extraction model and representable spans;
it is not a theorem about Go emission or a complete Wasm module. -/
theorem emitted_function_success (op : Op) (dst : Array UInt8) (offset : UInt32)
    (fuel : Nat) (left right : BitVec 32)
    (representable : dst.size < 2^32)
    (capacity : offset.toNat + 6 ≤ dst.size) (budget : 15 ≤ fuel) :
    ∃ out, WasmAssembler.wasm_assemble dst offset (assemblyPlan op) fuel =
      some (⟨0, 6⟩, out) ∧
      invoke 3 ((out.toList.drop offset.toNat).take 6) #[.i32 left, .i32 right] =
        .ok (eval op left right) := by
  have size : (functionBytes op).length = 6 := by cases op <;> rfl
  have fit : offset.toNat + (functionBytes op).length ≤ dst.size := by
    simpa [size] using capacity
  refine ⟨WasmAssembler.writeBytes dst offset.toNat (functionBytes op), ?_, ?_⟩
  · simpa [size] using WasmAssembler.assemble_admitted_exact dst offset
      (assemblyPlan op) (functionBytes op) fuel (by simp [assemblyPlan]) representable
      (assemblyPlan_encoding op) fit budget
  · rw [WasmAssembler.writeBytes_suffix _ _ _ fit]
    have span : (functionBytes op ++ dst.toList.drop
        (offset.toNat + (functionBytes op).length)).take 6 = functionBytes op := by
      rw [← size]
      simp
    rw [span]
    exact function_success op left right

inductive Target where
  | rv64 | arm64 | wasm
  deriving DecidableEq, Repr

inductive ABI where
  | native | wasmLocals
  deriving DecidableEq, Repr

/-- This checked slice only authorizes the exact Wasm-local signature/bytes.
Native targets must acquire their own execution proofs before admission. -/
def accepts (target : Target) (abi : ABI) (parameters : List Nat)
    (result : Nat) (op : Op) (bytes : List UInt8) : Bool :=
  decide (target = .wasm ∧ abi = .wasmLocals ∧ parameters = [32, 32] ∧
    result = 32 ∧ bytes = functionBytes op)

theorem accepts_iff (target : Target) (abi : ABI) (parameters : List Nat)
    (result : Nat) (op : Op) (bytes : List UInt8) :
    accepts target abi parameters result op bytes = true ↔
      target = .wasm ∧ abi = .wasmLocals ∧ parameters = [32, 32] ∧
        result = 32 ∧ bytes = functionBytes op := by
  simp [accepts]

/-- Admission binds the requested operation and complete byte sequence.
The conclusion is successful execution for all inputs, not an equal fault. -/
theorem accepted_execution {target : Target} {abi : ABI} {parameters : List Nat}
    {result : Nat} {op : Op} {bytes : List UInt8}
    (accepted : accepts target abi parameters result op bytes = true)
    (left right : BitVec 32) :
    invoke 3 bytes #[.i32 left, .i32 right] = .ok (eval op left right) := by
  have exactBytes := ((accepts_iff target abi parameters result op bytes).mp accepted).2.2.2.2
  rw [exactBytes]
  exact function_success op left right

/-! Kernel-checked mutation regressions. No stale certificate or source identity
is modeled: there is no certificate consumer or source projection in this slice. -/
example : accepts .wasm .wasmLocals [32, 32] 32 .and (functionBytes .and) = true := by decide +kernel
example : accepts .rv64 .wasmLocals [32, 32] 32 .and (functionBytes .and) = false := by decide +kernel
example : accepts .arm64 .wasmLocals [32, 32] 32 .and (functionBytes .and) = false := by decide +kernel
example : accepts .wasm .native [32, 32] 32 .and (functionBytes .and) = false := by decide +kernel
example : accepts .wasm .wasmLocals [64, 32] 32 .and (functionBytes .and) = false := by decide +kernel
example : accepts .wasm .wasmLocals [32, 32] 64 .and (functionBytes .and) = false := by decide +kernel
example : accepts .wasm .wasmLocals [32] 32 .and (functionBytes .and) = false := by decide +kernel
example : accepts .wasm .wasmLocals [32, 32] 32 .and (functionBytes .or) = false := by decide +kernel
example : accepts .wasm .wasmLocals [32, 32] 32 .and [32, 0, 32, 0, 113, 11] = false := by decide +kernel
example : accepts .wasm .wasmLocals [32, 32] 32 .and [32, 0, 32, 1, 106, 11] = false := by decide +kernel
example : accepts .wasm .wasmLocals [32, 32] 32 .and [32, 0, 32, 1, 113] = false := by decide +kernel
example : accepts .wasm .wasmLocals [32, 32] 32 .and [32, 0, 32, 1, 113, 11, 1] = false := by decide +kernel
example : invoke 3 [32, 0, 32, 1, 113] #[.i32 7, .i32 3] = .error .malformed := by rfl
example : invoke 3 [32, 0, 32, 1, 113, 11, 1] #[.i32 7, .i32 3] = .error .malformed := by rfl
example : invoke 3 [32, 0, 32, 1, 113, 15] #[.i32 7, .i32 3] = .error .malformed := by rfl
example : finish ⟨[], #[]⟩ [11] = .error .typeMismatch := by rfl
example : finish ⟨[.i64 0], #[]⟩ [11] = .error .typeMismatch := by rfl
example : finish ⟨[.i32 0, .i32 0], #[]⟩ [11] = .error .typeMismatch := by rfl
example : invoke 3 [32, 0, 32, 1, 113, 11] #[.i64 7, .i32 3] = .error .typeMismatch := by rfl
example : invoke 3 [32, 0, 32, 1, 113, 11] #[.i32 7] = .error .localOutOfBounds := by rfl

end Oak.BitwiseFunction
