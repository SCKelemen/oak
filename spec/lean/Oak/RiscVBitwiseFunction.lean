import Oak.BitwiseFunction
import Oak.RiscVCallExecution
import Oak.RiscVBranchEncoding

/-!
# Exact-byte RV64 u32 bitwise leaf functions

The grammar is exactly `op(parameter 0, parameter 1)` for shared AND/OR/XOR.
The eight bytes are `op a0, a0, a1; jalr zero, ra, 0`, uncompressed.
LP64D inputs/result are sign-extended from 32 bits, even for unsigned u32.
The independent field decoder consumes exactly eight bytes. Semantics reuse
Oak's zero-register writes and JALR transition; PC arithmetic is modular
64-bit under IALIGN=16. Return clears bit zero.

This is successful internal execution, not source/compiler, loading/fetch,
memory, privilege or trap correctness. Separate external Sail bridges prove
the table's encodings and register-operation bodies. Their composition with
this decoder, concrete Sail state and return is NOT proved here. A forward
encoder theorem is not a decoder theorem. No production verdict consumes this.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace Oak.RiscVBitwiseFunction
open Oak.BitwiseFunction (Op eval Target)
open Oak.RiscVCallExecution
open Oak.RiscVBranchEncoding (wordBytes fromBytes)
abbrev Bytes := List (BitVec 8)
def row : Op → Oak.RiscV.Enc.Encoding
  | .and => Oak.RiscV.Enc.and_
  | .or => Oak.RiscV.Enc.or_
  | .xor => Oak.RiscV.Enc.xor_
def bodyWord (op : Op) : BitVec 32 :=
  Oak.RiscV.Enc.encode (row op) (Oak.RiscV.Enc.rOperands 10 10 11)
def functionBytes (op : Op) : Bytes := wordBytes (bodyWord op) ++ wordBytes 0x00008067
/-- Independent mask/field decoding; unsupported words fail closed. -/
def decodeOp (word : BitVec 32) : Option Op :=
  if word &&& 0xfe00707f = 0x00007033 then some .and
  else if word &&& 0xfe00707f = 0x00006033 then some .or
  else if word &&& 0xfe00707f = 0x00004033 then some .xor
  else none
def eval64 : Op → X → X → X
  | .and, left, right => left &&& right
  | .or, left, right => left ||| right
  | .xor, left, right => left ^^^ right
def body (op : Op) (rd rs1 rs2 : Reg) (s : State) : State :=
  ⟨s.pc + 4, write s rd (eval64 op (read s rs1) (read s rs2))⟩
def executeWord (word : BitVec 32) (s : State) : Option State := do
  let op ← decodeOp word
  return body op (word.extractLsb' 7 5) (word.extractLsb' 15 5)
    (word.extractLsb' 20 5) s
/-- This leaf boundary admits only RET, not arbitrary JALR/control flow. -/
def executeBytes (bytes : Bytes) (s : State) : Option State :=
  match bytes with
  | [b0, b1, b2, b3, r0, r1, r2, r3] => do
      let after ← executeWord (fromBytes b0 b1 b2 b3) s
      if fromBytes r0 r1 r2 r3 = 0x00008067 then
        some (jalr 0 1 0 4 after)
      else none
  | _ => none
/-- Other caller registers are arbitrary; architectural x0 reads zero. -/
def entry (left right : BitVec 32) (pc : X) (caller : Reg → X) : State :=
  ⟨pc, fun r => if r = 10 then Oak.RiscV.widen 32 false left
    else if r = 11 then Oak.RiscV.widen 32 false right else caller r⟩
def finalState (op : Op) (s : State) : State := jalr 0 1 0 4 (body op 10 10 11 s)
def invoke (bytes : Bytes) (left right : BitVec 32) (pc : X)
    (caller : Reg → X) : Option (BitVec 32) := do
  let after ← executeBytes bytes (entry left right pc caller)
  return (read after 10).truncate 32

theorem exact_encoding (op : Op) :
    functionBytes op = (match op with
      | .and => [0x33, 0x75, 0xb5, 0, 0x67, 0x80, 0, 0]
      | .or => [0x33, 0x65, 0xb5, 0, 0x67, 0x80, 0, 0]
      | .xor => [0x33, 0x45, 0xb5, 0, 0x67, 0x80, 0, 0]) := by
  cases op <;> decide +kernel
/-- Decoding succeeds with the requested operator and ABI registers. -/
theorem decoded_execution (op : Op) (s : State) :
    executeBytes (functionBytes op) s = some (finalState op s) := by
  cases op <;> rfl
/-- Full-register ABI result, including sign extension of bit 31. -/
theorem eval64_widen (op : Op) (left right : BitVec 32) :
    eval64 op (Oak.RiscV.widen 32 false left) (Oak.RiscV.widen 32 false right) =
      Oak.RiscV.widen 32 false (eval op left right) := by
  cases op <;> simp [eval64, eval, Oak.RiscV.widen, Oak.RiscV.sextW]

theorem result_register (op : Op) (left right : BitVec 32) (pc : X)
    (caller : Reg → X) :
    read (finalState op (entry left right pc caller)) 10 =
      Oak.RiscV.widen 32 false (eval op left right) := by
  simp [finalState, jalr, body, Oak.RiscVCallExecution.read, write, entry, eval64_widen]
theorem return_pc (op : Op) (s : State) :
    (finalState op s).pc = clearLow (s.regs 1) := by
  simp [finalState, jalr, body, Oak.RiscVCallExecution.read, write]
theorem preserves_register (op : Op) (s : State) (r : Reg)
    (hz : r ≠ 0#5) (hr : r ≠ 10#5) :
    (finalState op s).regs r = s.regs r := by
  simp [finalState, jalr, body, write, hz, hr]
theorem zero_register (op : Op) (s : State) : (finalState op s).regs 0 = 0 := by
  simp [finalState, jalr, write]
/-- Success for every input, caller state and modular entry PC. -/
theorem function_success (op : Op) (left right : BitVec 32) (pc : X)
    (caller : Reg → X) :
    invoke (functionBytes op) left right pc caller = some (eval op left right) := by
  unfold invoke
  rw [decoded_execution]
  change some ((read (finalState op (entry left right pc caller)) 10).truncate 32) = _
  rw [result_register, Oak.RiscV.widen_truncate_u32]
inductive ABI where
  | lp64d | aapcs64 | wasmLocals
  deriving DecidableEq, Repr
/-- Admission fixes entire body, target, ABI and complete u32 signature. -/
def accepts (target : Target) (abi : ABI) (parameters : List Nat)
    (result : Nat) (op : Op) (bytes : Bytes) : Bool :=
  decide (target = .rv64 ∧ abi = .lp64d ∧ parameters = [32, 32] ∧
    result = 32 ∧ bytes = functionBytes op)
theorem accepts_iff (target : Target) (abi : ABI) (parameters : List Nat)
    (result : Nat) (op : Op) (bytes : Bytes) :
    accepts target abi parameters result op bytes = true ↔
      target = .rv64 ∧ abi = .lp64d ∧ parameters = [32, 32] ∧
        result = 32 ∧ bytes = functionBytes op := by simp [accepts]
theorem accepted_execution {target : Target} {abi : ABI} {parameters : List Nat}
    {result : Nat} {op : Op} {bytes : Bytes}
    (accepted : accepts target abi parameters result op bytes = true)
    (left right : BitVec 32) (pc : X) (caller : Reg → X) :
    invoke bytes left right pc caller = some (eval op left right) := by
  have h := ((accepts_iff target abi parameters result op bytes).mp accepted).2.2.2.2
  rw [h]
  exact function_success op left right pc caller
/-! Kernel-checked target/signature/operator/register/return/length mutations. -/
example : accepts .rv64 .lp64d [32, 32] 32 .and (functionBytes .and) = true := by decide +kernel
example : accepts .arm64 .lp64d [32, 32] 32 .and (functionBytes .and) = false := by decide +kernel
example : accepts .wasm .lp64d [32, 32] 32 .and (functionBytes .and) = false := by decide +kernel
example : accepts .rv64 .aapcs64 [32, 32] 32 .and (functionBytes .and) = false := by decide +kernel
example : accepts .rv64 .lp64d [64, 32] 32 .and (functionBytes .and) = false := by decide +kernel
example : accepts .rv64 .lp64d [32] 32 .and (functionBytes .and) = false := by decide +kernel
example : accepts .rv64 .lp64d [32, 32] 64 .and (functionBytes .and) = false := by decide +kernel
example : accepts .rv64 .lp64d [32, 32] 32 .and (functionBytes .or) = false := by decide +kernel
example : accepts .rv64 .lp64d [32, 32] 32 .and [0x33, 0x75, 0xa5, 0, 0x67, 0x80, 0, 0] = false := by decide +kernel
example : accepts .rv64 .lp64d [32, 32] 32 .and [0xb3, 0x75, 0xb5, 0, 0x67, 0x80, 0, 0] = false := by decide +kernel
example (s : State) : executeBytes [0x33, 0x75, 0xb5, 0, 0x67, 0x80, 0] s = none := by rfl
example (s : State) : executeBytes [0x33, 0x75, 0xb5, 0, 0x67, 0x80, 0, 0, 0] s = none := by rfl
example (s : State) : executeBytes [0x33, 0x75, 0xb5, 0, 0x67, 0, 0, 0] s = none := by rfl
example (s : State) : executeBytes [0x33, 0x75, 0xb5, 0x40, 0x67, 0x80, 0, 0] s = none := by rfl
end Oak.RiscVBitwiseFunction
