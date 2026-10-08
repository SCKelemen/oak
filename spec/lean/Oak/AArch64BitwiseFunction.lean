import Oak.BitwiseFunction
import Oak.AArch64ReturnEncoding

/-!
# Successful projected A64 u32 bitwise leaf functions

Exact little-endian `AND/ORR/EOR W0, W0, W1; RET X30` bytes implement the
shared two-u32-input/one-u32-result slice for every input in the explicit
no-fault scalar projection below. The ABI reads the low halves of X0/X1,
zero-extends the W0 write, preserves every other register, SP and NZCV, and
returns to the incoming X30. Upper input halves are unrestricted.

This is not full Arm execution: instruction fetch, alignment, translation,
PostDecode, BranchTo, faults and authenticated returns are excluded. The
pinned Sail bridge proves the ordinary RET decoder route, but lacks the
scalar logical-shifted decoder/body/register-write projection and dynamic
RET transition. Vector logical equations cannot discharge those obligations.
Source lowering, register allocation and Go correspondence are not universal
proofs here. No production verified verdict is enabled.
-/

set_option autoImplicit false
namespace Oak.AArch64BitwiseFunction

open Oak.BitwiseFunction (Op eval)

abbrev Registers := BitVec 5 → BitVec 64
structure State where
  regs : Registers
  pc : BitVec 64
  sp : BitVec 64
  nzcv : BitVec 4

structure Logical where
  op : Op
  rd : BitVec 5
  rn : BitVec 5
  rm : BitVec 5
  deriving DecidableEq, Repr

/-- Only 32-bit, non-inverted, LSL #0 logical-register forms are supported.
The mask deliberately fixes both shift fields, not just the instruction class. -/
def decodeLogical (word : BitVec 32) : Option Logical :=
  let rd := word.extractLsb' 0 5
  let rn := word.extractLsb' 5 5
  let rm := word.extractLsb' 16 5
  if word &&& 0xffe0fc00#32 == 0x0a000000#32 then some ⟨.and, rd, rn, rm⟩
  else if word &&& 0xffe0fc00#32 == 0x2a000000#32 then some ⟨.or, rd, rn, rm⟩
  else if word &&& 0xffe0fc00#32 == 0x4a000000#32 then some ⟨.xor, rd, rn, rm⟩
  else none

def readW (regs : Registers) (r : BitVec 5) : BitVec 32 :=
  if r == 31#5 then 0 else (regs r).extractLsb' 0 32

/-- W-register writes clear the high half; writes to WZR are discarded. -/
def writeW (regs : Registers) (r : BitVec 5) (value : BitVec 32) : Registers :=
  fun q => if r != 31#5 && q == r then value.zeroExtend 64 else regs q

def executeLogical (d : Logical) (s : State) : State :=
  let a := readW s.regs d.rn
  let b := readW s.regs d.rm
  let result := match d.op with
    | .and => a &&& b
    | .or => a ||| b
    | .xor => a ^^^ b
  { s with regs := writeW s.regs d.rd result, pc := s.pc + 4 }

/-- Ordinary non-PAC RET class. Dynamic BranchTo checks are outside this model. -/
def decodeRet (word : BitVec 32) : Option (BitVec 5) :=
  if word &&& 0xfffffc1f#32 == 0xd65f0000#32 then
    some (word.extractLsb' 5 5) else none

def readX (regs : Registers) (r : BitVec 5) : BitVec 64 :=
  if r == 31#5 then 0 else regs r

/-- Read one complete little-endian instruction; never pad truncated input. -/
def takeWord : List UInt8 → Option (BitVec 32 × List UInt8)
  | a :: b :: c :: d :: rest =>
      some (BitVec.ofNat 32 a.toNat ||| (BitVec.ofNat 32 b.toNat <<< 8) |||
        (BitVec.ofNat 32 c.toNat <<< 16) ||| (BitVec.ofNat 32 d.toNat <<< 24), rest)
  | _ => none

/-- Successful completion requires exactly one supported logical instruction,
then an ordinary RET, and exhaustion of the complete function bytes. -/
def invoke (bytes : List UInt8) (s : State) : Option State := do
  let (word, rest) ← takeWord bytes
  let d ← decodeLogical word
  let next := executeLogical d s
  let (retWord, trailing) ← takeWord rest
  let rn ← decodeRet retWord
  if trailing.isEmpty then
    some { next with pc := readX next.regs rn }
  else none

-- Checked against the real assembler by asm/aarch64_bitwise_function_lean_test.go.
def functionBytes : Op → List UInt8
  | .and => [0x00, 0x00, 0x01, 0x0a, 0xc0, 0x03, 0x5f, 0xd6]
  | .or  => [0x00, 0x00, 0x01, 0x2a, 0xc0, 0x03, 0x5f, 0xd6]
  | .xor => [0x00, 0x00, 0x01, 0x4a, 0xc0, 0x03, 0x5f, 0xd6]

def returned (op : Op) (s : State) : State :=
  { s with
    regs := writeW s.regs 0#5 (eval op (readW s.regs 0#5) (readW s.regs 1#5))
    pc := s.regs 30#5 }

/-- Total successful exact-byte execution, for arbitrary initial registers,
PC, SP and flags. No premise equates faults or assumes a successful run. -/
theorem function_success (op : Op) (s : State) :
    invoke (functionBytes op) s = some (returned op s) := by
  cases op <;> rfl

/-- The ABI result is zero-extended, including when incoming high halves are dirty. -/
theorem result_u32 (op : Op) (s : State) (left right : BitVec 32)
    (hleft : (s.regs 0#5).extractLsb' 0 32 = left)
    (hright : (s.regs 1#5).extractLsb' 0 32 = right) :
    (returned op s).regs 0#5 = (eval op left right).zeroExtend 64 := by
  simp [returned, writeW, readW, hleft, hright]

theorem preserves_other_registers (op : Op) (s : State) (r : BitVec 5)
    (h : r ≠ 0#5) : (returned op s).regs r = s.regs r := by
  simp [returned, writeW, h]

theorem return_boundary (op : Op) (s : State) :
    (returned op s).pc = s.regs 30#5 ∧
    (returned op s).sp = s.sp ∧ (returned op s).nzcv = s.nzcv := by
  exact ⟨rfl, rfl, rfl⟩

inductive ABI where
  | aapcs64U32 | wasmLocals | rv64
  deriving DecidableEq, Repr

/-- Exact requested operation, complete bytes, ABI and signature are bound.
This is a local slice admission predicate, not a production certificate. -/
def accepts (target : Oak.BitwiseFunction.Target) (abi : ABI)
    (parameters : List Nat) (result : Nat) (op : Op) (bytes : List UInt8) : Bool :=
  decide (target = .arm64 ∧ abi = .aapcs64U32 ∧ parameters = [32, 32] ∧
    result = 32 ∧ bytes = functionBytes op)

theorem accepted_execution {target : Oak.BitwiseFunction.Target} {abi : ABI}
    {parameters : List Nat} {result : Nat} {op : Op} {bytes : List UInt8}
    (h : accepts target abi parameters result op bytes = true) (s : State) :
    invoke bytes s = some (returned op s) := by
  have accepted : target = .arm64 ∧ abi = .aapcs64U32 ∧ parameters = [32, 32] ∧
      result = 32 ∧ bytes = functionBytes op := by simpa [accepts] using h
  rw [accepted.2.2.2.2]
  exact function_success op s

/-- Any alteration of the complete bytes is rejected, even if it decodes as
another valid function. This also covers every individual changed bit. -/
theorem rejects_changed_bytes (target : Oak.BitwiseFunction.Target) (abi : ABI)
    (parameters : List Nat) (result : Nat) (op : Op) (bytes : List UInt8)
    (changed : bytes ≠ functionBytes op) :
    accepts target abi parameters result op bytes = false := by
  simp [accepts, changed]

/-! Kernel-checked wrong opcode, width, register, shift, return and length checks. -/
example : decodeLogical 0x8a010000#32 = none := by decide +kernel
example : decodeLogical 0x0a010400#32 = none := by decide +kernel
example : decodeLogical 0x0a410000#32 = none := by decide +kernel
example : decodeLogical 0x0a210000#32 = none := by decide +kernel
example : decodeLogical 0x6a010000#32 = none := by decide +kernel
example : decodeRet 0xd65f03c1#32 = none := by decide +kernel
example : accepts .arm64 .aapcs64U32 [32,32] 32 .and (functionBytes .or) = false := by decide +kernel
example : accepts .wasm .aapcs64U32 [32,32] 32 .and (functionBytes .and) = false := by decide +kernel
example : accepts .arm64 .wasmLocals [32,32] 32 .and (functionBytes .and) = false := by decide +kernel
example : accepts .arm64 .aapcs64U32 [64,32] 32 .and (functionBytes .and) = false := by decide +kernel
example : accepts .arm64 .aapcs64U32 [32,32] 64 .and (functionBytes .and) = false := by decide +kernel
example : accepts .arm64 .aapcs64U32 [32,32] 32 .and [0,0,0,10,192,3,95,214] = false := by decide +kernel
example : accepts .arm64 .aapcs64U32 [32,32] 32 .and [0,0,1,10,160,3,95,214] = false := by decide +kernel
example : accepts .arm64 .aapcs64U32 [32,32] 32 .and [0,0,1,10,192,3,95] = false := by decide +kernel
example : accepts .arm64 .aapcs64U32 [32,32] 32 .and [0,0,1,10,192,3,95,214,0] = false := by decide +kernel
example (s : State) : invoke [0,0,1,10,192,3,95] s = none := by rfl
example (s : State) : invoke [0,0,1,10,192,3,95,214,0] s = none := by rfl
example (s : State) : invoke [0,0,1,10,193,3,95,214] s = none := by rfl

end Oak.AArch64BitwiseFunction
