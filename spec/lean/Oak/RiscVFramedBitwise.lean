import Oak.RiscVBitwiseFunction
import Oak.AArch64SpillMemory

/-!
# Actual RV64 native compiler's framed u32 bitwise functions

The currently emitted function is 36 bytes: allocate 96 bytes, save s1/s2,
copy a1 to s2, perform op a0,a0,a1, restore s1/s2 and sp, return. This module
uses the existing architecture-neutral byte store/load laws (housed in
AArch64SpillMemory) with RV64 registers and decoding. Memory is flat,
little-endian and no-fault. The invocation requires an external assertion that
the complete aligned, non-wrapping 96-byte frame is mapped readable/writable;
physical translation, permissions, device memory and instruction fetch are not
proved. Instruction bytes are immutable and separate from the data-memory
projection; coherence/disjointness with executable mappings is external.
Only sixteen bytes in that frame are written.

This theorem binds the concrete byte stream, not arbitrary compiler behavior
or source parsing. Production extraction pins are regression evidence.
-/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
namespace Oak.RiscVFramedBitwise
open Oak.BitwiseFunction (Op eval)
open Oak.RiscVCallExecution (X Reg read write clearLow)
open Oak.RiscVBitwiseFunction (Bytes eval64)
open Oak.AArch64SpillMemory (Memory storeBytes loadBytes)
open Oak.RiscVBranchEncoding (wordBytes fromBytes)

structure State where
  core : Oak.RiscVCallExecution.State
  mem : Memory

inductive Instruction where
  | addi (rd rs : Reg) (imm : BitVec 12)
  | store (rs base : Reg) (imm : BitVec 12)
  | load (rd base : Reg) (imm : BitVec 12)
  | bitwise (op : Op) (rd rs1 rs2 : Reg)
  | ret
  deriving DecidableEq

/-- Decode architectural masks and fields, independently from byte emission. -/
def decode (word : BitVec 32) : Option Instruction :=
  if word = 0x00008067 then some .ret
  else if word &&& 0x707f = 0x13 then
    some (.addi (word.extractLsb' 7 5) (word.extractLsb' 15 5) (word.extractLsb' 20 12))
  else if word &&& 0x707f = 0x3023 then
    some (.store (word.extractLsb' 20 5) (word.extractLsb' 15 5)
      ((word.extractLsb' 25 7) ++ (word.extractLsb' 7 5)))
  else if word &&& 0x707f = 0x3003 then
    some (.load (word.extractLsb' 7 5) (word.extractLsb' 15 5) (word.extractLsb' 20 12))
  else do
    let op ← Oak.RiscVBitwiseFunction.decodeOp word
    return .bitwise op (word.extractLsb' 7 5) (word.extractLsb' 15 5) (word.extractLsb' 20 5)

def address (s : State) (base : Reg) (imm : BitVec 12) : Nat :=
  (read s.core base + imm.signExtend 64).toNat

def put (s : State) (rd : Reg) (value : X) : State :=
  { s with core := ⟨s.core.pc + 4, write s.core rd value⟩ }

def execute (i : Instruction) (s : State) : State :=
  match i with
  | .addi rd rs imm => put s rd (read s.core rs + imm.signExtend 64)
  | .store rs base imm =>
      { core := ⟨s.core.pc + 4, s.core.regs⟩,
        mem := storeBytes 8 s.mem (address s base imm) (read s.core rs) }
  | .load rd base imm => put s rd (loadBytes 8 s.mem (address s base imm))
  | .bitwise op rd rs1 rs2 => put s rd (eval64 op (read s.core rs1) (read s.core rs2))
  | .ret => { s with core := Oak.RiscVCallExecution.jalr 0 1 0 4 s.core }

def run : List Instruction → State → State
  | [], s => s
  | i :: rest, s => run rest (execute i s)

def decodeBytes : Nat → Bytes → Option (List Instruction)
  | 0, [] => some []
  | n+1, b0 :: b1 :: b2 :: b3 :: rest => do
      let i ← decode (fromBytes b0 b1 b2 b3)
      let tail ← decodeBytes n rest
      return i :: tail
  | _, _ => none

def instructions (op : Op) : List Instruction :=
  [.addi 2 2 (-96), .store 9 2 0, .store 18 2 8, .addi 18 11 0,
   .bitwise op 10 10 11, .load 9 2 0, .load 18 2 8, .addi 2 2 96, .ret]

def functionBytes (op : Op) : Bytes :=
  ([0xfa010113, 0x00913023, 0x01213423, 0x00058913,
    Oak.RiscVBitwiseFunction.bodyWord op,
    0x00013483, 0x00813903, 0x06010113, 0x00008067] : List (BitVec 32)).flatMap wordBytes

theorem exact_decode (op : Op) : decodeBytes 9 (functionBytes op) = some (instructions op) := by
  cases op <;> rfl

def frameBase (s : State) : Nat := (s.core.regs 2).toNat - 96

def frameMemory (s : State) : Memory :=
  storeBytes 8 (storeBytes 8 s.mem (frameBase s) (s.core.regs 9))
    (frameBase s + 8) (s.core.regs 18)

/-- External mapping assertion means ordinary coherent read/write memory
throughout the frame, with no other agent modifying it during this function. -/
def frameSafe (mappedRW : Nat → Nat → Bool) (s : State) : Bool :=
  decide (96 ≤ (s.core.regs 2).toNat ∧ (s.core.regs 2).toNat % 16 = 0) &&
    mappedRW (frameBase s) 96

def invoke (mappedRW : Nat → Nat → Bool) (bytes : Bytes) (s : State) : Option State := do
  if frameSafe mappedRW s then
    let code ← decodeBytes 9 bytes
    return run code s
  else none

/-- Kernel-only 64-bit instance of the shared byte reconstruction theorem. -/
private theorem load_store64 (m : Memory) (a : Nat) (v : X) :
    loadBytes 8 (storeBytes 8 m a v) a = v := by
  exact Oak.AArch64SpillMemory.load_store .x64 m a v

-- Keep byte-map implementations opaque while simplifying machine-state projections.
-- The explicit memory lemmas above/below provide the required reconstruction laws.
attribute [local irreducible] storeBytes loadBytes

private theorem lower_sp (sp : X) (h : 96 ≤ sp.toNat) :
    (sp + (-96 : BitVec 12).signExtend 64).toNat = sp.toNat - 96 := by
  have hc : (-96 : BitVec 12).signExtend 64 = -(96#64) := by decide +kernel
  rw [hc, ← BitVec.sub_eq_add_neg]
  exact BitVec.toNat_sub_of_le (show 96#64 ≤ sp from h)

private theorem lower_sp_plus8 (sp : X) (h : 96 ≤ sp.toNat) :
    ((sp + (-96 : BitVec 12).signExtend 64) + (8 : BitVec 12).signExtend 64).toNat =
      sp.toNat - 96 + 8 := by
  have hs := sp.isLt
  have hlo := lower_sp sp h
  have hc : (8 : BitVec 12).signExtend 64 = 8#64 := by decide +kernel
  rw [hc, BitVec.toNat_add_of_lt]
  · rw [hlo]
    rfl
  · change (sp + (-96 : BitVec 12).signExtend 64).toNat + 8 < 2^64
    rw [hlo]
    omega

/-- Concrete success state: original register file except the result and
architectural x0, original sp/s1/s2/ra restored, and two saved words in memory. -/
def finalState (op : Op) (s : State) : State :=
  { core := ⟨clearLow (s.core.regs 1),
      write s.core 10 (eval64 op (read s.core 10) (read s.core 11))⟩,
    mem := frameMemory s }

private theorem execute_memory (i : Instruction) (s : State) :
    (execute i s).mem = match i with
      | .store rs base imm => storeBytes 8 s.mem (address s base imm) (read s.core rs)
      | _ => s.mem := by cases i <;> rfl

private theorem execute_registers (i : Instruction) (s : State) :
    (execute i s).core.regs = match i with
      | .addi rd rs imm => write s.core rd (read s.core rs + imm.signExtend 64)
      | .store _ _ _ => s.core.regs
      | .load rd base imm => write s.core rd (loadBytes 8 s.mem (address s base imm))
      | .bitwise op rd rs1 rs2 => write s.core rd (eval64 op (read s.core rs1) (read s.core rs2))
      | .ret => write s.core 0 (s.core.pc + 4) := by cases i <;> rfl

private theorem execute_pc (i : Instruction) (s : State) :
    (execute i s).core.pc = match i with
      | .ret => clearLow (read s.core 1 + BitVec.ofInt 64 0)
      | _ => s.core.pc + 4 := by cases i <;> rfl

theorem run_memory (op : Op) (s : State) (hsp : 96 ≤ (s.core.regs 2).toNat) :
    (run (instructions op) s).mem = frameMemory s := by
  simp only [instructions, run]
  simp only [execute_memory, execute_registers, execute_pc, address, Oak.RiscVCallExecution.read,
    write]
  have h20 : (2 : Reg) ≠ 0 := by decide +kernel
  have h90 : (9 : Reg) ≠ 0 := by decide +kernel
  have h92 : (9 : Reg) ≠ 2 := by decide +kernel
  have h180 : (18 : Reg) ≠ 0 := by decide +kernel
  have h182 : (18 : Reg) ≠ 2 := by decide +kernel
  have hzero : (0 : BitVec 12).signExtend 64 = 0#64 := rfl
  simp only [h20, h90, h92, h180, h182, if_false, if_true, hzero, BitVec.add_zero,
    lower_sp _ hsp, lower_sp_plus8 _ hsp]
  rfl
theorem run_pc (op : Op) (s : State) :
    (run (instructions op) s).core.pc = clearLow (s.core.regs 1) := by
  simp only [instructions, run]
  simp only [execute_memory, execute_registers, execute_pc, address, Oak.RiscVCallExecution.read,
    write, BitVec.reduceEq, if_false, if_true]
  change clearLow (s.core.regs 1 + 0#64) = _
  rw [BitVec.add_zero]

theorem run_registers (op : Op) (s : State) (hsp : 96 ≤ (s.core.regs 2).toNat) :
    (run (instructions op) s).core.regs =
      write s.core 10 (eval64 op (read s.core 10) (read s.core 11)) := by
  have hload1 : loadBytes 8 (frameMemory s) (frameBase s) = s.core.regs 9 := by
    unfold frameMemory
    rw [Oak.AArch64SpillMemory.load_disjoint 8 8 _ _ _ _ (Or.inl (Nat.le_refl _)), load_store64]
  have hload2 : loadBytes 8 (frameMemory s) (frameBase s + 8) = s.core.regs 18 := by
    unfold frameMemory
    exact load_store64 _ _ _
  simp only [frameMemory, frameBase] at hload1 hload2
  have hzero : (0 : BitVec 12).signExtend 64 = 0#64 := rfl
  have hcancel : (-96 : BitVec 12).signExtend 64 + (96 : BitVec 12).signExtend 64 = 0#64 := by decide +kernel
  funext r
  simp only [instructions, run]
  simp only [execute_memory, execute_registers, execute_pc, address, Oak.RiscVCallExecution.read,
    write, BitVec.reduceEq, if_false, if_true,
    hzero, BitVec.add_zero, lower_sp _ hsp, lower_sp_plus8 _ hsp, hload1, hload2]
  by_cases h0 : r = 0
  · simp only [h0, BitVec.reduceEq, if_true]
  · by_cases h2 : r = 2
    · simp only [h2, BitVec.reduceEq, if_true, if_false, BitVec.add_assoc, hcancel, BitVec.add_zero]
    · by_cases h9 : r = 9
      · simp only [h9, BitVec.reduceEq, if_true, if_false]
      · by_cases h18 : r = 18
        · simp only [h18, BitVec.reduceEq, if_true, if_false]
        · simp only [h0, h2, h9, h18, if_false]

private theorem state_ext {a b : State}
    (hp : a.core.pc = b.core.pc) (hr : a.core.regs = b.core.regs)
    (hm : a.mem = b.mem) : a = b := by
  cases a with | mk ac am =>
    cases b with | mk bc bm =>
      cases ac with | mk ap ar =>
        cases bc with | mk bp br =>
          dsimp only at hp hr hm
          subst bp
          subst br
          subst bm
          rfl

theorem run_success (op : Op) (s : State) (hsp : 96 ≤ (s.core.regs 2).toNat) :
    run (instructions op) s = finalState op s := by
  apply state_ext
  · exact run_pc op s
  · exact run_registers op s hsp
  · exact run_memory op s hsp

/-- Success requires a mapped ordinary stack frame, sufficient downward room,
and 16-byte alignment, rather than an equality between failed executions. -/
theorem function_success (op : Op) (s : State) (mappedRW : Nat → Nat → Bool)
    (safe : frameSafe mappedRW s = true) :
    invoke mappedRW (functionBytes op) s = some (finalState op s) := by
  have hsp : 96 ≤ (s.core.regs 2).toNat := by
    simp only [frameSafe, Bool.and_eq_true, decide_eq_true_eq] at safe
    exact safe.1.1
  simp only [invoke, safe, if_true, exact_decode]
  change some (run (instructions op) s) = _
  rw [run_success op s hsp]

theorem preserved_register (op : Op) (s : State) (r : Reg)
    (hzero : r ≠ 0#5) (hresult : r ≠ 10#5) :
    (finalState op s).core.regs r = s.core.regs r := by
  simp [finalState, write, hzero, hresult]

/-- The entire caller stack pointer and callee-saved registers are restored. -/
theorem stack_and_saves_restored (op : Op) (s : State) :
    (finalState op s).core.regs 2 = s.core.regs 2 ∧
    (finalState op s).core.regs 9 = s.core.regs 9 ∧
    (finalState op s).core.regs 18 = s.core.regs 18 := by
  simp [finalState, write]

theorem memory_footprint (op : Op) (s : State) (a : Nat)
    (outside : a < frameBase s ∨ frameBase s + 16 ≤ a) :
    (finalState op s).mem a = s.mem a := by
  dsimp only [finalState, frameMemory]
  rw [Oak.AArch64SpillMemory.store_outside 8 _ _ _ _ (by omega)]
  exact Oak.AArch64SpillMemory.store_outside 8 _ _ _ _ (by omega)

theorem writes_within_frame (s : State) (hsp : 96 ≤ (s.core.regs 2).toNat) :
    frameBase s + 16 ≤ (s.core.regs 2).toNat := by
  unfold frameBase
  omega

theorem accessed_addresses_fit (s : State) (hsp : 96 ≤ (s.core.regs 2).toNat) :
    frameBase s + 16 < 2^64 :=
  Nat.lt_of_le_of_lt (writes_within_frame s hsp) (s.core.regs 2).isLt

/-- The existing shared LP64D entry adapter makes the all-input result precise. -/
def entry (left right : BitVec 32) (pc : X) (caller : Reg → X) (mem : Memory) : State :=
  ⟨Oak.RiscVBitwiseFunction.entry left right pc caller, mem⟩

theorem result_register (op : Op) (left right : BitVec 32) (pc : X)
    (caller : Reg → X) (mem : Memory) :
    read (finalState op (entry left right pc caller mem)).core 10 =
      Oak.RiscV.widen 32 false (eval op left right) := by
  simp [finalState, entry, Oak.RiscVBitwiseFunction.entry, Oak.RiscVCallExecution.read,
    write, Oak.RiscVBitwiseFunction.eval64_widen]

/-- Observed result is the full u32 function result, not an OS exit status. -/
theorem all_input_result (op : Op) (left right : BitVec 32) (pc : X)
    (caller : Reg → X) (mem : Memory) (mappedRW : Nat → Nat → Bool)
    (safe : frameSafe mappedRW (entry left right pc caller mem) = true) :
    (invoke mappedRW (functionBytes op) (entry left right pc caller mem)).map
      (fun after => (read after.core 10).truncate 32) = some (eval op left right) := by
  rw [function_success op _ mappedRW safe]
  change some ((read (finalState op (entry left right pc caller mem)).core 10).truncate 32) = _
  rw [result_register, Oak.RiscV.widen_truncate_u32]
/-- Admission for this exact compiled wrapper; no source identity is inferred. -/
def accepts (target : Oak.BitwiseFunction.Target) (abi : Oak.RiscVBitwiseFunction.ABI)
    (parameters : List Nat) (result : Nat) (op : Op) (bytes : Bytes) : Bool :=
  decide (target = .rv64 ∧ abi = .lp64d ∧ parameters = [32, 32] ∧
    result = 32 ∧ bytes = functionBytes op)

theorem accepts_iff (target : Oak.BitwiseFunction.Target) (abi : Oak.RiscVBitwiseFunction.ABI)
    (parameters : List Nat) (result : Nat) (op : Op) (bytes : Bytes) :
    accepts target abi parameters result op bytes = true ↔
      target = .rv64 ∧ abi = .lp64d ∧ parameters = [32, 32] ∧
        result = 32 ∧ bytes = functionBytes op := by simp [accepts]

theorem accepted_success {target : Oak.BitwiseFunction.Target} {abi : Oak.RiscVBitwiseFunction.ABI}
    {parameters : List Nat} {result : Nat} {op : Op} {bytes : Bytes}
    (accepted : accepts target abi parameters result op bytes = true)
    (s : State) (mappedRW : Nat → Nat → Bool) (safe : frameSafe mappedRW s = true) :
    invoke mappedRW bytes s = some (finalState op s) := by
  have exactBytes := ((accepts_iff target abi parameters result op bytes).mp accepted).2.2.2.2
  rw [exactBytes]
  exact function_success op s mappedRW safe

example : accepts .rv64 .lp64d [32, 32] 32 .and (functionBytes .and) = true := by decide +kernel
example : accepts .arm64 .lp64d [32, 32] 32 .and (functionBytes .and) = false := by decide +kernel
example : accepts .rv64 .aapcs64 [32, 32] 32 .and (functionBytes .and) = false := by decide +kernel
example : accepts .rv64 .lp64d [64, 32] 32 .and (functionBytes .and) = false := by decide +kernel
example : accepts .rv64 .lp64d [32, 32] 64 .and (functionBytes .and) = false := by decide +kernel
example : accepts .rv64 .lp64d [32, 32] 32 .and (functionBytes .or) = false := by decide +kernel
example : accepts .rv64 .lp64d [32, 32] 32 .and (Oak.RiscVBitwiseFunction.functionBytes .and) = false := by decide +kernel
example : decodeBytes 9 ((functionBytes .and).take 35) = none := by rfl
example : decodeBytes 9 (functionBytes .and ++ [0]) = none := by rfl
example : decode 0x00000067 = none := by rfl
example (s : State) (bytes : Bytes) : invoke (fun _ _ => false) bytes s = none := by
  simp [invoke, frameSafe]
example : invoke (fun _ _ => true) (functionBytes .and)
    ⟨⟨0, fun _ => 0⟩, fun _ => 0⟩ = none := by rfl
example : invoke (fun _ _ => true) (functionBytes .and)
    ⟨⟨0, fun r => if r = 2 then 97 else 0⟩, fun _ => 0⟩ = none := by rfl
end Oak.RiscVFramedBitwise
