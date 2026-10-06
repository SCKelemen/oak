import Oak.RiscV

/-!
# RV64 signed 32-bit literal materialization

`rv64Expand` admits signed 32-bit LI literals. A signed 12-bit literal is
ADDI from x0; otherwise LUI writes the rounded upper part and ADDIW adds the
signed low part unless it is zero. The W operation is necessary when the
rounded LUI crosses bit 31 near the positive endpoint.

These are expansion and value-semantics proofs. Concrete Go expansion and
compressed/uncompressed byte streams are checked separately. This is not a
new universal encoder refinement or a Sail decoder/execution bridge.

ISA reference: https://docs.riscv.org/reference/isa/unpriv/rv64.html
-/

namespace Oak.RiscVMaterialization

abbrev X := BitVec 64

def high (value : Int) : Int := (value + 2048) / 4096
def low (value : Int) : Int := value - high value * 4096

def fits32 (value : Int) : Bool := decide (-2147483648 ≤ value ∧ value < 2147483648)
def fits12 (value : Int) : Bool := decide (-2048 ≤ value ∧ value < 2048)

inductive Step where
  | addi (imm : Int) -- ADDI rd, x0, imm
  | lui (imm : Int) -- LUI rd, imm
  | addiw (imm : Int) -- ADDIW rd, rd, imm
  deriving DecidableEq, Repr

def expand (value : Int) : Option (List Step) :=
  if fits32 value then
    if fits12 value then some [.addi value]
    else if low value = 0 then some [.lui (high value)]
    else some [.lui (high value), .addiw (low value)]
  else none

/-- Instruction semantics on the selected destination, for admitted operands.
ADDI starts from x0; LUI and ADDIW sign-extend a 32-bit result. -/
def step : Step → X → X
  | .addi imm, _ => BitVec.ofInt 64 imm
  | .lui imm, _ => (BitVec.ofInt 32 (imm * 4096)).signExtend 64
  | .addiw imm, acc => (acc.truncate 32 + BitVec.ofInt 32 imm).signExtend 64

def run (steps : List Step) (initial : X) : X := steps.foldl (fun acc s => step s acc) initial

def encodable : Step → Prop
  | .addi imm | .addiw imm => -2048 ≤ imm ∧ imm < 2048
  | .lui imm => -524288 ≤ imm ∧ imm < 1048576

instance (s : Step) : Decidable (encodable s) := by cases s <;> unfold encodable <;> infer_instance

theorem split_exact (value : Int) : high value * 4096 + low value = value := by
  unfold low
  omega

theorem low_bounds (value : Int) : -2048 ≤ low value ∧ low value < 2048 := by
  unfold low high
  omega

theorem high_bounds {value : Int} (h : fits32 value = true) :
    -524288 ≤ high value ∧ high value ≤ 524288 := by
  simp only [fits32, decide_eq_true_eq] at h
  unfold high
  omega

theorem high_as_shift (value : Int) : high value = (value + 2048) >>> 12 := by
  simp [high, Int.shiftRight_eq_div_pow]

theorem low_as_shift (value : Int) : low value = value - (high value <<< 12) := by
  simp [low, Int.shiftLeft_eq]

/-- All intermediate arithmetic stays far inside signed 64-bit bounds before
Go performs its arithmetic right shift and subtraction. -/
theorem split_intermediate_bounds {value : Int} (h : fits32 value = true) :
    -2147481600 ≤ value + 2048 ∧ value + 2048 ≤ 2147485695 ∧
    -2147483648 ≤ high value * 4096 ∧ high value * 4096 ≤ 2147483648 := by
  have hh := high_bounds h
  simp only [fits32, decide_eq_true_eq] at h
  omega

theorem signed12_field {imm : Int} (hlo : -2048 ≤ imm) (hhi : imm < 2048) :
    (BitVec.ofInt 12 imm).signExtend 64 = BitVec.ofInt 64 imm := by
  unfold BitVec.signExtend
  rw [BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)]

theorem expand_some_iff (value : Int) :
    (∃ steps, expand value = some steps) ↔ fits32 value = true := by
  unfold expand
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

theorem expand_encodable {value : Int} {steps : List Step} (h : expand value = some steps) :
    ∀ s ∈ steps, encodable s := by
  unfold expand at h
  split at h
  next h32 =>
    have hh := high_bounds h32
    have hl := low_bounds value
    split at h
    next h12 =>
      simp only [Option.some.injEq] at h
      subst steps
      simpa [encodable] using (show -2048 ≤ value ∧ value < 2048 from of_decide_eq_true h12)
    next h12 =>
      split at h <;> simp only [Option.some.injEq] at h <;> subst steps <;>
        simp [encodable] <;> omega
  next => contradiction

theorem expand_length {value : Int} {steps : List Step} (h : expand value = some steps) :
    steps.length = 1 ∨ steps.length = 2 := by
  unfold expand at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h; subst steps; simp
    · split at h <;> simp only [Option.some.injEq] at h <;> subst steps <;> simp
  · contradiction

theorem truncate_sign32 (value : BitVec 32) : (value.signExtend 64).truncate 32 = value := by
  ext i hi
  simp only [BitVec.getElem_setWidth]
  rw [BitVec.getLsbD_eq_getElem (by omega), BitVec.getElem_signExtend]
  simp [hi]

theorem sign32_exact {value : Int} (h : fits32 value = true) :
    (BitVec.ofInt 32 value).signExtend 64 = BitVec.ofInt 64 value := by
  simp only [fits32, decide_eq_true_eq] at h
  unfold BitVec.signExtend
  rw [BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)]

theorem lui_addiw (upper lower : Int) (initial : X) :
    run [.lui upper, .addiw lower] initial =
      (BitVec.ofInt 32 (upper * 4096 + lower)).signExtend 64 := by
  simp only [run, List.foldl, step, truncate_sign32, ← BitVec.ofInt_add]

theorem expand_correct {value : Int} {steps : List Step}
    (h : expand value = some steps) (initial : X) : run steps initial = BitVec.ofInt 64 value := by
  unfold expand at h
  split at h
  next h32 =>
    split at h
    next =>
      simp only [Option.some.injEq] at h
      subst steps
      rfl
    next =>
      split at h
      next hz =>
        have he := split_exact value
        have hh : high value * 4096 = value := by omega
        simp only [Option.some.injEq] at h
        subst steps
        simpa only [run, List.foldl, step, hh] using sign32_exact h32
      next =>
        simp only [Option.some.injEq] at h
        rw [← h, lui_addiw, split_exact, sign32_exact h32]
  next => contradiction

/-- Masking LUI's input to its 20-bit field leaves the shifted word unchanged. -/
theorem lui_field_wrap (upper : Int) :
    BitVec.ofInt 32 ((upper % 1048576) * 4096) = BitVec.ofInt 32 (upper * 4096) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt]
  omega

theorem lui_field_bits (upper : Int) :
    (BitVec.ofInt 20 upper ++ 0#12) = BitVec.ofInt 32 (upper * 4096) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append, BitVec.toNat_ofInt, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.zero_mod, Nat.or_zero]
  omega

/-- Sign extension followed by word truncation recovers the encoded low bits. -/
theorem truncate_int (value : Int) :
    (BitVec.ofInt 64 value).truncate 32 = BitVec.ofInt 32 value := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  omega

/-- ADDIW's word operation is the existing RV64 ADDW semantics with an immediate. -/
theorem addiw_matches_addw (imm : Int) (acc : X) :
    step (.addiw imm) acc = Oak.RiscV.addw acc (BitVec.ofInt 64 imm) := by
  simp [step, Oak.RiscV.addw, Oak.RiscV.sextW, truncate_int]

/-- x0 discards writes; every other register is preserved by the materializer. -/
def writeResult (registers : BitVec 5 → X) (rd : BitVec 5) (value : X) : BitVec 5 → X :=
  fun r => if r = 0#5 then 0 else if r = rd then value else registers r

def execute (rd : BitVec 5) : List Step → (BitVec 5 → X) → (BitVec 5 → X)
  | [], registers => registers
  | s :: rest, registers =>
      execute rd rest (writeResult registers rd (step s (if rd = 0#5 then 0 else registers rd)))

theorem execute_destination {rd : BitVec 5} (hr : rd ≠ 0#5) (steps : List Step)
    (registers : BitVec 5 → X) : execute rd steps registers rd = run steps (registers rd) := by
  induction steps generalizing registers with
  | nil => rfl
  | cons s rest ih =>
      simpa [execute, run, writeResult, hr] using
        ih (writeResult registers rd (step s (registers rd)))

theorem execute_other {rd r : BitVec 5} (hz : r ≠ 0#5) (hr : r ≠ rd)
    (steps : List Step) (registers : BitVec 5 → X) : execute rd steps registers r = registers r := by
  induction steps generalizing registers with
  | nil => rfl
  | cons s rest ih =>
      simpa [execute, writeResult, hz, hr] using
        ih (writeResult registers rd (step s (if rd = 0#5 then 0 else registers rd)))

theorem execute_zero (rd : BitVec 5) (steps : List Step) (registers : BitVec 5 → X)
    (hz : registers 0#5 = 0#64) : execute rd steps registers 0#5 = 0#64 := by
  induction steps generalizing registers with
  | nil => exact hz
  | cons s rest ih => exact ih _ (by simp [writeResult])

theorem expanded_destination {value : Int} {steps : List Step} (h : expand value = some steps)
    (rd : BitVec 5) (registers : BitVec 5 → X) (hz : registers 0#5 = 0#64) :
    execute rd steps registers rd = if rd = 0#5 then 0#64 else BitVec.ofInt 64 value := by
  by_cases hr : rd = 0#5
  · subst rd
    simpa using execute_zero 0#5 steps registers hz
  · rw [execute_destination hr, expand_correct h]
    simp [hr]

/-- Independent decoders for the materializer's emitted subset. Field and
source-register checks refuse other instructions rather than guessing them. -/
def decodeWide (rd : BitVec 5) (word : BitVec 32) : Option Step :=
  if word.extractLsb' 7 5 ≠ rd then none
  else if word &&& 0x7f = 0x37 then some (.lui (word.extractLsb' 12 20).toInt)
  else if word &&& 0x707f = 0x13 ∧ word.extractLsb' 15 5 = 0#5 then
    some (.addi (word.extractLsb' 20 12).toInt)
  else if word &&& 0x707f = 0x1b ∧ word.extractLsb' 15 5 = rd then
    some (.addiw (word.extractLsb' 20 12).toInt)
  else none

def decodeShort (rd : BitVec 5) (word : BitVec 16) : Option Step :=
  let imm := (word.extractLsb' 12 1 ++ word.extractLsb' 2 5).toInt
  if rd = 0#5 ∧ word = 1#16 then some (.addi 0)
  else if rd = 0#5 ∨ word.extractLsb' 7 5 ≠ rd then none
  else if word &&& 0xe003 = 0x4001 then some (.addi imm)
  else if word &&& 0xe003 = 0x6001 ∧ rd ≠ 2#5 ∧ imm ≠ 0 then some (.lui imm)
  else if word &&& 0xe003 = 0x2001 then some (.addiw imm)
  else none

def decodeBytes (rd : BitVec 5) : List (BitVec 8) → Option (List Step)
  | [] => some []
  | b0 :: b1 :: rest =>
      if b0 &&& 3#8 = 3#8 then
        match rest with
        | b2 :: b3 :: tail => do
            let s ← decodeWide rd (b3 ++ b2 ++ b1 ++ b0)
            return s :: (← decodeBytes rd tail)
        | _ => none
      else do
        let s ← decodeShort rd (b1 ++ b0)
        return s :: (← decodeBytes rd rest)
  | _ => none

/-- Observation after executing the decoded materializer subset, with x0
hardwired to zero and every other register initialized to the supplied value. -/
def observeBytes (rd : BitVec 5) (initial : X) (bytes : List (BitVec 8)) : Option X := do
  let steps ← decodeBytes rd bytes
  return execute rd steps (fun r => if r = 0#5 then 0#64 else initial) rd

example : expand 2147483647 = some [.lui 524288, .addiw (-1)] := by decide
example : run [.lui 524288, .addiw (-1)] 0 = 2147483647#64 := by decide
example : step (.lui 524288) 0 + BitVec.ofInt 64 (-1) ≠ 2147483647#64 := by decide
-- The byte oracle refuses truncation, a changed destination, a changed ADDI
-- source, and the stack-pointer form at C.LUI's rd=x2 position.
example : observeBytes 8 0 [0x37, 0x04, 0x00] = none := by decide
example : observeBytes 8 0 [0x93, 0x00, 0x10, 0x00] = none := by decide
example : observeBytes 8 0 [0x13, 0x84, 0x14, 0x00] = none := by decide
example : decodeShort 2 0x6105 = none := by decide

end Oak.RiscVMaterialization
