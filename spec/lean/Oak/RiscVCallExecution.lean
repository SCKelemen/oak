import Oak.RV64Relocation
import Oak.RiscVMaterialization

/-! Execution of the AUIPC/ADDI/JALR subset, with IALIGN=16 and modular
64-bit registers/PC. Instruction fetch, memory and traps are outside this
model. Immediate arguments are decoded signed fields. Production byte
correspondence is checked separately, not claimed as universal Go refinement.
ISA: https://docs.riscv.org/reference/isa/unpriv/rv32.html -/
namespace Oak.RiscVCallExecution
abbrev X := BitVec 64
abbrev Reg := BitVec 5
structure State where
  pc : X
  regs : Reg → X

def read (s : State) (r : Reg) : X := if r = 0 then 0 else s.regs r
def write (s : State) (rd : Reg) (v : X) : Reg → X :=
  fun r => if r = 0 then 0 else if r = rd then v else s.regs r
-- Clear bit zero, expressed arithmetically so evenness is kernel arithmetic.
def clearLow (v : X) : X := BitVec.ofNat 64 (v.toNat / 2 * 2)
def auipc (rd : Reg) (upper : Int) (s : State) : State :=
  ⟨s.pc + 4, write s rd (s.pc + BitVec.ofInt 64 (upper * 4096))⟩
def addi (rd rs : Reg) (imm : Int) (s : State) : State :=
  ⟨s.pc + 4, write s rd (read s rs + BitVec.ofInt 64 imm)⟩
def jalr (rd rs : Reg) (imm : Int) (length : X) (s : State) : State :=
  ⟨clearLow (read s rs + BitVec.ofInt 64 imm), write s rd (s.pc + length)⟩
def pair (call : Bool) (rd : Reg) (upper lower : Int) (s : State) : State :=
  let first := auipc rd upper s
  if call then jalr rd rd lower 4 first else addi rd rd lower first

theorem read_write_same (s : State) (rd : Reg) (h : rd ≠ 0#5) (v : X) :
    read ⟨pc, write s rd v⟩ rd = v := by simp [read, write, h]
theorem write_other (s : State) (rd r : Reg) (hz : r ≠ 0#5) (hr : r ≠ rd) (v : X) :
    write s rd v r = s.regs r := by simp [write, hz, hr]
theorem write_zero (s : State) (rd : Reg) (v : X) : write s rd v 0 = 0 := by simp [write]
theorem clearLow_even (v : X) : (clearLow v).toNat % 2 = 0 := by
  simp only [clearLow, BitVec.toNat_ofNat]
  omega
theorem clearLow_eq (v : X) (h : v.toNat % 2 = 0) : clearLow v = v := by
  apply BitVec.eq_of_toNat_eq
  simp only [clearLow, BitVec.toNat_ofNat]
  have := v.isLt
  omega

theorem jalr_target (s : State) (rd rs : Reg) (imm : Int) (length : X) :
    (jalr rd rs imm length s).pc = clearLow (read s rs + BitVec.ofInt 64 imm) := rfl
-- In particular rs=rd reads the old register before writing the return PC.
theorem jalr_alias (s : State) (rd : Reg) (h : rd ≠ 0#5) (imm : Int) (length : X) :
    (jalr rd rd imm length s).pc = clearLow (s.regs rd + BitVec.ofInt 64 imm) ∧
    (jalr rd rd imm length s).regs rd = s.pc + length := by simp [jalr, read, write, h]
theorem jalr_preserves (s : State) (rd rs r : Reg) (hz : r ≠ 0#5) (hr : r ≠ rd)
    (imm : Int) (length : X) : (jalr rd rs imm length s).regs r = s.regs r := by
  simp [jalr, write, hz, hr]
theorem return_pc (s : State) (length : X) :
    (jalr 0 1 0 length s).pc = clearLow (s.regs 1) := by simp [jalr, read]

theorem pair_target_sum (s : State) (rd : Reg) (hr : rd ≠ 0#5) (upper lower : Int) :
    (pair true rd upper lower s).pc =
      clearLow (s.pc + BitVec.ofInt 64 (upper * 4096 + lower)) := by
  simp [pair, jalr, auipc, read, write, hr, BitVec.ofInt_add, BitVec.add_assoc]
theorem pair_link (s : State) (rd : Reg) (hr : rd ≠ 0#5) (upper lower : Int) :
    (pair true rd upper lower s).regs rd = s.pc + 8 := by
  simp [pair, jalr, auipc, write, hr, BitVec.add_assoc]
theorem pair_address (s : State) (rd : Reg) (hr : rd ≠ 0#5) (upper lower : Int) :
    (pair false rd upper lower s).regs rd =
      s.pc + BitVec.ofInt 64 (upper * 4096 + lower) := by
  simp [pair, addi, auipc, read, write, hr, BitVec.ofInt_add, BitVec.add_assoc]
theorem pair_fallthrough (s : State) (rd : Reg) (upper lower : Int) :
    (pair false rd upper lower s).pc = s.pc + 8 := by
  simp [pair, addi, auipc, BitVec.add_assoc]
theorem pair_preserves (s : State) (call : Bool) (rd r : Reg) (hz : r ≠ 0#5) (hr : r ≠ rd)
    (upper lower : Int) : (pair call rd upper lower s).regs r = s.regs r := by
  cases call <;> simp [pair, jalr, addi, auipc, write, hz, hr]
theorem pair_zero (s : State) (call : Bool) (rd : Reg) (upper lower : Int) :
    (pair call rd upper lower s).regs 0 = 0 := by
  cases call <;> simp [pair, jalr, addi, write]

-- Connect relocation's decoded displacement theorem to modular execution.
def executePatched (call : Bool) (rd : Reg) (words : BitVec 32 × BitVec 32) (s : State) :=
  pair call rd (words.1.extractLsb' 12 20).toInt (words.2.extractLsb' 20 12).toInt s

theorem relocated_sum {call : Bool} {w0 w1 : BitVec 32} {place target : Nat}
    {patched : BitVec 32 × BitVec 32}
    (h : Oak.RV64Relocation.relocate call w0 w1 place target = some patched) :
    BitVec.ofNat 64 place + BitVec.ofInt 64 (Oak.RV64Relocation.decode patched.1 patched.2) =
      BitVec.ofNat 64 target := by
  have he := Oak.RV64Relocation.relocate_reaches h
  have hv := congrArg (BitVec.ofInt 64) he
  simpa [BitVec.ofInt_add] using hv

theorem relocated_call {w0 w1 : BitVec 32} {place target : Nat}
    {patched : BitVec 32 × BitVec 32}
    (h : Oak.RV64Relocation.relocate true w0 w1 place target = some patched)
    (rd : Reg) (hr : rd ≠ 0#5) (regs : Reg → X) :
    (executePatched true rd patched ⟨BitVec.ofNat 64 place, regs⟩).pc = BitVec.ofNat 64 target := by
  rw [executePatched, pair_target_sum _ _ hr]
  change clearLow (BitVec.ofNat 64 place + BitVec.ofInt 64 (Oak.RV64Relocation.decode patched.1 patched.2)) = _
  rw [relocated_sum h]
  apply clearLow_eq
  have hf := ((Oak.RV64Relocation.relocate_eq_some_iff true w0 w1 place target patched).mp h).1
  have he := Oak.RV64Relocation.call_target_even hf
  simp only [BitVec.toNat_ofNat]
  omega

theorem relocated_address {w0 w1 : BitVec 32} {place target : Nat}
    {patched : BitVec 32 × BitVec 32}
    (h : Oak.RV64Relocation.relocate false w0 w1 place target = some patched)
    (rd : Reg) (hr : rd ≠ 0#5) (regs : Reg → X) :
    (executePatched false rd patched ⟨BitVec.ofNat 64 place, regs⟩).regs rd = BitVec.ofNat 64 target := by
  rw [executePatched, pair_address _ _ hr]
  exact relocated_sum h

-- Independent instruction decoder. C.JR/C.JALR have a two-byte link address;
-- rs=0 is reserved/C.EBREAK, so neither is admitted here.
def wide (w : BitVec 32) (s : State) : Option State :=
  let rd := w.extractLsb' 7 5
  let rs := w.extractLsb' 15 5
  let imm := (w.extractLsb' 20 12).toInt
  if w &&& 0x7f = 0x17 then some (auipc rd (w.extractLsb' 12 20).toInt s)
  else if w &&& 0x707f = 0x13 then some (addi rd rs imm s)
  else if w &&& 0x707f = 0x67 then some (jalr rd rs imm 4 s)
  else none

-- The executable decoder agrees with the pair semantics for every admitted
-- fixed-field shape; this is not merely a displacement calculation.
theorem wide_pair (call : Bool) (upper lower : BitVec 32) (s : State)
    (hp : Oak.RV64Relocation.pairMatches call upper lower = true) :
    (do let first ← wide upper s; wide lower first) =
      some (executePatched call (upper.extractLsb' 7 5) (upper, lower) s) := by
  cases call <;>
    simp [Oak.RV64Relocation.pairMatches, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hp
  all_goals
    rcases hp with ⟨⟨⟨⟨h0, hn⟩, hd⟩, hs⟩, hl⟩
    have hnot : lower &&& 0x7f#32 ≠ 0x17#32 := by bv_decide
    simp_all [wide, executePatched, pair]

theorem patch_shape (call : Bool) (upper lower : BitVec 32) (hi : BitVec 20) (lo : BitVec 12)
    (hp : Oak.RV64Relocation.pairMatches call upper lower = true) :
    Oak.RV64Relocation.pairMatches call (Oak.RV64Relocation.patchUpper upper hi)
      (Oak.RV64Relocation.patchLower lower lo) = true := by
  unfold Oak.RV64Relocation.pairMatches Oak.RV64Relocation.patchUpper Oak.RV64Relocation.patchLower at *
  bv_decide

theorem relocated_shape {call : Bool} {w0 w1 : BitVec 32} {place target : Nat}
    {patched : BitVec 32 × BitVec 32}
    (h : Oak.RV64Relocation.relocate call w0 w1 place target = some patched) :
    Oak.RV64Relocation.pairMatches call patched.1 patched.2 = true := by
  obtain ⟨_, hp, he⟩ := (Oak.RV64Relocation.relocate_eq_some_iff call w0 w1 place target patched).mp h
  rw [he]
  exact patch_shape call w0 w1 _ _ hp

/-- Executing the actual patched instruction words reaches the call target
and writes place+8, or loads the address and falls through to place+8. -/
theorem relocated_words {call : Bool} {w0 w1 : BitVec 32} {place target : Nat}
    {patched : BitVec 32 × BitVec 32}
    (h : Oak.RV64Relocation.relocate call w0 w1 place target = some patched)
    (regs : Reg → X) :
    ((do let first ← wide patched.1 ⟨BitVec.ofNat 64 place, regs⟩
         wide patched.2 first).map
      (fun (s : State) => (s.pc, s.regs (patched.1.extractLsb' 7 5)))) =
      some (if call then (BitVec.ofNat 64 target, BitVec.ofNat 64 place + 8)
        else (BitVec.ofNat 64 place + 8, BitVec.ofNat 64 target)) := by
  have hp := relocated_shape h
  have hr : patched.1.extractLsb' 7 5 ≠ 0#5 := by
    simp [Oak.RV64Relocation.pairMatches, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hp
    exact hp.1.1.1.1.2
  rw [wide_pair call patched.1 patched.2 _ hp]
  cases call
  · simp only [Option.map_some, Bool.false_eq_true, ↓reduceIte]
    congr 1
    apply Prod.ext
    · simp [executePatched, pair, addi, auipc, BitVec.add_assoc]
    · exact relocated_address h _ hr regs
  · simp only [Option.map_some, ↓reduceIte]
    congr 1
    apply Prod.ext
    · exact relocated_call h _ hr regs
    · simp [executePatched, pair, jalr, auipc, write, hr, BitVec.add_assoc]

def short (w : BitVec 16) (s : State) : Option State :=
  let rs := w.extractLsb' 7 5
  if rs = 0 then none
  else if w &&& 0xf07f = 0x8002 then some (jalr 0 rs 0 2 s)
  else if w &&& 0xf07f = 0x9002 then some (jalr 1 rs 0 2 s)
  else none

def bytes (code : List (BitVec 8)) (s : State) : Option State :=
  match code with
  | [] => some s
  | b0 :: b1 :: rest =>
    if b0 &&& 3 = 3 then
      match rest with
      | b2 :: b3 :: tail =>
        if b0 &&& 0x7f = 0x67 ∧ tail ≠ [] then none
        else do bytes tail (← wide (b3 ++ b2 ++ b1 ++ b0) s)
      | _ => none
    else if rest = [] then short (b1 ++ b0) s else none
  | _ => none

def observe (code : List (BitVec 8)) (pc initial : X) (r : Reg) : Option (X × X × X) := do
  let s ← bytes code ⟨pc, fun _ => initial⟩
  return (s.pc, s.regs r, s.regs 0)
example : bytes [0x82, 0x80, 0x82, 0x80] ⟨0, fun _ => 0⟩ = none := by decide
example : bytes [0x67, 0x80, 0, 0, 0x82, 0x80] ⟨0, fun _ => 0⟩ = none := by decide
example : bytes [0x67, 0x80, 0] ⟨0, fun _ => 0⟩ = none := by decide
example : short 0x9002 ⟨0, fun _ => 0⟩ = none := by decide
end Oak.RiscVCallExecution
