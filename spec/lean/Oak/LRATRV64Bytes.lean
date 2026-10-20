import Oak.LRATNativeGuards
import Oak.RiscVComparison
import Oak.RiscVBitwiseFunction

/-! Exact uncompressed RV64 LRAT guard bodies, independently decoded from
words. Production tests pin these words to the encoder and ELF symbol bytes.
This is internal execution, not fetch, traps, caller, encoder, or whole-checker
correctness. Register, comparison and JALR semantics reuse existing models. -/
namespace Oak.LRATRV64Bytes
open Oak.RiscVCallExecution
open Oak.LRATNativeGuards

/-- Fail-closed decoder for the additional shift and literal instructions. -/
def step (w : BitVec 32) (s : State) : Option State :=
  let rd := w.extractLsb' 7 5
  let rs := w.extractLsb' 15 5
  let sh := (w.extractLsb' 20 6).toNat
  let imm := (w.extractLsb' 20 12).signExtend 32
  if w &&& 0xfc00707f = 0x1013 then
    some ⟨s.pc + 4, write s rd (read s rs <<< sh)⟩
  else if w &&& 0xfc00707f = 0x5013 then
    some ⟨s.pc + 4, write s rd (read s rs >>> sh)⟩
  else if w &&& 0x7f = 0x37 then
    some ⟨s.pc + 4, write s rd ((w &&& 0xfffff000).signExtend 64)⟩
  else if w &&& 0x707f = 0x1b then
    some ⟨s.pc + 4, write s rd (((read s rs).truncate 32 + imm).signExtend 64)⟩
  else match Oak.RiscVComparison.step w s with
    | some after => some after
    | none => Oak.RiscVBitwiseFunction.executeWord w s

/-- Exactly one final RET; trailing words and unsupported instructions fail. -/
def run : List (BitVec 32) → State → Option State
  | [], _ => none
  | [w], s => if w = 0x00008067 then some (jalr 0 1 0 4 s) else none
  | w :: rest, s => (step w s).bind (run rest)

def fitsWords : List (BitVec 32) :=
  [0x02051513, 0x02055513, 0x02059593, 0x0205d593,
   0x02061613, 0x02065613, 0x00a632b3, 0x0012c293,
   0x40a60333, 0x02031313, 0x02035313, 0x00b33533,
   0x00154513, 0x00557533, 0x00008067]
def allocWords : List (BitVec 32) :=
  [0x02051513, 0x02055513, 0x400002b7, 0xfff2829b, 0x00553533, 0x00008067]

def decodeWords : List (BitVec 8) → Option (List (BitVec 32))
  | [] => some []
  | a :: b :: c :: d :: rest =>
      (decodeWords rest).map (Oak.RiscVBranchEncoding.fromBytes a b c d :: ·)
  | _ => none

def executeBytes (bytes : List (BitVec 8)) (s : State) : Option State :=
  (decodeWords bytes).bind (fun words => run words s)
def fitsBytes := fitsWords.flatMap Oak.RiscVBranchEncoding.wordBytes
def allocBytes := allocWords.flatMap Oak.RiscVBranchEncoding.wordBytes

theorem decode_fits : decodeWords fitsBytes = some fitsWords := by decide
theorem decode_alloc : decodeWords allocBytes = some allocWords := by decide

def bit (b : Bool) : X := if b then 1 else 0

theorem fits_result (s : State) :
    (run fitsWords s).map (fun out => read out 10) =
      some (bit (rvFits (read s 10) (read s 11) (read s 12))) := by
  simp [fitsWords, run, step, Oak.RiscVComparison.step, Oak.RiscVComparison.decode,
    Oak.RiscVComparison.Instruction.execute, Oak.RiscVComparison.bit,
    Oak.RiscVBitwiseFunction.executeWord, Oak.RiscVBitwiseFunction.decodeOp,
    Oak.RiscVBitwiseFunction.body, Oak.RiscVBitwiseFunction.eval64,
    jalr, Oak.RiscVCallExecution.read, write, bit, rvFits, lowWord]
  all_goals
    simp only [BitVec.ult_iff_lt, BitVec.le_def, BitVec.lt_def]
    split <;> split <;> split <;> first | rfl | omega

theorem alloc_result (s : State) :
    (run allocWords s).map (fun out => read out 10) =
      some (bit (rvAlloc (read s 10))) := by
  simp [allocWords, run, step, Oak.RiscVComparison.step, Oak.RiscVComparison.decode,
    Oak.RiscVComparison.Instruction.execute, Oak.RiscVComparison.bit,
    jalr, Oak.RiscVCallExecution.read, write, bit, rvAlloc, lowWord]
  simp only [BitVec.ult_iff_lt]

theorem decoded_result (bytes : List (BitVec 8)) (words : List (BitVec 32))
    (s : State) (v : X) (hd : decodeWords bytes = some words)
    (hr : (run words s).map (fun out => read out 10) = some v) :
    (executeBytes bytes s).map (fun out => read out 10) = some v := by
  unfold executeBytes
  simp only [hd, Option.bind_some]
  exact hr

theorem fits_bytes_result (s : State) :
    (executeBytes fitsBytes s).map (fun out => read out 10) =
      some (bit (rvFits (read s 10) (read s 11) (read s 12))) :=
  decoded_result fitsBytes fitsWords s _ decode_fits (fits_result s)

theorem alloc_bytes_result (s : State) :
    (executeBytes allocBytes s).map (fun out => read out 10) =
      some (bit (rvAlloc (read s 10))) :=
  decoded_result allocBytes allocWords s _ decode_alloc (alloc_result s)

theorem fits_bytes_sound (s : State)
    (h : (executeBytes fitsBytes s).map (fun out => read out 10) = some 1) :
    ((read s 10).truncate 32).toNat + ((read s 11).truncate 32).toNat ≤
      ((read s 12).truncate 32).toNat := by
  rw [fits_bytes_result] at h
  have hp : rvFits (read s 10) (read s 11) (read s 12) = true := by
    cases hval : rvFits (read s 10) (read s 11) (read s 12) with
    | false => simp only [hval, bit, Bool.false_eq_true, if_false, Option.some.injEq] at h; contradiction
    | true => rfl
  exact rv_fits_sound _ _ _ hp

theorem alloc_bytes_sound (s : State)
    (h : (executeBytes allocBytes s).map (fun out => read out 10) = some 1) :
    (((read s 10).truncate 32).toNat + 1) * 4 < 4294967296 := by
  rw [alloc_bytes_result] at h
  have hp : rvAlloc (read s 10) = true := by
    cases hval : rvAlloc (read s 10) with
    | false => simp only [hval, bit, Bool.false_eq_true, if_false, Option.some.injEq] at h; contradiction
    | true => rfl
  exact rv_alloc_sound _ hp

theorem fits_return (s : State) :
    (run fitsWords s).map State.pc = some (clearLow (read s 1)) := by
  simp [fitsWords, run, step, Oak.RiscVComparison.step, Oak.RiscVComparison.decode,
    Oak.RiscVComparison.Instruction.execute, Oak.RiscVComparison.bit,
    Oak.RiscVBitwiseFunction.executeWord, Oak.RiscVBitwiseFunction.decodeOp,
    Oak.RiscVBitwiseFunction.body, Oak.RiscVBitwiseFunction.eval64,
    jalr, Oak.RiscVCallExecution.read, write]

theorem fits_frame (s : State) (r : Reg)
    (h0 : r ≠ 0#5) (h5 : r ≠ 5#5) (h10 : r ≠ 10#5) (h6 : r ≠ 6#5) (h11 : r ≠ 11#5) (h12 : r ≠ 12#5) :
    (run fitsWords s).map (fun out => out.regs r) = some (s.regs r) := by
  simp [fitsWords, run, step, Oak.RiscVComparison.step, Oak.RiscVComparison.decode,
    Oak.RiscVComparison.Instruction.execute, Oak.RiscVComparison.bit,
    Oak.RiscVBitwiseFunction.executeWord, Oak.RiscVBitwiseFunction.decodeOp,
    Oak.RiscVBitwiseFunction.body, Oak.RiscVBitwiseFunction.eval64,
    jalr, Oak.RiscVCallExecution.read, write, h0, h5, h10, h6, h11, h12]

theorem alloc_return (s : State) :
    (run allocWords s).map State.pc = some (clearLow (read s 1)) := by
  simp [allocWords, run, step, Oak.RiscVComparison.step, Oak.RiscVComparison.decode,
    Oak.RiscVComparison.Instruction.execute, Oak.RiscVComparison.bit,
    jalr, Oak.RiscVCallExecution.read, write]

theorem alloc_frame (s : State) (r : Reg)
    (h0 : r ≠ 0#5) (h5 : r ≠ 5#5) (h10 : r ≠ 10#5) :
    (run allocWords s).map (fun out => out.regs r) = some (s.regs r) := by
  simp [allocWords, run, step, Oak.RiscVComparison.step, Oak.RiscVComparison.decode,
    Oak.RiscVComparison.Instruction.execute, Oak.RiscVComparison.bit,
    jalr, Oak.RiscVCallExecution.read, write, h0, h5, h10]

end Oak.LRATRV64Bytes
