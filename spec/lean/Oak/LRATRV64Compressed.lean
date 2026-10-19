import Oak.LRATRV64Bytes

/-! Default hosted RV64 LRAT guards, including C.SLLI, C.SRLI, C.ADDIW and
C.JR ra mixed with 32-bit words. The decoder independently expands supported
compressed fields; execution retains their real 2/4-byte lengths. Unsupported
or truncated encodings fail closed. This is Oak's internal ISA model, not
instruction fetch, traps, or a Sail execution correspondence theorem. -/
namespace Oak.LRATRV64Compressed
open Oak.RiscVCallExecution
open Oak.LRATNativeGuards
open Oak.LRATRV64Bytes (step bit)

/-- Narrow C-extension decoder. Hints/reserved encodings are refused. -/
def expand (h : BitVec 16) : Option (BitVec 32) :=
  let rd := (h.extractLsb' 7 5).zeroExtend 32
  let compact := (h.extractLsb' 7 3).zeroExtend 32 + 8
  let imm := (h.extractLsb' 12 1) ++ (h.extractLsb' 2 5)
  if h = 0x8082 then some 0x00008067 -- C.JR ra
  else if h &&& 0xe003 = 0x0002 ∧ rd ≠ 0 ∧ imm ≠ 0 then
    some (0x1013 ||| (rd <<< 7) ||| (rd <<< 15) ||| (imm.zeroExtend 32 <<< 20))
  else if h &&& 0xec03 = 0x8001 ∧ imm ≠ 0 then
    some (0x5013 ||| (compact <<< 7) ||| (compact <<< 15) ||| (imm.zeroExtend 32 <<< 20))
  else if h &&& 0xe003 = 0x2001 ∧ rd ≠ 0 then
    some (0x1b ||| (rd <<< 7) ||| (rd <<< 15) ||| ((imm.signExtend 12).zeroExtend 32 <<< 20))
  else none

abbrev Instruction := BitVec 32 × X

def decode : List (BitVec 8) → Option (List Instruction)
  | [] => some []
  | a :: b :: rest =>
    let h := b ++ a
    if h &&& 3 = 3 then
      match rest with
      | c :: d :: tail =>
        (decode tail).map ((Oak.RiscVBranchEncoding.fromBytes a b c d, 4) :: ·)
      | _ => none
    else do
      let w ← expand h
      let tail ← decode rest
      return (w, 2) :: tail
  | _ => none

def advance (i : Instruction) (s : State) : Option State :=
  (step i.1 s).map (fun out => {out with pc := s.pc + i.2})

def run : List Instruction → State → Option State
  | [], _ => none
  | [i], s => if i.1 = 0x00008067 then some (jalr 0 1 0 i.2 s) else none
  | i :: rest, s => (advance i s).bind (run rest)

def executeBytes (bytes : List (BitVec 8)) (s : State) : Option State :=
  (decode bytes).bind (fun code => run code s)

def fitsCode : List Instruction := Oak.LRATRV64Bytes.fitsWords.zip
  [2, 2, 2, 2, 2, 2, 4, 4, 4, 2, 4, 4, 4, 4, 2]
def allocCode : List Instruction := Oak.LRATRV64Bytes.allocWords.zip [2, 2, 4, 2, 4, 2]
def halfBytes (h : BitVec 16) : List (BitVec 8) := [h.truncate 8, (h >>> 8).truncate 8]
def fitsBytes : List (BitVec 8) :=
  ([0x1502, 0x9101, 0x1582, 0x9181, 0x1602, 0x9201, 0x32b3, 0x00a6,
    0xc293, 0x0012, 0x0333, 0x40a6, 0x1302, 0x5313, 0x0203, 0x3533,
    0x00b3, 0x4513, 0x0015, 0x7533, 0x0055, 0x8082] : List (BitVec 16)).flatMap halfBytes
def allocBytes : List (BitVec 8) :=
  ([0x1502, 0x9101, 0x02b7, 0x4000, 0x32fd, 0x3533, 0x0055, 0x8082] : List (BitVec 16)).flatMap halfBytes

theorem decode_fits : decode fitsBytes = some fitsCode := by decide
theorem decode_alloc : decode allocBytes = some allocCode := by decide

theorem fits_result (s : State) :
    (run fitsCode s).map (fun out => read out 10) =
      some (bit (rvFits (read s 10) (read s 11) (read s 12))) := by
  simp [fitsCode, Oak.LRATRV64Bytes.fitsWords, run, advance, step, List.zip, Oak.RiscVComparison.step, Oak.RiscVComparison.decode,
    Oak.RiscVComparison.Instruction.execute, Oak.RiscVComparison.bit,
    Oak.RiscVBitwiseFunction.executeWord, Oak.RiscVBitwiseFunction.decodeOp,
    Oak.RiscVBitwiseFunction.body, Oak.RiscVBitwiseFunction.eval64,
    jalr, Oak.RiscVCallExecution.read, write, bit, rvFits, lowWord]
  all_goals
    simp only [BitVec.ult_iff_lt, BitVec.le_def, BitVec.lt_def]
    split <;> split <;> split <;> first | rfl | omega

theorem alloc_result (s : State) :
    (run allocCode s).map (fun out => read out 10) =
      some (bit (rvAlloc (read s 10))) := by
  simp [allocCode, Oak.LRATRV64Bytes.allocWords, run, advance, step, List.zip, Oak.RiscVComparison.step, Oak.RiscVComparison.decode,
    Oak.RiscVComparison.Instruction.execute, Oak.RiscVComparison.bit,
    jalr, Oak.RiscVCallExecution.read, write, bit, rvAlloc, lowWord]
  simp only [BitVec.ult_iff_lt]

theorem decoded_result (bytes : List (BitVec 8)) (words : List Instruction)
    (s : State) (v : X) (hd : decode bytes = some words)
    (hr : (run words s).map (fun out => read out 10) = some v) :
    (executeBytes bytes s).map (fun out => read out 10) = some v := by
  unfold executeBytes
  simp only [hd, Option.bind_some]
  exact hr

theorem fits_bytes_result (s : State) :
    (executeBytes fitsBytes s).map (fun out => read out 10) =
      some (bit (rvFits (read s 10) (read s 11) (read s 12))) :=
  decoded_result fitsBytes fitsCode s _ decode_fits (fits_result s)

theorem alloc_bytes_result (s : State) :
    (executeBytes allocBytes s).map (fun out => read out 10) =
      some (bit (rvAlloc (read s 10))) :=
  decoded_result allocBytes allocCode s _ decode_alloc (alloc_result s)

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
    (run fitsCode s).map State.pc = some (clearLow (read s 1)) := by
  simp [fitsCode, Oak.LRATRV64Bytes.fitsWords, run, advance, step, List.zip, Oak.RiscVComparison.step, Oak.RiscVComparison.decode,
    Oak.RiscVComparison.Instruction.execute, Oak.RiscVComparison.bit,
    Oak.RiscVBitwiseFunction.executeWord, Oak.RiscVBitwiseFunction.decodeOp,
    Oak.RiscVBitwiseFunction.body, Oak.RiscVBitwiseFunction.eval64,
    jalr, Oak.RiscVCallExecution.read, write]

theorem fits_frame (s : State) (r : Reg)
    (h0 : r ≠ 0#5) (h5 : r ≠ 5#5) (h10 : r ≠ 10#5) (h6 : r ≠ 6#5) (h11 : r ≠ 11#5) (h12 : r ≠ 12#5) :
    (run fitsCode s).map (fun out => out.regs r) = some (s.regs r) := by
  simp [fitsCode, Oak.LRATRV64Bytes.fitsWords, run, advance, step, List.zip, Oak.RiscVComparison.step, Oak.RiscVComparison.decode,
    Oak.RiscVComparison.Instruction.execute, Oak.RiscVComparison.bit,
    Oak.RiscVBitwiseFunction.executeWord, Oak.RiscVBitwiseFunction.decodeOp,
    Oak.RiscVBitwiseFunction.body, Oak.RiscVBitwiseFunction.eval64,
    jalr, Oak.RiscVCallExecution.read, write, h0, h5, h10, h6, h11, h12]

theorem alloc_return (s : State) :
    (run allocCode s).map State.pc = some (clearLow (read s 1)) := by
  simp [allocCode, Oak.LRATRV64Bytes.allocWords, run, advance, step, List.zip, Oak.RiscVComparison.step, Oak.RiscVComparison.decode,
    Oak.RiscVComparison.Instruction.execute, Oak.RiscVComparison.bit,
    jalr, Oak.RiscVCallExecution.read, write]

theorem alloc_frame (s : State) (r : Reg)
    (h0 : r ≠ 0#5) (h5 : r ≠ 5#5) (h10 : r ≠ 10#5) :
    (run allocCode s).map (fun out => out.regs r) = some (s.regs r) := by
  simp [allocCode, Oak.LRATRV64Bytes.allocWords, run, advance, step, List.zip, Oak.RiscVComparison.step, Oak.RiscVComparison.decode,
    Oak.RiscVComparison.Instruction.execute, Oak.RiscVComparison.bit,
    jalr, Oak.RiscVCallExecution.read, write, h0, h5, h10]

end Oak.LRATRV64Compressed
