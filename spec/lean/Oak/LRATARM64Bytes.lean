import Oak.LRATNativeGuards
import Oak.AArch64BitwiseFunction
import Oak.LRATRV64Bytes

/-! Exact A64 LRAT guard bytes in the no-fault scalar projection. W-register
reads/writes and subtraction flags reuse existing models. No fetch, alignment,
translation, PostDecode, BranchTo, traps, or full Sail execution is claimed. -/
namespace Oak.LRATARM64Bytes
open Oak.AssemblerSemantics (Flags flagsOf)
open Oak.AArch64BitwiseFunction (Registers readW writeW readX)

structure State where
  regs : Registers
  pc : BitVec 64
  sp : BitVec 64
  flags : Flags

-- CSET aliases CSINC Wd,WZR,WZR with the inverse condition in the word.
def lsValue (f : Flags) : BitVec 32 := if f.c && !f.z then 0 else 1
def loValue (f : Flags) : BitVec 32 := if f.c then 0 else 1

theorem ls_compare (a b : BitVec 32) :
    lsValue (flagsOf a b) = if a ≤ b then 1 else 0 := by
  unfold lsValue flagsOf
  simp only [← BitVec.le_def]
  bv_decide

theorem lo_compare (a b : BitVec 32) :
    loValue (flagsOf a b) = if a < b then 1 else 0 := by
  unfold loValue flagsOf
  simp only [← BitVec.le_def]
  bv_decide

/-- Only the emitted 32-bit, unshifted register forms and MOVN/MOVZ are
admitted. The CSET decoder fixes both source registers to WZR. -/
def step (w : BitVec 32) (s : State) : Option State :=
  let rd := w.extractLsb' 0 5
  let rn := w.extractLsb' 5 5
  let rm := w.extractLsb' 16 5
  let a := readW s.regs rn
  let b := readW s.regs rm
  let imm := (w.extractLsb' 5 16).zeroExtend 32 <<< ((w.extractLsb' 21 1).toNat * 16)
  if w &&& 0xffe0fc1f = 0x6b00001f then
    some { s with pc := s.pc + 4, flags := flagsOf a b }
  else if w &&& 0xffe0fc00 = 0x4b000000 then
    some { s with pc := s.pc + 4, regs := writeW s.regs rd (a - b) }
  else if w &&& 0xffffffe0 = 0x1a9f87e0 then
    some { s with pc := s.pc + 4, regs := writeW s.regs rd (lsValue s.flags) }
  else if w &&& 0xffffffe0 = 0x1a9f27e0 then
    some { s with pc := s.pc + 4, regs := writeW s.regs rd (loValue s.flags) }
  else if w &&& 0xffe0fc00 = 0x0a000000 then
    some { s with pc := s.pc + 4, regs := writeW s.regs rd (a &&& b) }
  else if w &&& 0xffc00000 = 0x12800000 then
    some { s with pc := s.pc + 4, regs := writeW s.regs rd (~~~imm) }
  else if w &&& 0xffc00000 = 0x52800000 then
    some { s with pc := s.pc + 4, regs := writeW s.regs rd imm }
  else none

def run : List (BitVec 32) → State → Option State
  | [], _ => none
  | [w], s => if w = 0xd65f03c0 then some { s with pc := readX s.regs 30 } else none
  | w :: rest, s => (step w s).bind (run rest)

def fitsWords : List (BitVec 32) :=
  [0x6b02001f, 0x1a9f87e9, 0x4b00004a, 0x6b0a003f, 0x1a9f87e0, 0x0a090000, 0xd65f03c0]
def allocWords : List (BitVec 32) := [0x12b80009, 0x6b09001f, 0x1a9f27e0, 0xd65f03c0]
def fitsBytes := fitsWords.flatMap Oak.RiscVBranchEncoding.wordBytes
def allocBytes := allocWords.flatMap Oak.RiscVBranchEncoding.wordBytes

def executeBytes (bytes : List (BitVec 8)) (s : State) : Option State :=
  (Oak.LRATRV64Bytes.decodeWords bytes).bind (fun words => run words s)

theorem decode_fits : Oak.LRATRV64Bytes.decodeWords fitsBytes = some fitsWords := by decide
theorem decode_alloc : Oak.LRATRV64Bytes.decodeWords allocBytes = some allocWords := by decide

def bit (b : Bool) : BitVec 64 := if b then 1 else 0

theorem fits_result (s : State) :
    (run fitsWords s).map (fun out => out.regs 0) =
      some (bit (Oak.LRATNativeGuards.armFits (readW s.regs 0) (readW s.regs 1) (readW s.regs 2))) := by
  simp [fitsWords, run, step, readW, writeW, ls_compare, bit, Oak.LRATNativeGuards.armFits]
  all_goals bv_decide

theorem alloc_result (s : State) :
    (run allocWords s).map (fun out => out.regs 0) =
      some (bit (Oak.LRATNativeGuards.armAlloc (readW s.regs 0))) := by
  simp [allocWords, run, step, readW, writeW, lo_compare, bit, Oak.LRATNativeGuards.armAlloc]
  all_goals bv_decide

theorem decoded_result (bytes : List (BitVec 8)) (words : List (BitVec 32))
    (s : State) (v : BitVec 64) (hd : Oak.LRATRV64Bytes.decodeWords bytes = some words)
    (hr : (run words s).map (fun out => out.regs 0) = some v) :
    (executeBytes bytes s).map (fun out => out.regs 0) = some v := by
  unfold executeBytes
  simp only [hd, Option.bind_some]
  exact hr

theorem fits_bytes_result (s : State) :
    (executeBytes fitsBytes s).map (fun out => out.regs 0) =
      some (bit (Oak.LRATNativeGuards.armFits (readW s.regs 0) (readW s.regs 1) (readW s.regs 2))) :=
  decoded_result fitsBytes fitsWords s _ decode_fits (fits_result s)

theorem alloc_bytes_result (s : State) :
    (executeBytes allocBytes s).map (fun out => out.regs 0) =
      some (bit (Oak.LRATNativeGuards.armAlloc (readW s.regs 0))) :=
  decoded_result allocBytes allocWords s _ decode_alloc (alloc_result s)

theorem fits_bytes_sound (s : State)
    (h : (executeBytes fitsBytes s).map (fun out => out.regs 0) = some 1) :
    (readW s.regs 0).toNat + (readW s.regs 1).toNat ≤ (readW s.regs 2).toNat := by
  rw [fits_bytes_result] at h
  have hp : Oak.LRATNativeGuards.armFits (readW s.regs 0) (readW s.regs 1) (readW s.regs 2) = true := by
    cases hv : Oak.LRATNativeGuards.armFits (readW s.regs 0) (readW s.regs 1) (readW s.regs 2) with
    | false => simp only [hv, bit, Bool.false_eq_true, if_false, Option.some.injEq] at h; contradiction
    | true => rfl
  exact Oak.LRATNativeGuards.arm_fits_sound (UInt32.ofBitVec (readW s.regs 0))
    (UInt32.ofBitVec (readW s.regs 1)) (UInt32.ofBitVec (readW s.regs 2)) hp

theorem alloc_bytes_sound (s : State)
    (h : (executeBytes allocBytes s).map (fun out => out.regs 0) = some 1) :
    ((readW s.regs 0).toNat + 1) * 4 < 4294967296 := by
  rw [alloc_bytes_result] at h
  have hp : Oak.LRATNativeGuards.armAlloc (readW s.regs 0) = true := by
    cases hv : Oak.LRATNativeGuards.armAlloc (readW s.regs 0) with
    | false => simp only [hv, bit, Bool.false_eq_true, if_false, Option.some.injEq] at h; contradiction
    | true => rfl
  apply (Oak.LRATBounds.alloc_fits_iff (UInt32.ofBitVec (readW s.regs 0)) 0).mp
  rw [Oak.LRATNativeGuards.arm_alloc_extracted]
  exact congrArg some hp

theorem fits_return (s : State) :
    (run fitsWords s).map State.pc = some (s.regs 30) := by
  simp [fitsWords, run, step, readW, writeW, readX]

theorem fits_sp (s : State) :
    (run fitsWords s).map State.sp = some s.sp := by
  simp [fitsWords, run, step]

theorem fits_frame (s : State) (r : BitVec 5)
    (h0 : r ≠ 0#5) (h9 : r ≠ 9#5) (h10 : r ≠ 10#5) :
    (run fitsWords s).map (fun out => out.regs r) = some (s.regs r) := by
  simp [fitsWords, run, step, readW, writeW, readX, h0, h9, h10]

theorem alloc_return (s : State) :
    (run allocWords s).map State.pc = some (s.regs 30) := by
  simp [allocWords, run, step, readW, writeW, readX]

theorem alloc_sp (s : State) :
    (run allocWords s).map State.sp = some s.sp := by
  simp [allocWords, run, step]

theorem alloc_frame (s : State) (r : BitVec 5)
    (h0 : r ≠ 0#5) (h9 : r ≠ 9#5) :
    (run allocWords s).map (fun out => out.regs r) = some (s.regs r) := by
  simp [allocWords, run, step, readW, writeW, readX, h0, h9]

end Oak.LRATARM64Bytes
