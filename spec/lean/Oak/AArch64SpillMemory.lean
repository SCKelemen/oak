import Oak.AArch64ControlFlow

/-! Byte-addressed, little-endian, no-fault semantics for the selector's
SP-relative unsigned-offset spill loads/stores. Signed narrow loads target W
registers. Stack allocation, permissions, faults and whole-program refinement
remain external obligations. -/
namespace Oak.AArch64SpillMemory
open Oak.AArch64BranchExecution (Registers readX)

inductive Kind | u8 | i8 | u16 | i16 | w32 | x64 deriving DecidableEq, Repr
def Kind.bytes : Kind → Nat | .u8 | .i8 => 1 | .u16 | .i16 => 2 | .w32 => 4 | .x64 => 8
def Kind.unsigned : Kind → Kind | .i8 => .u8 | .i16 => .u16 | k => k

def normalize (k : Kind) (v : BitVec 64) : BitVec 64 := match k with
  | .u8 => (v.truncate 8).zeroExtend 64
  | .i8 => ((v.truncate 8).signExtend 32).zeroExtend 64
  | .u16 => (v.truncate 16).zeroExtend 64
  | .i16 => ((v.truncate 16).signExtend 32).zeroExtend 64
  | .w32 => (v.truncate 32).zeroExtend 64
  | .x64 => v

abbrev Memory := Nat → BitVec 8
def storeBytes (n : Nat) (mem : Memory) (addr : Nat) (value : BitVec 64) : Memory :=
  fun a => if addr ≤ a ∧ a < addr + n then (value >>> (8 * (a - addr))).truncate 8 else mem a

def loadBytes : Nat → Memory → Nat → BitVec 64
  | 0, _, _ => 0
  | n+1, mem, addr => (mem addr).zeroExtend 64 ||| (loadBytes n mem (addr+1) <<< 8)

theorem store_outside (n : Nat) (mem : Memory) (addr a : Nat) (v : BitVec 64)
    (h : a < addr ∨ addr + n ≤ a) : storeBytes n mem addr v a = mem a := by
  simp only [storeBytes]; split <;> simp_all <;> omega

theorem load_store (k : Kind) (mem : Memory) (addr : Nat) (v : BitVec 64) :
    normalize k (loadBytes k.bytes (storeBytes k.bytes mem addr v) addr) = normalize k v := by
  cases k <;> simp [Kind.bytes, loadBytes, storeBytes, normalize, Nat.add_assoc] <;> bv_decide

theorem load_disjoint (n m : Nat) (mem : Memory) (a b : Nat) (v : BitVec 64)
    (h : a+n ≤ b ∨ b+m ≤ a) :
    loadBytes n (storeBytes m mem b v) a = loadBytes n mem a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [loadBytes]
    rw [store_outside m mem b a v (by omega), ih (a+1) (by omega)]

structure Access where
  load : Bool
  kind : Kind
  rt : BitVec 5
  offset : Nat
  deriving DecidableEq, Repr

/-- Fixed opcode and SP base; no pre/post-index, register offset or X signed loads. -/
def decode (word : BitVec 32) : Option Access := do
  let (load, k) ← match word &&& 0xffc003e0#32 with
    | 0x390003e0 => some (false, Kind.u8) | 0x790003e0 => some (false, Kind.u16)
    | 0xb90003e0 => some (false, Kind.w32) | 0xf90003e0 => some (false, Kind.x64)
    | 0x394003e0 => some (true, Kind.u8) | 0x39c003e0 => some (true, Kind.i8)
    | 0x794003e0 => some (true, Kind.u16) | 0x79c003e0 => some (true, Kind.i16)
    | 0xb94003e0 => some (true, Kind.w32) | 0xf94003e0 => some (true, Kind.x64)
    | _ => none
  pure ⟨load, k, word.extractLsb' 0 5, (word.extractLsb' 10 12).toNat * k.bytes⟩

structure State where
  core : Oak.AArch64BranchExecution.State
  sp : BitVec 64
  mem : Memory

def writeReg (regs : Registers) (rt : BitVec 5) (value : BitVec 64) : Registers :=
  fun r => if rt != 31#5 && r == rt then value else regs r

def execute (a : Access) (s : State) : State :=
  let address := s.sp.toNat + a.offset
  if a.load then
    { s with core := { s.core with pc := s.core.pc + 4, regs := writeReg s.core.regs a.rt (normalize a.kind (loadBytes a.kind.bytes s.mem address)) } }
  else
    { s with core := { s.core with pc := s.core.pc + 4 }, mem := storeBytes a.kind.bytes s.mem address (readX s.core.regs a.rt) }

/-- Reject misaligned SP and address-space wrapping; actual mappings and
access permissions are assumptions of the total-byte-memory projection. -/
def safe (a : Access) (s : State) : Bool :=
  decide (s.sp.toNat % 16 = 0 ∧ s.sp.toNat + a.offset + a.kind.bytes ≤ 2^64)
def step (word : BitVec 32) (s : State) : Option State := do
  let a ← decode word
  if safe a s then some (execute a s) else none

def checkPair (k : Kind) (src dst : BitVec 5) (offset : Nat) (st ld : BitVec 32) : Bool :=
  dst != 31#5 && decode st == some ⟨false, k.unsigned, src, offset⟩ &&
    decode ld == some ⟨true, k, dst, offset⟩

theorem checked_roundtrip (k : Kind) (src dst : BitVec 5) (offset : Nat)
    (st ld : BitVec 32) (s : State)
    (hc : checkPair k src dst offset st ld = true)
    (hs : s.sp.toNat % 16 = 0 ∧ s.sp.toNat + offset + k.bytes ≤ 2^64) :
    (step st s >>= step ld) = some
      { s with core := { s.core with pc := s.core.pc + 8, regs := writeReg s.core.regs dst (normalize k (readX s.core.regs src)) }, mem := storeBytes k.bytes s.mem (s.sp.toNat + offset) (readX s.core.regs src) } := by
  simp only [checkPair, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hc
  have hb : k.unsigned.bytes = k.bytes := by cases k <;> rfl
  simp only [step, hc.1.2, Bind.bind, Option.bind, safe, hb]
  simp only [hs, execute, Bool.false_eq_true, if_false]
  simp [step, hc.2, safe, execute, hs.1, hs.2, hb, load_store, BitVec.add_assoc]

/-- Physical byte address agrees with 64-bit addition when the access does not wrap. -/
theorem address_no_wrap (sp : BitVec 64) (offset bytes : Nat)
    (h : sp.toNat + offset + bytes ≤ 2^64) (hb : 0 < bytes) :
    (sp + BitVec.ofNat 64 offset).toNat = sp.toNat + offset := by
  simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod]
  omega

structure Slot where
  offset : Nat
  width : Nat
  deriving DecidableEq, Repr

def layoutValid (frame : Nat) (slots : List Slot) : Bool :=
  decide (frame ≤ 4080 ∧ frame % 16 = 0) &&
  slots.all (fun s => decide (s.width ∈ [1,2,4,8] ∧ s.offset % s.width = 0 ∧ s.offset+s.width ≤ frame)) &&
  (slots.zipIdx).all (fun (a,i) => (slots.zipIdx).all (fun (b,j) =>
    decide (i = j ∨ a.offset+a.width ≤ b.offset ∨ b.offset+b.width ≤ a.offset)))

theorem checked_slot (frame : Nat) (slots : List Slot) (slot : Slot)
    (h : layoutValid frame slots = true) (hm : slot ∈ slots) :
    slot.width ∈ [1,2,4,8] ∧ slot.offset % slot.width = 0 ∧ slot.offset+slot.width ≤ frame := by
  simp only [layoutValid, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.2 slot hm

theorem checked_disjoint (frame : Nat) (slots : List Slot) (a b : Slot) (i j : Nat)
    (h : layoutValid frame slots = true) (ha : (a,i) ∈ slots.zipIdx)
    (hb : (b,j) ∈ slots.zipIdx) (hne : i ≠ j) :
    a.offset+a.width ≤ b.offset ∨ b.offset+b.width ≤ a.offset := by
  simp only [layoutValid, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact (h.2 (a,i) ha (b,j) hb).resolve_left hne

theorem checked_slot_safe (frame : Nat) (slots : List Slot) (slot : Slot) (s : State) (k : Kind)
    (h : layoutValid frame slots = true) (hm : slot ∈ slots) (hw : slot.width = k.bytes)
    (hs : s.sp.toNat % 16 = 0 ∧ s.sp.toNat + frame ≤ 2^64) :
    s.sp.toNat % 16 = 0 ∧ s.sp.toNat + slot.offset + k.bytes ≤ 2^64 := by
  have bound := (checked_slot frame slots slot h hm).2.2
  constructor
  · exact hs.1
  · omega

theorem normalize_idempotent (k : Kind) (v : BitVec 64) :
    normalize k (normalize k v) = normalize k v := by
  cases k <;> simp only [normalize] <;> bv_decide

theorem writeReg_self (regs : Registers) (r : BitVec 5) (v : BitVec 64) (h : r ≠ 31#5) :
    writeReg regs r v r = v := by simp [writeReg, h]

theorem writeReg_other (regs : Registers) (r other : BitVec 5) (v : BitVec 64) (h : other ≠ r) :
    writeReg regs r v other = regs other := by simp [writeReg, h]

theorem checked_frame (frame : Nat) (slots : List Slot) (h : layoutValid frame slots = true) :
    frame ≤ 4080 ∧ frame % 16 = 0 := by
  simp only [layoutValid, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

theorem checked_store_preserves_slot (frame : Nat) (slots : List Slot) (a b : Slot)
    (i j sp : Nat) (mem : Memory) (v : BitVec 64)
    (h : layoutValid frame slots = true) (ha : (a,i) ∈ slots.zipIdx)
    (hb : (b,j) ∈ slots.zipIdx) (hne : i ≠ j) :
    loadBytes a.width (storeBytes b.width mem (sp+b.offset) v) (sp+a.offset) =
      loadBytes a.width mem (sp+a.offset) := by
  apply load_disjoint
  have hd := checked_disjoint frame slots a b i j h ha hb hne
  omega

end Oak.AArch64SpillMemory
