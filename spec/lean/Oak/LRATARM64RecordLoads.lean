import Oak.LRATARM64HeaderLoads

/-! Record fits argument preparation: LDR W1,[X19,Wm,UXTW #2],
MOV W0,#8, MOV W2,W20, then BL and the pinned guard.
The live base, length, index and non-wrapping memory extent remain premises. -/
set_option autoImplicit false
namespace Oak.LRATARM64RecordLoads
open Oak.LRATARM64Bytes
open Oak.AArch64BitwiseFunction (readW writeW)
open Oak.AArch64SpillMemory (Memory)
open Oak.LRATARM64HeaderLoads (index address Represents read32)

def prepared (s : State) (value : BitVec 32) : State :=
  { s with regs := writeW (writeW (writeW s.regs 1 value) 0 8) 2 (readW s.regs 20)
           pc := s.pc + 12 }

/-- Only the observed load and two fixed moves are admitted. -/
def prepare (load start limit : BitVec 32) (mem : Memory) (s : State) : Option State :=
  if load &&& 0xffe0ffff#32 = 0xb8605a61#32 ∧
      start = 0x52800100#32 ∧ limit = 0x2a1403e2#32 ∧ address load s + 4 ≤ 2^64 then
    some (prepared s (read32 mem (address load s)))
  else none

theorem prepare_record (load start limit : BitVec 32) (mem : Memory) (s : State)
    (words : Array UInt32)
    (shape : load &&& 0xffe0ffff#32 = 0xb8605a61#32)
    (hs : start = 0x52800100#32) (hl : limit = 0x2a1403e2#32)
    (representation : Represents mem (s.regs 19).toNat words)
    (inside : index load s < words.size)
    (extent : (s.regs 19).toNat + words.size * 4 ≤ 2^64) :
    prepare load start limit mem s = some (prepared s (words.getD (index load s) 0).toBitVec) := by
  have bound : address load s + 4 ≤ 2^64 := by unfold address; omega
  unfold prepare
  rw [if_pos ⟨shape, hs, hl, bound⟩]
  exact congrArg (fun v => some (prepared s v)) (representation (index load s) inside)

theorem prepared_arguments (s : State) (v : UInt32) :
    UInt32.ofBitVec (readW (prepared s v.toBitVec).regs 0) = 8 ∧
    UInt32.ofBitVec (readW (prepared s v.toBitVec).regs 1) = v ∧
    UInt32.ofBitVec (readW (prepared s v.toBitVec).regs 2) =
      UInt32.ofBitVec (readW s.regs 20) := by
  simp [prepared, readW, writeW,
    BitVec.extractLsb'_setWidth_of_le (by decide : 0 + 32 ≤ 64)]

def recordFits (load start limit call : BitVec 32) (mem : Memory) (s : State) : Option State :=
  (prepare load start limit mem s).bind (Oak.LRATARM64GuardCalls.fitsCall call)

private theorem compose {α β γ : Type} (entry : Option α) (f : α → Option β)
    (g : β → γ) (s : α) (result : Option γ)
    (he : entry = some s) (hf : (f s).map g = result) :
    (entry.bind f).map g = result := by rw [he]; exact hf

theorem record_refines (load start limit call : BitVec 32) (mem : Memory) (s : State)
    (words : Array UInt32) (fuel : Nat)
    (shape : load &&& 0xffe0ffff#32 = 0xb8605a61#32)
    (hs : start = 0x52800100#32) (hl : limit = 0x2a1403e2#32)
    (hc : call &&& 0xfc000000#32 = 0x94000000#32)
    (representation : Represents mem (s.regs 19).toNat words)
    (inside : index load s < words.size)
    (extent : (s.regs 19).toNat + words.size * 4 ≤ 2^64)
    (hi : index load s = 3)
    (length : UInt32.ofBitVec (readW s.regs 20) = UInt32.ofNat words.size) :
    (recordFits load start limit call mem s).map (fun out => out.regs 0) =
      (Oak.LRATBounds.lrat_fits 8 (words.getD 3 0) (UInt32.ofNat words.size) fuel).map bit := by
  have h := Oak.LRATARM64GuardCalls.fits_refines call
    (prepared s (words.getD (index load s) 0).toBitVec) fuel hc
  rw [(prepared_arguments s _).1, (prepared_arguments s _).2.1,
    (prepared_arguments s _).2.2, length] at h
  simpa only [hi, recordFits] using compose _ _ _ _ _
    (prepare_record load start limit mem s words shape hs hl representation inside extent) h

theorem record_return (load start limit call : BitVec 32) (mem : Memory) (s : State)
    (words : Array UInt32)
    (shape : load &&& 0xffe0ffff#32 = 0xb8605a61#32)
    (hs : start = 0x52800100#32) (hl : limit = 0x2a1403e2#32)
    (hc : call &&& 0xfc000000#32 = 0x94000000#32)
    (representation : Represents mem (s.regs 19).toNat words)
    (inside : index load s < words.size)
    (extent : (s.regs 19).toNat + words.size * 4 ≤ 2^64) :
    (recordFits load start limit call mem s).map State.pc = some (s.pc + 16) := by
  have h := Oak.LRATARM64GuardCalls.fits_return call
    (prepared s (words.getD (index load s) 0).toBitVec) hc
  simp only [prepared, BitVec.add_assoc] at h
  exact compose _ _ _ _ _
    (prepare_record load start limit mem s words shape hs hl representation inside extent) h

theorem record_sp (load start limit call : BitVec 32) (mem : Memory) (s : State)
    (words : Array UInt32)
    (shape : load &&& 0xffe0ffff#32 = 0xb8605a61#32)
    (hs : start = 0x52800100#32) (hl : limit = 0x2a1403e2#32)
    (hc : call &&& 0xfc000000#32 = 0x94000000#32)
    (representation : Represents mem (s.regs 19).toNat words)
    (inside : index load s < words.size)
    (extent : (s.regs 19).toNat + words.size * 4 ≤ 2^64) :
    (recordFits load start limit call mem s).map State.sp = some s.sp :=
  compose _ _ _ _ _
    (prepare_record load start limit mem s words shape hs hl representation inside extent)
    (Oak.LRATARM64GuardCalls.fits_sp call _ hc)

end Oak.LRATARM64RecordLoads
