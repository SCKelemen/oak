import Oak.LRATARM64GuardCalls
import Oak.AArch64SpillMemory

/-! The emitted LDR W0,[X19,Wm,UXTW #2] immediately before allocation guards.
Memory uses the existing total, little-endian byte model. A supplied header
representation, live X19 base, in-range index and non-wrapping extent justify
the access. This does not prove their establishment by earlier instructions,
permissions, translation, faults, or whole-preflight control flow. -/
set_option autoImplicit false
namespace Oak.LRATARM64HeaderLoads
open Oak.LRATARM64Bytes
open Oak.AArch64BitwiseFunction (readW writeW)
open Oak.AArch64SpillMemory (Memory loadBytes)

def read32 (mem : Memory) (addr : Nat) : BitVec 32 :=
  (loadBytes 4 mem addr).truncate 32

def Represents (mem : Memory) (base : Nat) (words : Array UInt32) : Prop :=
  ∀ i, i < words.size → read32 mem (base + i * 4) = (words.getD i 0).toBitVec

def index (word : BitVec 32) (s : State) : Nat :=
  (readW s.regs (word.extractLsb' 16 5)).toNat

def address (word : BitVec 32) (s : State) : Nat :=
  (s.regs 19).toNat + index word s * 4

def loaded (s : State) (value : BitVec 32) : State :=
  { s with regs := writeW s.regs 0 value, pc := s.pc + 4 }

/-- Fixed 32-bit load, X19 base, W0 destination, UXTW scaling by four.
Other widths, extensions, shifts, bases and destinations are refused. -/
def load (word : BitVec 32) (mem : Memory) (s : State) : Option State :=
  if word &&& 0xffe0ffff#32 = 0xb8605a60#32 ∧ address word s + 4 ≤ 2^64 then
    some (loaded s (read32 mem (address word s)))
  else none

theorem load_header (word : BitVec 32) (mem : Memory) (s : State) (words : Array UInt32)
    (shape : word &&& 0xffe0ffff#32 = 0xb8605a60#32)
    (representation : Represents mem (s.regs 19).toNat words)
    (inside : index word s < words.size)
    (extent : (s.regs 19).toNat + words.size * 4 ≤ 2^64) :
    load word mem s = some (loaded s (words.getD (index word s) 0).toBitVec) := by
  have bound : address word s + 4 ≤ 2^64 := by unfold address; omega
  have value := representation (index word s) inside
  unfold load
  rw [if_pos ⟨shape, bound⟩]
  exact congrArg (fun v => some (loaded s v)) value

/-- Compose the actual load, ordinary BL, and pinned allocation guard body. -/
def loadAlloc (word call : BitVec 32) (mem : Memory) (s : State) : Option State :=
  (load word mem s).bind (Oak.LRATARM64GuardCalls.allocCall call)

private theorem compose {α β γ : Type} (entry : Option α) (f : α → Option β)
    (g : β → γ) (s : α) (result : Option γ)
    (he : entry = some s) (hf : (f s).map g = result) :
    (entry.bind f).map g = result := by rw [he]; exact hf

/-- Exact source predicate, including rejection and unrestricted upper bits. -/
theorem allocation_refines (word call : BitVec 32) (mem : Memory) (s : State)
    (words : Array UInt32) (fuel : Nat)
    (shape : word &&& 0xffe0ffff#32 = 0xb8605a60#32)
    (callShape : call &&& 0xfc000000#32 = 0x94000000#32)
    (representation : Represents mem (s.regs 19).toNat words)
    (inside : index word s < words.size)
    (extent : (s.regs 19).toNat + words.size * 4 ≤ 2^64) :
    (loadAlloc word call mem s).map (fun out => out.regs 0) =
      (Oak.LRATBounds.lrat_alloc_fits (words.getD (index word s) 0) fuel).map bit := by
  have h := Oak.LRATARM64GuardCalls.alloc_refines call
    (loaded s (words.getD (index word s) 0).toBitVec) fuel callShape
  have hv (v : UInt32) : UInt32.ofBitVec (readW (loaded s v.toBitVec).regs 0) = v := by
    simp [loaded, readW, writeW, BitVec.extractLsb'_setWidth_of_le (by decide : 0 + 32 ≤ 64)]
  rw [hv] at h
  exact compose _ _ _ _ _ (load_header word mem s words shape representation inside extent) h

theorem allocation_return (word call : BitVec 32) (mem : Memory) (s : State)
    (words : Array UInt32)
    (shape : word &&& 0xffe0ffff#32 = 0xb8605a60#32)
    (callShape : call &&& 0xfc000000#32 = 0x94000000#32)
    (representation : Represents mem (s.regs 19).toNat words)
    (inside : index word s < words.size)
    (extent : (s.regs 19).toNat + words.size * 4 ≤ 2^64) :
    (loadAlloc word call mem s).map State.pc = some (s.pc + 8) := by
  have h := Oak.LRATARM64GuardCalls.alloc_return call
    (loaded s (words.getD (index word s) 0).toBitVec) callShape
  simp only [loaded, BitVec.add_assoc] at h
  exact compose _ _ _ _ _ (load_header word mem s words shape representation inside extent) h

theorem allocation_sp (word call : BitVec 32) (mem : Memory) (s : State)
    (words : Array UInt32)
    (shape : word &&& 0xffe0ffff#32 = 0xb8605a60#32)
    (callShape : call &&& 0xfc000000#32 = 0x94000000#32)
    (representation : Represents mem (s.regs 19).toNat words)
    (inside : index word s < words.size)
    (extent : (s.regs 19).toNat + words.size * 4 ≤ 2^64) :
    (loadAlloc word call mem s).map State.sp = some s.sp :=
  compose _ _ _ _ _ (load_header word mem s words shape representation inside extent)
    (Oak.LRATARM64GuardCalls.alloc_sp call _ callShape)

end Oak.LRATARM64HeaderLoads
