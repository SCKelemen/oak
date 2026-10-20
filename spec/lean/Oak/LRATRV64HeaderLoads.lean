import Oak.LRATRV64GuardCalls
import Oak.LRATHeaderMemory

/-! The emitted LW a0,0(rs1); ADDI s2,t0,0 before header allocation calls.
LW sign-extends; the guard normalizes its low 32 bits. A supplied address and
header representation connect this sequence to a source element. Address
formation, earlier branches, permissions and faults remain outside the proof. -/
set_option autoImplicit false
namespace Oak.LRATRV64HeaderLoads
open Oak.RiscVCallExecution
open Oak.LRATHeaderMemory
open Oak.AArch64SpillMemory (Memory)
open Oak.LRATRV64Bytes (bit)

def address (word : BitVec 32) (s : State) : Nat :=
  (read s (word.extractLsb' 15 5)).toNat

def loaded (s : State) (value : BitVec 32) : State :=
  ⟨s.pc + 4, write s 10 (value.signExtend 64)⟩

/-- Only LW into a0 with zero displacement; refuse address-space wrapping. -/
def load (word : BitVec 32) (mem : Memory) (s : State) : Option State :=
  if word &&& 0xfff07fff#32 = 0x00002503#32 ∧ address word s + 4 ≤ 2^64 then
    some (loaded s (read32 mem (address word s)))
  else none

/-- The intervening caller-state move is decoded by the existing ISA model. -/
def prepare (word : BitVec 32) (mem : Memory) (s : State) : Option State :=
  (load word mem s).bind (wide 0x00028913)

def prepared (s : State) (value : BitVec 32) : State :=
  addi 18 5 0 (loaded s value)

theorem prepare_header (word : BitVec 32) (mem : Memory) (s : State)
    (base i : Nat) (words : Array UInt32)
    (shape : word &&& 0xfff07fff#32 = 0x00002503#32)
    (atElement : address word s = base + i * 4)
    (representation : Represents mem base words)
    (inside : i < words.size) (extent : base + words.size * 4 ≤ 2^64) :
    prepare word mem s = some (prepared s (words.getD i 0).toBitVec) := by
  have bound : address word s + 4 ≤ 2^64 := by omega
  have value : read32 mem (address word s) = (words.getD i 0).toBitVec := by
    rw [atElement]; exact representation i inside
  unfold prepare load
  rw [if_pos ⟨shape, bound⟩, value]
  simp only [Option.bind_some]
  rfl

theorem prepared_argument (s : State) (value : UInt32) :
    UInt32.ofBitVec ((read (prepared s value.toBitVec) 10).truncate 32) = value := by
  have width (v : BitVec 32) : (v.signExtend 64).truncate 32 = v := by
    ext i hi
    have hi64 : i < 64 := by omega
    simp [BitVec.getElem_setWidth, BitVec.getElem_signExtend, BitVec.getLsbD_eq_getElem, hi, hi64]
  simp [prepared, loaded, addi, Oak.RiscVCallExecution.read, write, width]

theorem prepared_pc (s : State) (value : BitVec 32) :
    (prepared s value).pc = s.pc + 8 := by
  simp [prepared, loaded, addi, BitVec.add_assoc]

private theorem compose {α β γ : Type} (entry : Option α) (f : α → Option β)
    (g : β → γ) (s : α) (result : Option γ)
    (he : entry = some s) (hf : (f s).map g = result) :
    (entry.bind f).map g = result := by rw [he]; exact hf

namespace RV64
open Oak.LRATRV64GuardCalls.RV64

def loadAlloc (word : BitVec 32) (call : BitVec 32 × BitVec 32) (mem : Memory) (s : State) : Option State :=
  (prepare word mem s).bind (allocCall call)

theorem allocation_refines (word : BitVec 32) (call : BitVec 32 × BitVec 32)
    (mem : Memory) (s : State) (base i : Nat) (words : Array UInt32) (fuel : Nat)
    (shape : word &&& 0xfff07fff#32 = 0x00002503#32)
    (callShape : Oak.RV64Relocation.pairMatches true call.1 call.2 = true)
    (link : call.1.extractLsb' 7 5 = 1#5)
    (atElement : address word s = base + i * 4)
    (representation : Represents mem base words)
    (inside : i < words.size) (extent : base + words.size * 4 ≤ 2^64) :
    (loadAlloc word call mem s).map (fun out => read out 10) =
      (Oak.LRATBounds.lrat_alloc_fits (words.getD i 0) fuel).map bit := by
  have h := alloc_refines call (prepared s (words.getD i 0).toBitVec) fuel callShape link
  rw [prepared_argument] at h
  exact compose _ _ _ _ _ (prepare_header word mem s base i words shape atElement representation inside extent) h

theorem allocation_return (word : BitVec 32) (call : BitVec 32 × BitVec 32)
    (mem : Memory) (s : State) (base i : Nat) (words : Array UInt32)
    (shape : word &&& 0xfff07fff#32 = 0x00002503#32)
    (callShape : Oak.RV64Relocation.pairMatches true call.1 call.2 = true)
    (link : call.1.extractLsb' 7 5 = 1#5)
    (atElement : address word s = base + i * 4)
    (representation : Represents mem base words)
    (inside : i < words.size) (extent : base + words.size * 4 ≤ 2^64) :
    (loadAlloc word call mem s).map State.pc = some (clearLow (s.pc + 16)) := by
  have h := alloc_return call (prepared s (words.getD i 0).toBitVec) callShape link
  rw [prepared_pc] at h
  have sum : (s.pc + 8) + 8 = s.pc + 16 := by simp [BitVec.add_assoc]
  rw [sum] at h
  exact compose _ _ _ _ _ (prepare_header word mem s base i words shape atElement representation inside extent) h

end RV64

namespace RV64Compressed
open Oak.LRATRV64GuardCalls.RV64Compressed

def loadAlloc (word : BitVec 32) (call : BitVec 32 × BitVec 32) (mem : Memory) (s : State) : Option State :=
  (prepare word mem s).bind (allocCall call)

theorem allocation_refines (word : BitVec 32) (call : BitVec 32 × BitVec 32)
    (mem : Memory) (s : State) (base i : Nat) (words : Array UInt32) (fuel : Nat)
    (shape : word &&& 0xfff07fff#32 = 0x00002503#32)
    (callShape : Oak.RV64Relocation.pairMatches true call.1 call.2 = true)
    (link : call.1.extractLsb' 7 5 = 1#5)
    (atElement : address word s = base + i * 4)
    (representation : Represents mem base words)
    (inside : i < words.size) (extent : base + words.size * 4 ≤ 2^64) :
    (loadAlloc word call mem s).map (fun out => read out 10) =
      (Oak.LRATBounds.lrat_alloc_fits (words.getD i 0) fuel).map bit := by
  have h := alloc_refines call (prepared s (words.getD i 0).toBitVec) fuel callShape link
  rw [prepared_argument] at h
  exact compose _ _ _ _ _ (prepare_header word mem s base i words shape atElement representation inside extent) h

theorem allocation_return (word : BitVec 32) (call : BitVec 32 × BitVec 32)
    (mem : Memory) (s : State) (base i : Nat) (words : Array UInt32)
    (shape : word &&& 0xfff07fff#32 = 0x00002503#32)
    (callShape : Oak.RV64Relocation.pairMatches true call.1 call.2 = true)
    (link : call.1.extractLsb' 7 5 = 1#5)
    (atElement : address word s = base + i * 4)
    (representation : Represents mem base words)
    (inside : i < words.size) (extent : base + words.size * 4 ≤ 2^64) :
    (loadAlloc word call mem s).map State.pc = some (clearLow (s.pc + 16)) := by
  have h := alloc_return call (prepared s (words.getD i 0).toBitVec) callShape link
  rw [prepared_pc] at h
  have sum : (s.pc + 8) + 8 = s.pc + 16 := by simp [BitVec.add_assoc]
  rw [sum] at h
  exact compose _ _ _ _ _ (prepare_header word mem s base i words shape atElement representation inside extent) h

end RV64Compressed

end Oak.LRATRV64HeaderLoads
