import Oak.AArch64SpillMemory

/-! Shared little-endian header representation for native LRAT argument loads.
The total byte memory does not establish permissions or fault freedom. -/
set_option autoImplicit false
namespace Oak.LRATHeaderMemory
open Oak.AArch64SpillMemory (Memory loadBytes)

def read32 (mem : Memory) (addr : Nat) : BitVec 32 :=
  (loadBytes 4 mem addr).truncate 32

def Represents (mem : Memory) (base : Nat) (words : Array UInt32) : Prop :=
  ∀ i, i < words.size → read32 mem (base + i * 4) = (words.getD i 0).toBitVec

end Oak.LRATHeaderMemory
