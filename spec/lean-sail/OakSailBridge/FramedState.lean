import OakSailBridge.FramedMemoryExecution
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
namespace OakSailBridge.BitwiseDecoded
open LeanRV64D Sail Sail.ConcurrencyInterfaceV1
attribute [local irreducible] store64

theorem memoryConfig_store64 (s : State) (regions : List PMA_Region) (addr : Nat)
    (value : BitVec 64) (hc : MemoryConfig s regions) :
    MemoryConfig (store64 s addr value) regions := by
  constructor
  · simpa only [store64_regs] using hc.privilege
  · simpa only [store64_regs] using hc.status
  · simpa only [store64_regs] using hc.masking
  · simpa only [store64_regs] using hc.regions
  · simpa only [store64_regs] using hc.htif
  · simpa only [store64_regs] using hc.pmpcfg
  · simpa only [store64_regs] using hc.pmpaddr

/-- Only registers actually written by the frame are covered here. -/
def FrameRegister (r : Register) : Prop :=
  r = .x2 ∨ r = .x9 ∨ r = .x18 ∨ r = .x10 ∨ r = .nextPC

theorem memoryConfig_set (s : State) (regions : List PMA_Region)
    (r : Register) (v : RegisterType r) (h : FrameRegister r)
    (hc : MemoryConfig s regions) : MemoryConfig (setRegister s r v) regions := by
  rcases hc with ⟨hp,hm,hmask,hr,ht,hc,ha⟩
  rcases h with h|h|h|h|h <;> subst r <;> constructor <;>
    simpa [setRegister, Std.ExtDHashMap.get?_insert] using ‹_›

theorem config_set_frame (s : State) (r : Register) (v : RegisterType r)
    (h : FrameRegister r) (hc : ConfigOK s) : ConfigOK (setRegister s r v) := by
  rcases h with h|h|h|h|h <;> subst r <;>
    simpa [ConfigOK, setRegister, Std.ExtDHashMap.get?_insert] using hc

theorem config_store64 (s : State) (addr : Nat) (value : BitVec 64)
    (hc : ConfigOK s) : ConfigOK (store64 s addr value) := by
  simpa only [ConfigOK, store64_regs] using hc

theorem setRegister_self (s : State) (r : Register) (v : RegisterType r)
    (h : s.regs.get? r = some v) : setRegister s r v = s := by
  have he : s.regs.insert r v = s.regs := by
    apply Std.ExtDHashMap.ext_get?
    intro q
    by_cases hq : r = q
    · subst q; simpa [Std.ExtDHashMap.get?_insert] using h.symm
    · simp [Std.ExtDHashMap.get?_insert, hq]
  cases s
  simp_all [setRegister]

theorem setRegister_same (s : State) (r : Register) (v w : RegisterType r) :
    setRegister (setRegister s r v) r w = setRegister s r w := by
  have he : (s.regs.insert r v).insert r w = s.regs.insert r w := by
    apply Std.ExtDHashMap.ext_get?
    intro q
    by_cases hq : r = q <;> simp [Std.ExtDHashMap.get?_insert, hq]
  cases s
  simp_all [setRegister]

theorem setRegister_comm (s : State) (r q : Register) (v : RegisterType r)
    (w : RegisterType q) (h : r ≠ q) :
    setRegister (setRegister s r v) q w = setRegister (setRegister s q w) r v := by
  have he : (s.regs.insert r v).insert q w = (s.regs.insert q w).insert r v := by
    apply Std.ExtDHashMap.ext_get?
    intro t
    by_cases hr : r = t
    · subst t; simp [Std.ExtDHashMap.get?_insert, h, Ne.symm h]
    · by_cases hq : q = t <;> simp [Std.ExtDHashMap.get?_insert, hr, hq]
  cases s
  simp_all [setRegister]

end OakSailBridge.BitwiseDecoded
