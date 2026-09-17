import Oak.AArch64Encoding

/-!
# AArch64 BRK encoding and selected exception arguments

The exact software-breakpoint row and a pure reading of its target-EL rule.
Current EL, EL2Enabled, and register contents are supplied values, not reads
from Arm state. Nothing here executes an exception or establishes that a
handler cannot resume the program.
-/

namespace Oak.AArch64BreakpointEncoding

open Oak.AArch64Encoding

-- OAK-A64-BRK-ENC-BEGIN (checked against asm/encodings_gen.go)
def brk : Encoding := ⟨"BRK_EX_exception", "brk", 0xd4200000#32, 0xffe0001f#32, [⟨"opc", 23, 3⟩, ⟨"imm16", 20, 16⟩, ⟨"op2", 4, 3⟩, ⟨"LL", 1, 2⟩]⟩
-- OAK-A64-BRK-ENC-END

def encodeBrk (immediate : BitVec 16) : BitVec 32 :=
  (brk.value &&& brk.mask) ||| (immediate.zeroExtend 32 <<< 5)

def bbmTrap : BitVec 32 := encodeBrk 1#16

theorem bbm_trap_word : bbmTrap = 0xd4200020#32 := by decide

theorem encodeBrk_fixed_bits (immediate : BitVec 16) :
    encodeBrk immediate &&& brk.mask = brk.value := by
  unfold encodeBrk brk
  bv_decide

theorem encodeBrk_extract (immediate : BitVec 16) :
    (encodeBrk immediate).extractLsb' 5 16 = immediate := by
  unfold encodeBrk brk
  bv_decide

/-- Pure target selection in `AArch64_SoftwareBreakpoint`. This is not EL2
    admission or a proof that the selected exception call is reached. -/
def softwareBreakpointTarget (currentEL : BitVec 2) (el2Enabled : Bool)
    (hcr mdcr : BitVec 64) : BitVec 2 :=
  let routeToEL2 := el2Enabled && (currentEL == 0#2 || currentEL == 1#2) &&
    (hcr.extractLsb' 27 1 == 1#1 || mdcr.extractLsb' 8 1 == 1#1)
  if (currentEL.toNat : Int) > 1 then currentEL
  else if routeToEL2 then 2#2 else 1#2

theorem software_breakpoint_at_el2 (enabled : Bool) (hcr mdcr : BitVec 64) :
    softwareBreakpointTarget 2#2 enabled hcr mdcr = 2#2 := by
  simp [softwareBreakpointTarget]

theorem software_breakpoint_at_el3 (enabled : Bool) (hcr mdcr : BitVec 64) :
    softwareBreakpointTarget 3#2 enabled hcr mdcr = 3#2 := by
  simp [softwareBreakpointTarget]

theorem software_breakpoint_lower_el (el : BitVec 2)
    (lower : el = 0#2 ∨ el = 1#2) (enabled : Bool) (hcr mdcr : BitVec 64) :
    softwareBreakpointTarget el enabled hcr mdcr =
      if enabled && (hcr.extractLsb' 27 1 == 1#1 || mdcr.extractLsb' 8 1 == 1#1)
      then 2#2 else 1#2 := by
  rcases lower with rfl | rfl <;> simp [softwareBreakpointTarget]

end Oak.AArch64BreakpointEncoding
