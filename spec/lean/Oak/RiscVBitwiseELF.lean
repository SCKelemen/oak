import Oak.MinimalELF
import Oak.RiscVBitwiseFunction

/-!
# Admitted RV64 ELF body bytes preserve the universal u32 result

The body address is explicit and must be aligned and inside the single RX
load segment. This does not assert that ELF entry/startup reaches that address
or supplies the arguments: the caller still supplies the LP64D entry register
state, including a return address. Linux process exit is not the observable;
the full 32-bit function result is. No OS loader implementation is verified.
-/
set_option autoImplicit false
namespace Oak.RiscVBitwiseELF
open Oak.BitwiseFunction (Op eval)
open Oak.RiscVCallExecution (Reg X)
open Oak.RiscVBitwiseFunction (functionBytes invoke)

theorem body_length (op : Op) : (functionBytes op).length = 8 := by
  cases op <;> decide +kernel

/-- Exact file and virtual address binding, with successful all-input execution
from the stated ABI state after flat loading of the admitted body bytes. -/
theorem admitted_function {image : Oak.MinimalELF.Bytes} {address : Nat} {op : Op}
    (accepted : Oak.MinimalELF.admittedBytes .rv64 image address (functionBytes op) = true)
    (left right : BitVec 32) (caller : Reg → X) :
    (Oak.MinimalELF.loadBytes image address 8).bind
      (fun bytes => invoke bytes left right (BitVec.ofNat 64 address) caller) =
      some (eval op left right) := by
  rw [← body_length op]
  exact Oak.MinimalELF.admitted_execution
    (fun bytes => invoke bytes left right (BitVec.ofNat 64 address) caller)
    (eval op left right) accepted
    (Oak.RiscVBitwiseFunction.function_success op left right (BitVec.ofNat 64 address) caller)
end Oak.RiscVBitwiseELF
