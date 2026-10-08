import ScalarExecution.Defs

/-! Arbitrary effectful cut callees of intact extracted Arm bodies. There is no
successful default instance. Full architectural configuration, control checks,
SP, authentication, and BranchTo behavior are not defined by this interface. -/
namespace ScalarExecution
structure Boundaries where
  LSL_C : {w : Nat} → BitVec w → Nat → SailM (BitVec w × BitVec 1)
  LSR : {w : Nat} → BitVec w → Nat → SailM (BitVec w)
  ASR : {w : Nat} → BitVec w → Nat → SailM (BitVec w)
  ROR : {w : Nat} → BitVec w → Nat → SailM (BitVec w)
  HaveBTIExt : Unit → SailM Bool
  UsingAArch32 : Unit → SailM Bool
  BranchTargetCheck : Unit → SailM Unit
  HavePACExt : Unit → SailM Bool
  aget_SP : {w : Nat} → SailM (BitVec w)
  AuthIA : BitVec 64 → BitVec 64 → SailM (BitVec 64)
  AuthIB : BitVec 64 → BitVec 64 → SailM (BitVec 64)
  aget_PC : Unit → SailM (BitVec 64)
  BranchTo : {w : Nat} → BitVec w → BranchType → SailM Unit
end ScalarExecution
