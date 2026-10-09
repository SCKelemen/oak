import ReturnExecution.Defs
namespace ReturnExecution
structure Boundaries where
 UsingAArch32 : Unit → SailM Bool
 IsInHost : Unit → SailM Bool
 SignExtend__1 : {N w : Nat} → BitVec w → SailM (BitVec N)
 ELUsingAArch32 : BitVec 2 → SailM Bool
 HavePACExt : Unit → SailM Bool
 HaveVirtHostExt : Unit → SailM Bool
 ELIsInHost : BitVec 2 → SailM Bool
 get_SCR : Unit → SailM (BitVec 32)
end ReturnExecution
