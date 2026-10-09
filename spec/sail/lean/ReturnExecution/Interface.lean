import ReturnExecution.Defs
namespace ReturnExecution
structure Boundaries where
 IsInHost : Unit → SailM Bool
 SignExtend__1 : {N w : Nat} → BitVec w → SailM (BitVec N)
 ELIsInHost : BitVec 2 → SailM Bool
 __IMPDEF_boolean : String → SailM Bool
 get_SCR : Unit → SailM (BitVec 32)
end ReturnExecution
