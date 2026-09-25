import STRExecution.Defs

/-!
Explicit, arbitrary unimplemented callees of the copied Arm instruction.
There is no default instance and no successful placeholder implementation.
All callbacks can change state or fail, including feature queries and calls
that the old source marked pure. This permits effects beyond those annotations;
it does not establish a real-callee or full-architectural-state refinement.
The non-SP STR theorem does not invoke those extra branches.

Sail's Lean exporter erases the source constraints. In particular writeMem's
bit width and byte count are independent here because the generated generic
body does not carry its proof that 8 * (datasize / 8) = datasize. The proved
STR64 entry fixes these to 64 bits and 8 bytes. Real-callee instantiation must
respect these domains; this record itself does not establish that refinement.
-/

namespace STRExecution

structure Boundaries where
  HaveMTEExt : Unit → SailM Bool
  SetNotTagCheckedInstruction : Bool → SailM Unit
  ConstrainUnpredictable : Unpredictable → SailM Constraint
  EndOfInstruction : Unit → SailM Unit
  CheckSPAlignment : Unit → SailM Unit
  aget_SP : {width : Nat} → SailM (BitVec width)
  aset_SP : {width : Nat} → BitVec width → SailM Unit
  aset_X : {width : Nat} → Nat → BitVec width → SailM Unit
  aset_Mem : {width : Nat} → BitVec 64 → Nat → AccType → BitVec width → SailM Unit
  aget_Mem : BitVec 64 → (size : Nat) → AccType → SailM (BitVec (8 * size))
  Prefetch : BitVec 64 → BitVec 5 → SailM Unit
  SignExtend__0 : {width : Nat} → BitVec width → (size : Int) → SailM (BitVec size.toNat)
  ZeroExtend__0 : {width : Nat} → BitVec width → (size : Int) → SailM (BitVec size.toNat)

end STRExecution
