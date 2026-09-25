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

/-- Explicit callees of the complete original aset_Mem body. They retain
arbitrary effects/failures; in particular alignment is not assumed successful
and endian reversal is not assumed pure. The generated SCTLR_EL2 read is
concrete and guarded by the original short-circuit control structure.
Width/count constraints erased by Sail are supplied only for proved entries. -/
structure MemoryBoundaries where
  HaveNV2Ext : Unit → SailM Bool
  BigEndian : Unit → SailM Bool
  BigEndianReverse : {width : Nat} → BitVec width → SailM (BitVec width)
  AArch64_CheckAlignment : BitVec 64 → Int → AccType → Bool → SailM Bool
  Align__1 : {width : Nat} → BitVec width → Int → SailM (BitVec width)
  AArch64_aset_MemSingle : {width : Nat} → BitVec 64 → Nat → AccType → Bool → BitVec width → SailM Unit

/-- Explicit deeper callees of the complete original MemSingle body. Full
address/fault/access descriptors are retained; no VA-to-PA cast substitutes for
translation. Abort and TagCheckFail are arbitrary actions: if one returns
normally, the original body continues. No architectural non-return premise is
silently installed. These callbacks do not establish full-state refinement. -/
structure MemSingleBoundaries where
  AArch64_TranslateAddress : BitVec 64 → AccType → Bool → Bool → Int → SailM AddressDescriptor
  AArch64_Abort : BitVec 64 → FaultRecord → SailM Unit
  ProcessorID : Unit → SailM Int
  ClearExclusiveByAddress : FullAddress → Int → Int → SailM Unit
  CreateAccessDescriptor : AccType → SailM AccessDescriptor
  AccessIsTagChecked : BitVec 64 → AccType → SailM Bool
  TransformTag : BitVec 64 → SailM (BitVec 4)
  CheckTag : AddressDescriptor → BitVec 4 → Bool → SailM Bool
  TagCheckFail : BitVec 64 → Bool → SailM Unit
  aset__Mem : AddressDescriptor → (size : Nat) → AccessDescriptor → BitVec (8 * size) → SailM Unit

end STRExecution
