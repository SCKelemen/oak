import Oak.NativeBitwiseObject

/- Audit every exported theorem closure. Expected axioms are a subset of
   propext, Quot.sound, Classical.choice; no sorryAx or evaluator oracle. -/
#print axioms Oak.NativeBitwiseObject.fromUInt8_length
#print axioms Oak.NativeBitwiseObject.toUInt8_length
#print axioms Oak.NativeBitwiseObject.to_fromUInt8
#print axioms Oak.NativeBitwiseObject.from_toUInt8
#print axioms Oak.NativeBitwiseObject.fromUInt8_injective
#print axioms Oak.NativeBitwiseObject.profile_unique
#print axioms Oak.NativeBitwiseObject.profile_named
#print axioms Oak.NativeBitwiseObject.extract_sound
#print axioms Oak.NativeBitwiseObject.accepted_named_body
#print axioms Oak.NativeBitwiseObject.accepted_layout_bounds
#print axioms Oak.NativeBitwiseObject.accepted_architecture_no_relocations
#print axioms Oak.NativeBitwiseObject.named_load
#print axioms Oak.NativeBitwiseObject.named_fetch_byte
#print axioms Oak.NativeBitwiseObject.accepted_arm_execution
#print axioms Oak.NativeBitwiseObject.accepted_rv_execution
