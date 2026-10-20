import Oak.WasmBitwiseModuleCopy

/-! Kernel regression controls for the universal copy proof. These finite
examples supplement the quantified theorems; they do not establish a complete
module-writer refinement or source-compilation result. -/

open Oak.WasmAssembler
set_option autoImplicit false

-- Nonuniform sentinels on both sides, with a precise copy and final index.
example : wasm_bitwise_module.loop2 #[19, 23, 29, 31, 37, 41, 43]
    #[65, 90, 48] 3 0 2 4 = some (#[19, 23, 65, 90, 48, 41, 43], 3) := by
  decide +kernel

-- A partially consumed source starts at pos + i, not at pos.
example : wasm_bitwise_module.loop2 #[19, 23, 29, 31, 37, 41, 43]
    #[65, 90, 48] 3 1 2 3 = some (#[19, 23, 29, 90, 48, 41, 43], 3) := by
  decide +kernel

-- Missing the final guard is fuel exhaustion, not a returned partial success.
example : wasm_bitwise_module.loop2 #[19, 23, 29, 31, 37, 41, 43]
    #[65, 90, 48] 3 0 2 3 = none := by decide +kernel

-- Copy correctness is independent of the separate ASCII-validation phase.
example : wasm_bitwise_module.loop2 #[19, 23, 29, 31, 37]
    #[0, 128, 255] 3 0 1 4 = some (#[19, 0, 128, 255, 37], 3) := by
  decide +kernel

-- A zero-length copy may be positioned at the exact destination end.
example : wasm_bitwise_module.loop2 #[19, 23] #[] 0 0 2 1 =
    some (#[19, 23], 0) := by decide +kernel

-- Full capacity with no spare suffix remains a successful exact copy.
example : wasm_bitwise_module.loop2 #[19, 23, 29, 31] #[65, 90] 2 0 2 3 =
    some (#[19, 23, 65, 90], 2) := by decide +kernel

-- Wrong prefix, copied byte, suffix, and final index are all rejected.
example : wasm_bitwise_module.loop2 #[19, 23, 29, 31, 37] #[65, 90] 2 0 1 3 ≠
    some (#[0, 65, 90, 31, 37], 2) := by decide +kernel
example : wasm_bitwise_module.loop2 #[19, 23, 29, 31, 37] #[65, 90] 2 0 1 3 ≠
    some (#[19, 65, 91, 31, 37], 2) := by decide +kernel
example : wasm_bitwise_module.loop2 #[19, 23, 29, 31, 37] #[65, 90] 2 0 1 3 ≠
    some (#[19, 65, 90, 0, 37], 2) := by decide +kernel
example : wasm_bitwise_module.loop2 #[19, 23, 29, 31, 37] #[65, 90] 2 0 1 3 ≠
    some (#[19, 65, 90, 31, 37], 1) := by decide +kernel

-- The raw extracted array semantics can drop a store outside the theorem's
-- fitting domain. This result is deliberately NOT claimed as a safe success.
example : wasm_bitwise_module.loop2 #[19, 23] #[65] 1 0 2 2 =
    some (#[19, 23], 1) := by decide +kernel
example : ¬ ((2 : UInt32).toNat + (#[65] : Array UInt8).size ≤
    (#[19, 23] : Array UInt8).size) := by decide +kernel

-- A caller-supplied n larger than the array can also read a default. The
-- universal proof fixes n to the actual representable name size, excluding it.
example : wasm_bitwise_module.loop2 #[19, 23, 29, 31] #[65] 2 0 1 3 =
    some (#[19, 65, 0, 31], 2) := by decide +kernel
example : (2 : UInt32) ≠ (#[65] : Array UInt8).size.toUInt32 := by decide +kernel

-- Instantiation of the universal theorem, not evaluation of a finite output.
example (dst name : Array UInt8) (pos : UInt32) (fuel : Nat)
    (hn : name.size < 2^32) (hd : dst.size < 2^32)
    (hfit : pos.toNat + name.size ≤ dst.size) (hf : name.size + 1 ≤ fuel) :
    wasm_bitwise_module.loop2 dst name name.size.toUInt32 0 pos fuel =
      some (writeBytes dst pos.toNat name.toList, name.size.toUInt32) := by
  exact bitwise_name_copy_exact dst name pos fuel hn hd hfit hf

/-- info: 'Oak.WasmAssembler.bitwise_name_copy_index' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bitwise_name_copy_index
/-- info: 'Oak.WasmAssembler.bitwise_name_copy_suffix_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bitwise_name_copy_suffix_exact
/-- info: 'Oak.WasmAssembler.bitwise_name_copy_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bitwise_name_copy_exact
/-- info: 'Oak.WasmAssembler.bitwise_name_copy_contents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bitwise_name_copy_contents
/-- info: 'Oak.WasmAssembler.bitwise_name_copy_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bitwise_name_copy_suffix
/-- info: 'Oak.WasmAssembler.bitwise_name_copy_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bitwise_name_copy_bytes
/-- info: 'Oak.WasmAssembler.bitwise_name_copy_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bitwise_name_copy_frame
/-- info: 'Oak.WasmAssembler.bitwise_name_copy_fuel_independent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bitwise_name_copy_fuel_independent
