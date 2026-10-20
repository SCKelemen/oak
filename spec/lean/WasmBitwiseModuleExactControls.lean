import Oak.WasmBitwiseModuleExact

/-! Kernel controls supplement the universal module-writer refinement. They
check length-boundary encodings, exact capacity, arbitrary spare bytes, fuel
exhaustion, refusal, and output mutations; they are not the universal proof. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
open Oak.WasmAssembler Oak.BitwiseFunction Oak.BitwiseModule

private def nameOf (n : Nat) : Array UInt8 := (List.replicate n 65).toArray
private def bufferOf (n : Nat) : Array UInt8 := ((List.range n).map UInt8.ofNat).toArray
private def sentinels : List UInt8 := [19,23,29,31,37,41,43]

-- Apply the universal actual-writer theorem, then use its general list-frame
-- law instead of reevaluating hundreds of imperative array stores per fixture.
private theorem fixture_exact (n size fuel : Nat) (tag : UInt32) (op : Op)
    (htag : 1 ≤ tag ∧ tag ≤ 3) (hop : bitwiseModuleOp tag = op)
    (hlo : 1 ≤ (nameOf n).size) (hhi : (nameOf n).size ≤ 256)
    (hname : (nameOf n).toList.all bitwiseNameByte = true)
    (hsize : (namedModuleBytes op (nameOf n).toList).length = size)
    (hsmall : size + sentinels.length < 2^32)
    (hf : max ((nameOf n).size + 1) 15 ≤ fuel) :
    wasm_bitwise_module ((bufferOf size).toList ++ sentinels).toArray tag (nameOf n) fuel =
      some (UInt32.ofNat size, (namedModuleBytes op (nameOf n).toList ++ sentinels).toArray) := by
  have hd : (((bufferOf size).toList ++ sentinels).toArray).size = size + sentinels.length := by
    simp [bufferOf]
  have hb : (bufferOf size).toList.length = size := by simp [bufferOf]
  rw [bitwise_module_exact _ _ _ _ htag hlo hhi hname (by omega)
    (by rw [hop, hsize, hd]; omega) hf, hop, hsize]
  apply congrArg (fun out => some (UInt32.ofNat size, out))
  apply Array.toList_inj.mp
  have h := writeBytes_suffix ((bufferOf size).toList ++ sentinels).toArray 0
    (namedModuleBytes op (nameOf n).toList) (by simp [hsize, hd])
  have hs : ((bufferOf size).toList ++ sentinels).drop size = sentinels := by
    simpa only [hb] using (List.drop_left (l₁ := (bufferOf size).toList) (l₂ := sentinels))
  simpa only [List.drop_zero, List.toList_toArray, Nat.zero_add, hsize, hs] using h

-- Explicit ULEB transition fields and independently counted complete lengths.
example : (namedModuleBytes .and (nameOf 123).toList).length = 161 := by decide +kernel
example : ((namedModuleBytes .and (nameOf 123).toList).drop 22).take 3 = [127,1,123] := by decide +kernel
example : (namedModuleBytes .and (nameOf 124).toList).length = 163 := by decide +kernel
example : ((namedModuleBytes .and (nameOf 124).toList).drop 22).take 4 = [128,1,1,124] := by decide +kernel
example : (namedModuleBytes .and (nameOf 127).toList).length = 166 := by decide +kernel
example : ((namedModuleBytes .and (nameOf 127).toList).drop 22).take 4 = [131,1,1,127] := by decide +kernel
example : (namedModuleBytes .and (nameOf 128).toList).length = 168 := by decide +kernel
example : ((namedModuleBytes .and (nameOf 128).toList).drop 22).take 5 = [133,1,1,128,1] := by decide +kernel
example : (namedModuleBytes .and (nameOf 256).toList).length = 296 := by decide +kernel
example : ((namedModuleBytes .and (nameOf 256).toList).drop 22).take 5 = [133,2,1,128,2] := by decide +kernel

-- The true sufficient bound is used, not an unproved convenient large budget.
-- Each spare destination byte is distinct and is checked in the actual result.
example : wasm_bitwise_module ((bufferOf 39).toList ++ sentinels).toArray
    1 (nameOf 1) 15 = some (39, (namedModuleBytes .and (nameOf 1).toList ++ sentinels).toArray) := by
  apply fixture_exact 1 39 15 1 .and <;> decide +kernel
example : wasm_bitwise_module ((bufferOf 39).toList ++ sentinels).toArray
    2 (nameOf 1) 15 = some (39, (namedModuleBytes .or (nameOf 1).toList ++ sentinels).toArray) := by
  apply fixture_exact 1 39 15 2 .or <;> decide +kernel
example : wasm_bitwise_module ((bufferOf 39).toList ++ sentinels).toArray
    3 (nameOf 1) 15 = some (39, (namedModuleBytes .xor (nameOf 1).toList ++ sentinels).toArray) := by
  apply fixture_exact 1 39 15 3 .xor <;> decide +kernel
example : wasm_bitwise_module ((bufferOf 161).toList ++ sentinels).toArray
    1 (nameOf 123) 124 = some (161, (namedModuleBytes .and (nameOf 123).toList ++ sentinels).toArray) := by
  apply fixture_exact 123 161 124 1 .and <;> decide +kernel
example : wasm_bitwise_module ((bufferOf 161).toList ++ sentinels).toArray
    2 (nameOf 123) 124 = some (161, (namedModuleBytes .or (nameOf 123).toList ++ sentinels).toArray) := by
  apply fixture_exact 123 161 124 2 .or <;> decide +kernel
example : wasm_bitwise_module ((bufferOf 161).toList ++ sentinels).toArray
    3 (nameOf 123) 124 = some (161, (namedModuleBytes .xor (nameOf 123).toList ++ sentinels).toArray) := by
  apply fixture_exact 123 161 124 3 .xor <;> decide +kernel
example : wasm_bitwise_module ((bufferOf 163).toList ++ sentinels).toArray
    1 (nameOf 124) 125 = some (163, (namedModuleBytes .and (nameOf 124).toList ++ sentinels).toArray) := by
  apply fixture_exact 124 163 125 1 .and <;> decide +kernel
example : wasm_bitwise_module ((bufferOf 163).toList ++ sentinels).toArray
    2 (nameOf 124) 125 = some (163, (namedModuleBytes .or (nameOf 124).toList ++ sentinels).toArray) := by
  apply fixture_exact 124 163 125 2 .or <;> decide +kernel
example : wasm_bitwise_module ((bufferOf 163).toList ++ sentinels).toArray
    3 (nameOf 124) 125 = some (163, (namedModuleBytes .xor (nameOf 124).toList ++ sentinels).toArray) := by
  apply fixture_exact 124 163 125 3 .xor <;> decide +kernel
example : wasm_bitwise_module ((bufferOf 166).toList ++ sentinels).toArray
    1 (nameOf 127) 128 = some (166, (namedModuleBytes .and (nameOf 127).toList ++ sentinels).toArray) := by
  apply fixture_exact 127 166 128 1 .and <;> decide +kernel
example : wasm_bitwise_module ((bufferOf 166).toList ++ sentinels).toArray
    2 (nameOf 127) 128 = some (166, (namedModuleBytes .or (nameOf 127).toList ++ sentinels).toArray) := by
  apply fixture_exact 127 166 128 2 .or <;> decide +kernel
example : wasm_bitwise_module ((bufferOf 166).toList ++ sentinels).toArray
    3 (nameOf 127) 128 = some (166, (namedModuleBytes .xor (nameOf 127).toList ++ sentinels).toArray) := by
  apply fixture_exact 127 166 128 3 .xor <;> decide +kernel
example : wasm_bitwise_module ((bufferOf 168).toList ++ sentinels).toArray
    1 (nameOf 128) 129 = some (168, (namedModuleBytes .and (nameOf 128).toList ++ sentinels).toArray) := by
  apply fixture_exact 128 168 129 1 .and <;> decide +kernel
example : wasm_bitwise_module ((bufferOf 168).toList ++ sentinels).toArray
    2 (nameOf 128) 129 = some (168, (namedModuleBytes .or (nameOf 128).toList ++ sentinels).toArray) := by
  apply fixture_exact 128 168 129 2 .or <;> decide +kernel
example : wasm_bitwise_module ((bufferOf 168).toList ++ sentinels).toArray
    3 (nameOf 128) 129 = some (168, (namedModuleBytes .xor (nameOf 128).toList ++ sentinels).toArray) := by
  apply fixture_exact 128 168 129 3 .xor <;> decide +kernel
example : wasm_bitwise_module ((bufferOf 296).toList ++ sentinels).toArray
    1 (nameOf 256) 257 = some (296, (namedModuleBytes .and (nameOf 256).toList ++ sentinels).toArray) := by
  apply fixture_exact 256 296 257 1 .and <;> decide +kernel
example : wasm_bitwise_module ((bufferOf 296).toList ++ sentinels).toArray
    2 (nameOf 256) 257 = some (296, (namedModuleBytes .or (nameOf 256).toList ++ sentinels).toArray) := by
  apply fixture_exact 256 296 257 2 .or <;> decide +kernel
example : wasm_bitwise_module ((bufferOf 296).toList ++ sentinels).toArray
    3 (nameOf 256) 257 = some (296, (namedModuleBytes .xor (nameOf 256).toList ++ sentinels).toArray) := by
  apply fixture_exact 256 296 257 3 .xor <;> decide +kernel

-- Exact fit, including no implicit extra destination byte.
example : wasm_bitwise_module (bufferOf 39) 1 #[65] 15 =
    some (39, (namedModuleBytes .and [65]).toArray) := by decide +kernel

-- Ordinary capacity refusal remains distinct from extraction fuel exhaustion.
example : wasm_bitwise_module (bufferOf 38) 1 #[65] 15 = some (0, bufferOf 38) := by decide +kernel
example : wasm_bitwise_module (bufferOf 295) 3 (nameOf 256) 257 = some (0, bufferOf 295) := by
  apply bitwise_module_insufficient_capacity <;> decide +kernel
example : wasm_bitwise_module (bufferOf 39) 1 #[65] 1 = none := by decide +kernel
example : wasm_bitwise_module (bufferOf 39) 1 #[65] 0 = none := by decide +kernel

-- Bad tag, non-ASCII, late NUL, and excluded length still refuse unchanged.
example : wasm_bitwise_module (bufferOf 39) 4 #[65] 15 = some (0, bufferOf 39) := by decide +kernel
example : wasm_bitwise_module (bufferOf 40) 1 #[65,128] 15 = some (0, bufferOf 40) := by decide +kernel
example : wasm_bitwise_module (bufferOf 40) 1 #[65,0] 15 = some (0, bufferOf 40) := by decide +kernel
example : wasm_bitwise_module #[19,23,29] 1 (nameOf 257) 258 = some (0, #[19,23,29]) := by decide +kernel

-- Wrong count, header, copied name, final body byte, and preserved suffix.
example : wasm_bitwise_module ((bufferOf 39).toList ++ sentinels).toArray 1 #[65] 15 ≠
    some (38, (namedModuleBytes .and [65] ++ sentinels).toArray) := by decide +kernel
example : wasm_bitwise_module ((bufferOf 39).toList ++ sentinels).toArray 1 #[65] 15 ≠
    some (39, ((namedModuleBytes .and [65] ++ sentinels).toArray.setIfInBounds 0 1)) := by decide +kernel
example : wasm_bitwise_module ((bufferOf 39).toList ++ sentinels).toArray 1 #[65] 15 ≠
    some (39, ((namedModuleBytes .and [65] ++ sentinels).toArray.setIfInBounds 25 66)) := by decide +kernel
example : wasm_bitwise_module ((bufferOf 39).toList ++ sentinels).toArray 1 #[65] 15 ≠
    some (39, ((namedModuleBytes .and [65] ++ sentinels).toArray.setIfInBounds 38 0)) := by decide +kernel
example : wasm_bitwise_module ((bufferOf 39).toList ++ sentinels).toArray 1 #[65] 15 ≠
    some (39, ((namedModuleBytes .and [65] ++ sentinels).toArray.setIfInBounds 39 0)) := by decide +kernel

-- Quantified application: this checks the public theorem's actual interface.
example (dst name : Array UInt8) (op : UInt32) (fuel : Nat)
    (hop : 1 ≤ op ∧ op ≤ 3) (lo : 1 ≤ name.size) (hi : name.size ≤ 256)
    (valid : name.toList.all bitwiseNameByte = true) (represented : dst.size < 2^32)
    (fits : (namedModuleBytes (bitwiseModuleOp op) name.toList).length ≤ dst.size)
    (budget : max (name.size + 1) 15 ≤ fuel) :
    ∃ written out, wasm_bitwise_module dst op name fuel = some (written, out) ∧
      ∀ left right : BitVec 32,
        invokeModule name.toList (out.toList.take written.toNat) left right =
          .ok (eval (bitwiseModuleOp op) left right) :=
  bitwise_module_success dst name op fuel hop lo hi valid represented fits budget

/-- info: 'Oak.WasmAssembler.bitwise_module_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bitwise_module_exact
/-- info: 'Oak.WasmAssembler.bitwise_module_contents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bitwise_module_contents
/-- info: 'Oak.WasmAssembler.bitwise_module_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bitwise_module_output
/-- info: 'Oak.WasmAssembler.bitwise_module_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bitwise_module_bytes
/-- info: 'Oak.WasmAssembler.bitwise_module_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bitwise_module_admitted
/-- info: 'Oak.WasmAssembler.bitwise_module_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bitwise_module_success
/-- info: 'Oak.WasmAssembler.bitwise_module_fuel_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bitwise_module_fuel_independent
/-- info: 'Oak.WasmAssembler.bitwise_module_insufficient_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bitwise_module_insufficient_capacity
/-- info: 'Oak.BitwiseModule.named_loaded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms named_loaded
/-- info: 'Oak.BitwiseModule.named_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms named_admitted
/-- info: 'Oak.BitwiseModule.named_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms named_success
