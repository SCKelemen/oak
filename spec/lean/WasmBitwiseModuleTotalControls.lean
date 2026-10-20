import Oak.WasmBitwiseModuleTotal

/-! Nonvacuity, branch-boundary, and fuel controls for the universal total
result. These supplement, rather than replace, the quantified proof. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
open Oak.WasmAssembler Oak.BitwiseModule

private def nameOf (n : Nat) : Array UInt8 := (List.replicate n 65).toArray
private def bufferOf (n : Nat) : Array UInt8 := (List.replicate n 173).toArray

private theorem success_control (dst name : Array UInt8) (op : UInt32) (count : Nat)
    (hd : dst.size < 2^32) (hn : name.size < 2^32)
    (hop : 1 ≤ op ∧ op ≤ 3) (hlen : 1 ≤ name.size ∧ name.size ≤ 256)
    (hname : moduleNameBytes name = true)
    (hfit : (namedModuleBytes (bitwiseModuleOp op) name.toList).length ≤ dst.size)
    (hcount : (namedModuleBytes (bitwiseModuleOp op) name.toList).length = count) :
    wasm_bitwise_module dst op name 257 =
      some (UInt32.ofNat count, writeBytes dst 0
        (namedModuleBytes (bitwiseModuleOp op) name.toList)) := by
  rw [bitwise_module_total _ _ _ _ hd hn (by decide)]
  simp only [moduleResult, if_pos hop, if_pos hlen, hname, ↓reduceIte, if_pos hfit]
  rw [hcount]

private theorem refusal_control (dst name : Array UInt8) (op : UInt32)
    (hd : dst.size < 2^32) (hn : name.size < 2^32)
    (hbad : ¬ ((1 ≤ op ∧ op ≤ 3) ∧ (1 ≤ name.size ∧ name.size ≤ 256) ∧
      moduleNameBytes name = true ∧
      (namedModuleBytes (bitwiseModuleOp op) name.toList).length ≤ dst.size)) :
    wasm_bitwise_module dst op name 257 = some (0, dst) :=
  (bitwise_module_refusal_iff dst name op 257 hd hn (by decide)).mpr hbad

-- A structural fuel control avoids repeatedly evaluating the imperative scan
-- on a large literal array. It proves exhaustion independent of byte values.
private theorem scan_exhausted (name : Array UInt8) (n : UInt32) (fuel : Nat) :
    ∀ (ok : Bool) (i : UInt32), i.toNat + fuel ≤ n.toNat →
      wasm_bitwise_module.loop1 name n ok i fuel = none := by
  induction fuel with
  | zero => intro ok i h; rfl
  | succ fuel ih =>
    intro ok i h
    have hi : i < n := by rw [UInt32.lt_iff_toNat_lt]; omega
    have hnb : n.toNat < 2^32 := n.toNat_lt
    have hnext : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt32.toNat_add]
      change (i.toNat + 1) % 2^32 = i.toNat + 1
      exact Nat.mod_eq_of_lt (by omega)
    simp only [wasm_bitwise_module.loop1, decide_eq_true hi, ↓reduceIte]
    split <;> simp only [bind, Option.bind, pure] <;>
      apply ih <;> rw [hnext] <;> omega

-- The independent byte predicate has both admitted and refused inhabitants.
example : moduleNameBytes #[1,65,127] = true := by decide +kernel
example : moduleNameBytes #[1,0,127] = false := by decide +kernel
example : moduleNameBytes #[1,128,127] = false := by decide +kernel
example : moduleNameBytes #[255] = false := by decide +kernel

-- Each operation tag has a nonzero actual result at the uniform budget.
example : wasm_bitwise_module (bufferOf 39) 1 #[65] 257 =
    some (39, writeBytes (bufferOf 39) 0 (namedModuleBytes .and [65])) := by
  apply success_control (bufferOf 39) #[65] 1 39 <;> decide +kernel
example : wasm_bitwise_module (bufferOf 39) 2 #[65] 257 =
    some (39, writeBytes (bufferOf 39) 0 (namedModuleBytes .or [65])) := by
  apply success_control (bufferOf 39) #[65] 2 39 <;> decide +kernel
example : wasm_bitwise_module (bufferOf 39) 3 #[65] 257 =
    some (39, writeBytes (bufferOf 39) 0 (namedModuleBytes .xor [65])) := by
  apply success_control (bufferOf 39) #[65] 3 39 <;> decide +kernel

-- The largest valid name needs the terminal scan guard. At 256 fuel the
-- actual scan exhausts; at 257 the complete actual module succeeds.
example : wasm_bitwise_module (bufferOf 296) 3 (nameOf 256) 256 = none := by
  have hs := scan_exhausted (nameOf 256) 256 256 true 0 (by decide)
  simp only [wasm_bitwise_module]
  have hn : (nameOf 256).size.toUInt32 = 256 := by decide +kernel
  rw [hn]
  simp [hs]
example : wasm_bitwise_module (bufferOf 296) 3 (nameOf 256) 257 =
    some (296, writeBytes (bufferOf 296) 0
      (namedModuleBytes .xor (nameOf 256).toList)) := by
  apply success_control (bufferOf 296) (nameOf 256) 3 296 <;> decide +kernel

-- The independent full capacity boundary distinguishes success and refusal.
example : moduleResult (bufferOf 295) 3 (nameOf 256) = (0, bufferOf 295) := by
  apply (module_result_refuses_iff _ _ _).mpr
  decide +kernel
example : (moduleResult (bufferOf 296) 3 (nameOf 256)).1 = 296 := by decide +kernel
example : wasm_bitwise_module (bufferOf 295) 3 (nameOf 256) 257 =
    some (0, bufferOf 295) := by
  apply refusal_control <;> decide +kernel
example : wasm_bitwise_module (bufferOf 38) 1 #[65] 257 =
    some (0, bufferOf 38) := by
  apply refusal_control <;> decide +kernel

-- Concrete nonvacuity controls for all remaining independent refusal reasons.
example : wasm_bitwise_module #[19,23,29] 0 #[65] 257 =
    some (0, #[19,23,29]) := by decide +kernel
example : wasm_bitwise_module #[19,23,29] 4 #[65] 257 =
    some (0, #[19,23,29]) := by decide +kernel
example : wasm_bitwise_module #[19,23,29] 4294967295 #[65] 257 =
    some (0, #[19,23,29]) := by decide +kernel
example : wasm_bitwise_module #[19,23,29] 1 #[] 257 =
    some (0, #[19,23,29]) := by decide +kernel
example : wasm_bitwise_module (bufferOf 40) 1 #[65,0] 257 =
    some (0, bufferOf 40) := by decide +kernel
example : wasm_bitwise_module (bufferOf 40) 1 #[65,128] 257 =
    some (0, bufferOf 40) := by decide +kernel
example : wasm_bitwise_module (bufferOf 296) 1
    ((List.replicate 255 (65 : UInt8) ++ [0]).toArray) 257 = some (0, bufferOf 296) := by
  apply refusal_control <;> decide +kernel

-- Excluded natural lengths bypass scanning even with zero fuel. The symbolic
-- upper representable boundary does not allocate a multi-gigabyte fixture.
example : wasm_bitwise_module #[19,23,29] 1 (nameOf 257) 0 =
    some (0, #[19,23,29]) := by decide +kernel
example : wasm_bitwise_module #[19,23,29] 1 (nameOf 4096) 0 =
    some (0, #[19,23,29]) := by decide +kernel
example (dst name : Array UInt8) (op : UInt32)
    (hn : name.size < 2^32) (hbig : 256 < name.size) :
    wasm_bitwise_module dst op name 0 = some (0, dst) := by
  apply bitwise_module_invalid_length
  intro h
  have := (module_length_guard_iff name hn).mp h
  omega
example (dst name : Array UInt8) (op : UInt32)
    (hn : name.size = 2^32 - 1) :
    wasm_bitwise_module dst op name 0 = some (0, dst) := by
  apply bitwise_module_invalid_length
  intro h
  have := (module_length_guard_iff name (by omega)).mp h
  omega
example (dst name : Array UInt8) :
    wasm_bitwise_module dst 0 name 0 = some (0, dst) := by
  apply bitwise_module_invalid_op
  decide

-- A real late byte, not an array default, witnesses failed validation.
example : ∃ (j : Nat) (hj : j < (#[65,66,0] : Array UInt8).size),
    (#[65,66,0] : Array UInt8)[j] = 0 ∨ 128 ≤ (#[65,66,0] : Array UInt8)[j] := by
  exact module_bad_name_witness #[65,66,0] (by decide)

-- The quantification exposes only representability and a uniform budget.
example (dst name : Array UInt8) (op : UInt32) (fuel : Nat)
    (hd : dst.size < 2^32) (hn : name.size < 2^32) (hf : 257 ≤ fuel) :
    wasm_bitwise_module dst op name fuel = some (moduleResult dst op name) :=
  bitwise_module_total dst name op fuel hd hn hf
example (dst name : Array UInt8) (op : UInt32) (fuel₁ fuel₂ : Nat)
    (hd : dst.size < 2^32) (hn : name.size < 2^32)
    (hf₁ : 257 ≤ fuel₁) (hf₂ : 257 ≤ fuel₂) :
    wasm_bitwise_module dst op name fuel₁ = wasm_bitwise_module dst op name fuel₂ :=
  bitwise_module_total_fuel_independent dst name op fuel₁ fuel₂ hd hn hf₁ hf₂

-- Mutation controls ensure the result is not vacuously always refusal.
example : moduleResult (bufferOf 39) 1 #[65] ≠ (0, bufferOf 39) := by decide +kernel
example : moduleResult (bufferOf 38) 1 #[65] ≠
    (39, writeBytes (bufferOf 38) 0 (namedModuleBytes .and [65])) := by decide +kernel
example : wasm_bitwise_module #[19,23,29] 1 (nameOf 4096) 257 ≠ none := by decide +kernel
