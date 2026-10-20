import Oak.WasmBitwiseModuleExtracted

/-! Universal early-guard laws for the mechanically extracted complete-module
writer. These are not complete success, termination, or output-refinement laws.
In particular, they do not assume that getD/setIfInBounds prove Oak safety. -/
set_option autoImplicit false
namespace Oak.WasmAssembler

/-- Invalid operation tags refuse before inspecting name bytes or touching dst,
even when no extraction fuel is available. -/
theorem bitwise_module_invalid_op (dst name : Array UInt8) (op : UInt32) (fuel : Nat)
    (bad : ¬ (1 ≤ op ∧ op ≤ 3)) :
    wasm_bitwise_module dst op name fuel = some (0, dst) := by
  simp only [wasm_bitwise_module]
  have guard : (decide (op ≥ (1 : UInt32)) && decide (op ≤ (3 : UInt32))) = false := by
    cases h : (decide (op ≥ (1 : UInt32)) && decide (op ≤ (3 : UInt32)))
    · rfl
    · exact False.elim (bad (by simpa using h))
  simp [guard]

/-- The represented length guard refuses without reading any name byte. -/
theorem bitwise_module_invalid_length (dst name : Array UInt8) (op : UInt32) (fuel : Nat)
    (bad : ¬ (1 ≤ name.size.toUInt32 ∧ name.size.toUInt32 ≤ 256)) :
    wasm_bitwise_module dst op name fuel = some (0, dst) := by
  simp only [wasm_bitwise_module]
  have guard : (decide (name.size.toUInt32 ≥ (1 : UInt32)) &&
      decide (name.size.toUInt32 ≤ (256 : UInt32))) = false := by
    cases h : (decide (name.size.toUInt32 ≥ (1 : UInt32)) && decide (name.size.toUInt32 ≤ (256 : UInt32)))
    · rfl
    · exact False.elim (bad (by simpa using h))
  simp only [Bool.and_assoc, guard, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- No validation or copy iteration occurs once its guard is false. -/
theorem bitwise_name_scan_done (name : Array UInt8) (n i : UInt32) (ok : Bool)
    (fuel : Nat) (done : ¬ i < n) :
    wasm_bitwise_module.loop1 name n ok i (fuel + 1) = some (ok, i) := by
  simp [wasm_bitwise_module.loop1, done]

theorem bitwise_name_copy_done (dst name : Array UInt8) (n i pos : UInt32)
    (fuel : Nat) (done : ¬ i < n) :
    wasm_bitwise_module.loop2 dst name n i pos (fuel + 1) = some (dst, i) := by
  simp [wasm_bitwise_module.loop2, done]

end Oak.WasmAssembler
