import Oak.BitwiseModule
import Oak.WasmEncoding

/-!
# Complete named bitwise modules

A compositional byte specification and loader proof for every admitted export
name, including multi-byte name and export-section lengths. This layer is
independent of the extracted module writer.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace Oak.BitwiseModule
open Oak.BitwiseFunction Oak.WasmExecution

def namedExportSize (name : List UInt8) : Nat :=
  name.length + (Oak.WasmEncoding.encode 32 false name.length).length + 3

def namedModuleBytes (op : Op) (name : List UInt8) : List UInt8 :=
  [0,97,115,109,1,0,0,0,1,7,1,96,2,127,127,1,127,3,2,1,0,7] ++
    WasmEncoding.encode 32 false (namedExportSize name) ++ [1] ++
    WasmEncoding.encode 32 false name.length ++ name ++ [0,0,10,9,1,7,0] ++
    functionBytes op

private theorem functionBytes_length (op : Op) : (functionBytes op).length = 6 := by
  simp [functionBytes, bodyBytes]

private theorem uint32_range {n : Nat} (h : n < 2^32) :
    WasmLEB.inRange 32 false n := by
  simp only [WasmLEB.inRange, Bool.false_eq_true, ↓reduceIte]
  constructor
  · exact Int.natCast_nonneg _
  · exact_mod_cast h

private theorem encoded_length_le_five {n : Nat} (h : n < 2^32) :
    (WasmEncoding.encode 32 false n).length ≤ 5 := by
  have hb := WasmEncoding.encode_byte_budget (by decide : 0 < 32) (uint32_range h)
  omega

theorem namedExportSize_le (name : List UInt8) (bounded : name.length ≤ 256) :
    namedExportSize name ≤ 264 := by
  have hn : name.length < 2^32 := by omega
  have hl := encoded_length_le_five hn
  unfold namedExportSize
  omega

theorem namedModuleBytes_length (op : Op) (name : List UInt8) :
    (namedModuleBytes op name).length = 36 + name.length +
      (WasmEncoding.encode 32 false name.length).length +
      (WasmEncoding.encode 32 false (namedExportSize name)).length := by
  simp only [namedModuleBytes, List.length_append, List.length_cons,
    List.length_nil, functionBytes_length]
  omega

theorem namedModuleBytes_length_le (op : Op) (name : List UInt8)
    (bounded : name.length ≤ 256) :
    (namedModuleBytes op name).length ≤ 312 := by
  have hn : name.length < 2^32 := by omega
  have he : namedExportSize name < 2^32 := by
    have := namedExportSize_le name bounded
    omega
  have hl := encoded_length_le_five hn
  have hel := encoded_length_le_five he
  rw [namedModuleBytes_length]
  omega

private theorem takeBytes_append (front suffix : List UInt8) :
    takeBytes front.length (front ++ suffix) = some (front, suffix) := by
  simp [takeBytes]

private theorem readNat_encoded (n : Nat) (suffix : List UInt8)
    (bounded : n < 2^32) :
    readNat (WasmEncoding.encode 32 false n ++ suffix) = some (n, suffix) := by
  rw [readNat, WasmEncoding.decode_encode (by decide) (uint32_range bounded)]
  simp

private theorem readSection_encoded (id : UInt8) (payload suffix : List UInt8)
    (bounded : payload.length < 2^32) :
    readSection id (id :: (WasmEncoding.encode 32 false payload.length ++
      (payload ++ suffix))) = some (payload, suffix) := by
  simp [readSection, expectByte, readNat_encoded _ _ bounded, takeBytes_append]

private theorem readNat_seven (rest : List UInt8) :
    readNat (7 :: rest) = some (7, rest) := by rfl

private def namedExportPayload (name : List UInt8) : List UInt8 :=
  [1] ++ WasmEncoding.encode 32 false name.length ++ name ++ [0,0]

private theorem namedExportPayload_length (name : List UInt8) :
    (namedExportPayload name).length = namedExportSize name := by
  simp only [namedExportPayload, namedExportSize, List.length_append,
    List.length_cons, List.length_nil]
  omega

private theorem named_export_section (name : List UInt8) (rest : List UInt8)
    (bounded : name.length ≤ 256) :
    readSection 7 (7 :: (WasmEncoding.encode 32 false (namedExportSize name) ++
      (namedExportPayload name ++ rest))) = some (namedExportPayload name, rest) := by
  rw [← namedExportPayload_length]
  apply readSection_encoded
  rw [namedExportPayload_length]
  have := namedExportSize_le name bounded
  omega

private theorem takeBytes_header (rest : List UInt8) :
    takeBytes 8 (0 :: 97 :: 115 :: 109 :: 1 :: 0 :: 0 :: 0 :: rest) =
      some ([0,97,115,109,1,0,0,0], rest) := by rfl

private theorem readSection_types (rest : List UInt8) :
    readSection 1 (1 :: 7 :: 1 :: 96 :: 2 :: 127 :: 127 :: 1 :: 127 :: rest) =
      some ([1,96,2,127,127,1,127], rest) := by rfl

private theorem readSection_functions (rest : List UInt8) :
    readSection 3 (3 :: 2 :: 1 :: 0 :: rest) = some ([1,0], rest) := by rfl

private theorem readSection_code (op : Op) :
    readSection 10 (10 :: 9 :: 1 :: 7 :: 0 :: functionBytes op) =
      some ([1,7,0] ++ functionBytes op, []) := by rfl

private theorem takeBytes_body (op : Op) :
    takeBytes 7 (0 :: functionBytes op) = some (0 :: functionBytes op, []) := by rfl

private theorem expectNat_zero (rest : List UInt8) :
    expectNat 0 (0 :: rest) = some rest := by rfl
private theorem expectNat_one (rest : List UInt8) :
    expectNat 1 (1 :: rest) = some rest := by rfl
private theorem expectNat_two (rest : List UInt8) :
    expectNat 2 (2 :: rest) = some rest := by rfl

/-- Every nonempty bounded ASCII export name is loaded exactly, including its
complete function body and the two possible multi-byte length prefixes. -/
theorem named_loaded (op : Op) (name : List UInt8)
    (nonempty : name ≠ []) (bounded : name.length ≤ 256)
    (ascii : ∀ b ∈ name, b.toNat < 128) :
    load name (namedModuleBytes op name) = some ⟨name, functionBytes op⟩ := by
  have hall : name.all (fun b => b.toNat < 128) = true := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using ascii
  have hn : name.length < 2^32 := by omega
  have hbad : ¬(name = [] ∨ 256 < name.length ∨
      ¬name.all (fun b => b.toNat < 128)) := by simp [nonempty, hall]; omega
  have he := named_export_section name ([10,9,1,7,0] ++ functionBytes op) bounded
  simp only [namedExportPayload, List.append_assoc, List.cons_append, List.nil_append] at he
  unfold load
  rw [if_neg hbad]
  simp only [namedModuleBytes, List.append_assoc, List.cons_append, List.nil_append]
  simp only [takeBytes_header, readSection_types, readSection_functions, he,
    expectNat_one, expectNat_two, expectNat_zero, expectByte,
    Option.bind_eq_bind, Option.bind_some, ne_eq, not_true_eq_false,
    ↓reduceIte, finished]
  rw [readNat_encoded _ _ hn]
  simp [takeBytes_append, readSection_code, expectNat_one, expectNat_zero,
    readNat_seven, takeBytes_body]

/-- The full named module passes the bitwise target, signature, and body check. -/
theorem named_admitted (op : Op) (name : List UInt8)
    (nonempty : name ≠ []) (bounded : name.length ≤ 256)
    (ascii : ∀ b ∈ name, b.toNat < 128) :
    acceptsModule .wasm .wasmLocals [32,32] 32 op name
      (namedModuleBytes op name) = true := by
  rw [acceptsModule, named_loaded op name nonempty bounded ascii]
  simp [accepts]

/-- Every admitted name and every pair of 32-bit inputs reaches the exact
common bitwise result through complete-module loading and invocation. -/
theorem named_success (op : Op) (name : List UInt8)
    (nonempty : name ≠ []) (bounded : name.length ≤ 256)
    (ascii : ∀ b ∈ name, b.toNat < 128) (left right : BitVec 32) :
    invokeModule name (namedModuleBytes op name) left right =
      .ok (eval op left right) :=
  admitted_module_success (named_admitted op name nonempty bounded ascii) left right

end Oak.BitwiseModule
