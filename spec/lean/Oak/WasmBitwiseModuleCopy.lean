import Oak.WasmBitwiseModuleValidation
import Oak.WasmAssemblerBytes

/-! Universal success and framing of the actual extracted module writer's name
copy loop. The mathematical `writeBytes` is the existing shared definition from
`WasmAssemblerBytes`; no replacement writer or returning-run assumption is used.
The array name and destination model disjoint Oak spans. The complete footprint
must fit a representable destination, every source read and store is in bounds,
and all u32 additions and loop increments are proved nonwrapping.

This is a compositional copy result, not a successful full-module envelope or
source-compilation theorem. Capacity preflight, fixed fields, LEB fields, and the
final assembler call still have to be composed to prove the complete writer. -/

set_option autoImplicit false
namespace Oak.WasmAssembler

/-- On each actual copy iteration, the source index and destination address are
in bounds. Both the destination-address sum and next source index are exact
natural additions, not wrapped u32 arithmetic. -/
theorem bitwise_name_copy_index (dst name : Array UInt8) (pos i : UInt32)
    (hn : name.size < 2^32) (hd : dst.size < 2^32)
    (hfit : pos.toNat + name.size ≤ dst.size) (hi : i < name.size.toUInt32) :
    i.toNat < name.size ∧ (pos + i).toNat = pos.toNat + i.toNat ∧
      (pos + i).toNat < dst.size ∧ (i + 1).toNat = i.toNat + 1 ∧
      (i + 1).toNat ≤ name.size := by
  have hs := bitwise_name_scan_index name i hn hi
  have ha : (pos + i).toNat = pos.toNat + i.toNat := by
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
  exact ⟨hs.1, ha, by omega, hs.2.1, hs.2.2⟩

private theorem copy_name_head (name : Array UInt8) (pre : List UInt8)
    (b : UInt8) (rest : List UInt8) (he : name.toList = pre ++ b :: rest) :
    name.getD pre.length 0 = b := by
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, he, List.getElem?_append]
  simp

/-- Exact execution from an arbitrary already-consumed name prefix. Fuel counts
one iteration per remaining byte plus the final guard. The arbitrary initial
destination is changed only by the exact remaining bytes, at their true offset.
The induction derives source/store bounds from `bitwise_name_copy_index` at each
iteration, excluding any dependence on out-of-bounds defaults or dropped stores. -/
theorem bitwise_name_copy_suffix_exact (name : Array UInt8) (remaining : List UInt8) :
    ∀ (pre : List UInt8) (dst : Array UInt8) (pos : UInt32) (fuel : Nat),
      name.size < 2^32 → dst.size < 2^32 →
      name.toList = pre ++ remaining → pos.toNat + name.size ≤ dst.size →
      remaining.length + 1 ≤ fuel →
      wasm_bitwise_module.loop2 dst name name.size.toUInt32
          (UInt32.ofNat pre.length) pos fuel =
        some (writeBytes dst (pos.toNat + pre.length) remaining, name.size.toUInt32) := by
  induction remaining with
  | nil =>
    intro pre dst pos fuel hn hd he hfit hf
    have hlen : pre.length = name.size := by
      simpa using congrArg List.length he.symm
    cases fuel with
    | zero => omega
    | succ fuel => simp [wasm_bitwise_module.loop2, hlen, writeBytes]
  | cons b rest ih =>
    intro pre dst pos fuel hn hd he hfit hf
    have hlen : name.size = pre.length + (rest.length + 1) := by
      simpa using congrArg List.length he
    have hpre : (UInt32.ofNat pre.length).toNat = pre.length := by
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    have hname : name.size.toUInt32.toNat = name.size := by
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hn]
    have hguard : UInt32.ofNat pre.length < name.size.toUInt32 := by
      rw [UInt32.lt_iff_toNat_lt, hpre, hname]
      omega
    have hsafe := bitwise_name_copy_index dst name pos (UInt32.ofNat pre.length)
      hn hd hfit hguard
    have hread : name.getD (UInt32.ofNat pre.length).toNat 0 = b := by
      rw [hpre]
      exact copy_name_head name pre b rest he
    have hindex : UInt32.ofNat pre.length + 1 = UInt32.ofNat (pre ++ [b]).length := by
      apply UInt32.toNat_inj.mp
      rw [hsafe.2.2.2.1, hpre, UInt32.toNat_ofNat',
        Nat.mod_eq_of_lt (by simp; omega)]
      simp
    have htail : name.toList = (pre ++ [b]) ++ rest := by
      simpa [List.append_assoc] using he
    cases fuel with
    | zero => simp only [List.length_cons] at hf; omega
    | succ fuel =>
      have hr := ih (pre ++ [b]) (dst.setIfInBounds (pos.toNat + pre.length) b)
        pos fuel hn (by simpa using hd) htail (by simpa using hfit)
        (by simp only [List.length_cons] at hf; omega)
      simp only [wasm_bitwise_module.loop2, decide_eq_true hguard, ↓reduceIte, hread]
      rw [hindex, hsafe.2.1, hpre, hr]
      simp [writeBytes, Nat.add_assoc]

/-- Every fully fitting name copy terminates with exactly its bytes and final
length. No successful-return hypothesis or valid-ASCII hypothesis is needed:
byte validation is a separate already-proved phase of the complete writer. -/
theorem bitwise_name_copy_exact (dst name : Array UInt8) (pos : UInt32) (fuel : Nat)
    (hn : name.size < 2^32) (hd : dst.size < 2^32)
    (hfit : pos.toNat + name.size ≤ dst.size) (hf : name.size + 1 ≤ fuel) :
    wasm_bitwise_module.loop2 dst name name.size.toUInt32 0 pos fuel =
      some (writeBytes dst pos.toNat name.toList, name.size.toUInt32) := by
  simpa using bitwise_name_copy_suffix_exact name name.toList [] dst pos fuel
    hn hd (by simp) hfit (by simpa using hf)

/-- Exact indexed contents and unchanged storage size for the actual returned
copy. The interval theorem includes both the untouched prefix and suffix. -/
theorem bitwise_name_copy_contents (dst name : Array UInt8) (pos : UInt32) (fuel : Nat)
    (hn : name.size < 2^32) (hd : dst.size < 2^32)
    (hfit : pos.toNat + name.size ≤ dst.size) (hf : name.size + 1 ≤ fuel) :
    ∃ out, wasm_bitwise_module.loop2 dst name name.size.toUInt32 0 pos fuel =
        some (out, name.size.toUInt32) ∧ out.size = dst.size ∧
      ∀ j, out[j]? =
        if pos.toNat ≤ j ∧ j < pos.toNat + name.size
          then name[j - pos.toNat]? else dst[j]? := by
  refine ⟨writeBytes dst pos.toNat name.toList,
    bitwise_name_copy_exact dst name pos fuel hn hd hfit hf,
    writeBytes_size _ _ _, ?_⟩
  intro j
  simpa using writeBytes_get dst pos.toNat name.toList (by simpa using hfit) j

/-- The returned destination's copied slice is the entire name followed by the
original suffix. This is exact for arbitrary destination contents and offsets. -/
theorem bitwise_name_copy_suffix (dst name : Array UInt8) (pos : UInt32) (fuel : Nat)
    (hn : name.size < 2^32) (hd : dst.size < 2^32)
    (hfit : pos.toNat + name.size ≤ dst.size) (hf : name.size + 1 ≤ fuel) :
    ∃ out, wasm_bitwise_module.loop2 dst name name.size.toUInt32 0 pos fuel =
        some (out, name.size.toUInt32) ∧
      out.toList.drop pos.toNat = name.toList ++ dst.toList.drop (pos.toNat + name.size) := by
  refine ⟨writeBytes dst pos.toNat name.toList,
    bitwise_name_copy_exact dst name pos fuel hn hd hfit hf, ?_⟩
  simpa using writeBytes_suffix dst pos.toNat name.toList (by simpa using hfit)

/-- Every source byte becomes the corresponding genuine in-bounds destination
byte. `some` and the explicit output bound prevent an absent optional lookup
from masquerading as byte equality. -/
theorem bitwise_name_copy_bytes (dst name : Array UInt8) (pos : UInt32) (fuel : Nat)
    (hn : name.size < 2^32) (hd : dst.size < 2^32)
    (hfit : pos.toNat + name.size ≤ dst.size) (hf : name.size + 1 ≤ fuel) :
    ∃ out, wasm_bitwise_module.loop2 dst name name.size.toUInt32 0 pos fuel =
        some (out, name.size.toUInt32) ∧ out.size = dst.size ∧
      ∀ (j : Nat) (hj : j < name.size),
        pos.toNat + j < out.size ∧ out[pos.toNat + j]? = some name[j] := by
  obtain ⟨out, hr, hsize, hget⟩ := bitwise_name_copy_contents dst name pos fuel hn hd hfit hf
  refine ⟨out, hr, hsize, ?_⟩
  intro j hj
  refine ⟨by omega, ?_⟩
  rw [hget, if_pos (by omega), Nat.add_sub_cancel_left]
  simp [hj]

/-- The exact initial prefix and suffix around the copied interval are
preserved, including when the initial destination contains nonuniform bytes. -/
theorem bitwise_name_copy_frame (dst name : Array UInt8) (pos : UInt32) (fuel : Nat)
    (hn : name.size < 2^32) (hd : dst.size < 2^32)
    (hfit : pos.toNat + name.size ≤ dst.size) (hf : name.size + 1 ≤ fuel) :
    ∃ out, wasm_bitwise_module.loop2 dst name name.size.toUInt32 0 pos fuel =
        some (out, name.size.toUInt32) ∧ out.size = dst.size ∧
      out.toList.take pos.toNat = dst.toList.take pos.toNat ∧
      out.toList.drop (pos.toNat + name.size) = dst.toList.drop (pos.toNat + name.size) := by
  obtain ⟨out, hr, hsize, hget⟩ := bitwise_name_copy_contents dst name pos fuel hn hd hfit hf
  refine ⟨out, hr, hsize, ?_, ?_⟩
  · apply List.ext_getElem?
    intro j
    simp only [List.getElem?_take, Array.getElem?_toList]
    by_cases hj : j < pos.toNat
    · simp [hj, hget, show ¬ (pos.toNat ≤ j ∧ j < pos.toNat + name.size) by omega]
    · simp [hj]
  · apply List.ext_getElem?
    intro j
    simp only [List.getElem?_drop, Array.getElem?_toList]
    rw [hget, if_neg (by omega)]

/-- Above the exact guard-count bound, extraction fuel cannot affect the
returned destination or final source index. -/
theorem bitwise_name_copy_fuel_independent (dst name : Array UInt8) (pos : UInt32)
    (fuel₁ fuel₂ : Nat) (hn : name.size < 2^32) (hd : dst.size < 2^32)
    (hfit : pos.toNat + name.size ≤ dst.size)
    (hf₁ : name.size + 1 ≤ fuel₁) (hf₂ : name.size + 1 ≤ fuel₂) :
    wasm_bitwise_module.loop2 dst name name.size.toUInt32 0 pos fuel₁ =
      wasm_bitwise_module.loop2 dst name name.size.toUInt32 0 pos fuel₂ := by
  rw [bitwise_name_copy_exact dst name pos fuel₁ hn hd hfit hf₁,
    bitwise_name_copy_exact dst name pos fuel₂ hn hd hfit hf₂]

end Oak.WasmAssembler
