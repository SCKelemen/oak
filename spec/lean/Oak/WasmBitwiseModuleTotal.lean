import Oak.WasmBitwiseModuleExact

/-! Total outcomes of the actual extracted complete-module writer on
representable arrays. The independent result has no execution or fuel input.
Invalid operation and natural-length guards precede name validation, so the
uniform fuel budget does not assume a scan of arbitrarily large names. -/
set_option autoImplicit false
namespace Oak.WasmAssembler

/-- The independent, natural-byte predicate for the module writer's name
domain. This is not a source-language identifier predicate. -/
def moduleNameBytes (name : Array UInt8) : Bool :=
  name.toList.all fun b => decide (1 ≤ b.toNat ∧ b.toNat ≤ 127)

/-- Complete mathematical API result. The four branch conditions use the
operation tag, actual natural name length, actual byte values, and complete
independent module length. No extracted execution result is inspected. -/
def moduleResult (dst : Array UInt8) (op : UInt32) (name : Array UInt8) :
    UInt32 × Array UInt8 :=
  if 1 ≤ op ∧ op ≤ 3 then
    if 1 ≤ name.size ∧ name.size ≤ 256 then
      if moduleNameBytes name then
        let bytes := Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList
        if bytes.length ≤ dst.size then
          (UInt32.ofNat bytes.length, writeBytes dst 0 bytes)
        else (0, dst)
      else (0, dst)
    else (0, dst)
  else (0, dst)

/-- Natural byte bounds agree with the existing validation specification. -/
theorem module_name_bytes_iff (name : Array UInt8) :
    moduleNameBytes name = true ↔ name.toList.all bitwiseNameByte = true := by
  rw [bitwise_name_all_iff]
  simp only [moduleNameBytes, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h b hb
    have hbyte := h b hb
    constructor
    · intro hz
      subst b
      simp at hbyte
    · rw [UInt8.lt_iff_toNat_lt]
      change b.toNat < 128
      omega
  · intro h b hb
    have hbyte := h b hb
    have hz : b.toNat ≠ 0 := by
      intro he
      apply hbyte.1
      exact UInt8.toNat_inj.mp he
    have hlow : b.toNat < 128 := UInt8.lt_iff_toNat_lt.mp hbyte.2
    omega

/-- Failed validation has a genuine in-bounds malformed byte. Neither
`getD` nor an out-of-bounds default appears in this witness. -/
theorem module_bad_name_witness (name : Array UInt8)
    (hbad : moduleNameBytes name ≠ true) :
    ∃ (j : Nat) (hj : j < name.size), name[j] = 0 ∨ 128 ≤ name[j] := by
  have hex : ∃ b ∈ name.toList, b = 0 ∨ 128 ≤ b := by
    apply Classical.byContradiction
    intro hn
    apply hbad
    apply (module_name_bytes_iff name).mpr
    apply (bitwise_name_all_iff name).mpr
    intro b hb
    have hz : b ≠ 0 := by
      intro he
      exact hn ⟨b, hb, Or.inl he⟩
    have hhigh : ¬ 128 ≤ b := by
      intro he
      exact hn ⟨b, hb, Or.inr he⟩
    refine ⟨hz, ?_⟩
    rw [UInt8.lt_iff_toNat_lt]
    rw [UInt8.le_iff_toNat_le] at hhigh
    change ¬ 128 ≤ b.toNat at hhigh
    change b.toNat < 128
    omega
  obtain ⟨b, hb, hbyte⟩ := hex
  have hmem : b ∈ name := by simpa using hb
  obtain ⟨j, hj, he⟩ := Array.mem_iff_getElem.mp hmem
  exact ⟨j, hj, by simpa only [he] using hbyte⟩

/-- The represented length guard is exactly the natural-length guard when
the source span is representable. This includes names much longer than 256. -/
theorem module_length_guard_iff (name : Array UInt8) (hn : name.size < 2^32) :
    (1 ≤ name.size.toUInt32 ∧ name.size.toUInt32 ≤ 256) ↔
      (1 ≤ name.size ∧ name.size ≤ 256) := by
  have he : name.size.toUInt32.toNat = name.size := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hn]
  simp only [UInt32.le_iff_toNat_le, he]
  rfl

/-- Uniform total-outcome refinement. Every representable input returns an
ordinary successful or refused API result with 257 or more extraction fuel.
The proof derives the run; there is no returned-run premise. -/
theorem bitwise_module_total (dst name : Array UInt8) (op : UInt32) (fuel : Nat)
    (hd : dst.size < 2^32) (hn : name.size < 2^32) (hf : 257 ≤ fuel) :
    wasm_bitwise_module dst op name fuel = some (moduleResult dst op name) := by
  by_cases hop : 1 ≤ op ∧ op ≤ 3
  · by_cases hlen : 1 ≤ name.size ∧ name.size ≤ 256
    · by_cases hname : moduleNameBytes name = true
      · have hscan := (module_name_bytes_iff name).mp hname
        by_cases hfit :
            (Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList).length ≤ dst.size
        · simpa only [moduleResult, if_pos hop, if_pos hlen, hname, ↓reduceIte, if_pos hfit] using
            bitwise_module_exact dst name op fuel hop hlen.1 hlen.2 hscan hd hfit
              (by omega)
        · simpa only [moduleResult, if_pos hop, if_pos hlen, hname, ↓reduceIte, if_neg hfit] using
            bitwise_module_insufficient_capacity dst name op fuel hop hlen.1 hlen.2 hscan hd
              (by omega) (by omega)
      · obtain ⟨j, hj, hbad⟩ := module_bad_name_witness name hname
        simpa only [moduleResult, if_pos hop, if_pos hlen, if_neg hname] using
          bitwise_module_invalid_name_at dst name op fuel j hn (by omega) hj hbad
    · have hguard : ¬ (1 ≤ name.size.toUInt32 ∧ name.size.toUInt32 ≤ 256) :=
        fun h => hlen ((module_length_guard_iff name hn).mp h)
      simpa only [moduleResult, if_pos hop, if_neg hlen] using
        bitwise_module_invalid_length dst name op fuel hguard
  · simpa only [moduleResult, if_neg hop] using
      bitwise_module_invalid_op dst name op fuel hop

/-- A successful module count is nonzero and does not wrap. This prevents the
refusal branch from being confused with a zero-length "successful" module. -/
theorem module_success_count (name : Array UInt8) (op : UInt32)
    (hbounded : name.size ≤ 256) :
    (UInt32.ofNat
      (Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList).length).toNat =
        (Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList).length ∧
    UInt32.ofNat
      (Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList).length ≠ 0 := by
  have hmax := Oak.BitwiseModule.namedModuleBytes_length_le
    (bitwiseModuleOp op) name.toList (by simpa using hbounded)
  have hmin := Oak.BitwiseModule.namedModuleBytes_length (bitwiseModuleOp op) name.toList
  have he : (UInt32.ofNat
      (Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList).length).toNat =
        (Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList).length := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  refine ⟨he, ?_⟩
  intro hz
  have := congrArg UInt32.toNat hz
  rw [he] at this
  change (Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList).length = 0 at this
  omega

/-- Exactly the failed independent input conditions produce the mathematical
refusal result. In particular, capacity is for the entire module. -/
theorem module_result_refuses_iff (dst name : Array UInt8) (op : UInt32) :
    moduleResult dst op name = (0, dst) ↔
      ¬ ((1 ≤ op ∧ op ≤ 3) ∧ (1 ≤ name.size ∧ name.size ≤ 256) ∧
        moduleNameBytes name = true ∧
        (Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList).length ≤ dst.size) := by
  by_cases hop : 1 ≤ op ∧ op ≤ 3
  · by_cases hlen : 1 ≤ name.size ∧ name.size ≤ 256
    · by_cases hname : moduleNameBytes name = true
      · by_cases hfit :
            (Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList).length ≤ dst.size
        · have hcount := (module_success_count name op hlen.2).2
          simp [moduleResult, hop, hlen, hname, hfit, hcount]
        · simp [moduleResult, hop, hlen, hname, hfit]
      · simp [moduleResult, hop, hlen, hname]
    · simp [moduleResult, hop, hlen]
  · simp [moduleResult, hop]

/-- Complete unchanged-buffer refusal classification for the actual writer.
No successful or returning execution is assumed. -/
theorem bitwise_module_refusal_iff (dst name : Array UInt8) (op : UInt32) (fuel : Nat)
    (hd : dst.size < 2^32) (hn : name.size < 2^32) (hf : 257 ≤ fuel) :
    wasm_bitwise_module dst op name fuel = some (0, dst) ↔
      ¬ ((1 ≤ op ∧ op ≤ 3) ∧ (1 ≤ name.size ∧ name.size ≤ 256) ∧
        moduleNameBytes name = true ∧
        (Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList).length ≤ dst.size) := by
  rw [bitwise_module_total dst name op fuel hd hn hf, Option.some.injEq]
  exact module_result_refuses_iff dst name op

/-- The entire mathematical result preserves the destination's allocated
length, on successes and all refusal branches. -/
theorem module_result_size (dst name : Array UInt8) (op : UInt32) :
    (moduleResult dst op name).2.size = dst.size := by
  unfold moduleResult
  split
  · split
    · split
      · dsimp only
        split <;> simp
      · rfl
    · rfl
  · rfl

/-- Sufficient fuel rules out extraction exhaustion for all representable
inputs, including ordinary refusals. -/
theorem bitwise_module_terminates (dst name : Array UInt8) (op : UInt32) (fuel : Nat)
    (hd : dst.size < 2^32) (hn : name.size < 2^32) (hf : 257 ≤ fuel) :
    ∃ result, wasm_bitwise_module dst op name fuel = some result :=
  ⟨moduleResult dst op name, bitwise_module_total dst name op fuel hd hn hf⟩

/-- All sufficient fuel values agree, throughout the entire representable
input space rather than only the successful profile domain. -/
theorem bitwise_module_total_fuel_independent
    (dst name : Array UInt8) (op : UInt32) (fuel₁ fuel₂ : Nat)
    (hd : dst.size < 2^32) (hn : name.size < 2^32)
    (hf₁ : 257 ≤ fuel₁) (hf₂ : 257 ≤ fuel₂) :
    wasm_bitwise_module dst op name fuel₁ = wasm_bitwise_module dst op name fuel₂ := by
  rw [bitwise_module_total dst name op fuel₁ hd hn hf₁,
    bitwise_module_total dst name op fuel₂ hd hn hf₂]

end Oak.WasmAssembler
