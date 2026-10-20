import Oak.WasmBitwiseModuleCopy
import Oak.BitwiseNamedModule

/-! Universal success-domain refinement of the actual extracted complete
bitwise module writer. Arrays retain the existing disjoint-span boundary. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace Oak.WasmAssembler

private theorem nat_u32_range (n : Nat) (hn : n < 2^32) :
    Oak.WasmLEB.inRange 32 false (n : Int) := by
  simp only [Oak.WasmLEB.inRange, Bool.false_eq_true, ↓reduceIte]
  constructor <;> omega

private theorem nat_u64_range (n : Nat) (hn : n < 2^32) :
    Oak.WasmLEB.inRange 64 false (n : Int) := by
  simp only [Oak.WasmLEB.inRange, Bool.false_eq_true, ↓reduceIte]
  constructor <;> omega

/-- Natural sizes in the module profile have the same canonical ULEB bytes in
32- and 64-bit helpers. No helper result or successful run is assumed. -/
theorem bitwise_uleb_size_exact (n fuel : Nat) (hn : n < 2^32) (hf : 10 ≤ fuel) :
    wasm_uleb_size (UInt32.ofNat n).toUInt64 fuel =
      some (UInt32.ofNat (Oak.WasmEncoding.encode 32 false n).length) := by
  rw [uleb_size_exact _ _ hf, UInt32.toNat_toUInt64, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt hn,
    Oak.WasmEncoding.encode_width_irrelevant (by decide : 0 < 64) (by decide : 0 < 32)
      (nat_u64_range n hn) (nat_u32_range n hn)]

/-- Every ULEB field in this profile is written at its exact natural offset,
with sufficient helper fuel and a proved complete in-bounds footprint. -/
theorem bitwise_write_uleb_exact (dst : Array UInt8) (offset n fuel : Nat)
    (hd : dst.size < 2^32) (hn : n < 2^32) (ho : offset < 2^32)
    (hf : 11 ≤ fuel)
    (hfit : offset + (Oak.WasmEncoding.encode 32 false n).length ≤ dst.size) :
    wasm_write_uleb dst (UInt32.ofNat offset) (UInt32.ofNat n).toUInt64 fuel =
      some (UInt32.ofNat (Oak.WasmEncoding.encode 32 false n).length,
        writeBytes dst offset (Oak.WasmEncoding.encode 32 false n)) := by
  rw [write_uleb_exact _ _ _ _ hf hd, UInt32.toNat_toUInt64,
    show (UInt32.ofNat n).toNat = n from by rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hn],
    Oak.WasmEncoding.encode_width_irrelevant (by decide : 0 < 64) (by decide : 0 < 32)
      (nat_u64_range n hn) (nat_u32_range n hn),
    UInt32.toNat_ofNat', Nat.mod_eq_of_lt ho, if_pos hfit]

/-- The total mathematical operation named by every admitted writer tag. -/
def bitwiseModuleOp (op : UInt32) : Oak.BitwiseFunction.Op :=
  if op = 1 then .and else if op = 2 then .or else .xor

private theorem admitted_op_cases (op : UInt32) (ho : 1 ≤ op ∧ op ≤ 3) :
    op = 1 ∨ op = 2 ∨ op = 3 := by
  have hlo := UInt32.le_iff_toNat_le.mp ho.1
  have hhi := UInt32.le_iff_toNat_le.mp ho.2
  have h : op.toNat = 1 ∨ op.toNat = 2 ∨ op.toNat = 3 := by
    change 1 ≤ op.toNat at hlo
    change op.toNat ≤ 3 at hhi
    omega
  rcases h with h | h | h
  · exact Or.inl (UInt32.toNat_inj.mp h)
  · exact Or.inr (Or.inl (UInt32.toNat_inj.mp h))
  · exact Or.inr (Or.inr (UInt32.toNat_inj.mp h))

private theorem bitwise_plan_eq (op : UInt32) (ho : 1 ≤ op ∧ op ≤ 3) :
    (#[⟨32, 0⟩, ⟨32, 1⟩, ⟨112 + op, 0⟩, ⟨11, 0⟩] : Array WasmInstruction) =
      Oak.BitwiseFunction.assemblyPlan (bitwiseModuleOp op) := by
  rcases admitted_op_cases op ho with rfl | rfl | rfl <;> rfl

private theorem bitwise_function_length (op : Oak.BitwiseFunction.Op) :
    (Oak.BitwiseFunction.functionBytes op).length = 6 := by
  cases op <;> rfl

/-- Successful execution of the actual complete extracted module writer for
every fitting profile input. The fuel bound covers name scan/copy, both ULEB
helpers, and the four-instruction body assembler. -/
theorem bitwise_module_exact (dst name : Array UInt8) (op : UInt32) (fuel : Nat)
    (hop : 1 ≤ op ∧ op ≤ 3) (hnlo : 1 ≤ name.size) (hnhi : name.size ≤ 256)
    (hname : name.toList.all bitwiseNameByte = true) (hd : dst.size < 2^32)
    (hfit : (Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList).length ≤ dst.size)
    (hf : max (name.size + 1) 15 ≤ fuel) :
    wasm_bitwise_module dst op name fuel =
      some (UInt32.ofNat (Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList).length,
        writeBytes dst 0 (Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList)) := by
  let n := name.size
  let a := Oak.WasmEncoding.encode 32 false n
  let e := n + a.length + 3
  let b := Oak.WasmEncoding.encode 32 false e
  let t := 36 + n + a.length + b.length
  have hn : n < 2^32 := by dsimp [n]; omega
  have ha : a.length ≤ 5 := by
    have := Oak.WasmEncoding.encode_byte_budget (by decide : 0 < 32) (nat_u32_range n hn)
    dsimp [a]; omega
  have he : e < 2^32 := by dsimp [e, n]; omega
  have hb : b.length ≤ 5 := by
    have := Oak.WasmEncoding.encode_byte_budget (by decide : 0 < 32) (nat_u32_range e he)
    dsimp [b]; omega
  have ht : t < 2^32 := by dsimp [t, n]; omega
  have hlen : (Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList).length = t := by
    simp [Oak.BitwiseModule.namedModuleBytes_length, Oak.BitwiseModule.namedExportSize, t, n, a, b, e]
  have hcap : t ≤ dst.size := by rwa [hlen] at hfit
  have hnf : n + 1 ≤ fuel := by dsimp [n]; omega
  have h15 : 15 ≤ fuel := by omega
  have hn32 : name.size.toUInt32.toNat = n := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hn]
  have hlo : (1 : UInt32) ≤ name.size.toUInt32 := by
    rw [UInt32.le_iff_toNat_le, hn32]; exact hnlo
  have hhi : name.size.toUInt32 ≤ (256 : UInt32) := by
    rw [UInt32.le_iff_toNat_le, hn32]; exact hnhi
  have hscan := bitwise_name_validation_exact name fuel hn hnf
  rw [hname] at hscan
  have hs₁ := bitwise_uleb_size_exact n fuel hn (by omega)
  have he32 : (name.size.toUInt32 + UInt32.ofNat a.length) + 3 = UInt32.ofNat e := by
    simp [e, n, UInt32.ofNat_add]
  have hs₂ := bitwise_uleb_size_exact e fuel he (by omega)
  have ht32 : ((36 + name.size.toUInt32) + UInt32.ofNat a.length) + UInt32.ofNat b.length =
      UInt32.ofNat t := by simp [t, n, UInt32.ofNat_add]
  have hcapacity : UInt32.ofNat t ≤ dst.size.toUInt32 := by
    rw [UInt32.le_iff_toNat_le]
    simp only [UInt32.toNat_ofNat', Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hd]
    exact hcap
  let header : List UInt8 := [0,97,115,109,1,0,0,0,1,7,1,96,2,127,127,1,127,3,2,1,0,7]
  let d₀ := writeBytes dst 0 header
  let d₁ := writeBytes d₀ 22 b
  let d₂ := d₁.setIfInBounds (22 + b.length) 1
  let d₃ := writeBytes d₂ (23 + b.length) a
  let p := 23 + b.length + a.length
  let d₄ := writeBytes d₃ p name.toList
  let q := p + n
  let d₅ := writeBytes d₄ q [0,0,10,9,1,7,0]
  have hp : p < 2^32 := by dsimp [p]; omega
  have hq : q + 7 < 2^32 := by dsimp [q, p, n]; omega
  have hw₁ := bitwise_write_uleb_exact d₀ 22 e fuel (by simpa [d₀] using hd) he
    (by decide) (by omega) (by change 22 + b.length ≤ d₀.size; simp only [d₀, writeBytes_size]; dsimp [t] at hcap; omega)
  have hw₂ := bitwise_write_uleb_exact d₂ (23 + b.length) n fuel
    (by simpa [d₂, d₁, d₀] using hd) hn (by omega) (by omega)
    (by change 23 + b.length + a.length ≤ d₂.size; simp only [d₂, d₁, d₀, Array.size_setIfInBounds, writeBytes_size]; dsimp [t] at hcap; omega)
  have hcopy := bitwise_name_copy_exact d₃ name (UInt32.ofNat p) fuel hn
    (by simpa [d₃, d₂, d₁, d₀] using hd)
    (by simp only [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hp];
        dsimp [d₃, d₂, d₁, d₀]; simp only [Array.size_setIfInBounds, writeBytes_size];
        dsimp [p, t, n] at *; omega) hnf
  simp only [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hp] at hcopy
  have hpos₁ : (22 : UInt32) + UInt32.ofNat b.length = UInt32.ofNat (22 + b.length) := by
    simp [UInt32.ofNat_add]
  have hpos₂ : (22 : UInt32) + UInt32.ofNat b.length + 1 = UInt32.ofNat (23 + b.length) := by
    rw [hpos₁]
    change UInt32.ofNat (22 + b.length) + UInt32.ofNat 1 = _
    rw [← UInt32.ofNat_add]; congr 1; omega
  have hpos₃ : (22 : UInt32) + UInt32.ofNat b.length + 1 + UInt32.ofNat a.length = UInt32.ofNat p := by
    rw [hpos₂, ← UInt32.ofNat_add]
  have hpos₄ : UInt32.ofNat p + name.size.toUInt32 = UInt32.ofNat q := by
    simp [q, n, UInt32.ofNat_add]
  have hqnat : (UInt32.ofNat q).toNat = q := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have hqi (k : UInt32) (hk : k.toNat ≤ 7) : (UInt32.ofNat q + k).toNat = q + k.toNat := by
    rw [UInt32.toNat_add, hqnat, Nat.mod_eq_of_lt (by omega)]
  have hbodypos : UInt32.ofNat q + 7 = UInt32.ofNat (q + 7) := by
    change UInt32.ofNat q + UInt32.ofNat 7 = _
    rw [← UInt32.ofNat_add]
  have hbodyfit : (UInt32.ofNat (q + 7)).toNat +
      (Oak.BitwiseFunction.functionBytes (bitwiseModuleOp op)).length ≤ d₅.size := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hq, bitwise_function_length]
    simp only [d₅, d₄, d₃, d₂, d₁, d₀, writeBytes_size, Array.size_setIfInBounds]
    dsimp [q, p, t] at *
    omega
  have hasm := assemble_admitted_exact d₅ (UInt32.ofNat (q + 7))
    (Oak.BitwiseFunction.assemblyPlan (bitwiseModuleOp op))
    (Oak.BitwiseFunction.functionBytes (bitwiseModuleOp op)) fuel
    (by simp [Oak.BitwiseFunction.assemblyPlan])
    (by simpa [d₅, d₄, d₃, d₂, d₁, d₀] using hd)
    (Oak.BitwiseFunction.assemblyPlan_encoding (bitwiseModuleOp op)) hbodyfit
    (by simpa [Oak.BitwiseFunction.assemblyPlan] using h15)
  simp only [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hq, bitwise_function_length] at hasm
  simp only [wasm_bitwise_module, decide_eq_true hop.1, decide_eq_true hop.2,
    decide_eq_true hlo, decide_eq_true hhi, Bool.true_and, ↓reduceIte,
    hscan, bind, Option.bind, pure]
  rw [hlen]
  rw [hs₁]
  dsimp only
  rw [he32, hs₂]
  dsimp only
  rw [ht32]
  simp only [decide_eq_true hcapacity, ↓reduceIte]
  simp only [d₀, header, writeBytes, Nat.reduceAdd] at hw₁
  simp only [UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  erw [hw₁]
  dsimp only
  rw [hpos₃, hpos₂, hpos₁]
  simp only [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (show 22 + b.length < 2^32 by omega)]
  erw [hw₂]
  dsimp only
  erw [hcopy]
  rw [hpos₄]
  dsimp only
  rw [bitwise_plan_eq op hop, hbodypos]
  simp only [hqnat, hqi 1 (by decide), hqi 2 (by decide), hqi 3 (by decide),
    hqi 4 (by decide), hqi 5 (by decide), hqi 6 (by decide),
    UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  erw [hasm]
  dsimp only
  apply congrArg (fun out => some (UInt32.ofNat t, out))
  change writeBytes d₅ (q + 7) (Oak.BitwiseFunction.functionBytes (bitwiseModuleOp op)) =
    writeBytes dst 0 (header ++ b ++ [1] ++ a ++ name.toList ++ [0,0,10,9,1,7,0] ++
      Oak.BitwiseFunction.functionBytes (bitwiseModuleOp op))
  have hheader : header.length = 22 := rfl
  have hsingle (d : Array UInt8) (i : Nat) : writeBytes d i [1] = d.setIfInBounds i 1 := rfl
  simp only [writeBytes_append, List.length_append, List.length_cons, List.length_nil,
    hheader, hsingle, Array.length_toList, Nat.zero_add, Nat.reduceAdd]
  simp only [d₅, d₄, d₃, d₂, d₁, d₀, q, p, n, Nat.add_assoc]
  simp only [← Nat.add_assoc, show 22 + b.length + 1 = 23 + b.length by omega]

/-- The actual returned destination is the complete independently specified
module followed by the original suffix, for arbitrary original storage. -/
theorem bitwise_module_contents (dst name : Array UInt8) (op : UInt32) (fuel : Nat)
    (hop : 1 ≤ op ∧ op ≤ 3) (hnlo : 1 ≤ name.size) (hnhi : name.size ≤ 256)
    (hname : name.toList.all bitwiseNameByte = true) (hd : dst.size < 2^32)
    (hfit : (Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList).length ≤ dst.size)
    (hf : max (name.size + 1) 15 ≤ fuel) :
    ∃ written out, wasm_bitwise_module dst op name fuel = some (written, out) ∧
      written.toNat = (Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList).length ∧
      out.size = dst.size ∧
      out.toList = Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList ++
        dst.toList.drop written.toNat := by
  let bs := Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList
  have hb : bs.length < 2^32 := by
    have := Oak.BitwiseModule.namedModuleBytes_length_le (bitwiseModuleOp op) name.toList (by simpa using hnhi)
    dsimp [bs]; omega
  have hw : (UInt32.ofNat bs.length).toNat = bs.length := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hb]
  refine ⟨UInt32.ofNat bs.length, writeBytes dst 0 bs,
    bitwise_module_exact dst name op fuel hop hnlo hnhi hname hd hfit hf,
    hw, writeBytes_size _ _ _, ?_⟩
  rw [hw]
  simpa using writeBytes_suffix dst 0 bs (by simpa using hfit)

/-- The reported extent is an exact module prefix; the destination length and
entire suffix remain unchanged. Both facts describe the returned actual run. -/
theorem bitwise_module_output (dst name : Array UInt8) (op : UInt32) (fuel : Nat)
    (hop : 1 ≤ op ∧ op ≤ 3) (hnlo : 1 ≤ name.size) (hnhi : name.size ≤ 256)
    (hname : name.toList.all bitwiseNameByte = true) (hd : dst.size < 2^32)
    (hfit : (Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList).length ≤ dst.size)
    (hf : max (name.size + 1) 15 ≤ fuel) :
    ∃ written out, wasm_bitwise_module dst op name fuel = some (written, out) ∧
      written.toNat = (Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList).length ∧
      out.size = dst.size ∧
      out.toList.take written.toNat = Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList ∧
      out.toList.drop written.toNat = dst.toList.drop written.toNat := by
  obtain ⟨written, out, hr, hw, hs, hc⟩ :=
    bitwise_module_contents dst name op fuel hop hnlo hnhi hname hd hfit hf
  refine ⟨written, out, hr, hw, hs, ?_, ?_⟩
  · rw [hc, hw]; simp
  · rw [hc, hw]; simp

/-- Every emitted byte is a genuine in-bounds output byte. Optional lookups
cannot hide a dropped fixed store or an out-of-bounds copy default. -/
theorem bitwise_module_bytes (dst name : Array UInt8) (op : UInt32) (fuel : Nat)
    (hop : 1 ≤ op ∧ op ≤ 3) (hnlo : 1 ≤ name.size) (hnhi : name.size ≤ 256)
    (hname : name.toList.all bitwiseNameByte = true) (hd : dst.size < 2^32)
    (hfit : (Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList).length ≤ dst.size)
    (hf : max (name.size + 1) 15 ≤ fuel) :
    ∃ out, wasm_bitwise_module dst op name fuel =
        some (UInt32.ofNat (Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList).length, out) ∧
      ∀ (j : Nat) (hj : j < (Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList).length),
        j < out.size ∧ out[j]? = some (Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList)[j] := by
  let bs := Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList
  refine ⟨writeBytes dst 0 bs,
    bitwise_module_exact dst name op fuel hop hnlo hnhi hname hd hfit hf, ?_⟩
  intro j hj
  refine ⟨by simp only [writeBytes_size]; omega, ?_⟩
  rw [writeBytes_get dst 0 bs (by simpa using hfit) j]
  simp [bs, show j < bs.length from hj]

private theorem module_name_nonempty (name : Array UInt8) (hn : 1 ≤ name.size) :
    name.toList ≠ [] := by
  intro he
  have := congrArg List.length he
  simp only [Array.length_toList, List.length_nil] at this
  omega

private theorem module_name_ascii (name : Array UInt8)
    (hname : name.toList.all bitwiseNameByte = true) :
    ∀ b ∈ name.toList, b.toNat < 128 := by
  intro b hb
  have h := ((bitwise_name_all_iff name).mp hname b hb).2
  exact UInt8.lt_iff_toNat_lt.mp h

/-- The exact output returned by the writer is accepted by the existing
complete-module checker. This derives a returned run and does not assume one. -/
theorem bitwise_module_admitted (dst name : Array UInt8) (op : UInt32) (fuel : Nat)
    (hop : 1 ≤ op ∧ op ≤ 3) (hnlo : 1 ≤ name.size) (hnhi : name.size ≤ 256)
    (hname : name.toList.all bitwiseNameByte = true) (hd : dst.size < 2^32)
    (hfit : (Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList).length ≤ dst.size)
    (hf : max (name.size + 1) 15 ≤ fuel) :
    ∃ written out, wasm_bitwise_module dst op name fuel = some (written, out) ∧
      Oak.BitwiseModule.acceptsModule .wasm .wasmLocals [32,32] 32 (bitwiseModuleOp op)
        name.toList (out.toList.take written.toNat) = true := by
  obtain ⟨written, out, hr, _, _, hp, _⟩ :=
    bitwise_module_output dst name op fuel hop hnlo hnhi hname hd hfit hf
  refine ⟨written, out, hr, ?_⟩
  rw [hp]
  exact Oak.BitwiseModule.named_admitted (bitwiseModuleOp op) name.toList
    (module_name_nonempty name hnlo) (by simpa using hnhi) (module_name_ascii name hname)

/-- Loading and invoking the actual emitted module returns the common bitwise
result for every pair of 32-bit inputs. This is the existing restricted Wasm
module semantics, not a source-parser, full-compiler, or native ISA theorem. -/
theorem bitwise_module_success (dst name : Array UInt8) (op : UInt32) (fuel : Nat)
    (hop : 1 ≤ op ∧ op ≤ 3) (hnlo : 1 ≤ name.size) (hnhi : name.size ≤ 256)
    (hname : name.toList.all bitwiseNameByte = true) (hd : dst.size < 2^32)
    (hfit : (Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList).length ≤ dst.size)
    (hf : max (name.size + 1) 15 ≤ fuel) :
    ∃ written out, wasm_bitwise_module dst op name fuel = some (written, out) ∧
      ∀ left right : BitVec 32,
        Oak.BitwiseModule.invokeModule name.toList (out.toList.take written.toNat) left right =
          .ok (Oak.BitwiseFunction.eval (bitwiseModuleOp op) left right) := by
  obtain ⟨written, out, hr, ha⟩ :=
    bitwise_module_admitted dst name op fuel hop hnlo hnhi hname hd hfit hf
  exact ⟨written, out, hr, fun left right => Oak.BitwiseModule.admitted_module_success ha left right⟩

/-- All sufficient extraction budgets agree on the complete returned module
and original destination suffix throughout the successful profile domain. -/
theorem bitwise_module_fuel_independent (dst name : Array UInt8) (op : UInt32) (fuel₁ fuel₂ : Nat)
    (hop : 1 ≤ op ∧ op ≤ 3) (hnlo : 1 ≤ name.size) (hnhi : name.size ≤ 256)
    (hname : name.toList.all bitwiseNameByte = true) (hd : dst.size < 2^32)
    (hfit : (Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList).length ≤ dst.size)
    (hf₁ : max (name.size + 1) 15 ≤ fuel₁) (hf₂ : max (name.size + 1) 15 ≤ fuel₂) :
    wasm_bitwise_module dst op name fuel₁ = wasm_bitwise_module dst op name fuel₂ := by
  rw [bitwise_module_exact dst name op fuel₁ hop hnlo hnhi hname hd hfit hf₁,
    bitwise_module_exact dst name op fuel₂ hop hnlo hnhi hname hd hfit hf₂]

/-- With a valid profile name and operation, insufficient complete capacity
returns ordinary zero-count refusal and the untouched destination. This path
needs only validation and size-helper fuel; it never enters the write phases. -/
theorem bitwise_module_insufficient_capacity (dst name : Array UInt8) (op : UInt32) (fuel : Nat)
    (hop : 1 ≤ op ∧ op ≤ 3) (hnlo : 1 ≤ name.size) (hnhi : name.size ≤ 256)
    (hname : name.toList.all bitwiseNameByte = true) (hd : dst.size < 2^32)
    (hshort : dst.size < (Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList).length)
    (hf : max (name.size + 1) 10 ≤ fuel) :
    wasm_bitwise_module dst op name fuel = some (0, dst) := by
  let n := name.size
  let a := Oak.WasmEncoding.encode 32 false n
  let e := n + a.length + 3
  let b := Oak.WasmEncoding.encode 32 false e
  let t := 36 + n + a.length + b.length
  have hn : n < 2^32 := by dsimp [n]; omega
  have ha : a.length ≤ 5 := by
    have := Oak.WasmEncoding.encode_byte_budget (by decide : 0 < 32) (nat_u32_range n hn)
    dsimp [a]; omega
  have he : e < 2^32 := by dsimp [e, n]; omega
  have hb : b.length ≤ 5 := by
    have := Oak.WasmEncoding.encode_byte_budget (by decide : 0 < 32) (nat_u32_range e he)
    dsimp [b]; omega
  have ht : t < 2^32 := by dsimp [t, n]; omega
  have hlen : (Oak.BitwiseModule.namedModuleBytes (bitwiseModuleOp op) name.toList).length = t := by
    simp [Oak.BitwiseModule.namedModuleBytes_length, Oak.BitwiseModule.namedExportSize, t, n, a, b, e]
  have hn32 : name.size.toUInt32.toNat = n := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hn]
  have hlo : (1 : UInt32) ≤ name.size.toUInt32 := by
    rw [UInt32.le_iff_toNat_le, hn32]; exact hnlo
  have hhi : name.size.toUInt32 ≤ (256 : UInt32) := by
    rw [UInt32.le_iff_toNat_le, hn32]; exact hnhi
  have hscan := bitwise_name_validation_exact name fuel hn (by omega)
  rw [hname] at hscan
  have hs₁ := bitwise_uleb_size_exact n fuel hn (by omega)
  have he32 : (name.size.toUInt32 + UInt32.ofNat a.length) + 3 = UInt32.ofNat e := by
    simp [e, n, UInt32.ofNat_add]
  have hs₂ := bitwise_uleb_size_exact e fuel he (by omega)
  have ht32 : ((36 + name.size.toUInt32) + UInt32.ofNat a.length) + UInt32.ofNat b.length =
      UInt32.ofNat t := by simp [t, n, UInt32.ofNat_add]
  have hcapacity : ¬ UInt32.ofNat t ≤ dst.size.toUInt32 := by
    rw [UInt32.le_iff_toNat_le]
    simp only [UInt32.toNat_ofNat', Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hd]
    rw [hlen] at hshort
    omega
  simp only [wasm_bitwise_module, decide_eq_true hop.1, decide_eq_true hop.2,
    decide_eq_true hlo, decide_eq_true hhi, Bool.true_and, ↓reduceIte,
    hscan, bind, Option.bind, pure]
  rw [hs₁]
  dsimp only
  rw [he32, hs₂]
  dsimp only
  rw [ht32]
  simp [hcapacity]

end Oak.WasmAssembler
