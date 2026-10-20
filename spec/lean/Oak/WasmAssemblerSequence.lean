import Oak.WasmAssemblerInstruction

/-! Composition of exact instruction writes through the extracted sequence loops. -/
namespace Oak.WasmAssembler

private theorem plan_head (plan : Array WasmInstruction) (pre : List WasmInstruction)
    (ins : WasmInstruction) (rest : List WasmInstruction)
    (hp : plan.toList = pre ++ ins :: rest) : plan.getD pre.length default = ins := by
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, hp, List.getElem?_append]
  simp

/-- The extracted emission loop writes exactly the remaining sequence and
terminates with one guard per instruction plus the eleven-step writer budget. -/
theorem assemble_emit_exact (plan : Array WasmInstruction) (remaining : List WasmInstruction) :
    ∀ (pre : List WasmInstruction) (dst : Array UInt8) (pos : UInt32) (bs : List UInt8) (fuel : Nat),
      plan.size < 2^32 → dst.size < 2^32 → plan.toList = pre ++ remaining →
      instructionSequence remaining = some bs → pos.toNat + bs.length ≤ dst.size →
      remaining.length + 11 ≤ fuel →
      wasm_assemble.loop2 dst plan (UInt32.ofNat pre.length) pos fuel =
        some (writeBytes dst pos.toNat bs, UInt32.ofNat plan.size, UInt32.ofNat (pos.toNat + bs.length)) := by
  induction remaining with
  | nil =>
    intro pre dst pos bs fuel hp hd he hb hfit hf
    simp [instructionSequence] at hb
    subst bs
    have hlen : pre.length = plan.size := by simpa using congrArg List.length he.symm
    cases fuel with
    | zero => omega
    | succ fuel => simp [wasm_assemble.loop2, hlen, writeBytes]
  | cons ins rest ih =>
    intro pre dst pos bs fuel hp hd he hb hfit hf
    cases hi : instructionBytes ins with
    | none => simp [instructionSequence, hi] at hb
    | some front =>
      cases ht : instructionSequence rest with
      | none => simp [instructionSequence, hi, ht] at hb
      | some tail =>
        simp [instructionSequence, hi, ht] at hb
        subst bs
        have hlen : plan.size = pre.length + (rest.length + 1) := by
          simpa using congrArg List.length he
        have hn : (UInt32.ofNat pre.length).toNat = pre.length := by
          rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
        have hpn : plan.size.toUInt32.toNat = plan.size := by
          rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hp]
        have hg : UInt32.ofNat pre.length < plan.size.toUInt32 := by
          rw [UInt32.lt_iff_toNat_lt, hn, hpn]; omega
        have hget : plan.getD (UInt32.ofNat pre.length).toNat default = ins := by
          rw [hn]; exact plan_head plan pre ins rest he
        have hfront : pos.toNat + front.length ≤ dst.size := by
          simp only [List.length_append] at hfit; omega
        have hfn : (UInt32.ofNat front.length).toNat = front.length := by
          rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
        have hpos : (pos + UInt32.ofNat front.length).toNat = pos.toNat + front.length := by
          rw [UInt32.toNat_add, hfn, Nat.mod_eq_of_lt (by omega)]
        have hindex : UInt32.ofNat pre.length + 1 = UInt32.ofNat (pre ++ [ins]).length := by
          simp [UInt32.ofNat_add]
        have hplan : plan.toList = (pre ++ [ins]) ++ rest := by simpa [List.append_assoc] using he
        cases fuel with
        | zero => omega
        | succ fuel =>
          have hw := write_instruction_admitted dst pos ins front fuel (by simp only [List.length_cons] at hf; omega) hd hi hfront
          have hr := ih (pre ++ [ins]) (writeBytes dst pos.toNat front)
            (pos + UInt32.ofNat front.length) tail fuel hp (by simpa using hd) hplan ht
            (by simp only [writeBytes_size, hpos]; simp only [List.length_append] at hfit; omega)
            (by simp only [List.length_cons] at hf; omega)
          simp only [wasm_assemble.loop2, decide_eq_true hg, ↓reduceIte, hget, hw, bind, Option.bind]
          rw [hindex, hr, hpos, ← writeBytes_append]
          simp [Nat.add_assoc]

/-- The extracted preflight loop accepts every valid fitting sequence, computes
its exact byte count without wrap, and terminates within the same budget. -/
theorem assemble_preflight_exact (plan : Array WasmInstruction) (remaining : List WasmInstruction) :
    ∀ (pre : List WasmInstruction) (dst : Array UInt8) (offset total : UInt32) (bs : List UInt8) (fuel : Nat),
      plan.size < 2^32 → dst.size < 2^32 → plan.toList = pre ++ remaining →
      instructionSequence remaining = some bs → offset.toNat + total.toNat + bs.length ≤ dst.size →
      remaining.length + 11 ≤ fuel →
      wasm_assemble.loop1 dst offset plan total (UInt32.ofNat pre.length) true fuel =
        some (UInt32.ofNat (total.toNat + bs.length), UInt32.ofNat plan.size, true) := by
  induction remaining with
  | nil =>
    intro pre dst offset total bs fuel hp hd he hb hfit hf
    simp [instructionSequence] at hb
    subst bs
    have hlen : pre.length = plan.size := by simpa using congrArg List.length he.symm
    cases fuel with
    | zero => omega
    | succ fuel => simp [wasm_assemble.loop1, hlen]
  | cons ins rest ih =>
    intro pre dst offset total bs fuel hp hd he hb hfit hf
    cases hi : instructionBytes ins with
    | none => simp [instructionSequence, hi] at hb
    | some front =>
      cases ht : instructionSequence rest with
      | none => simp [instructionSequence, hi, ht] at hb
      | some tail =>
        simp [instructionSequence, hi, ht] at hb
        subst bs
        have hlen : plan.size = pre.length + (rest.length + 1) := by
          simpa using congrArg List.length he
        have hn : (UInt32.ofNat pre.length).toNat = pre.length := by
          rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
        have hpn : plan.size.toUInt32.toNat = plan.size := by
          rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hp]
        have hdn : dst.size.toUInt32.toNat = dst.size := by
          rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hd]
        have hg : UInt32.ofNat pre.length < plan.size.toUInt32 := by
          rw [UInt32.lt_iff_toNat_lt, hn, hpn]; omega
        have hget : plan.getD (UInt32.ofNat pre.length).toNat default = ins := by
          rw [hn]; exact plan_head plan pre ins rest he
        have hfront : offset.toNat + total.toNat + front.length ≤ dst.size := by
          simp only [List.length_append] at hfit; omega
        have hfn : (UInt32.ofNat front.length).toNat = front.length := by
          rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
        have hbase : offset ≤ dst.size.toUInt32 ∧ total ≤ dst.size.toUInt32 - offset := by
          apply (range_guard_iff _ _ _).mpr; rw [hdn]; omega
        have hspace : UInt32.ofNat front.length ≤ dst.size.toUInt32 - offset - total := by
          rw [UInt32.le_iff_toNat_le, hfn,
            UInt32.toNat_sub_of_le _ _ hbase.2, UInt32.toNat_sub_of_le _ _ hbase.1, hdn]
          omega
        have hnonzero : UInt32.ofNat front.length ≠ 0 := by
          have hb := instruction_bytes_bounds hi
          intro hz; have := congrArg UInt32.toNat hz; rw [hfn] at this
          change front.length = 0 at this; omega
        have htotal : (total + UInt32.ofNat front.length).toNat = total.toNat + front.length := by
          rw [UInt32.toNat_add, hfn, Nat.mod_eq_of_lt (by omega)]
        have hindex : UInt32.ofNat pre.length + 1 = UInt32.ofNat (pre ++ [ins]).length := by
          simp [UInt32.ofNat_add]
        have hplan : plan.toList = (pre ++ [ins]) ++ rest := by simpa [List.append_assoc] using he
        cases fuel with
        | zero => omega
        | succ fuel =>
          have hs : wasm_instruction_size ins fuel = some (UInt32.ofNat front.length) := by
            rw [instruction_size_exact _ _ (by simp only [List.length_cons] at hf; omega), hi]; rfl
          have hr := ih (pre ++ [ins]) dst offset (total + UInt32.ofNat front.length) tail fuel hp hd hplan ht
            (by rw [htotal]; simp only [List.length_append] at hfit; omega)
            (by simp only [List.length_cons] at hf; omega)
          simp only [wasm_assemble.loop1, decide_eq_true hg, Bool.and_true, ↓reduceIte, hget,
            hs, bind, Option.bind, bne_iff_ne, decide_eq_true hspace, ↓reduceIte]
          rw [if_pos hnonzero]
          simp only [pure]
          rw [hindex, hr, htotal]
          simp [Nat.add_assoc]

/-- End-to-end exact bytes for every valid fitting instruction plan through
both mechanically extracted loops. Fuel grows with instruction count, not
with the numeric magnitude of operands. -/
theorem assemble_admitted_exact (dst : Array UInt8) (offset : UInt32)
    (plan : Array WasmInstruction) (bs : List UInt8) (fuel : Nat)
    (hp : plan.size < 2^32) (hd : dst.size < 2^32)
    (he : instructionSequence plan.toList = some bs)
    (hfit : offset.toNat + bs.length ≤ dst.size) (hf : plan.size + 11 ≤ fuel) :
    wasm_assemble dst offset plan fuel =
      some (⟨0, UInt32.ofNat bs.length⟩, writeBytes dst offset.toNat bs) := by
  have ho : offset ≤ dst.size.toUInt32 := by
    rw [UInt32.le_iff_toNat_le, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hd]; omega
  have hr := assemble_preflight_exact plan plan.toList [] dst offset 0 bs fuel hp hd (by simp) he
    (by simpa using hfit) (by simpa using hf)
  have hw := assemble_emit_exact plan plan.toList [] dst offset bs fuel hp hd (by simp) he hfit (by simpa using hf)
  simp only [List.length_nil, show UInt32.ofNat 0 = 0 by rfl, UInt32.toNat_zero, Nat.zero_add] at hr hw
  simp [wasm_assemble, ho, hr, hw]

/-- Independent sequence decoding recovers all original tokens, in order,
from the actual assembled buffer and returns its untouched suffix. -/
theorem assemble_decode (dst out : Array UInt8) (offset : UInt32)
    (plan : Array WasmInstruction) (bs : List UInt8) (fuel : Nat) (result : WasmAssembly)
    (hp : plan.size < 2^32) (hd : dst.size < 2^32)
    (he : instructionSequence plan.toList = some bs)
    (hfit : offset.toNat + bs.length ≤ dst.size) (hf : plan.size + 11 ≤ fuel)
    (hw : wasm_assemble dst offset plan fuel = some (result, out)) :
    Oak.WasmInstruction.decodeMany plan.size (out.toList.drop offset.toNat) =
      some (plan.toList.map (fun ins => (ins.opcode.toUInt8, ins.immediate.toInt)),
        dst.toList.drop (offset.toNat + bs.length)) := by
  rw [assemble_admitted_exact _ _ _ _ _ hp hd he hfit hf] at hw
  cases hw
  rw [writeBytes_suffix _ _ _ hfit]
  simpa using Oak.WasmInstruction.decode_assemble (instructionSequence_model he)
    (dst.toList.drop (offset.toNat + bs.length))

/-- Exact success frame: the array length is unchanged, emitted bytes occupy
precisely the reported window, and every other byte retains its old value. -/
theorem assemble_success_bytes (dst out : Array UInt8) (offset : UInt32)
    (plan : Array WasmInstruction) (bs : List UInt8) (fuel : Nat) (result : WasmAssembly)
    (hp : plan.size < 2^32) (hd : dst.size < 2^32)
    (he : instructionSequence plan.toList = some bs)
    (hfit : offset.toNat + bs.length ≤ dst.size) (hf : plan.size + 11 ≤ fuel)
    (hw : wasm_assemble dst offset plan fuel = some (result, out)) (j : Nat) :
    out.size = dst.size ∧ out[j]? =
      if offset.toNat ≤ j ∧ j < offset.toNat + bs.length
      then bs[j - offset.toNat]? else dst[j]? := by
  rw [assemble_admitted_exact _ _ _ _ _ hp hd he hfit hf] at hw
  cases hw
  exact ⟨writeBytes_size _ _ _, writeBytes_get _ _ _ hfit _⟩

end Oak.WasmAssembler
