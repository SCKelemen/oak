import Oak.WasmAssemblerSequence

/-! Total refinement of the extracted two-pass scalar assembler, including
invalid plans and capacity refusal. Fuel exhaustion remains a distinct result. -/
namespace Oak.WasmAssembler

private theorem plan_head (plan : Array WasmInstruction) (pre : List WasmInstruction)
    (ins : WasmInstruction) (rest : List WasmInstruction)
    (hp : plan.toList = pre ++ ins :: rest) : plan.getD pre.length default = ins := by
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, hp, List.getElem?_append]
  simp

/-- Once preflight refuses, its next guard terminates without reading another
instruction. This holds even at an otherwise invalid index or offset. -/
theorem preflight_stopped (dst : Array UInt8) (offset : UInt32)
    (plan : Array WasmInstruction) (total i : UInt32) (fuel : Nat) :
    wasm_assemble.loop1 dst offset plan total i false (fuel + 1) = some (total, i, false) := by
  simp [wasm_assemble.loop1]

/-- Every invalid or non-fitting suffix reaches a returned preflight refusal
within the instruction-count budget. The already-reserved prefix is in bounds;
no success or returning-run assumption is used. -/
theorem assemble_preflight_refuses (plan : Array WasmInstruction) (remaining : List WasmInstruction) :
    ∀ (pre : List WasmInstruction) (dst : Array UInt8) (offset total : UInt32) (fuel : Nat),
      plan.size < 2^32 → dst.size < 2^32 → plan.toList = pre ++ remaining →
      offset.toNat + total.toNat ≤ dst.size → remaining.length + 11 ≤ fuel →
      (¬ ∃ bs, instructionSequence remaining = some bs ∧
        offset.toNat + total.toNat + bs.length ≤ dst.size) →
      ∃ total' i', wasm_assemble.loop1 dst offset plan total (UInt32.ofNat pre.length) true fuel =
        some (total', i', false) := by
  induction remaining with
  | nil =>
    intro pre dst offset total fuel hp hd he hbase hf hbad
    exact False.elim (hbad ⟨[], rfl, by simpa using hbase⟩)
  | cons ins rest ih =>
    intro pre dst offset total fuel hp hd he hbase hf hbad
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
    have hindex : UInt32.ofNat pre.length + 1 = UInt32.ofNat (pre ++ [ins]).length := by
      simp [UInt32.ofNat_add]
    have hplan : plan.toList = (pre ++ [ins]) ++ rest := by simpa [List.append_assoc] using he
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hsize := instruction_size_exact ins fuel (by simp only [List.length_cons] at hf; omega)
      have hpositive : 0 < fuel := by simp only [List.length_cons] at hf; omega
      cases hi : instructionBytes ins with
      | none =>
        have hs : wasm_instruction_size ins fuel = some 0 := by simpa [hi] using hsize
        refine ⟨total, UInt32.ofNat pre.length + 1, ?_⟩
        cases fuel with
        | zero => omega
        | succ fuel =>
          rw [wasm_assemble.loop1]
          simp only [decide_eq_true hg, Bool.and_true, ↓reduceIte, hget, hs, bind, Option.bind]
          simp [preflight_stopped]
      | some front =>
        have hs : wasm_instruction_size ins fuel = some (UInt32.ofNat front.length) := by
          simpa [hi] using hsize
        have hb := instruction_bytes_bounds hi
        have hfn : (UInt32.ofNat front.length).toNat = front.length := by
          rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
        have hnonzero : UInt32.ofNat front.length ≠ 0 := by
          intro hz; have := congrArg UInt32.toNat hz; rw [hfn] at this
          change front.length = 0 at this; omega
        have hreserved : offset ≤ dst.size.toUInt32 ∧ total ≤ dst.size.toUInt32 - offset := by
          apply (range_guard_iff _ _ _).mpr; rwa [hdn]
        have hspace : (UInt32.ofNat front.length ≤ dst.size.toUInt32 - offset - total) ↔
            offset.toNat + total.toNat + front.length ≤ dst.size := by
          rw [UInt32.le_iff_toNat_le, hfn,
            UInt32.toNat_sub_of_le _ _ hreserved.2, UInt32.toNat_sub_of_le _ _ hreserved.1, hdn]
          omega
        by_cases hfit : offset.toNat + total.toNat + front.length ≤ dst.size
        · have hsfit := hspace.mpr hfit
          have htotal : (total + UInt32.ofNat front.length).toNat = total.toNat + front.length := by
            rw [UInt32.toNat_add, hfn, Nat.mod_eq_of_lt (by omega)]
          have htail : ¬ ∃ bs, instructionSequence rest = some bs ∧
              offset.toNat + (total + UInt32.ofNat front.length).toNat + bs.length ≤ dst.size := by
            rintro ⟨tail, ht, htf⟩
            apply hbad
            refine ⟨front ++ tail, ?_, ?_⟩
            · simp [instructionSequence, hi, ht]
            · rw [htotal] at htf; simp only [List.length_append]; omega
          obtain ⟨total', i', hr⟩ := ih (pre ++ [ins]) dst offset (total + UInt32.ofNat front.length) fuel
            hp hd hplan (by rw [htotal]; omega)
            (by simp only [List.length_cons] at hf; omega) htail
          refine ⟨total', i', ?_⟩
          simp only [wasm_assemble.loop1, decide_eq_true hg, Bool.and_true, ↓reduceIte, hget,
            hs, bind, Option.bind, bne_iff_ne, decide_eq_true hsfit, ↓reduceIte]
          rw [if_pos hnonzero]
          simp only [pure]
          rw [hindex, hr]
        · have hsfit : ¬ UInt32.ofNat front.length ≤ dst.size.toUInt32 - offset - total := by
            exact fun h => hfit (hspace.mp h)
          refine ⟨total, UInt32.ofNat pre.length + 1, ?_⟩
          cases fuel with
          | zero => omega
          | succ fuel =>
            rw [wasm_assemble.loop1]
            simp only [decide_eq_true hg, Bool.and_true, ↓reduceIte, hget, hs, bind, Option.bind]
            simp [hsfit, preflight_stopped]

/-- Every plan that is invalid or does not fit terminates with failure status,
zero bytes reported, and the complete original buffer. This includes empty
plans at out-of-range offsets and arbitrarily late malformed instructions. -/
theorem assemble_refuses (dst : Array UInt8) (offset : UInt32)
    (plan : Array WasmInstruction) (fuel : Nat)
    (hp : plan.size < 2^32) (hd : dst.size < 2^32) (hf : plan.size + 11 ≤ fuel)
    (hbad : ¬ ∃ bs, instructionSequence plan.toList = some bs ∧
      offset.toNat + bs.length ≤ dst.size) :
    wasm_assemble dst offset plan fuel = some (⟨1, 0⟩, dst) := by
  by_cases ho : offset ≤ dst.size.toUInt32
  · have hbase : offset.toNat + (0 : UInt32).toNat ≤ dst.size := by
      rw [UInt32.le_iff_toNat_le, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hd] at ho
      simpa using ho
    have hbad' : ¬ ∃ bs, instructionSequence plan.toList = some bs ∧
        offset.toNat + (0 : UInt32).toNat + bs.length ≤ dst.size := by simpa using hbad
    obtain ⟨total, i, hr⟩ := assemble_preflight_refuses plan plan.toList [] dst offset 0 fuel
      hp hd (by simp) hbase (by simpa using hf) hbad'
    simp only [List.length_nil, show UInt32.ofNat 0 = 0 by rfl] at hr
    simp [wasm_assemble, ho, hr]
  · cases fuel with
    | zero => omega
    | succ fuel => exact assemble_offset_past_end dst offset plan fuel ho

/-- Total mathematical result: validity and complete capacity determine
admission; accepted output contains exactly the independent sequence bytes. -/
def assemblyResult (dst : Array UInt8) (offset : UInt32) (plan : Array WasmInstruction) :
    WasmAssembly × Array UInt8 :=
  match instructionSequence plan.toList with
  | none => (⟨1, 0⟩, dst)
  | some bs => if offset.toNat + bs.length ≤ dst.size
      then (⟨0, UInt32.ofNat bs.length⟩, writeBytes dst offset.toNat bs)
      else (⟨1, 0⟩, dst)

/-- Complete universal contract for both success and refusal. For every
representable disjoint plan/destination and every u32 offset, `plan.size + 11`
fuel suffices and the mechanically extracted assembler equals its model. -/
theorem assemble_exact (dst : Array UInt8) (offset : UInt32)
    (plan : Array WasmInstruction) (fuel : Nat)
    (hp : plan.size < 2^32) (hd : dst.size < 2^32) (hf : plan.size + 11 ≤ fuel) :
    wasm_assemble dst offset plan fuel = some (assemblyResult dst offset plan) := by
  cases he : instructionSequence plan.toList with
  | none =>
    rw [assemblyResult, he]
    apply assemble_refuses dst offset plan fuel hp hd hf
    simp [he]
  | some bs =>
    by_cases hfit : offset.toNat + bs.length ≤ dst.size
    · simp only [assemblyResult, he, if_pos hfit]
      exact assemble_admitted_exact dst offset plan bs fuel hp hd he hfit hf
    · simp only [assemblyResult, he, if_neg hfit]
      apply assemble_refuses dst offset plan fuel hp hd hf
      simpa [he] using hfit

/-- Above the proved bound, changing extraction fuel cannot change any status,
size, or destination byte, even for invalid or non-fitting plans. -/
theorem assemble_fuel_independent (dst : Array UInt8) (offset : UInt32)
    (plan : Array WasmInstruction) (fuel₁ fuel₂ : Nat)
    (hp : plan.size < 2^32) (hd : dst.size < 2^32)
    (hf₁ : plan.size + 11 ≤ fuel₁) (hf₂ : plan.size + 11 ≤ fuel₂) :
    wasm_assemble dst offset plan fuel₁ = wasm_assemble dst offset plan fuel₂ := by
  rw [assemble_exact _ _ _ _ hp hd hf₁, assemble_exact _ _ _ _ hp hd hf₂]

/-- No input in the represented span domain can exhaust the proved budget. -/
theorem assemble_terminates (dst : Array UInt8) (offset : UInt32)
    (plan : Array WasmInstruction) (fuel : Nat)
    (hp : plan.size < 2^32) (hd : dst.size < 2^32) (hf : plan.size + 11 ≤ fuel) :
    ∃ result out, wasm_assemble dst offset plan fuel = some (result, out) := by
  exact ⟨(assemblyResult dst offset plan).1, (assemblyResult dst offset plan).2,
    assemble_exact dst offset plan fuel hp hd hf⟩

/-- Success is equivalent to independent encoding validity and complete
capacity. No malformed or overflowing plan can be accepted. -/
theorem assemble_admission_iff (dst : Array UInt8) (offset : UInt32)
    (plan : Array WasmInstruction) (fuel : Nat)
    (hp : plan.size < 2^32) (hd : dst.size < 2^32) (hf : plan.size + 11 ≤ fuel) :
    (wasm_assemble dst offset plan fuel).map (fun r => r.1.status) = some 0 ↔
      ∃ bs, instructionSequence plan.toList = some bs ∧ offset.toNat + bs.length ≤ dst.size := by
  rw [assemble_exact _ _ _ _ hp hd hf]
  cases he : instructionSequence plan.toList with
  | none => simp [assemblyResult, he]
  | some bs =>
    by_cases hfit : offset.toNat + bs.length ≤ dst.size <;> simp [assemblyResult, he, hfit]

/-- Refusal occurs exactly when the independent plan is invalid or does not
fit, and it always includes the zero-count and unchanged-buffer guarantee. -/
theorem assemble_refusal_iff (dst : Array UInt8) (offset : UInt32)
    (plan : Array WasmInstruction) (fuel : Nat)
    (hp : plan.size < 2^32) (hd : dst.size < 2^32) (hf : plan.size + 11 ≤ fuel) :
    wasm_assemble dst offset plan fuel = some (⟨1, 0⟩, dst) ↔
      ¬ ∃ bs, instructionSequence plan.toList = some bs ∧ offset.toNat + bs.length ≤ dst.size := by
  rw [assemble_exact _ _ _ _ hp hd hf]
  cases he : instructionSequence plan.toList with
  | none => simp [assemblyResult, he]
  | some bs =>
    by_cases hfit : offset.toNat + bs.length ≤ dst.size <;> simp [assemblyResult, he, hfit]

end Oak.WasmAssembler
