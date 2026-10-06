import Oak.WasmAssemblerExtracted

/-!
Laws of the mechanically extracted `asm/selfhost/wasm.oak`, with the modeling
boundary documented in `95-extraction.md`. `none` means insufficient extraction
fuel, never assembler refusal. Refusal is a returned zero byte count or nonzero
assembly status. Arrays model disjoint spans with lengths representable in u32.
-/

namespace Oak.WasmAssembler

/-- The subtraction-based footprint guard is exactly the mathematical range
check, including its empty-at-end case. No wrapping sum is used for admission. -/
theorem range_guard_iff (length offset size : UInt32) :
    (offset ≤ length ∧ size ≤ length - offset) ↔
      offset.toNat + size.toNat ≤ length.toNat := by
  constructor
  · rintro ⟨ho, hs⟩
    rw [UInt32.le_iff_toNat_le, UInt32.toNat_sub_of_le _ _ ho] at hs
    rw [UInt32.le_iff_toNat_le] at ho
    omega
  · intro h
    have ho : offset ≤ length := by rw [UInt32.le_iff_toNat_le]; omega
    refine ⟨ho, ?_⟩
    rw [UInt32.le_iff_toNat_le, UInt32.toNat_sub_of_le _ _ ho]
    omega

/-- Every admitted loop index addresses the original array, with no u32 wrap. -/
theorem admitted_store (dst : Array UInt8) (offset size i : UInt32)
    (h : offset ≤ dst.size.toUInt32 ∧ size ≤ dst.size.toUInt32 - offset)
    (hi : i < size) :
    (offset + i).toNat = offset.toNat + i.toNat ∧
      (offset + i).toNat < dst.size := by
  have hr := (range_guard_iff _ _ _).mp h
  have hl := dst.size.toUInt32.toNat_lt
  have hm : dst.size.toUInt32.toNat ≤ dst.size := by
    simp only [UInt32.toNat_ofNat']
    exact Nat.mod_le _ _
  rw [UInt32.lt_iff_toNat_lt] at hi
  have he : (offset + i).toNat = offset.toNat + i.toNat := by
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
  exact ⟨he, by omega⟩

theorem write_uleb_refuses (dst : Array UInt8) (offset : UInt32) (value : UInt64)
    (fuel : Nat) (size : UInt32) (hs : wasm_uleb_size value fuel = some size)
    (h : ¬(offset ≤ dst.size.toUInt32 ∧ size ≤ dst.size.toUInt32 - offset)) :
    wasm_write_uleb dst offset value fuel = some (0, dst) := by
  simp [wasm_write_uleb, hs, h]

theorem write_sleb_refuses (dst : Array UInt8) (offset : UInt32) (value : Int64)
    (fuel : Nat) (size : UInt32) (hs : wasm_sleb_size value fuel = some size)
    (h : ¬(offset ≤ dst.size.toUInt32 ∧ size ≤ dst.size.toUInt32 - offset)) :
    wasm_write_sleb dst offset value fuel = some (0, dst) := by
  simp [wasm_write_sleb, hs, h]

theorem write_instruction_refuses (dst : Array UInt8) (offset : UInt32)
    (ins : WasmInstruction) (fuel : Nat) (size : UInt32)
    (hs : wasm_instruction_size ins fuel = some size)
    (h : ¬(size ≠ 0 ∧ offset ≤ dst.size.toUInt32 ∧ size ≤ dst.size.toUInt32 - offset)) :
    wasm_write_instruction dst offset ins fuel = some (0, dst) := by
  simp [wasm_write_instruction, hs, h, and_assoc]

/-- All returned assembly failures preserve the complete buffer, even when
validation discovers a bad instruction late in the plan. -/
theorem assemble_failure_atomic (dst out : Array UInt8) (offset : UInt32)
    (plan : Array WasmInstruction) (fuel : Nat) (result : WasmAssembly)
    (h : wasm_assemble dst offset plan fuel = some (result, out))
    (hf : result.status ≠ 0) : result.size = 0 ∧ out = dst := by
  unfold wasm_assemble at h
  cases hp : wasm_assemble.loop1 dst offset plan 0 0
      (decide (offset ≤ dst.size.toUInt32)) fuel with
  | none => simp [hp] at h
  | some state =>
    rcases state with ⟨total, i, ok⟩
    cases ok with
    | false => simp [hp] at h; rcases h with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    | true =>
      cases hw : wasm_assemble.loop2 dst plan 0 offset fuel with
      | none => simp [hp, hw] at h
      | some state =>
        rcases state with ⟨out', i', pos'⟩
        simp [hp, hw] at h
        rcases h with ⟨rfl, rfl⟩
        exact False.elim (hf rfl)

/-- A destination offset beyond the span fails before reading any instruction. -/
theorem assemble_offset_past_end (dst : Array UInt8) (offset : UInt32)
    (plan : Array WasmInstruction) (fuel : Nat) (h : ¬offset ≤ dst.size.toUInt32) :
    wasm_assemble dst offset plan (fuel + 1) = some (⟨1, 0⟩, dst) := by
  simp [wasm_assemble, wasm_assemble.loop1, h]

theorem assemble_empty (dst : Array UInt8) (offset : UInt32) (fuel : Nat)
    (h : offset ≤ dst.size.toUInt32) :
    wasm_assemble dst offset #[] (fuel + 1) = some (⟨0, 0⟩, dst) := by
  simp [wasm_assemble, wasm_assemble.loop1, wasm_assemble.loop2, h]

/-- Extending a preflight total cannot wrap, and retains the destination bound. -/
theorem reserve_no_wrap (length offset total size : UInt32)
    (h : offset.toNat + total.toNat ≤ length.toNat)
    (hs : size ≤ length - offset - total) :
    (total + size).toNat = total.toNat + size.toNat ∧
      offset.toNat + (total + size).toNat ≤ length.toNat := by
  have ho : offset ≤ length := by rw [UInt32.le_iff_toNat_le]; omega
  have ht : total ≤ length - offset := by
    rw [UInt32.le_iff_toNat_le, UInt32.toNat_sub_of_le _ _ ho]; omega
  rw [UInt32.le_iff_toNat_le, UInt32.toNat_sub_of_le _ _ ht,
    UInt32.toNat_sub_of_le _ _ ho] at hs
  have hl := length.toNat_lt
  have he : (total + size).toNat = total.toNat + size.toNat := by
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
  exact ⟨he, by omega⟩

/-- The actual preflight loop preserves its capacity invariant at every step,
including the failure step. The instruction-size function is not assumed to
return a bounded value: the loop guard itself establishes the bound. -/
theorem preflight_bound (dst : Array UInt8) (offset : UInt32)
    (plan : Array WasmInstruction) (fuel : Nat) :
    ∀ (total i : UInt32) (ok : Bool) (total' i' : UInt32) (ok' : Bool),
      offset.toNat + total.toNat ≤ dst.size.toUInt32.toNat →
      wasm_assemble.loop1 dst offset plan total i ok fuel = some (total', i', ok') →
      offset.toNat + total'.toNat ≤ dst.size.toUInt32.toNat := by
  induction fuel with
  | zero => intro total i ok total' i' ok' hb h; simp [wasm_assemble.loop1] at h
  | succ fuel ih =>
    intro total i ok total' i' ok' hb h
    simp only [wasm_assemble.loop1] at h
    split at h
    · cases hs : wasm_instruction_size (plan.getD i.toNat default) fuel with
      | none => rw [hs] at h; simp at h
      | some size =>
        rw [hs] at h
        simp only [bind, Option.bind] at h
        by_cases hg : size ≠ 0 ∧ size ≤ dst.size.toUInt32 - offset - total
        · simp [hg] at h
          exact ih _ _ _ _ _ _ (reserve_no_wrap _ _ _ _ hb hg.2).2 h
        · simp [hg] at h
          exact ih _ _ _ _ _ _ hb h
    · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      exact hb

/-- A byte writer preserves the array's length and every byte outside its
admitted destination window. This describes the entire original storage. -/
def Frame (before after : Array UInt8) (offset size : UInt32) : Prop :=
  after.size = before.size ∧ ∀ j, j < offset.toNat ∨ offset.toNat + size.toNat ≤ j →
    after[j]? = before[j]?

private theorem store_frame (dst : Array UInt8) (offset size i : UInt32) (b : UInt8)
    (hb : offset ≤ dst.size.toUInt32 ∧ size ≤ dst.size.toUInt32 - offset)
    (hi : i < size) : Frame dst (dst.setIfInBounds (offset + i).toNat b) offset size := by
  have hidx := admitted_store dst offset size i hb hi
  refine ⟨Array.size_setIfInBounds, ?_⟩
  intro j hj
  have hi' := UInt32.lt_iff_toNat_lt.mp hi
  exact Array.getElem?_setIfInBounds_ne (by omega)

private theorem frame_trans {a b c : Array UInt8} {offset size : UInt32}
    (hab : Frame a b offset size) (hbc : Frame b c offset size) : Frame a c offset size :=
  ⟨hbc.1.trans hab.1, fun j hj => (hbc.2 j hj).trans (hab.2 j hj)⟩

/-- Universal frame law of the extracted unsigned writer loop. -/
theorem uleb_loop_frame (offset size : UInt32) (fuel : Nat) :
    ∀ (dst out : Array UInt8) (v v' : UInt64) (i i' : UInt32),
      (offset ≤ dst.size.toUInt32 ∧ size ≤ dst.size.toUInt32 - offset) →
      wasm_write_uleb.loop1 dst offset size v i fuel = some (out, v', i') →
      Frame dst out offset size := by
  induction fuel with
  | zero => intro dst out v v' i i' hb h; simp [wasm_write_uleb.loop1] at h
  | succ fuel ih =>
    intro dst out v v' i i' hb h
    simp only [wasm_write_uleb.loop1] at h
    split at h
    · rename_i hi
      have hi' : i < size := by simpa using hi
      split at h <;> simp only [pure, bind, Option.bind] at h
      all_goals
        exact frame_trans (store_frame dst offset size i _ hb hi')
          (ih _ _ _ _ _ _ (by simpa using hb) h)
    · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, fun _ _ => rfl⟩

/-- Universal frame law of the extracted signed writer loop. -/
theorem sleb_loop_frame (offset size : UInt32) (fuel : Nat) :
    ∀ (dst out : Array UInt8) (v v' : Int64) (i i' : UInt32),
      (offset ≤ dst.size.toUInt32 ∧ size ≤ dst.size.toUInt32 - offset) →
      wasm_write_sleb.loop1 dst offset size v i fuel = some (out, v', i') →
      Frame dst out offset size := by
  induction fuel with
  | zero => intro dst out v v' i i' hb h; simp [wasm_write_sleb.loop1] at h
  | succ fuel ih =>
    intro dst out v v' i i' hb h
    simp only [wasm_write_sleb.loop1] at h
    split at h
    · rename_i hi
      have hi' : i < size := by simpa using hi
      split at h <;> simp only [pure, bind, Option.bind, wasm_signed_next] at h
      all_goals
        exact frame_trans (store_frame dst offset size i _ hb hi')
          (ih _ _ _ _ _ _ (by simpa using hb) h)
    · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, fun _ _ => rfl⟩

/-- Oak truncating division plus its negative-remainder correction is exactly
the floor quotient required by SLEB, for every signed 64-bit value. -/
theorem signed_next_floor (v : Int64) (fuel : Nat) :
    (wasm_signed_next v fuel).map Int64.toInt = some (v.toInt / 128) := by
  have hd : (v / (128 : Int64)).toInt = v.toInt.tdiv 128 := by
    simpa using Int64.toInt_div_of_ne_right v (128 : Int64) (by decide)
  have hz : (v % (128 : Int64) = 0) ↔ 128 ∣ v.toInt := by
    rw [← Int64.toInt_inj, Int64.toInt_mod]
    change v.toInt.tmod 128 = 0 ↔ 128 ∣ v.toInt
    exact Int.dvd_iff_tmod_eq_zero.symm
  have hlo := v.le_toInt
  have hhi := v.toInt_lt
  simp only [wasm_signed_next, pure, Option.map_some]
  split
  · rename_i h
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at h
    have hn : v.toInt < 0 := Int64.lt_iff_toInt_lt.mp h.1
    have hm : ¬128 ∣ v.toInt := fun he => h.2 (hz.mpr he)
    rw [Int64.toInt_sub, hd, Int.tdiv_eq_ediv]
    simp only [show ¬(0 ≤ v.toInt ∨ 128 ∣ v.toInt) from by omega, if_false]
    change some ((v.toInt / 128 + 1 - 1).bmod (2^64)) = some (v.toInt / 128)
    congr 1
    rw [Int.bmod_eq_of_le (by omega) (by omega)]
    omega
  · rename_i h
    have hc : 0 ≤ v.toInt ∨ 128 ∣ v.toInt := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, not_and, Classical.not_not] at h
      by_cases hn : v.toInt < 0
      · exact Or.inr (hz.mp (h (Int64.lt_iff_toInt_lt.mpr hn)))
      · exact Or.inl (by omega)
    rw [hd, Int.tdiv_eq_ediv]
    simp [hc]

/-- Every returning ULEB writer preserves bytes outside its reported extent. -/
theorem write_uleb_frame (dst out : Array UInt8) (offset : UInt32) (value : UInt64)
    (fuel : Nat) (written : UInt32)
    (h : wasm_write_uleb dst offset value fuel = some (written, out)) :
    Frame dst out offset written := by
  unfold wasm_write_uleb at h
  cases hs : wasm_uleb_size value fuel with
  | none => simp [hs] at h
  | some size =>
    simp only [hs, bind, Option.bind] at h
    by_cases hb : offset ≤ dst.size.toUInt32 ∧ size ≤ dst.size.toUInt32 - offset
    · simp only [Bool.and_eq_true, decide_eq_true_eq, if_pos hb] at h
      cases hw : wasm_write_uleb.loop1 dst offset size value 0 fuel with
      | none => simp [hw] at h
      | some state =>
        rcases state with ⟨out', v', i'⟩
        simp [hw] at h
        rcases h with ⟨rfl, rfl⟩
        exact uleb_loop_frame _ _ _ _ _ _ _ _ _ hb hw
    · simp [hb] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨rfl, fun _ _ => rfl⟩

/-- Every returning SLEB writer preserves bytes outside its reported extent. -/
theorem write_sleb_frame (dst out : Array UInt8) (offset : UInt32) (value : Int64)
    (fuel : Nat) (written : UInt32)
    (h : wasm_write_sleb dst offset value fuel = some (written, out)) :
    Frame dst out offset written := by
  unfold wasm_write_sleb at h
  cases hs : wasm_sleb_size value fuel with
  | none => simp [hs] at h
  | some size =>
    simp only [hs, bind, Option.bind] at h
    by_cases hb : offset ≤ dst.size.toUInt32 ∧ size ≤ dst.size.toUInt32 - offset
    · simp only [Bool.and_eq_true, decide_eq_true_eq, if_pos hb] at h
      cases hw : wasm_write_sleb.loop1 dst offset size value 0 fuel with
      | none => simp [hw] at h
      | some state =>
        rcases state with ⟨out', v', i'⟩
        simp [hw] at h
        rcases h with ⟨rfl, rfl⟩
        exact sleb_loop_frame _ _ _ _ _ _ _ _ _ hb hw
    · simp [hb] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨rfl, fun _ _ => rfl⟩

/-- Successful assembly reports a total within the original span. This is a
preflight result; it does not yet assert that each emitted instruction refines
its mathematical byte encoding. -/
theorem assemble_success_bound (dst out : Array UInt8) (offset : UInt32)
    (plan : Array WasmInstruction) (fuel : Nat) (result : WasmAssembly)
    (h : wasm_assemble dst offset plan fuel = some (result, out))
    (hs : result.status = 0) : offset.toNat + result.size.toNat ≤ dst.size := by
  have ho : offset ≤ dst.size.toUInt32 := by
    apply Classical.byContradiction
    intro hn
    cases fuel with
    | zero => simp [wasm_assemble, wasm_assemble.loop1] at h
    | succ fuel =>
      rw [assemble_offset_past_end dst offset plan fuel hn] at h
      cases h
      contradiction
  have hb : offset.toNat + (0 : UInt32).toNat ≤ dst.size.toUInt32.toNat := by
    simpa using UInt32.le_iff_toNat_le.mp ho
  have hm : dst.size.toUInt32.toNat ≤ dst.size := by
    simp only [UInt32.toNat_ofNat']; exact Nat.mod_le _ _
  unfold wasm_assemble at h
  cases hp : wasm_assemble.loop1 dst offset plan 0 0
      (decide (offset ≤ dst.size.toUInt32)) fuel with
  | none => simp [hp] at h
  | some state =>
    rcases state with ⟨total, i, ok⟩
    have ht := preflight_bound dst offset plan fuel 0 0 _ total i ok hb hp
    cases ok with
    | false =>
      simp [hp] at h
      rcases h with ⟨rfl, rfl⟩
      contradiction
    | true =>
      cases hw : wasm_assemble.loop2 dst plan 0 offset fuel with
      | none => simp [hp, hw] at h
      | some state =>
        rcases state with ⟨out', i', pos'⟩
        simp [hp, hw] at h
        rcases h with ⟨rfl, rfl⟩
        exact Nat.le_trans ht hm

end Oak.WasmAssembler
