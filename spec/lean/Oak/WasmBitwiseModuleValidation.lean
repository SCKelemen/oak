import Oak.WasmBitwiseModuleGuards

/-! Universal name validation and transactional malformed-name refusal for the
mechanically extracted complete Wasm module writer. This module proves no
successful envelope, byte-layout, or full module-refinement result. The array
name and destination model disjoint Oak spans; representability and extraction
fuel are explicit. Every validation read is in bounds and every loop increment
is nonwrapping, independently of the extraction's default array operations. -/

set_option autoImplicit false
namespace Oak.WasmAssembler

/-- The writer's permitted name bytes: non-NUL, seven-bit ASCII. This is only
its proposal domain, not the source language's identifier grammar. -/
def bitwiseNameByte (b : UInt8) : Bool := decide (b ≠ 0 ∧ b < 128)

/-- A true validation guard addresses the actual name array. Incrementing that
index reaches at most its represented length, without wrapping. -/
theorem bitwise_name_scan_index (name : Array UInt8) (i : UInt32)
    (hn : name.size < 2^32) (hi : i < name.size.toUInt32) :
    i.toNat < name.size ∧ (i + 1).toNat = i.toNat + 1 ∧
      (i + 1).toNat ≤ name.size := by
  have hlen : name.size.toUInt32.toNat = name.size := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hn]
  rw [UInt32.lt_iff_toNat_lt, hlen] at hi
  have hnext : (i + 1).toNat = i.toNat + 1 := by
    rw [UInt32.toNat_add]
    change (i.toNat + 1) % 2^32 = i.toNat + 1
    exact Nat.mod_eq_of_lt (by omega)
  exact ⟨hi, hnext, by omega⟩

private theorem name_head (name : Array UInt8) (pre : List UInt8)
    (b : UInt8) (rest : List UInt8) (he : name.toList = pre ++ b :: rest) :
    name.getD pre.length 0 = b := by
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, he, List.getElem?_append]
  simp

private theorem scan_flag (b : UInt8) (ok : Bool) :
    (if b == 0 || decide (b ≥ 128) then false else ok) =
      (ok && bitwiseNameByte b) := by
  by_cases hz : b = 0
  · simp [hz, bitwiseNameByte]
  · by_cases hhigh : 128 ≤ b
    · have hnot : ¬ b < 128 := by
        rw [UInt8.le_iff_toNat_le] at hhigh
        rw [UInt8.lt_iff_toNat_lt]
        omega
      simp [hz, hhigh, hnot, bitwiseNameByte]
    · have hlow : b < 128 := by
        rw [UInt8.le_iff_toNat_le] at hhigh
        rw [UInt8.lt_iff_toNat_lt]
        omega
      simp [hz, hhigh, hlow, bitwiseNameByte]

/-- Exact validation of every remaining suffix, including an already-false
flag and malformed bytes arbitrarily late in the name. The explicit budget
counts one guard per remaining byte and one final guard, with no returned-run
assumption. The induction uses `bitwise_name_scan_index` at every read. -/
theorem bitwise_name_scan_exact (name : Array UInt8) (remaining : List UInt8) :
    ∀ (pre : List UInt8) (ok : Bool) (fuel : Nat),
      name.size < 2^32 → name.toList = pre ++ remaining →
      remaining.length + 1 ≤ fuel →
      wasm_bitwise_module.loop1 name name.size.toUInt32 ok
          (UInt32.ofNat pre.length) fuel =
        some (ok && remaining.all bitwiseNameByte, name.size.toUInt32) := by
  induction remaining with
  | nil =>
    intro pre ok fuel hn he hf
    have hlen : pre.length = name.size := by
      simpa using congrArg List.length he.symm
    cases fuel with
    | zero => omega
    | succ fuel => simp [wasm_bitwise_module.loop1, hlen]
  | cons b rest ih =>
    intro pre ok fuel hn he hf
    have hlen : name.size = pre.length + (rest.length + 1) := by
      simpa using congrArg List.length he
    have hpre : (UInt32.ofNat pre.length).toNat = pre.length := by
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    have hname : name.size.toUInt32.toNat = name.size := by
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hn]
    have hguard : UInt32.ofNat pre.length < name.size.toUInt32 := by
      rw [UInt32.lt_iff_toNat_lt, hpre, hname]
      omega
    have hsafe := bitwise_name_scan_index name (UInt32.ofNat pre.length) hn hguard
    have hread : name.getD (UInt32.ofNat pre.length).toNat 0 = b := by
      rw [hpre]
      exact name_head name pre b rest he
    have hindex : UInt32.ofNat pre.length + 1 = UInt32.ofNat (pre ++ [b]).length := by
      apply UInt32.toNat_inj.mp
      rw [hsafe.2.1, hpre, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by simp; omega)]
      simp
    have htail : name.toList = (pre ++ [b]) ++ rest := by
      simpa [List.append_assoc] using he
    cases fuel with
    | zero => simp only [List.length_cons] at hf; omega
    | succ fuel =>
      have hr := ih (pre ++ [b]) (ok && bitwiseNameByte b) fuel hn htail
        (by simp only [List.length_cons] at hf; omega)
      simp only [wasm_bitwise_module.loop1, decide_eq_true hguard, ↓reduceIte, hread]
      split <;> rename_i hbad
      · have hflag : (ok && bitwiseNameByte b) = false := by
          simpa [hbad] using (scan_flag b ok).symm
        simp only [bind, Option.bind, pure]
        rw [hindex]
        simpa [List.all_cons, ← Bool.and_assoc, hflag] using hr
      · have hflag : (ok && bitwiseNameByte b) = ok := by
          simpa [hbad] using (scan_flag b ok).symm
        simp only [bind, Option.bind, pure]
        rw [hindex]
        simpa [← Bool.and_assoc, hflag] using hr


/-- Whole-name validation returns the exact domain predicate and the final
represented length. Sufficient fuel guarantees a returned result. -/
theorem bitwise_name_validation_exact (name : Array UInt8) (fuel : Nat)
    (hn : name.size < 2^32) (hf : name.size + 1 ≤ fuel) :
    wasm_bitwise_module.loop1 name name.size.toUInt32 true 0 fuel =
      some (name.toList.all bitwiseNameByte, name.size.toUInt32) := by
  simpa using bitwise_name_scan_exact name name.toList [] true fuel hn
    (by simp) (by simpa using hf)

/-- The mathematical predicate exactly characterizes the writer's allowed
name bytes; the source language may impose additional identifier constraints. -/
theorem bitwise_name_all_iff (name : Array UInt8) :
    name.toList.all bitwiseNameByte = true ↔
      ∀ b ∈ name.toList, b ≠ 0 ∧ b < 128 := by
  rw [List.all_eq_true]
  simp only [bitwiseNameByte, decide_eq_true_eq]

/-- Any malformed name byte, including an arbitrarily late one, makes the
actual complete writer return zero and the complete original destination.
This quantifies over all operation tags and all destinations: an earlier
operation/length refusal is also unchanged. No destination bound is needed
because this path never reads or writes it. The name span remains representable
and has enough fuel for its entire validation loop. -/
theorem bitwise_module_invalid_name (dst name : Array UInt8) (op : UInt32)
    (fuel : Nat) (hn : name.size < 2^32) (hf : name.size + 1 ≤ fuel)
    (hbad : ∃ b ∈ name.toList, b = 0 ∨ 128 ≤ b) :
    wasm_bitwise_module dst op name fuel = some (0, dst) := by
  have hall : name.toList.all bitwiseNameByte = false := by
    cases he : name.toList.all bitwiseNameByte with
    | false => rfl
    | true =>
      obtain ⟨b, hb, hz | hhigh⟩ := hbad
      · exact False.elim ((bitwise_name_all_iff name).mp he b hb |>.1 hz)
      · have hlow := ((bitwise_name_all_iff name).mp he b hb).2
        rw [UInt8.le_iff_toNat_le] at hhigh
        rw [UInt8.lt_iff_toNat_lt] at hlow
        omega
  have hscan := bitwise_name_validation_exact name fuel hn hf
  rw [hall] at hscan
  simp only [wasm_bitwise_module]
  split
  · simp [hscan]
  · rfl

/-- Indexed form: the bad byte is a genuine in-bounds source element, not an
out-of-bounds `getD` default supplied by the extracted array model. -/
theorem bitwise_module_invalid_name_at (dst name : Array UInt8) (op : UInt32)
    (fuel j : Nat) (hn : name.size < 2^32) (hf : name.size + 1 ≤ fuel)
    (hj : j < name.size) (hbad : name[j] = 0 ∨ 128 ≤ name[j]) :
    wasm_bitwise_module dst op name fuel = some (0, dst) := by
  apply bitwise_module_invalid_name dst name op fuel hn hf
  exact ⟨name[j], by simp, hbad⟩

end Oak.WasmAssembler
