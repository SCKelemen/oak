import Oak.WasmAssemblerBytes
import Oak.WasmInstruction

/-! Refinement of extracted scalar instruction writes and their composition. -/
namespace Oak.WasmEncoding

/-- Canonical bytes depend on the value, not the choice of an admitting width. -/
theorem encode_width_irrelevant {w₁ w₂ : Nat} {s : Bool} {v : Int}
    (hp₁ : 0 < w₁) (hp₂ : 0 < w₂)
    (hr₁ : WasmLEB.inRange w₁ s v) (hr₂ : WasmLEB.inRange w₂ s v) :
    encode w₁ s v = encode w₂ s v := by
  induction w₁ using Nat.strongRecOn generalizing w₂ v with
  | ind w₁ ih =>
    rw [encode_step hp₁ hr₁, encode_step hp₂ hr₂]
    by_cases ht : terminal s v
    · simp [ht]
    · have h₁ := continuation_width hp₁ hr₁ ht
      have h₂ := continuation_width hp₂ hr₂ ht
      simp only [if_neg ht]
      rw [ih (w₁ - 7) (by omega) (by omega) (by omega)
        (quotient_range h₁ hr₁) (quotient_range h₂ hr₂)]

end Oak.WasmEncoding
namespace Oak.WasmAssembler

private def kindCode : Option Oak.WasmInstruction.Immediate → UInt32
  | none => 0
  | some .plain => 1
  | some .block => 2
  | some .index => 3
  | some .s32 => 4
  | some .s64 => 5

private theorem kind_table : ∀ n : Fin 256,
    wasm_instruction_kind (UInt32.ofNat n.val) 0 =
      some (kindCode (Oak.WasmInstruction.kind (UInt8.ofNat n.val))) := by decide +kernel

/-- Complete opcode dispatch correspondence, including rejecting wide opcodes
rather than truncating them to an accepted byte. -/
theorem instruction_kind_exact (op : UInt32) (fuel : Nat) :
    wasm_instruction_kind op fuel = some (if op.toNat < 256
      then kindCode (Oak.WasmInstruction.kind op.toUInt8) else 0) := by
  have hf : wasm_instruction_kind op fuel = wasm_instruction_kind op 0 := rfl
  rw [hf]
  by_cases h : op.toNat < 256
  · rw [if_pos h]
    simpa using kind_table ⟨op.toNat, h⟩
  · rw [if_neg h]
    have ho : 256 ≤ op.toNat := by omega
    simp only [wasm_instruction_kind, pure, Bool.or_eq_true,
      Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    simp only [← UInt32.toNat_inj, UInt32.le_iff_toNat_le]
    simp only [UInt32.toNat_ofNat]
    split <;> rename_i h₁
    · omega
    · split <;> rename_i h₂
      · omega
      · split <;> rename_i h₃
        · omega
        · split <;> rename_i h₄
          · omega
          · split <;> rename_i h₅
            · omega
            · rfl

/-- The independent scalar grammar, with wide opcodes rejected before narrowing. -/
def instructionBytes (ins : WasmInstruction) : Option (List UInt8) :=
  if ins.opcode.toNat < 256 then Oak.WasmInstruction.encode ins.opcode.toUInt8 ins.immediate.toInt
  else none

private theorem unsigned_int (v : Int64) (h : 0 ≤ v.toInt) :
    (v.toUInt64.toNat : Int) = v.toInt := by
  have he := v.toBitVec.toInt_eq_toNat_bmod
  change v.toInt = (v.toUInt64.toNat : Int).bmod (2^64) at he
  have hb := v.toUInt64.toNat_lt
  rw [Int.bmod] at he
  split at he <;> omega

private theorem signed_range (v : Int64) : WasmLEB.inRange 64 true v.toInt :=
  ⟨v.le_toInt, v.toInt_lt⟩

private theorem size_u32 (v : Int64) (fuel : Nat) (hf : 10 ≤ fuel)
    (hr : WasmLEB.inRange 32 false v.toInt) :
    wasm_uleb_size v.toUInt64 fuel =
      some (UInt32.ofNat (WasmEncoding.encode 32 false v.toInt).length) := by
  have hu := unsigned_int v hr.1
  rw [uleb_size_exact _ _ hf, hu]
  rw [WasmEncoding.encode_width_irrelevant (by decide : 0 < 64) (by decide : 0 < 32) _ hr]
  simp only [WasmLEB.inRange, Bool.false_eq_true, ↓reduceIte] at hr ⊢
  constructor <;> omega

private theorem size_s32 (v : Int64) (fuel : Nat) (hf : 10 ≤ fuel)
    (hr : WasmLEB.inRange 32 true v.toInt) :
    wasm_sleb_size v fuel =
      some (UInt32.ofNat (WasmEncoding.encode 32 true v.toInt).length) := by
  rw [sleb_size_exact _ _ hf,
    WasmEncoding.encode_width_irrelevant (by decide : 0 < 64) (by decide : 0 < 32) (signed_range v) hr]

/-- Sizing terminates for every machine instruction, returning zero exactly
for rejection and the independent encoding's length for acceptance. -/
theorem instruction_size_exact (ins : WasmInstruction) (fuel : Nat) (hf : 10 ≤ fuel) :
    wasm_instruction_size ins fuel =
      some (UInt32.ofNat ((instructionBytes ins).getD []).length) := by
  by_cases ho : ins.opcode.toNat < 256
  · cases hk : Oak.WasmInstruction.kind ins.opcode.toUInt8 with
    | none => simp [wasm_instruction_size, instruction_kind_exact, instructionBytes, ho,
        Oak.WasmInstruction.encode, hk, kindCode]
    | some k =>
      cases k with
      | plain =>
        simp [wasm_instruction_size, instruction_kind_exact, instructionBytes, ho,
          Oak.WasmInstruction.encode, hk, kindCode, ← Int64.toInt_inj]
        split <;> simp_all
      | block =>
        simp [wasm_instruction_size, instruction_kind_exact, instructionBytes, ho,
          Oak.WasmInstruction.encode, hk, kindCode, ← Int64.toInt_inj, Oak.WasmInstruction.blockType, or_assoc]
        split <;> simp_all
      | index =>
        have hg : (0 ≤ ins.immediate.toInt ∧ ins.immediate.toInt ≤ 4294967295) ↔
            WasmLEB.inRange 32 false ins.immediate.toInt := by
          simp [WasmLEB.inRange]; omega
        by_cases hr : WasmLEB.inRange 32 false ins.immediate.toInt
        · simp [wasm_instruction_size, instruction_kind_exact, instructionBytes, ho,
            Oak.WasmInstruction.encode, hk, kindCode, size_u32 _ _ hf hr,
            Int64.le_iff_toInt_le, hg, hr, UInt32.ofNat_add, UInt32.add_comm]
        · simp [wasm_instruction_size, instruction_kind_exact, instructionBytes, ho,
            Oak.WasmInstruction.encode, hk, kindCode,
            Int64.le_iff_toInt_le, hg, hr]
      | s32 =>
        have hg : (-2147483648 ≤ ins.immediate.toInt ∧ ins.immediate.toInt ≤ 2147483647) ↔
            WasmLEB.inRange 32 true ins.immediate.toInt := by
          simp [WasmLEB.inRange]; omega
        by_cases hr : WasmLEB.inRange 32 true ins.immediate.toInt
        · simp [wasm_instruction_size, instruction_kind_exact, instructionBytes, ho,
            Oak.WasmInstruction.encode, hk, kindCode, size_s32 _ _ hf hr,
            Int64.le_iff_toInt_le, hg, hr, UInt32.ofNat_add, UInt32.add_comm]
        · simp [wasm_instruction_size, instruction_kind_exact, instructionBytes, ho,
            Oak.WasmInstruction.encode, hk, kindCode,
            Int64.le_iff_toInt_le, hg, hr]
      | s64 =>
        simp [wasm_instruction_size, instruction_kind_exact, instructionBytes, ho,
          Oak.WasmInstruction.encode, hk, kindCode, signed_range,
          sleb_size_exact _ _ hf, UInt32.ofNat_add, UInt32.add_comm]
  · simp [wasm_instruction_size, instruction_kind_exact, instructionBytes, ho]

private theorem encoding_bounds {op v bs} (h : Oak.WasmInstruction.encode op v = some bs) :
    0 < bs.length ∧ bs.length ≤ 11 := by
  cases hk : Oak.WasmInstruction.kind op with
  | none => simp [Oak.WasmInstruction.encode, hk] at h
  | some k =>
    cases k <;> simp [Oak.WasmInstruction.encode, hk] at h
    all_goals obtain ⟨hr, rfl⟩ := h
    · simp
    · simp
    · have := WasmEncoding.encode_byte_budget (by decide : 0 < 32) hr
      simp only [List.length_cons]; omega
    · have := WasmEncoding.encode_byte_budget (by decide : 0 < 32) hr
      simp only [List.length_cons]; omega
    · have := WasmEncoding.encode_byte_budget (by decide : 0 < 64) hr
      simp only [List.length_cons]; omega

/-- Every accepted instruction has a nonempty footprint of at most eleven bytes. -/
theorem instruction_bytes_bounds {ins bs} (h : instructionBytes ins = some bs) :
    0 < bs.length ∧ bs.length ≤ 11 := by
  unfold instructionBytes at h
  split at h
  · exact encoding_bounds h
  · contradiction

private theorem write_unsigned_width (dst : Array UInt8) (offset : UInt32) (v : Int64)
    (fuel : Nat) (hf : 11 ≤ fuel) (hs : dst.size < 2^32)
    (hr : WasmLEB.inRange 32 false v.toInt) :
    wasm_write_uleb dst offset v.toUInt64 fuel =
      some (if offset.toNat + (WasmEncoding.encode 32 false v.toInt).length ≤ dst.size
        then (UInt32.ofNat (WasmEncoding.encode 32 false v.toInt).length,
          writeBytes dst offset.toNat (WasmEncoding.encode 32 false v.toInt)) else (0, dst)) := by
  rw [write_uleb_exact _ _ _ _ hf hs, unsigned_int v hr.1]
  have hr64 : WasmLEB.inRange 64 false v.toInt := by
    simp [WasmLEB.inRange] at hr ⊢; omega
  rw [WasmEncoding.encode_width_irrelevant (by decide : 0 < 64) (by decide : 0 < 32) hr64 hr]

private theorem write_signed_width (dst : Array UInt8) (offset : UInt32) (v : Int64)
    (fuel w : Nat) (hf : 11 ≤ fuel) (hs : dst.size < 2^32)
    (hp : 0 < w) (hr : WasmLEB.inRange w true v.toInt) :
    wasm_write_sleb dst offset v fuel =
      some (if offset.toNat + (WasmEncoding.encode w true v.toInt).length ≤ dst.size
        then (UInt32.ofNat (WasmEncoding.encode w true v.toInt).length,
          writeBytes dst offset.toNat (WasmEncoding.encode w true v.toInt)) else (0, dst)) := by
  rw [write_sleb_exact _ _ _ _ hf hs,
    WasmEncoding.encode_width_irrelevant (by decide : 0 < 64) hp (signed_range v) hr]

/-- A valid, fitting instruction always terminates and writes exactly the
independent grammar's bytes. No successful-run premise is needed. -/
theorem write_instruction_admitted (dst : Array UInt8) (offset : UInt32)
    (ins : WasmInstruction) (bs : List UInt8) (fuel : Nat)
    (hf : 11 ≤ fuel) (hsmall : dst.size < 2^32)
    (he : instructionBytes ins = some bs) (hfit : offset.toNat + bs.length ≤ dst.size) :
    wasm_write_instruction dst offset ins fuel =
      some (UInt32.ofNat bs.length, writeBytes dst offset.toNat bs) := by
  have hb := instruction_bytes_bounds he
  have hn : (UInt32.ofNat bs.length).toNat = bs.length := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have hd : dst.size.toUInt32.toNat = dst.size := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hsmall]
  have hne : UInt32.ofNat bs.length ≠ 0 := by
    intro hz; have := congrArg UInt32.toNat hz; simp only [hn, UInt32.toNat_zero] at this; omega
  have hg : offset ≤ dst.size.toUInt32 ∧ UInt32.ofNat bs.length ≤ dst.size.toUInt32 - offset := by
    apply (range_guard_iff _ _ _).mpr; rwa [hn, hd]
  have hs : wasm_instruction_size ins fuel = some (UInt32.ofNat bs.length) := by
    rw [instruction_size_exact _ _ (by omega), he]; rfl
  have hnext : (offset + 1).toNat = offset.toNat + 1 := by
    rw [UInt32.toNat_add]; change (offset.toNat + 1) % 2^32 = _; omega
  have ho : ins.opcode.toNat < 256 := by
    unfold instructionBytes at he; split at he
    · assumption
    · contradiction
  have he' : Oak.WasmInstruction.encode ins.opcode.toUInt8 ins.immediate.toInt = some bs := by
    simpa [instructionBytes, ho] using he
  have hguard : ((UInt32.ofNat bs.length != 0) && decide (offset ≤ dst.size.toUInt32) &&
      decide (UInt32.ofNat bs.length ≤ dst.size.toUInt32 - offset)) = true := by
    simp [hne, hg]
  simp only [wasm_write_instruction, hs, bind, Option.bind, hguard, ↓reduceIte]
  cases hk : Oak.WasmInstruction.kind ins.opcode.toUInt8 with
  | none => simp [Oak.WasmInstruction.encode, hk] at he'
  | some k =>
    have hkind : wasm_instruction_kind ins.opcode fuel = some (kindCode (some k)) := by
      simp [instruction_kind_exact, ho, hk]
    cases k with
    | plain =>
      simp [Oak.WasmInstruction.encode, hk] at he'
      obtain ⟨hv, rfl⟩ := he'
      simp [hkind, kindCode, writeBytes]
    | block =>
      simp [Oak.WasmInstruction.encode, hk] at he'
      obtain ⟨hv, rfl⟩ := he'
      rcases hv with hv | hv | hv
      all_goals
        have hv' : ins.immediate = Int64.ofInt ins.immediate.toInt := by simp
        simp [hkind, kindCode, writeBytes, hnext]
        rw [hv', hv]
        rfl
    | index =>
      simp [Oak.WasmInstruction.encode, hk] at he'
      obtain ⟨hr, rfl⟩ := he'
      have hw := write_unsigned_width (dst.setIfInBounds offset.toNat ins.opcode.toUInt8)
        (offset + 1) ins.immediate fuel hf (by simpa using hsmall) hr
      have htail : (offset + 1).toNat + (WasmEncoding.encode 32 false ins.immediate.toInt).length ≤
          (dst.setIfInBounds offset.toNat ins.opcode.toUInt8).size := by
        simp only [Array.size_setIfInBounds, hnext]; simp only [List.length_cons] at hfit; omega
      rw [if_pos htail] at hw
      simp [hkind, kindCode, hw, writeBytes, hnext]
    | s32 =>
      simp [Oak.WasmInstruction.encode, hk] at he'
      obtain ⟨hr, rfl⟩ := he'
      have hw := write_signed_width (dst.setIfInBounds offset.toNat ins.opcode.toUInt8)
        (offset + 1) ins.immediate fuel 32 hf (by simpa using hsmall) (by decide) hr
      have htail : (offset + 1).toNat + (WasmEncoding.encode 32 true ins.immediate.toInt).length ≤
          (dst.setIfInBounds offset.toNat ins.opcode.toUInt8).size := by
        simp only [Array.size_setIfInBounds, hnext]; simp only [List.length_cons] at hfit; omega
      rw [if_pos htail] at hw
      simp [hkind, kindCode, hw, writeBytes, hnext]
    | s64 =>
      simp [Oak.WasmInstruction.encode, hk] at he'
      obtain ⟨hr, rfl⟩ := he'
      have hw := write_signed_width (dst.setIfInBounds offset.toNat ins.opcode.toUInt8)
        (offset + 1) ins.immediate fuel 64 hf (by simpa using hsmall) (by decide) hr
      have htail : (offset + 1).toNat + (WasmEncoding.encode 64 true ins.immediate.toInt).length ≤
          (dst.setIfInBounds offset.toNat ins.opcode.toUInt8).size := by
        simp only [Array.size_setIfInBounds, hnext]; simp only [List.length_cons] at hfit; omega
      rw [if_pos htail] at hw
      simp [hkind, kindCode, hw, writeBytes, hnext]

/-- Complete instruction writer contract, including invalid operands, invalid
opcodes, and capacity refusal. Every refusal preserves the entire buffer. -/
theorem write_instruction_exact (dst : Array UInt8) (offset : UInt32)
    (ins : WasmInstruction) (fuel : Nat) (hf : 11 ≤ fuel) (hsmall : dst.size < 2^32) :
    wasm_write_instruction dst offset ins fuel = some (
      match instructionBytes ins with
      | none => (0, dst)
      | some bs => if offset.toNat + bs.length ≤ dst.size
          then (UInt32.ofNat bs.length, writeBytes dst offset.toNat bs) else (0, dst)) := by
  cases he : instructionBytes ins with
  | none =>
    have hs : wasm_instruction_size ins fuel = some 0 := by
      rw [instruction_size_exact _ _ (by omega), he]; rfl
    exact write_instruction_refuses dst offset ins fuel 0 hs (by simp)
  | some bs =>
    by_cases hfit : offset.toNat + bs.length ≤ dst.size
    · simp only [if_pos hfit]
      exact write_instruction_admitted dst offset ins bs fuel hf hsmall he hfit
    · simp only [if_neg hfit]
      have hb := instruction_bytes_bounds he
      have hn : (UInt32.ofNat bs.length).toNat = bs.length := by
        rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
      have hd : dst.size.toUInt32.toNat = dst.size := by
        rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hsmall]
      have hs : wasm_instruction_size ins fuel = some (UInt32.ofNat bs.length) := by
        rw [instruction_size_exact _ _ (by omega), he]; rfl
      apply write_instruction_refuses dst offset ins fuel _ hs
      intro hg
      have hb := (range_guard_iff _ _ _).mp hg.2
      rw [hn, hd] at hb
      exact hfit hb

/-- The independent decoder recovers the original instruction and untouched
suffix from the actual buffer produced by the extracted writer. -/
theorem write_instruction_decode (dst out : Array UInt8) (offset written : UInt32)
    (ins : WasmInstruction) (bs : List UInt8) (fuel : Nat)
    (hf : 11 ≤ fuel) (hsmall : dst.size < 2^32)
    (he : instructionBytes ins = some bs) (hfit : offset.toNat + bs.length ≤ dst.size)
    (hw : wasm_write_instruction dst offset ins fuel = some (written, out)) :
    Oak.WasmInstruction.decode (out.toList.drop offset.toNat) =
      some ((ins.opcode.toUInt8, ins.immediate.toInt), dst.toList.drop (offset.toNat + bs.length)) := by
  rw [write_instruction_admitted _ _ _ _ _ hf hsmall he hfit] at hw
  cases hw
  rw [writeBytes_suffix _ _ _ hfit]
  unfold instructionBytes at he
  split at he
  · exact Oak.WasmInstruction.decode_encode he _
  · contradiction

/-- Adjacent writes compose into one contiguous write, with no buffer-size or
machine-address assumptions hidden in the list algebra. -/
theorem writeBytes_append (dst : Array UInt8) (offset : Nat) (a b : List UInt8) :
    writeBytes dst offset (a ++ b) =
      writeBytes (writeBytes dst offset a) (offset + a.length) b := by
  induction a generalizing dst offset with
  | nil => simp [writeBytes]
  | cons v a ih =>
    simpa [writeBytes, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (ih (dst.setIfInBounds offset v) (offset + 1))

/-- Independent byte assembly for machine instruction records. -/
def instructionSequence : List WasmInstruction → Option (List UInt8)
  | [] => some []
  | ins :: rest => do
    let front ← instructionBytes ins
    let tail ← instructionSequence rest
    some (front ++ tail)

/-- Mapping machine records to grammar tokens preserves the sequence bytes. -/
theorem instructionSequence_model {plan bs} (h : instructionSequence plan = some bs) :
    Oak.WasmInstruction.assemble (plan.map fun ins => (ins.opcode.toUInt8, ins.immediate.toInt)) = some bs := by
  induction plan generalizing bs with
  | nil => simpa [instructionSequence, Oak.WasmInstruction.assemble] using h
  | cons ins rest ih =>
    cases he : instructionBytes ins with
    | none => simp [instructionSequence, he] at h
    | some front =>
      cases ht : instructionSequence rest with
      | none => simp [instructionSequence, he, ht] at h
      | some tail =>
        simp [instructionSequence, he, ht] at h
        subst bs
        have he' : Oak.WasmInstruction.encode ins.opcode.toUInt8 ins.immediate.toInt = some front := by
          unfold instructionBytes at he; split at he
          · exact he
          · contradiction
        simp [Oak.WasmInstruction.assemble, he', ih ht]

end Oak.WasmAssembler
