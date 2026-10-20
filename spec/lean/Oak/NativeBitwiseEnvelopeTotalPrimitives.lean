import Oak.NativeBitwiseEnvelopeCorrectness

/-! Refusal-side facts about the actual extracted native writer. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
namespace Oak.BitwiseELFProducer

private theorem array_head_total (src : Array UInt8) (pre : List UInt8)
    (b : UInt8) (rest : List UInt8) (he : src.toList = pre ++ b :: rest) :
    src.getD pre.length 0 = b := by
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, he, List.getElem?_append]
  simp

/-- Total short-circuit scan. On an invalid byte the final index need not reach
    the name's end; the returned flag records precisely all remaining bytes. -/
theorem name_scan_total_suffix (name : Array UInt8) (remaining : List UInt8) :
    ∀ (pre : List UInt8) (ok : Bool) (fuel : Nat), name.size < 2^32 →
      name.toList = pre ++ remaining → remaining.length + 1 ≤ fuel →
      ∃ i, native_bitwise_elf_image.loop1 name ok (UInt32.ofNat pre.length) fuel =
        some (ok && remaining.all (fun b => decide (0 < b ∧ b < 128)), i) ∧
        i.toNat ≤ name.size := by
  induction remaining with
  | nil =>
    intro pre ok fuel hn he hf
    have hlen : pre.length = name.size := by simpa using congrArg List.length he.symm
    have hv : name.size.toUInt32.toNat = name.size := by
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hn]
    cases fuel with
    | zero => omega
    | succ fuel => exact ⟨name.size.toUInt32, by simp [native_bitwise_elf_image.loop1, hlen], by omega⟩
  | cons b rest ih =>
    intro pre ok fuel hn he hf
    have hlen : name.size = pre.length + (rest.length + 1) := by
      simpa using congrArg List.length he
    have hpre : (UInt32.ofNat pre.length).toNat = pre.length := by
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    have hname : name.size.toUInt32.toNat = name.size := by
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hn]
    have hguard : UInt32.ofNat pre.length < name.size.toUInt32 := by
      rw [UInt32.lt_iff_toNat_lt, hpre, hname]; omega
    have hsafe := scan_index name (UInt32.ofNat pre.length) hn hguard
    have hread : name.getD (UInt32.ofNat pre.length).toNat 0 = b := by
      rw [hpre]; exact array_head_total name pre b rest he
    have hindex : UInt32.ofNat pre.length + 1 = UInt32.ofNat (pre ++ [b]).length := by
      apply UInt32.toNat_inj.mp
      rw [hsafe.2.1, hpre, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by simp; omega)]
      simp
    have htail : name.toList = (pre ++ [b]) ++ rest := by
      simpa [List.append_assoc] using he
    cases fuel with
    | zero => simp only [List.length_cons] at hf; omega
    | succ fuel =>
      cases ok with
      | false => exact ⟨UInt32.ofNat pre.length, by simp [native_bitwise_elf_image.loop1], by omega⟩
      | true =>
        obtain ⟨i, hr, hi⟩ := ih (pre ++ [b]) (decide (0 < b ∧ b < 128)) fuel hn htail
          (by simp only [List.length_cons] at hf; omega)
        refine ⟨i, ?_, hi⟩
        simpa only [native_bitwise_elf_image.loop1, decide_eq_true hguard, Bool.and_self,
          ↓reduceIte, hread, hindex, Bool.decide_and, List.all_cons, Bool.true_and] using hr

theorem name_scan_total (name : Array UInt8) (ok : Bool) (fuel : Nat)
    (hn : name.size < 2^32) (hf : name.size + 1 ≤ fuel) :
    ∃ i, native_bitwise_elf_image.loop1 name ok 0 fuel =
      some (ok && name.toList.all (fun b => decide (0 < b ∧ b < 128)), i) ∧
      i.toNat ≤ name.size := by
  simpa using name_scan_total_suffix name name.toList [] ok fuel hn (by simp) (by simpa using hf)

/-- Packed 32-bit reads lose no information about any of their four bytes. -/
theorem packed_read_octets (a b c d : UInt8) :
    wordOctets (((a.toUInt32 ||| (b.toUInt32 <<< 8)) ||| (c.toUInt32 <<< 16)) |||
      (d.toUInt32 <<< 24)) = [a,b,c,d] := by
  simp only [wordOctets, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    apply UInt8.toBitVec_inj.mp
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp (disch := omega) [UInt32.toBitVec_toUInt8, UInt8.toBitVec_toUInt32,
      UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt32.toBitVec_shiftRight,
      BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.getLsbD_of_ge]
    all_goals
      have h7 : i ≤ 7 := by omega
      have h15 : i ≤ 15 := by omega
      simp_all +arith


def readValue (src : Array UInt8) (offset : Nat) : UInt32 :=
  ((src.getD offset 0).toUInt32 ||| ((src.getD (offset+1) 0).toUInt32 <<< 8)) |||
    ((src.getD (offset+2) 0).toUInt32 <<< 16) ||| ((src.getD (offset+3) 0).toUInt32 <<< 24)

/-- All four actual read indices are nonwrapping and in bounds. -/
theorem native_read_value (src : Array UInt8) (offset : UInt32) (fuel : Nat)
    (hn : src.size < 2^32) (hfit : offset.toNat + 4 ≤ src.size) :
    native_bitwise_elf_read src offset fuel = some (readValue src offset.toNat) := by
  have h1 : (offset + 1).toNat = offset.toNat + 1 := by
    rw [UInt32.toNat_add]; change (offset.toNat + 1) % 2^32 = _
    exact Nat.mod_eq_of_lt (by omega)
  have h2 : (offset + 2).toNat = offset.toNat + 2 := by
    rw [UInt32.toNat_add]; change (offset.toNat + 2) % 2^32 = _
    exact Nat.mod_eq_of_lt (by omega)
  have h3 : (offset + 3).toNat = offset.toNat + 3 := by
    rw [UInt32.toNat_add]; change (offset.toNat + 3) % 2^32 = _
    exact Nat.mod_eq_of_lt (by omega)
  simp [native_bitwise_elf_read, readValue, h1, h2, h3]

private theorem take_four (xs : List UInt8) (h : 4 ≤ xs.length) :
    xs.take 4 = [xs.getD 0 0, xs.getD 1 0, xs.getD 2 0, xs.getD 3 0] := by
  match xs with
  | a :: b :: c :: d :: rest => rfl
  | [] => simp at h
  | [_] => simp at h
  | [_, _] => simp at h
  | [_, _, _] => simp at h

/-- This byte equation uses a real four-byte slice, never an absent-byte default. -/
theorem read_value_bytes (src : Array UInt8) (offset : Nat)
    (hfit : offset + 4 ≤ src.size) :
    (src.toList.drop offset).take 4 = wordOctets (readValue src offset) := by
  rw [take_four _ (by simp; omega), readValue, packed_read_octets]
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop,
    Array.getD_eq_getD_getElem?, ← Array.getElem?_toList]

/-- Boolean intermediate for the actual source's fixed startup word checks. -/
def startupCheck (m : Oak.MinimalELF.Machine) (text : Array UInt8) : Bool :=
  match m with
  | .arm64 => (readValue text 0 == 0x94000003) &&
      (readValue text 4 == 0x52800ba8) && (readValue text 8 == 0xd4000001)
  | .rv64 => (readValue text 0 == 0x00000097) &&
      (readValue text 4 == 0x010080e7) && (readValue text 8 == 0x05d00893) &&
      (readValue text 12 == 0x00000073)

/-- Byte-level inversion of every checked startup word under the checked text
length. The reverse direction is the existing exact read theorem. -/
theorem startupCheck_iff (m : Oak.MinimalELF.Machine) (text : Array UInt8)
    (ht : text.size = Oak.NativeBitwiseImage.textSize m) :
    startupCheck m text = true ↔ text.toList.take (Oak.NativeBitwiseImage.stubSize m) =
      Oak.NativeBitwiseObject.toUInt8 (Oak.NativeBitwiseImage.startup m) := by
  constructor
  · intro hc
    cases m with
    | arm64 =>
      simp only [startupCheck, Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨h0, h4⟩, h8⟩ := hc
      have b0 := read_value_bytes text 0 (by simp [Oak.NativeBitwiseImage.textSize,
        Oak.NativeBitwiseImage.stubSize, Oak.NativeBitwiseImage.bodySize] at ht; omega)
      have b4 := read_value_bytes text 4 (by simp [Oak.NativeBitwiseImage.textSize,
        Oak.NativeBitwiseImage.stubSize, Oak.NativeBitwiseImage.bodySize] at ht; omega)
      have b8 := read_value_bytes text 8 (by simp [Oak.NativeBitwiseImage.textSize,
        Oak.NativeBitwiseImage.stubSize, Oak.NativeBitwiseImage.bodySize] at ht; omega)
      rw [h0] at b0; simp only [List.drop_zero] at b0; rw [h4] at b4; rw [h8] at b8
      change text.toList.take (8+4) = _
      rw [List.take_add, show (8 : Nat) = 4+4 from rfl, List.take_add]
      rw [b0, b4, b8]; rfl
    | rv64 =>
      simp only [startupCheck, Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨⟨h0, h4⟩, h8⟩, h12⟩ := hc
      have hf (off : Nat) (ho : off ≤ 12) : off+4 ≤ text.size := by
        simp [Oak.NativeBitwiseImage.textSize, Oak.NativeBitwiseImage.stubSize,
          Oak.NativeBitwiseImage.bodySize] at ht; omega
      have b0 := read_value_bytes text 0 (hf 0 (by omega))
      have b4 := read_value_bytes text 4 (hf 4 (by omega))
      have b8 := read_value_bytes text 8 (hf 8 (by omega))
      have b12 := read_value_bytes text 12 (hf 12 (by omega))
      rw [h0] at b0; simp only [List.drop_zero] at b0; rw [h4] at b4; rw [h8] at b8; rw [h12] at b12
      change text.toList.take (12+4) = _
      rw [List.take_add, show (12 : Nat) = 8+4 from rfl, List.take_add,
        show (8 : Nat) = 4+4 from rfl, List.take_add]
      rw [b0, b4, b8, b12]; rfl
  · intro hp
    have he : text.toList = Oak.NativeBitwiseObject.toUInt8 (Oak.NativeBitwiseImage.startup m) ++
        text.toList.drop (Oak.NativeBitwiseImage.stubSize m) := by
      rw [← hp]; exact (List.take_append_drop _ _).symm
    have hr := startup_reads m text _ 0 he
    have hn : text.size < 2^32 := by
      cases m <;> simp [Oak.NativeBitwiseImage.textSize, Oak.NativeBitwiseImage.stubSize,
        Oak.NativeBitwiseImage.bodySize] at ht <;> omega
    have hf (off : UInt32) (ho : off.toNat + 4 ≤ Oak.NativeBitwiseImage.stubSize m) :
        off.toNat + 4 ≤ text.size := by
      rw [ht]; unfold Oak.NativeBitwiseImage.textSize; omega
    cases m with
    | arm64 =>
      obtain ⟨h0,h4,h8⟩ := hr.1 rfl
      rw [native_read_value text 0 0 hn (hf 0 (by decide))] at h0
      rw [native_read_value text 4 0 hn (hf 4 (by decide))] at h4
      rw [native_read_value text 8 0 hn (hf 8 (by decide))] at h8
      exact (by simpa only [startupCheck, Bool.and_eq_true, beq_iff_eq, UInt32.toNat_ofNat, Nat.reduceMod] using
        And.intro (And.intro (Option.some.inj h0) (Option.some.inj h4)) (Option.some.inj h8))
    | rv64 =>
      obtain ⟨h0,h4,h8,h12⟩ := hr.2 rfl
      rw [native_read_value text 0 0 hn (hf 0 (by decide))] at h0
      rw [native_read_value text 4 0 hn (hf 4 (by decide))] at h4
      rw [native_read_value text 8 0 hn (hf 8 (by decide))] at h8
      rw [native_read_value text 12 0 hn (hf 12 (by decide))] at h12
      exact (by simpa only [startupCheck, Bool.and_eq_true, beq_iff_eq, UInt32.toNat_ofNat, Nat.reduceMod] using
        And.intro (And.intro (And.intro (Option.some.inj h0) (Option.some.inj h4))
          (Option.some.inj h8)) (Option.some.inj h12))

end Oak.BitwiseELFProducer
