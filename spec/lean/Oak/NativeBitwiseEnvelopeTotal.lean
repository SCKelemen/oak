import Oak.NativeBitwiseEnvelopeTotalPrimitives
import Oak.NativeBitwiseEnvelopeTotalSpec

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
namespace Oak.BitwiseELFProducer
open Oak.NativeBitwiseEnvelope
open Oak.MinimalELF (Machine)
open Oak.WasmAssembler (writeBytes writeBytes_suffix)

def sourceInitial (m : Machine) (dst text name : Array UInt8) : Bool :=
  (text.size.toUInt32 == (if archTag m == 1 then 12 else 16) +
    (if archTag m == 1 then 8 else 36)) &&
      decide (dst.size.toUInt32 ≥ sourceSections m name.size.toUInt32 + 384)

/-- All natural/source size conversions, including layout alignment and the
complete envelope size, are exact before any refusal or mutation. -/
theorem sourceInitial_eq (m : Machine) (dst text name : Array UInt8)
    (hn : name.size ≤ 256) (hd : dst.size < 2^32) (ht : text.size < 2^32) :
    sourceInitial m dst text name =
      decide (text.size = Oak.NativeBitwiseImage.textSize m ∧ Capacity m dst name) := by
  have hdval : dst.size.toUInt32.toNat = dst.size := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hd]
  have htval : text.size.toUInt32.toNat = text.size := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt ht]
  have hsections := sourceSections_nat m name hn
  have hsmall : Oak.NativeBitwiseImage.shOffset m
      (Oak.NativeBitwiseObject.fromUInt8 name.toList) + 384 ≤ 4928 := by
    have bound := E_size_bound m name.toList (List.replicate (Oak.NativeBitwiseImage.bodySize m) 0)
      (by simpa using hn) (by simp)
    rw [E_length m name.toList _ (by simp)] at bound
    exact bound
  have hsize : (sourceSections m name.size.toUInt32 + 384).toNat =
      Oak.NativeBitwiseImage.shOffset m (Oak.NativeBitwiseObject.fromUInt8 name.toList) + 384 := by
    rw [UInt32.toNat_add, hsections]
    change (_ + 384) % 2^32 = _
    exact Nat.mod_eq_of_lt (by omega)
  have hlen : ((if archTag m == 1 then 12 else 16) +
      (if archTag m == 1 then 8 else 36) : UInt32).toNat = Oak.NativeBitwiseImage.textSize m := by
    cases m <;> rfl
  simp only [beq_iff_eq] at hlen
  apply Bool.eq_iff_iff.mpr
  change sourceInitial m dst text name = true ↔ decide _ = true
  rw [decide_eq_true_eq]
  simp only [sourceInitial, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  change _ ∧ (sourceSections m name.size.toUInt32 + 384 ≤ dst.size.toUInt32) ↔ _
  rw [← UInt32.toNat_inj, htval, hlen, UInt32.le_iff_toNat_le, hdval, hsize]
  rfl

/-- A rejected outer guard performs no array update and needs no loop fuel. -/
theorem image_refuses_outer (dst text name : Array UInt8) (arch : UInt32) (fuel : Nat)
    (hguard : (((arch == 1 || arch == 2) && decide (name.size.toUInt32 > 0)) &&
      decide (name.size.toUInt32 ≤ 256)) = false) :
    native_bitwise_elf_image dst text arch name fuel = some (0, dst) := by
  simp only [native_bitwise_elf_image, hguard, Bool.false_eq_true, ↓reduceIte,
    pure, Bind.bind, Option.bind]

/-- Refusal after the actual scan, before the first destination write. -/
theorem image_refuses_scan (m : Machine) (dst text name : Array UInt8) (fuel : Nat)
    (hnlo : 0 < name.size) (hnhi : name.size ≤ 256) (i : UInt32)
    (hscan : native_bitwise_elf_image.loop1 name (sourceInitial m dst text name) 0 fuel =
      some (false, i)) :
    native_bitwise_elf_image dst text (archTag m) name fuel = some (0, dst) := by
  have hnval : name.size.toUInt32.toNat = name.size := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have hnlo32 : (0 : UInt32) < name.size.toUInt32 := by
    rw [UInt32.lt_iff_toNat_lt, hnval]; exact hnlo
  have hnhi32 : name.size.toUInt32 ≤ (256 : UInt32) := by
    rw [UInt32.le_iff_toNat_le, hnval]; exact hnhi
  have harch : (archTag m == 1 || archTag m == 2) = true := by cases m <;> rfl
  simp only [sourceInitial, sourceSections] at hscan
  simp only [native_bitwise_elf_image, decide_eq_true hnlo32, decide_eq_true hnhi32,
    harch, Bool.and_self, ↓reduceIte]
  simp only [GE.ge] at hscan ⊢
  erw [hscan]
  rfl

/-- Startup failure is checked through the actual three/four four-byte reads,
with the complete read footprints supplied by the exact text-length guard. -/
theorem image_refuses_startup (m : Machine) (dst text name : Array UInt8) (fuel : Nat)
    (hnlo : 0 < name.size) (hnhi : name.size ≤ 256)
    (ht : text.size = Oak.NativeBitwiseImage.textSize m) (i : UInt32)
    (hscan : native_bitwise_elf_image.loop1 name (sourceInitial m dst text name) 0 fuel =
      some (true, i)) (hstartup : startupCheck m text = false) :
    native_bitwise_elf_image dst text (archTag m) name fuel = some (0, dst) := by
  have hnval : name.size.toUInt32.toNat = name.size := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have hnlo32 : (0 : UInt32) < name.size.toUInt32 := by
    rw [UInt32.lt_iff_toNat_lt, hnval]; exact hnlo
  have hnhi32 : name.size.toUInt32 ≤ (256 : UInt32) := by
    rw [UInt32.le_iff_toNat_le, hnval]; exact hnhi
  have harch : (archTag m == 1 || archTag m == 2) = true := by cases m <;> rfl
  have htrep : text.size < 2^32 := by
    cases m <;> simp [Oak.NativeBitwiseImage.textSize, Oak.NativeBitwiseImage.stubSize,
      Oak.NativeBitwiseImage.bodySize] at ht <;> omega
  have hr (off : UInt32) (ho : off.toNat+4 ≤ Oak.NativeBitwiseImage.stubSize m) :
      native_bitwise_elf_read text off fuel = some (readValue text off.toNat) :=
    native_read_value text off fuel htrep (by rw [ht]; unfold Oak.NativeBitwiseImage.textSize; omega)
  simp only [sourceInitial, sourceSections] at hscan
  simp only [native_bitwise_elf_image, decide_eq_true hnlo32, decide_eq_true hnhi32,
    harch, Bool.and_self, ↓reduceIte]
  simp only [GE.ge] at hscan ⊢
  erw [hscan]
  simp only [Bind.bind, Option.bind, ↓reduceIte]
  cases m with
  | arm64 =>
    simp only [startupCheck] at hstartup
    have h0 := hr 0 (by decide); have h4 := hr 4 (by decide); have h8 := hr 8 (by decide)
    simp only [archTag, beq_self_eq_true, ↓reduceIte, h0, h4, h8,
      UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod, hstartup,
      Bool.false_eq_true, ↓reduceIte, pure]
  | rv64 =>
    simp only [startupCheck] at hstartup
    have h0 := hr 0 (by decide); have h4 := hr 4 (by decide); have h8 := hr 8 (by decide)
    have h12 := hr 12 (by decide)
    simp only [archTag, show ((2 : UInt32) == 1) = false by decide, Bool.false_eq_true,
      ↓reduceIte, h0, h4, h8, h12, UInt32.toNat_ofNat,
      Nat.reducePow, Nat.reduceMod, hstartup, Bool.false_eq_true, ↓reduceIte, pure]

/-- Complete architecture-specific outcome, with no successful-run hypothesis. -/
theorem image_total_machine (m : Machine) (dst text name : Array UInt8) (fuel : Nat)
    (hd : dst.size < 2^32) (ht : text.size < 2^32) (hn : name.size < 2^32)
    (hf : 4929 ≤ fuel) :
    native_bitwise_elf_image dst text (archTag m) name fuel =
      some (if Eligible m dst text name then envelopeSuccess m dst text name else (0, dst)) := by
  by_cases he : Eligible m dst text name
  · rw [if_pos he]
    obtain ⟨⟨hnlo,hnhi,hnb⟩,htlen,hstartup,hcap⟩ := he
    have hb : (bodyFromText m text).length = Oak.NativeBitwiseImage.bodySize m := by
      simp only [bodyFromText, List.length_drop, Array.length_toList, htlen,
        Oak.NativeBitwiseImage.textSize]; omega
    have htext : text.toList = Oak.NativeBitwiseObject.toUInt8 (Oak.NativeBitwiseImage.startup m) ++
        bodyFromText m text := by
      unfold bodyFromText
      rw [← hstartup]; exact (List.take_append_drop _ _).symm
    have hfit : (E m name.toList (bodyFromText m text)).length ≤ dst.size := by
      rw [E_length m name.toList _ hb]; exact hcap
    have hr := image_exact m dst text name (bodyFromText m text) fuel
      hnlo hnhi hnb hb htext hd hfit hf
    have hout : writeBytes dst 0 (E m name.toList (bodyFromText m text)) =
        (E m name.toList (bodyFromText m text) ++
          dst.toList.drop (E m name.toList (bodyFromText m text)).length).toArray := by
      apply Array.toList_inj.mp
      simpa using writeBytes_suffix dst 0 (E m name.toList (bodyFromText m text)) (by simpa using hfit)
    rw [envelopeSuccess, ← hout]; exact hr
  · rw [if_neg he]
    by_cases hlen : 0 < name.size ∧ name.size ≤ 256
    · have hinit := sourceInitial_eq m dst text name hlen.2 hd ht
      obtain ⟨i,hscan,_⟩ := name_scan_total name (sourceInitial m dst text name) fuel hn (by omega)
      by_cases hi : text.size = Oak.NativeBitwiseImage.textSize m ∧ Capacity m dst name
      · have hisource : sourceInitial m dst text name = true := by rw [hinit]; simp [hi]
        by_cases hb : ∀ b ∈ name.toList, 0 < b ∧ b < 128
        · have hbtrue : name.toList.all (fun b => decide (0 < b ∧ b < 128)) = true := by
            simpa only [List.all_eq_true, decide_eq_true_eq] using hb
          have hscantrue : native_bitwise_elf_image.loop1 name (sourceInitial m dst text name) 0 fuel =
              some (true, i) := by simpa only [hisource, hbtrue, Bool.true_and] using hscan
          have hp : ¬StartupValid m text := by
            intro hp; exact he ⟨⟨hlen.1,hlen.2,hb⟩,hi.1,hp,hi.2⟩
          have hcheck : startupCheck m text = false := by
            apply Bool.eq_false_iff.mpr
            intro hc; exact hp ((startupCheck_iff m text hi.1).mp hc)
          exact image_refuses_startup m dst text name fuel hlen.1 hlen.2 hi.1 i hscantrue hcheck
        · have hbfalse : name.toList.all (fun b => decide (0 < b ∧ b < 128)) = false := by
            apply Bool.eq_false_iff.mpr
            intro hc
            apply hb
            intro b hbmem
            exact of_decide_eq_true ((List.all_eq_true.mp hc) b hbmem)
          apply image_refuses_scan m dst text name fuel hlen.1 hlen.2 i
          simpa only [hisource, hbfalse, Bool.and_false] using hscan
      · have hisource : sourceInitial m dst text name = false := by rw [hinit]; simp [hi]
        apply image_refuses_scan m dst text name fuel hlen.1 hlen.2 i
        simpa only [hisource, Bool.false_and] using hscan
    · apply image_refuses_outer
      have hnval : name.size.toUInt32.toNat = name.size := by
        rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hn]
      have harch : (archTag m == 1 || archTag m == 2) = true := by cases m <;> rfl
      apply Bool.eq_false_iff.mpr
      intro hg
      apply hlen
      simpa only [harch, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq,
        UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le, hnval,
        UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod] using hg

/-- Universal total-outcome refinement of the actual complete extracted writer.
Every representable input reaches the independently specified success or an
unchanged zero-return refusal with the same uniform sufficient fuel bound. -/
theorem image_total (dst text name : Array UInt8) (arch : UInt32) (fuel : Nat)
    (hd : dst.size < 2^32) (ht : text.size < 2^32) (hn : name.size < 2^32)
    (hf : 4929 ≤ fuel) :
    native_bitwise_elf_image dst text arch name fuel = some (envelopeResult dst text arch name) := by
  by_cases h1 : arch = 1
  · subst arch
    simpa [envelopeResult, archTag] using image_total_machine .arm64 dst text name fuel hd ht hn hf
  · by_cases h2 : arch = 2
    · subst arch
      simpa [envelopeResult, archTag] using image_total_machine .rv64 dst text name fuel hd ht hn hf
    · rw [envelopeResult, if_neg h1, if_neg h2]
      apply image_refuses_outer
      simp [h1,h2]


/-- An independently inadmissible proposal always returns zero and the original
array, including every byte of any nonuniform caller buffer. -/
theorem image_refusal_exact (dst text name : Array UInt8) (arch : UInt32) (fuel : Nat)
    (hd : dst.size < 2^32) (ht : text.size < 2^32) (hn : name.size < 2^32)
    (hf : 4929 ≤ fuel)
    (hbad : ¬∃ m : Machine, arch = archTag m ∧ Eligible m dst text name) :
    native_bitwise_elf_image dst text arch name fuel = some (0, dst) := by
  rw [image_total dst text name arch fuel hd ht hn hf]
  unfold envelopeResult
  split
  · next h1 =>
    have he : ¬Eligible .arm64 dst text name := by
      intro he; exact hbad ⟨.arm64, by simpa [archTag] using h1, he⟩
    rw [if_neg he]
  · split
    · next h2 =>
      have he : ¬Eligible .rv64 dst text name := by
        intro he; exact hbad ⟨.rv64, by simpa [archTag] using h2, he⟩
      rw [if_neg he]
    · rfl

/-- Sufficient uniform fuel excludes partial fuel exhaustion on every input in
    the representable-array domain, including every invalid proposal. -/
theorem image_total_ne_none (dst text name : Array UInt8) (arch : UInt32) (fuel : Nat)
    (hd : dst.size < 2^32) (ht : text.size < 2^32) (hn : name.size < 2^32)
    (hf : 4929 ≤ fuel) : native_bitwise_elf_image dst text arch name fuel ≠ none := by
  rw [image_total dst text name arch fuel hd ht hn hf]
  exact Option.some_ne_none _

end Oak.BitwiseELFProducer
