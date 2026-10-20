import Oak.NativeBitwiseEnvelope

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
namespace Oak.BitwiseELFProducer
open Oak.WasmAssembler (writeBytes writeBytes_size writeBytes_suffix)
open Oak.NativeBitwiseEnvelope
open Oak.MinimalELF (Machine)

theorem add32_nat (a b : UInt32) (h : a.toNat+b.toNat < 2^32) :
    (a+b).toNat = a.toNat+b.toNat := by
  rw [UInt32.toNat_add, Nat.mod_eq_of_lt h]

theorem mul32_nat (a b : UInt32) (h : a.toNat*b.toNat < 2^32) :
    (a*b).toNat = a.toNat*b.toNat := by
  rw [UInt32.toNat_mul, Nat.mod_eq_of_lt h]

def sourceSections (m : Machine) (n : UInt32) : UInt32 :=
  (((4096 + (if archTag m == 1 then 32 else 64) + 72 + n + 13 + 48) / 8) * 8)

theorem sourceSections_nat (m : Machine) (name : Array UInt8) (hn : name.size ≤ 256) :
    (sourceSections m name.size.toUInt32).toNat =
      Oak.NativeBitwiseImage.shOffset m (Oak.NativeBitwiseObject.fromUInt8 name.toList) := by
  have hnrep : name.size < 2^32 := by omega
  have hnval : name.size.toUInt32.toNat = name.size := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hnrep]
  cases m <;>
    simp (disch := omega) [sourceSections, archTag, add32_nat, mul32_nat,
      UInt32.toNat_div, hnval, Oak.NativeBitwiseImage.shOffset, Oak.NativeBitwiseObject.align8,
      Oak.NativeBitwiseImage.shstrOffset, Oak.NativeBitwiseImage.strOffset, Oak.NativeBitwiseImage.symOffset,
      Oak.NativeBitwiseImage.textOffset, Oak.NativeBitwiseImage.loadSize] <;> omega

/-- Startup reads are actual in-bounds source bytes, obtained from the supplied
linked-text equation rather than out-of-bounds defaults. -/
theorem startup_reads (m : Machine) (text : Array UInt8) (body : List UInt8) (fuel : Nat)
    (ht : text.toList = Oak.NativeBitwiseObject.toUInt8 (Oak.NativeBitwiseImage.startup m) ++ body) :
    (m = .arm64 →
      native_bitwise_elf_read text 0 fuel = some 0x94000003 ∧
      native_bitwise_elf_read text 4 fuel = some 0x52800ba8 ∧
      native_bitwise_elf_read text 8 fuel = some 0xd4000001) ∧
    (m = .rv64 →
      native_bitwise_elf_read text 0 fuel = some 0x00000097 ∧
      native_bitwise_elf_read text 4 fuel = some 0x010080e7 ∧
      native_bitwise_elf_read text 8 fuel = some 0x05d00893 ∧
      native_bitwise_elf_read text 12 fuel = some 0x00000073) := by
  cases m <;> simp [native_bitwise_elf_read, Array.getD_eq_getD_getElem?,
    ← Array.getElem?_toList, ht, Oak.NativeBitwiseObject.toUInt8, Oak.NativeBitwiseImage.startup] <;> decide +kernel

theorem writer_patches_exact (m : Machine) (dst text name : Array UInt8) (body : List UInt8) (fuel : Nat)
    (hnlo : 0 < name.size) (hnhi : name.size ≤ 256)
    (hnbytes : ∀ b ∈ name.toList, 0 < b ∧ b < 128)
    (hb : body.length = Oak.NativeBitwiseImage.bodySize m)
    (ht : text.toList = Oak.NativeBitwiseObject.toUInt8 (Oak.NativeBitwiseImage.startup m) ++ body)
    (hd : dst.size < 2^32)
    (hcap : Oak.NativeBitwiseImage.shOffset m (Oak.NativeBitwiseObject.fromUInt8 name.toList) + 384 ≤ dst.size)
    (hf : 4929 ≤ fuel) :
    native_bitwise_elf_image dst text (archTag m) name fuel =
      some (UInt32.ofNat (Oak.NativeBitwiseImage.shOffset m (Oak.NativeBitwiseObject.fromUInt8 name.toList) + 384),
        applyPatches (writeBytes dst 0 (List.replicate
          (Oak.NativeBitwiseImage.shOffset m (Oak.NativeBitwiseObject.fromUInt8 name.toList) + 384) 0))
          (nativePatches m name.toList text.toList)) := by
  have hnrep : name.size < 2^32 := by omega
  have hnval : name.size.toUInt32.toNat = name.size := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hnrep]
  have hdval : dst.size.toUInt32.toNat = dst.size := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hd]
  have htlen : text.size = Oak.NativeBitwiseImage.textSize m := by
    have hh := congrArg List.length ht
    simpa [Oak.NativeBitwiseImage.textSize, hb] using hh
  have htrep : text.size < 2^32 := by cases m <;> simp_all [Oak.NativeBitwiseImage.textSize, Oak.NativeBitwiseImage.stubSize, Oak.NativeBitwiseImage.bodySize]
  have htval : text.size.toUInt32.toNat = text.size := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt htrep]
  have hsmall : Oak.NativeBitwiseImage.shOffset m (Oak.NativeBitwiseObject.fromUInt8 name.toList) + 384 ≤ 4928 := by
    simpa only [E_length m name.toList body hb] using E_size_bound m name.toList body (by simpa using hnhi) hb
  have hsections := sourceSections_nat m name hnhi
  have hsize : (sourceSections m name.size.toUInt32 + 384).toNat =
      Oak.NativeBitwiseImage.shOffset m (Oak.NativeBitwiseObject.fromUInt8 name.toList) + 384 := by
    rw [UInt32.toNat_add, hsections]
    change (_ + 384) % 2^32 = _
    exact Nat.mod_eq_of_lt (by omega)
  have hsizeEq : sourceSections m name.size.toUInt32 + 384 = UInt32.ofNat
      (Oak.NativeBitwiseImage.shOffset m (Oak.NativeBitwiseObject.fromUInt8 name.toList) + 384) := by
    rw [← hsize, UInt32.ofNat_toNat]
  have hcapacity : dst.size.toUInt32 ≥ sourceSections m name.size.toUInt32 + 384 := by
    change sourceSections m name.size.toUInt32 + 384 ≤ dst.size.toUInt32
    rw [UInt32.le_iff_toNat_le, hdval, hsize]; exact hcap
  have hnlo32 : (0 : UInt32) < name.size.toUInt32 := by rw [UInt32.lt_iff_toNat_lt, hnval]; exact hnlo
  have hnhi32 : name.size.toUInt32 ≤ (256 : UInt32) := by rw [UInt32.le_iff_toNat_le, hnval]; exact hnhi
  have hscan := name_scan_exact name fuel hnrep hnbytes (by omega)
  have hread := startup_reads m text body fuel ht
  have hsdef : (((4096 + (if archTag m == 1 then 32 else 64) + 72 + name.size.toUInt32 + 13 + 48) / 8) * 8) = sourceSections m name.size.toUInt32 := rfl
  have hlen32 : text.size.toUInt32 = (if archTag m == 1 then 12 else 16) + (if archTag m == 1 then 8 else 36) := by
    cases m <;> simp_all [archTag, Oak.NativeBitwiseImage.textSize, Oak.NativeBitwiseImage.stubSize, Oak.NativeBitwiseImage.bodySize]
  have harch : (archTag m == 1 || archTag m == 2) = true := by cases m <;> rfl
  simp only [native_bitwise_elf_image, hsdef, hlen32, beq_self_eq_true,
    decide_eq_true hcapacity, decide_eq_true hnlo32, decide_eq_true hnhi32,
    harch, Bool.and_self, ↓reduceIte, hscan, Bind.bind, Option.bind]
  have hzero := zero_exact dst (sourceSections m name.size.toUInt32 + 384) fuel
    (by rw [hsize]; exact hcap) (by rw [hsize]; omega)
  rw [hsize] at hzero
  have hmin := (shOffset_bounds m name.toList).1
  cases m with
  | arm64 =>
    rcases hread.1 rfl with ⟨hr0, hr4, hr8⟩
    simp only [Oak.NativeBitwiseImage.textSize, Oak.NativeBitwiseImage.stubSize, Oak.NativeBitwiseImage.bodySize] at htlen
    simp only [Oak.NativeBitwiseImage.shstrOffset, Oak.NativeBitwiseImage.strOffset, Oak.NativeBitwiseImage.symOffset,
      Oak.NativeBitwiseImage.textOffset, Oak.NativeBitwiseImage.loadSize, Oak.NativeBitwiseObject.fromUInt8_length, Array.length_toList] at hmin
    simp [archTag, hr0, hr4, hr8, hzero]
    simp (disch := (first | assumption | (simp [writeBytes_size, hsections, hnval]; omega) | omega)) only [native_word_bytes, text_copy_exact, name_copy_exact, writeBytes_size, Bind.bind, Option.bind, pure]
    simp +arith (disch := omega) [nativePatches, applyPatches, hsizeEq, hsections, hnval,
      Nat.mod_eq_of_lt, Oak.NativeBitwiseImage.stubSize, Oak.NativeBitwiseImage.bodySize,
      Oak.NativeBitwiseImage.loadSize, Oak.NativeBitwiseImage.symOffset, Oak.NativeBitwiseImage.strOffset,
      Oak.NativeBitwiseImage.textOffset, Oak.NativeBitwiseImage.shstrOffset, Oak.NativeBitwiseObject.fromUInt8_length,
      Oak.MinimalELF.Machine.number, Oak.MinimalELF.Machine.abiFlags]
  | rv64 =>
    rcases hread.2 rfl with ⟨hr0, hr4, hr8, hr12⟩
    simp only [Oak.NativeBitwiseImage.textSize, Oak.NativeBitwiseImage.stubSize, Oak.NativeBitwiseImage.bodySize] at htlen
    simp only [Oak.NativeBitwiseImage.shstrOffset, Oak.NativeBitwiseImage.strOffset, Oak.NativeBitwiseImage.symOffset,
      Oak.NativeBitwiseImage.textOffset, Oak.NativeBitwiseImage.loadSize, Oak.NativeBitwiseObject.fromUInt8_length, Array.length_toList] at hmin
    simp [archTag, hr0, hr4, hr8, hr12, hzero]
    simp (disch := (first | assumption | (simp [writeBytes_size, hsections, hnval]; omega) | omega)) only [native_word_bytes, text_copy_exact, name_copy_exact, writeBytes_size, Bind.bind, Option.bind, pure]
    simp +arith (disch := omega) [nativePatches, applyPatches, hsizeEq, hsections, hnval,
      Nat.mod_eq_of_lt, Oak.NativeBitwiseImage.stubSize, Oak.NativeBitwiseImage.bodySize,
      Oak.NativeBitwiseImage.loadSize, Oak.NativeBitwiseImage.symOffset, Oak.NativeBitwiseImage.strOffset,
      Oak.NativeBitwiseImage.textOffset, Oak.NativeBitwiseImage.shstrOffset, Oak.NativeBitwiseObject.fromUInt8_length,
      Oak.MinimalELF.Machine.number, Oak.MinimalELF.Machine.abiFlags]

end Oak.BitwiseELFProducer
