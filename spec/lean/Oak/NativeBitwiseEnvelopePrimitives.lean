import Oak.NativeBitwiseEnvelopeExtracted
import Oak.WasmAssemblerBytes

/-! Source-extracted native envelope primitives. Every successful path below has
explicit representability, complete footprint, and sufficient-fuel premises.
The list writes are specifications, never assumed execution outcomes. -/
set_option autoImplicit false
namespace Oak.BitwiseELFProducer
open Oak.WasmAssembler (writeBytes writeBytes_size writeBytes_get writeBytes_suffix)

/-- The source guard entails a genuine array read and a nonwrapping increment. -/
theorem scan_index (name : Array UInt8) (i : UInt32)
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

private theorem array_head (src : Array UInt8) (pre : List UInt8)
    (b : UInt8) (rest : List UInt8) (he : src.toList = pre ++ b :: rest) :
    src.getD pre.length 0 = b := by
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, he, List.getElem?_append]
  simp

/-- The native scan stops on a bad byte. On the stated all-valid domain it
examines the complete remaining name and returns true and its exact length. -/
theorem name_scan_suffix (name : Array UInt8) (remaining : List UInt8) :
    ∀ (pre : List UInt8) (fuel : Nat), name.size < 2^32 →
      name.toList = pre ++ remaining →
      (∀ b ∈ remaining, 0 < b ∧ b < 128) → remaining.length + 1 ≤ fuel →
      native_bitwise_elf_image.loop1 name true (UInt32.ofNat pre.length) fuel =
        some (true, name.size.toUInt32) := by
  induction remaining with
  | nil =>
    intro pre fuel hn he hv hf
    have hlen : pre.length = name.size := by
      simpa using congrArg List.length he.symm
    cases fuel with
    | zero => omega
    | succ fuel => simp [native_bitwise_elf_image.loop1, hlen]
  | cons b rest ih =>
    intro pre fuel hn he hv hf
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
      rw [hpre]; exact array_head name pre b rest he
    have hindex : UInt32.ofNat pre.length + 1 = UInt32.ofNat (pre ++ [b]).length := by
      apply UInt32.toNat_inj.mp
      rw [hsafe.2.1, hpre, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by simp; omega)]
      simp
    have htail : name.toList = (pre ++ [b]) ++ rest := by
      simpa [List.append_assoc] using he
    have hb := hv b (by simp)
    cases fuel with
    | zero => simp only [List.length_cons] at hf; omega
    | succ fuel =>
      have hr := ih (pre ++ [b]) fuel hn htail (by intro c hc; exact hv c (by simp [hc]))
        (by simp only [List.length_cons] at hf; omega)
      simp only [native_bitwise_elf_image.loop1, decide_eq_true hguard, Bool.and_self,
        ↓reduceIte, hread, decide_eq_true hb.1, decide_eq_true hb.2, Bool.and_self, hindex]
      exact hr

theorem name_scan_exact (name : Array UInt8) (fuel : Nat)
    (hn : name.size < 2^32) (hv : ∀ b ∈ name.toList, 0 < b ∧ b < 128)
    (hf : name.size + 1 ≤ fuel) :
    native_bitwise_elf_image.loop1 name true 0 fuel = some (true, name.size.toUInt32) := by
  simpa using name_scan_suffix name name.toList [] fuel hn (by simp) hv (by simpa using hf)

/-- Each zeroing store is inside the destination and each increment is exact. -/
theorem zero_index (dst : Array UInt8) (size i : UInt32)
    (hf : size.toNat ≤ dst.size) (hi : i < size) :
    i.toNat < dst.size ∧ (i + 1).toNat = i.toNat + 1 := by
  have hlt := UInt32.lt_iff_toNat_lt.mp hi
  have hs := size.toNat_lt
  constructor
  · omega
  · rw [UInt32.toNat_add]
    change (i.toNat + 1) % 2^32 = i.toNat + 1
    exact Nat.mod_eq_of_lt (by omega)

theorem zero_loop_exact (size : UInt32) (fuel : Nat) :
    ∀ (dst : Array UInt8) (i : UInt32), size.toNat ≤ dst.size →
      i.toNat ≤ size.toNat → size.toNat - i.toNat + 1 ≤ fuel →
      native_bitwise_elf_image.loop2 dst size i fuel =
        some (writeBytes dst i.toNat (List.replicate (size.toNat - i.toNat) 0), size) := by
  induction fuel with
  | zero => intro dst i hfit hi hf; omega
  | succ fuel ih =>
    intro dst i hfit hi hf
    by_cases hlt : i < size
    · have hs := zero_index dst size i hfit hlt
      have hlt' := UInt32.lt_iff_toNat_lt.mp hlt
      have hrest : size.toNat - i.toNat = (size.toNat - (i + 1).toNat) + 1 := by omega
      have hr := ih (dst.setIfInBounds i.toNat 0) (i+1)
        (by simpa using hfit) (by omega) (by omega)
      simp only [native_bitwise_elf_image.loop2, decide_eq_true hlt, ↓reduceIte]
      rw [hr, hrest, List.replicate_succ, writeBytes, hs.2]
    · have he : i = size := by
        apply UInt32.toNat_inj.mp
        rw [UInt32.lt_iff_toNat_lt] at hlt
        omega
      subst i
      simp [native_bitwise_elf_image.loop2, writeBytes]

theorem zero_exact (dst : Array UInt8) (size : UInt32) (fuel : Nat)
    (hfit : size.toNat ≤ dst.size) (hf : size.toNat + 1 ≤ fuel) :
    native_bitwise_elf_image.loop2 dst size 0 fuel =
      some (writeBytes dst 0 (List.replicate size.toNat 0), size) := by
  simpa using zero_loop_exact size fuel dst 0 hfit (by simp) (by simpa using hf)

/-- Four exact bytes of a mathematical u32 word, before serialization joins. -/
def wordOctets (value : UInt32) : List UInt8 :=
  [value.toUInt8, (value >>> 8).toUInt8, (value >>> 16).toUInt8, (value >>> 24).toUInt8]

/-- The word helper's full footprint is checked, excluding dropped stores. -/
theorem word_exact (dst : Array UInt8) (offset value : UInt32) (fuel : Nat)
    (hd : dst.size < 2^32) (hfit : offset.toNat + 4 ≤ dst.size) :
    native_bitwise_elf_word dst offset value fuel =
      some ((), writeBytes dst offset.toNat (wordOctets value)) := by
  have h1 : (offset + 1).toNat = offset.toNat + 1 := by
    rw [UInt32.toNat_add]
    change (offset.toNat + 1) % 2^32 = offset.toNat + 1
    exact Nat.mod_eq_of_lt (by omega)
  have h2 : (offset + 2).toNat = offset.toNat + 2 := by
    rw [UInt32.toNat_add]
    change (offset.toNat + 2) % 2^32 = offset.toNat + 2
    exact Nat.mod_eq_of_lt (by omega)
  have h3 : (offset + 3).toNat = offset.toNat + 3 := by
    rw [UInt32.toNat_add]
    change (offset.toNat + 3) % 2^32 = offset.toNat + 3
    exact Nat.mod_eq_of_lt (by omega)
  simp [native_bitwise_elf_word, wordOctets, writeBytes, h1, h2, h3, Nat.add_assoc]

/-- Copy indices prove source access, destination access and both u32 sums. -/
theorem copy_index (dst src : Array UInt8) (pos i : UInt32)
    (hn : src.size < 2^32) (hd : dst.size < 2^32)
    (hfit : pos.toNat + src.size ≤ dst.size) (hi : i < src.size.toUInt32) :
    i.toNat < src.size ∧ (pos + i).toNat = pos.toNat + i.toNat ∧
      (pos + i).toNat < dst.size ∧ (i + 1).toNat = i.toNat + 1 ∧
      (i + 1).toNat ≤ src.size := by
  have hs := scan_index src i hn hi
  have ha : (pos + i).toNat = pos.toNat + i.toNat := by
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
  exact ⟨hs.1, ha, by omega, hs.2.1, hs.2.2⟩

/-- Exact source-extracted text copy from any consumed prefix. -/
theorem text_copy_suffix (src : Array UInt8) (remaining : List UInt8) :
    ∀ (pre : List UInt8) (dst : Array UInt8) (fuel : Nat),
      src.size < 2^32 → dst.size < 2^32 →
      src.toList = pre ++ remaining → 4096 + src.size ≤ dst.size →
      remaining.length + 1 ≤ fuel →
      native_bitwise_elf_image.loop3 dst src (UInt32.ofNat pre.length) fuel =
        some (writeBytes dst (4096 + pre.length) remaining, src.size.toUInt32) := by
  induction remaining with
  | nil =>
    intro pre dst fuel hn hd he hfit hf
    have hlen : pre.length = src.size := by
      simpa using congrArg List.length he.symm
    cases fuel with
    | zero => omega
    | succ fuel => simp [native_bitwise_elf_image.loop3, hlen, writeBytes]
  | cons b rest ih =>
    intro pre dst fuel hn hd he hfit hf
    have hlen : src.size = pre.length + (rest.length + 1) := by
      simpa using congrArg List.length he
    have hpre : (UInt32.ofNat pre.length).toNat = pre.length := by
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    have hsrc : src.size.toUInt32.toNat = src.size := by
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hn]
    have hguard : UInt32.ofNat pre.length < src.size.toUInt32 := by
      rw [UInt32.lt_iff_toNat_lt, hpre, hsrc]; omega

    have hsafe := copy_index dst src 4096 (UInt32.ofNat pre.length)
      hn hd (by simpa using hfit) hguard
    have hread : src.getD (UInt32.ofNat pre.length).toNat 0 = b := by
      rw [hpre]; exact array_head src pre b rest he
    have hindex : UInt32.ofNat pre.length + 1 = UInt32.ofNat (pre ++ [b]).length := by
      apply UInt32.toNat_inj.mp
      rw [hsafe.2.2.2.1, hpre, UInt32.toNat_ofNat',
        Nat.mod_eq_of_lt (by simp; omega)]
      simp
    have htail : src.toList = (pre ++ [b]) ++ rest := by
      simpa [List.append_assoc] using he
    cases fuel with
    | zero => simp only [List.length_cons] at hf; omega
    | succ fuel =>
      have hr := ih (pre ++ [b]) (dst.setIfInBounds (4096 + pre.length) b)
        fuel hn (by simpa using hd) htail (by simpa using hfit)
        (by simp only [List.length_cons] at hf; omega)
      simp only [native_bitwise_elf_image.loop3, decide_eq_true hguard, ↓reduceIte, hread]
      rw [hindex, hsafe.2.1, hpre]
      change native_bitwise_elf_image.loop3 (dst.setIfInBounds (4096 + pre.length) b) src _ fuel = _
      rw [hr]
      simp [writeBytes, Nat.add_assoc]

/-- Exact source-extracted name copy from any consumed prefix. -/
theorem name_copy_suffix (src : Array UInt8) (remaining : List UInt8) :
    ∀ (pre : List UInt8) (dst : Array UInt8) (str : UInt32) (fuel : Nat),
      src.size < 2^32 → dst.size < 2^32 →
      src.toList = pre ++ remaining → str.toNat + 12 + src.size ≤ dst.size →
      remaining.length + 1 ≤ fuel →
      native_bitwise_elf_image.loop4 dst src str (UInt32.ofNat pre.length) fuel =
        some (writeBytes dst (str.toNat + 12 + pre.length) remaining, src.size.toUInt32) := by
  induction remaining with
  | nil =>
    intro pre dst str fuel hn hd he hfit hf
    have hlen : pre.length = src.size := by
      simpa using congrArg List.length he.symm
    cases fuel with
    | zero => omega
    | succ fuel => simp [native_bitwise_elf_image.loop4, hlen, writeBytes]
  | cons b rest ih =>
    intro pre dst str fuel hn hd he hfit hf
    have hlen : src.size = pre.length + (rest.length + 1) := by
      simpa using congrArg List.length he
    have hpre : (UInt32.ofNat pre.length).toNat = pre.length := by
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    have hsrc : src.size.toUInt32.toNat = src.size := by
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hn]
    have hguard : UInt32.ofNat pre.length < src.size.toUInt32 := by
      rw [UInt32.lt_iff_toNat_lt, hpre, hsrc]; omega
    have hpos : (str + 12).toNat = str.toNat + 12 := by
      rw [UInt32.toNat_add]
      change (str.toNat + 12) % 2^32 = str.toNat + 12
      exact Nat.mod_eq_of_lt (by omega)
    have hsafe := copy_index dst src (str + 12) (UInt32.ofNat pre.length)
      hn hd (by rw [hpos]; exact hfit) hguard
    have hread : src.getD (UInt32.ofNat pre.length).toNat 0 = b := by
      rw [hpre]; exact array_head src pre b rest he
    have hindex : UInt32.ofNat pre.length + 1 = UInt32.ofNat (pre ++ [b]).length := by
      apply UInt32.toNat_inj.mp
      rw [hsafe.2.2.2.1, hpre, UInt32.toNat_ofNat',
        Nat.mod_eq_of_lt (by simp; omega)]
      simp
    have htail : src.toList = (pre ++ [b]) ++ rest := by
      simpa [List.append_assoc] using he
    cases fuel with
    | zero => simp only [List.length_cons] at hf; omega
    | succ fuel =>
      have hr := ih (pre ++ [b]) (dst.setIfInBounds (str.toNat + 12 + pre.length) b)
        str fuel hn (by simpa using hd) htail (by simpa using hfit)
        (by simp only [List.length_cons] at hf; omega)
      simp only [native_bitwise_elf_image.loop4, decide_eq_true hguard, ↓reduceIte, hread]
      rw [hindex, hsafe.2.1, hpre, hpos]
      rw [hr]
      simp [writeBytes, Nat.add_assoc]

theorem text_copy_exact (dst text : Array UInt8) (fuel : Nat)
    (ht : text.size < 2^32) (hd : dst.size < 2^32)
    (hfit : 4096 + text.size ≤ dst.size) (hf : text.size + 1 ≤ fuel) :
    native_bitwise_elf_image.loop3 dst text 0 fuel =
      some (writeBytes dst 4096 text.toList, text.size.toUInt32) := by
  simpa using text_copy_suffix text text.toList [] dst fuel ht hd (by simp) hfit (by simpa using hf)

theorem name_copy_exact (dst name : Array UInt8) (str : UInt32) (fuel : Nat)
    (hn : name.size < 2^32) (hd : dst.size < 2^32)
    (hfit : str.toNat + 12 + name.size ≤ dst.size) (hf : name.size + 1 ≤ fuel) :
    native_bitwise_elf_image.loop4 dst name str 0 fuel =
      some (writeBytes dst (str.toNat + 12) name.toList, name.size.toUInt32) := by
  simpa using name_copy_suffix name name.toList [] dst str fuel hn hd (by simp) hfit (by simpa using hf)

end Oak.BitwiseELFProducer
