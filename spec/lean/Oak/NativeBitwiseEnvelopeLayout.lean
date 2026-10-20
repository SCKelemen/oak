import Oak.NativeBitwiseEnvelopePrimitives
import Oak.NativeBitwiseEnvelopeSpec

/-! Array update algebra connecting zero-and-overwrite implementation to a
separately specified field concatenation. Ordered patches are only an
intermediate normal form for the actual stores, not the envelope specification. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Oak.BitwiseELFProducer
open Oak.WasmAssembler (writeBytes writeBytes_size writeBytes_get)
open Oak.NativeBitwiseEnvelope (wordBytes word32Bytes)

theorem wordOctets_eq (v : UInt32) : wordOctets v = word32Bytes v.toNat := by
  have shift (n : UInt32) : (v >>> n).toUInt8 = UInt8.ofNat (v.toNat / 2^(n.toNat % 32)) := by
    apply UInt8.toNat.inj
    simp only [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow, UInt8.toNat_ofNat']
  have h0 : v.toUInt8 = UInt8.ofNat (v.toNat % 256) := by
    apply UInt8.toNat.inj
    simp [UInt32.toNat_toUInt8, UInt8.toNat_ofNat']
  simp only [wordOctets, word32Bytes, wordBytes, h0, shift]
  simp only [show (8 : UInt32).toNat % 32 = 8 by decide,
    show (16 : UInt32).toNat % 32 = 16 by decide,
    show (24 : UInt32).toNat % 32 = 24 by decide]
  have hmod (n : Nat) : UInt8.ofNat (n % 256) = UInt8.ofNat n := by
    apply UInt8.toNat.inj; simp [UInt8.toNat_ofNat']
  simp [Nat.div_div_eq_div_mul, hmod]

theorem native_word_bytes (dst : Array UInt8) (offset value : UInt32) (fuel : Nat)
    (hd : dst.size < 2^32) (hfit : offset.toNat + 4 ≤ dst.size) :
    native_bitwise_elf_word dst offset value fuel =
      some ((), writeBytes dst offset.toNat (word32Bytes value.toNat)) := by
  rw [word_exact dst offset value fuel hd hfit, wordOctets_eq]

theorem bytes_append (dst : Array UInt8) (offset : Nat) (a b : List UInt8) :
    writeBytes dst offset (a ++ b) =
      writeBytes (writeBytes dst offset a) (offset + a.length) b := by
  induction a generalizing dst offset with
  | nil => simp [writeBytes]
  | cons v a ih =>
    simpa [writeBytes, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (ih (dst.setIfInBounds offset v) (offset + 1))

/-- Replace an in-bounds subrange of one complete mathematical write. -/
theorem bytes_overlay (dst : Array UInt8) (offset : Nat) (pre old new post : List UInt8)
    (hlen : new.length = old.length)
    (hfit : offset + (pre ++ old ++ post).length ≤ dst.size) :
    writeBytes (writeBytes dst offset (pre ++ old ++ post)) (offset + pre.length) new =
      writeBytes dst offset (pre ++ new ++ post) := by
  apply Array.ext_getElem?
  intro j
  have hfit2 : offset + (pre ++ new ++ post).length ≤ dst.size := by simpa [hlen] using hfit
  have hfnew : offset + pre.length + new.length ≤ (writeBytes dst offset (pre ++ old ++ post)).size := by
    simp only [writeBytes_size, List.length_append] at *; omega
  rw [writeBytes_get _ _ _ hfnew, writeBytes_get _ _ _ hfit2]
  by_cases hp : j < offset
  · rw [if_neg (by omega), if_neg (by omega), writeBytes_get _ _ _ hfit, if_neg (by omega)]
  · by_cases hpre : j < offset + pre.length
    · rw [if_neg (by omega), if_pos (by simp only [List.length_append]; omega),
        writeBytes_get _ _ _ hfit, if_pos (by simp only [List.length_append]; omega)]
      simp [List.getElem?_append, show j-offset < pre.length by omega, show j-offset < pre.length+old.length by omega,
        show j-offset < pre.length+new.length by omega]
    · by_cases hn : j < offset + pre.length + new.length
      · rw [if_pos (by omega), if_pos (by simp only [List.length_append]; omega)]
        simp [List.getElem?_append, show ¬j-offset < pre.length by omega,
          show j-(offset+pre.length) < new.length by omega, show j-offset-pre.length = j-(offset+pre.length) by omega]
      · rw [if_neg (by omega), writeBytes_get _ _ _ hfit]
        by_cases hpost : j < offset + (pre ++ old ++ post).length
        · rw [if_pos (by omega), if_pos (by simpa [hlen] using And.intro (Nat.le_of_not_lt hp) hpost)]
          simp [List.getElem?_append, show ¬j-offset < pre.length by omega,
            show ¬j-offset-pre.length < old.length by omega, hlen]
        · rw [if_neg (by omega), if_neg (by simpa [hlen] using (show ¬(offset ≤ j ∧ j < offset+(pre++old++post).length) by omega))]

abbrev Patch := Nat × List UInt8

def applyPatches (dst : Array UInt8) : List Patch → Array UInt8
  | [] => dst
  | (pos, bs) :: rest => applyPatches (writeBytes dst pos bs) rest

def patchBytes (cursor total : Nat) : List Patch → List UInt8
  | [] => List.replicate (total-cursor) 0
  | (pos, bs) :: rest => List.replicate (pos-cursor) 0 ++ bs ++ patchBytes (pos+bs.length) total rest

def OrderedPatches (cursor total : Nat) : List Patch → Prop
  | [] => cursor ≤ total
  | (pos, bs) :: rest => cursor ≤ pos ∧ pos + bs.length ≤ total ∧ OrderedPatches (pos+bs.length) total rest

theorem patchBytes_length (cursor total : Nat) (patches : List Patch)
    (h : OrderedPatches cursor total patches) :
    (patchBytes cursor total patches).length = total-cursor := by
  induction patches generalizing cursor with
  | nil => simp [patchBytes]
  | cons p rest ih =>
    rcases p with ⟨pos, bs⟩
    rcases h with ⟨hc, hp, hr⟩
    simp only [patchBytes, List.length_append, List.length_replicate, ih _ hr]
    omega

/-- Complete fitting sorted patches applied to a zeroed interval are exactly
its independent concatenated gaps and payloads. -/
theorem zero_patches (cursor total : Nat) (patches : List Patch) :
    ∀ dst : Array UInt8, OrderedPatches cursor total patches → total ≤ dst.size →
      applyPatches (writeBytes dst cursor (List.replicate (total-cursor) 0)) patches =
        writeBytes dst cursor (patchBytes cursor total patches) := by
  induction patches generalizing cursor with
  | nil => intros; rfl
  | cons p rest ih =>
    intro dst horder hfit
    rcases p with ⟨pos, bs⟩
    rcases horder with ⟨hc, hp, hr⟩
    have splitZero : List.replicate (total-cursor) (0 : UInt8) =
        List.replicate (pos-cursor) 0 ++ List.replicate bs.length 0 ++ List.replicate (total-(pos+bs.length)) 0 := by
      rw [List.replicate_append_replicate, List.replicate_append_replicate]
      congr 1; omega
    have hf : cursor + (List.replicate (pos-cursor) (0 : UInt8) ++ List.replicate bs.length 0 ++
        List.replicate (total-(pos+bs.length)) 0).length ≤ dst.size := by simp; omega
    simp only [applyPatches]
    have hover := bytes_overlay dst cursor (List.replicate (pos-cursor) 0)
      (List.replicate bs.length 0) bs (List.replicate (total-(pos+bs.length)) 0) (by simp) hf
    have hpos : cursor + (List.replicate (pos-cursor) (0 : UInt8)).length = pos := by simp; omega
    rw [hpos] at hover
    rw [splitZero, hover]
    rw [bytes_append dst cursor (List.replicate (pos-cursor) 0 ++ bs),
      show cursor+(List.replicate (pos-cursor) (0 : UInt8) ++ bs).length = pos+bs.length by simp; omega]
    rw [ih (pos+bs.length) _ hr (by simpa using hfit)]
    rw [patchBytes, bytes_append dst cursor (List.replicate (pos-cursor) 0 ++ bs)]
    congr 1
    simp only [List.length_append, List.length_replicate]
    omega

end Oak.BitwiseELFProducer
