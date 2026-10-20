import Oak.NativeBitwiseEnvelopeSuccess
import Oak.NativeBitwiseEnvelopeProfile

/-!
# Source-extracted strict native envelope success

For arbitrary initially populated destination arrays and arbitrary fixed-extent
body proposals, the actual extracted source writer terminates with exactly the
independent ELF field serialization. There is no successful-run assumption.
Only the reported prefix is an artifact: the original destination suffix is
preserved and is not admitted as trailing ELF bytes. Name and body proposals
remain subject to the unchanged source/image checker. No source compiler, ISA,
Linux execution, generic linker, or extractor correctness theorem is claimed.
-/
set_option autoImplicit false
namespace Oak.BitwiseELFProducer
open Oak.WasmAssembler (writeBytes writeBytes_size writeBytes_suffix)
open Oak.NativeBitwiseEnvelope
open Oak.MinimalELF (Machine)

/-- Universal exact successful execution of the actual extracted native writer.
The name/text representation bounds follow from their explicit bounded lengths;
only destination representation remains an independent premise. Both input
arrays represent disjoint Oak read-only borrows from the destination. -/
theorem image_exact (m : Machine) (dst text name : Array UInt8) (body : List UInt8) (fuel : Nat)
    (hnlo : 0 < name.size) (hnhi : name.size ≤ 256)
    (hnbytes : ∀ b ∈ name.toList, 0 < b ∧ b < 128)
    (hb : body.length = Oak.NativeBitwiseImage.bodySize m)
    (ht : text.toList = Oak.NativeBitwiseObject.toUInt8 (Oak.NativeBitwiseImage.startup m) ++ body)
    (hd : dst.size < 2^32) (hcap : (E m name.toList body).length ≤ dst.size)
    (hf : 4929 ≤ fuel) :
    native_bitwise_elf_image dst text (archTag m) name fuel =
      some (UInt32.ofNat (E m name.toList body).length, writeBytes dst 0 (E m name.toList body)) := by
  have hc : Oak.NativeBitwiseImage.shOffset m (Oak.NativeBitwiseObject.fromUInt8 name.toList) + 384 ≤ dst.size := by
    simpa only [E_length m name.toList body hb] using hcap
  have htlen : text.toList.length = Oak.NativeBitwiseImage.textSize m := by
    simp [ht, Oak.NativeBitwiseImage.textSize, hb]
  rw [writer_patches_exact m dst text name body fuel hnlo hnhi hnbytes hb ht hd hc hf]
  have hp := zero_patches 0 _ _ dst (nativePatches_ordered m name.toList text.toList htlen) hc
  simp only [Nat.sub_zero] at hp
  rw [hp]
  simp only [ht, nativePatches_bytes m name.toList body hb, E_length m name.toList body hb]

/-- Exact successful return, unchanged storage size, and every byte including
an arbitrary nonuniform suffix. The result is not conditional on having run. -/
theorem image_frame (m : Machine) (dst text name : Array UInt8) (body : List UInt8) (fuel : Nat)
    (hnlo : 0 < name.size) (hnhi : name.size ≤ 256)
    (hnbytes : ∀ b ∈ name.toList, 0 < b ∧ b < 128)
    (hb : body.length = Oak.NativeBitwiseImage.bodySize m)
    (ht : text.toList = Oak.NativeBitwiseObject.toUInt8 (Oak.NativeBitwiseImage.startup m) ++ body)
    (hd : dst.size < 2^32) (hcap : (E m name.toList body).length ≤ dst.size)
    (hf : 4929 ≤ fuel) :
    ∃ out, native_bitwise_elf_image dst text (archTag m) name fuel =
        some (UInt32.ofNat (E m name.toList body).length, out) ∧
      out.size = dst.size ∧ out.toList = E m name.toList body ++ dst.toList.drop (E m name.toList body).length := by
  refine ⟨writeBytes dst 0 (E m name.toList body),
    image_exact m dst text name body fuel hnlo hnhi hnbytes hb ht hd hcap hf,
    writeBytes_size _ _ _, ?_⟩
  simpa using writeBytes_suffix dst 0 (E m name.toList body) (by simpa using hcap)

/-- The actual successful writer output has a strict admitted reported prefix
and preserves the original suffix. Its returned u32 length is exact. Body bytes
remain arbitrary proposals: this theorem establishes envelope admission only. -/
theorem image_output_admitted (m : Machine) (dst text name : Array UInt8) (body : List UInt8) (fuel : Nat)
    (hnlo : 0 < name.size) (hnhi : name.size ≤ 256)
    (hnbytes : ∀ b ∈ name.toList, 0 < b ∧ b < 128)
    (hb : body.length = Oak.NativeBitwiseImage.bodySize m)
    (ht : text.toList = Oak.NativeBitwiseObject.toUInt8 (Oak.NativeBitwiseImage.startup m) ++ body)
    (hd : dst.size < 2^32) (hcap : (E m name.toList body).length ≤ dst.size)
    (hf : 4929 ≤ fuel) :
    ∃ (written : UInt32) (out : Array UInt8),
      native_bitwise_elf_image dst text (archTag m) name fuel = some (written, out) ∧
      written.toNat = (E m name.toList body).length ∧ out.size = dst.size ∧
      out.toList.take written.toNat = E m name.toList body ∧
      out.toList.drop written.toNat = dst.toList.drop written.toNat ∧
      Oak.NativeBitwiseImage.StrictProfile m (Oak.NativeBitwiseObject.fromUInt8 name.toList)
        (Oak.NativeBitwiseObject.fromUInt8 (out.toList.take written.toNat)) ∧
      Oak.NativeBitwiseImage.accepts m (Oak.NativeBitwiseObject.fromUInt8 name.toList)
        (Oak.NativeBitwiseObject.fromUInt8 (out.toList.take written.toNat))
        (Oak.NativeBitwiseObject.fromUInt8 body) = true := by
  obtain ⟨out, hrun, hsize, hbytes⟩ := image_frame m dst text name body fuel hnlo hnhi hnbytes hb ht hd hcap hf
  have hbound := E_size_bound m name.toList body (by simpa using hnhi) hb
  have hlen : (UInt32.ofNat (E m name.toList body).length).toNat = (E m name.toList body).length := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have hprefix : out.toList.take (E m name.toList body).length = E m name.toList body := by
    rw [hbytes]; simp
  have hsuffix : out.toList.drop (E m name.toList body).length = dst.toList.drop (E m name.toList body).length := by
    rw [hbytes]; simp
  refine ⟨_, out, hrun, hlen, hsize, ?_, ?_, ?_, ?_⟩
  · simpa only [hlen] using hprefix
  · simpa only [hlen] using hsuffix
  · rw [hlen, hprefix]
    exact E_strictProfile m name.toList body (by simpa using hnlo) (by simpa using hnhi) hb
      (valid_name_bridge name.toList hnbytes)
  · rw [hlen, hprefix]
    exact E_accepts m name.toList body (by simpa using hnlo) (by simpa using hnhi) hb
      (valid_name_bridge name.toList hnbytes)

end Oak.BitwiseELFProducer
