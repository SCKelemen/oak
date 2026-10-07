import Oak.Stdlib.TimeClockLaws
import Init.Data.Array.Extract
namespace Oak.Stdlib.Time
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- Every valid clock round-trips through any destination with eighteen bytes
    available. The returned prefix is bounded and the rest is preserved. -/
theorem time_codec_roundtrip (t : Time) (dst : Array UInt8) (fuel : Nat)
    (hv : time_valid t fuel = some true) (hd : 18 ≤ dst.size) (hs : dst.size < 4294967296) :
    ∃ n out, format_iso_time dst t (fuel + 40) = some (.Ok n, out) ∧
      8 ≤ n.toNat ∧ n.toNat ≤ 18 ∧ out.size = dst.size ∧
      parse_iso_time (out.extract 0 n.toNat) (fuel + 40) = some (.Ok t) ∧
      ∀ k, n.toNat ≤ k → out[k]? = dst[k]? := by
  obtain ⟨text, hl, hh, hw, hp⟩ := clock_encoding t fuel hv
  have hlen : text.size.toUInt32.toNat = text.size := UInt32.toNat_ofNat_of_lt' (by change text.size < 4294967296; omega)
  obtain ⟨out, hc, ho, he⟩ := copy_time_text_complete dst
    (text ++ Array.replicate (18-text.size) 0) text.size.toUInt32 (fuel + 40)
    (by rw [hlen]; omega) hs (by simp [hlen]) (by rw [hlen]; omega)
  have he' : out.extract 0 text.size.toUInt32.toNat = text := by
    rw [he, hlen]
    simp [Array.extract_append]
  have hf : format_iso_time dst t (fuel + 40) = some (.Ok text.size.toUInt32, out) := by
    unfold format_iso_time
    simp only [bind, pure]
    have hv' : time_valid t (fuel + 40) = some true := hv
    rw [hv', Option.bind_some]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    rw [hw, Option.bind_some, hc]
    rfl
  refine ⟨text.size.toUInt32, out, hf, by simpa [hlen] using hl,
    by simpa [hlen] using hh, ho, ?_, ?_⟩
  · rw [he']
    exact hp
  · exact (format_iso_time_frame dst out t (.Ok text.size.toUInt32) (fuel + 40) hf).2

end Oak.Stdlib.Time
