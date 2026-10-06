import Oak.Stdlib.TimeCalendarExtracted

/-! # Temporal formatter storage contracts
These are kernel-checked control-flow/array arguments over the extraction.
They make no claim about the canonical content of a successful prefix.
-/
namespace Oak.Stdlib.Time
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- Errors preserve every byte. Success preserves allocation size and every
    byte outside the reported prefix. Optional indexing also covers empty arrays. -/
def FormatFrame (dst : Array UInt8) (result : Result_u32_TimeError) (out : Array UInt8) : Prop :=
  match result with
  | .Err _ => out = dst
  | .Ok n => out.size = dst.size ∧ ∀ k, n.toNat ≤ k → out[k]? = dst[k]?

private theorem copy_loop_frame (dst text out : Array UInt8) (size pos finish : UInt32) (fuel : Nat)
    (h : copy_time_text.loop1 dst text size pos fuel = some (out, finish)) :
    out.size = dst.size ∧ ∀ k, size.toNat ≤ k → out[k]? = dst[k]? := by
  induction fuel generalizing dst pos with
  | zero => simp [copy_time_text.loop1] at h
  | succ fuel ih =>
    simp only [copy_time_text.loop1] at h
    split at h
    · rename_i hlt
      have hlt' : pos.toNat < size.toNat := UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true hlt)
      obtain ⟨hs, hk⟩ := ih _ _ h
      refine ⟨by simpa using hs, ?_⟩
      intro k hbound
      rw [hk k hbound, Array.getElem?_setIfInBounds_ne (by omega : pos.toNat ≠ k)]
    · cases h
      exact ⟨rfl, fun _ _ => rfl⟩

/-- The sole write to caller storage satisfies the frame contract. -/
theorem copy_time_text_frame (dst text out : Array UInt8) (size : UInt32)
    (result : Result_u32_TimeError) (fuel : Nat)
    (h : copy_time_text dst text size fuel = some (result, out)) :
    FormatFrame dst result out := by
  unfold copy_time_text at h
  simp only [bind, pure, Option.bind_eq_some_iff, Prod.exists] at h
  obtain ⟨r, a, h, he⟩ := h
  cases he
  split at h
  · cases h
    rfl
  · simp only [Option.bind_eq_some_iff, Prod.exists] at h
    obtain ⟨a, pos, h, he⟩ := h
    cases he
    exact copy_loop_frame _ _ _ _ _ _ _ h


/-- `format_iso_date` preserves the destination on every error and the suffix on success. -/
theorem format_iso_date_frame (dst out : Array UInt8) (d : Date)
    (result : Result_u32_TimeError) (fuel : Nat)
    (h : format_iso_date dst d fuel = some (result, out)) :
    FormatFrame dst result out := by
  unfold format_iso_date at h
  simp only [bind, pure] at h
  grind only [Option.bind_eq_some_iff, copy_time_text_frame, FormatFrame]

/-- `format_iso_time` preserves the destination on every error and the suffix on success. -/
theorem format_iso_time_frame (dst out : Array UInt8) (t : Time)
    (result : Result_u32_TimeError) (fuel : Nat)
    (h : format_iso_time dst t fuel = some (result, out)) :
    FormatFrame dst result out := by
  unfold format_iso_time at h
  simp only [bind, pure] at h
  grind only [Option.bind_eq_some_iff, copy_time_text_frame, FormatFrame]

/-- `format_iso_datetime` preserves the destination on every error and the suffix on success. -/
theorem format_iso_datetime_frame (dst out : Array UInt8) (dt : DateTime)
    (result : Result_u32_TimeError) (fuel : Nat)
    (h : format_iso_datetime dst dt fuel = some (result, out)) :
    FormatFrame dst result out := by
  unfold format_iso_datetime at h
  simp only [bind, pure] at h
  grind only [Option.bind_eq_some_iff, copy_time_text_frame, FormatFrame]

/-- `format_rfc3339_datetime` preserves the destination on every error and the suffix on success. -/
theorem format_rfc3339_datetime_frame (dst out : Array UInt8) (z : OffsetDateTime)
    (result : Result_u32_TimeError) (fuel : Nat)
    (h : format_rfc3339_datetime dst z fuel = some (result, out)) :
    FormatFrame dst result out := by
  unfold format_rfc3339_datetime at h
  simp only [bind, pure] at h
  grind only [Option.bind_eq_some_iff, copy_time_text_frame, FormatFrame]

/-- `format_iso_period` preserves the destination on every error and the suffix on success. -/
theorem format_iso_period_frame (dst out : Array UInt8) (p : Period)
    (result : Result_u32_TimeError) (fuel : Nat)
    (h : format_iso_period dst p fuel = some (result, out)) :
    FormatFrame dst result out := by
  unfold format_iso_period at h
  simp only [bind, pure, Prod.eta, Option.bind_fun_some] at h
  split at h
  · cases h
    rfl
  · simp only [Option.bind_eq_some_iff] at h
    -- Intermediate writes affect temporary buffers; only the final copy touches dst.
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := h
    exact copy_time_text_frame _ _ _ _ _ _ h

/-- `format_iso_duration` preserves the destination on every error and the suffix on success. -/
theorem format_iso_duration_frame (dst out : Array UInt8) (d : Duration)
    (result : Result_u32_TimeError) (fuel : Nat)
    (h : format_iso_duration dst d fuel = some (result, out)) :
    FormatFrame dst result out := by
  unfold format_iso_duration at h
  simp only [bind, pure] at h
  grind only [Option.bind_eq_some_iff, format_iso_period_frame, FormatFrame]

end Oak.Stdlib.Time
