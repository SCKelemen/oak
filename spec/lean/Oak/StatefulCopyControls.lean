import Oak.StatefulCopy

/-! Kernel-checked nonvacuity and negative controls for the representation
adapter. These are model controls, not fresh native/C/Wasm execution fixtures. -/

namespace Oak.StatefulCopy.Controls

open Oak.Stdlib.Bytes Oak.ViewRefinement

def destinationBacking : Array UInt8 := #[201, 8, 9, 10, 202]
def sourceBacking : Array UInt8 := #[203, 0, 255, 204]

def allocations : Allocations := fun owner =>
  if owner = 0 then some ⟨16, 5⟩ else if owner = 1 then some ⟨32, 4⟩ else none

def memory : Memory := fun a =>
  if 16 ≤ a ∧ a < 21 then some (destinationBacking.getD (a - 16) 0)
  else if 32 ≤ a ∧ a < 36 then some (sourceBacking.getD (a - 32) 0)
  else none

def destination (v : View) : ByteView := ⟨0, 16, v⟩
def source (v : View) : ByteView := ⟨1, 32, v⟩

def permissions (dv sv : View) : Permissions :=
  ⟨(source sv).contains, (destination dv).contains⟩

/-- A family of inhabited invocations, not only one assumed safe state. Every
window may vary within live nonempty backing; bytes include zero and high bits. -/
theorem valid_windows (dv sv : View) (hd : dv.start + dv.len ≤ 5)
    (hs : sv.start + sv.len ≤ 4) :
    Invocation allocations 8 (permissions dv sv) memory (destination dv) (source sv)
      destinationBacking sourceBacking := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨rfl, hd, by change dv.len < 256 * 16777216; omega, by change 16 + 5 < 256; decide, ?_⟩
    intro k hk
    change k < 5 at hk
    simp [memory, destination, show 16 ≤ 16 + k ∧ 16 + k < 21 by omega]
  · refine ⟨rfl, hs, by change sv.len < 256 * 16777216; omega, by change 32 + 4 < 256; decide, ?_⟩
    intro k hk
    change k < 4 at hk
    simp [memory, source, show ¬ (16 ≤ 32 + k ∧ 32 + k < 21) by omega,
      show 32 ≤ 32 + k ∧ 32 + k < 36 by omega]
  · intro a ha; exact ha
  · intro a ha; exact ha
  · intro a ha hb
    simp only [ByteView.contains, ByteView.base, destination, source] at ha hb
    omega

def dst : ByteView := destination ⟨1, 3⟩
def src : ByteView := source ⟨1, 2⟩

/-- Nonzero-offset success, copied zero/high byte, untouched suffix, both
canaries, original source, and an unmapped external byte. -/
theorem successful_copy :
    ∃ r after, liftedCopy memory dst src destinationBacking sourceBacking 3 = some (r, after) ∧
      r = .Ok 2 ∧ callerObservation 2 r = true ∧
      after 17 = some 0 ∧ after 18 = some 255 ∧ after 19 = some 10 ∧
      after 16 = some 201 ∧ after 20 = some 202 ∧
      after 33 = some 0 ∧ after 34 = some 255 ∧ after 255 = none := by
  refine ⟨.Ok 2, writeWindow memory dst #[0, 255, 10], ?_, ?_⟩
  · rfl
  · decide

/-- A symbolic theorem application on the concrete inhabited family, including
all source/prefix/suffix/frame conclusions rather than only selected bytes. -/
theorem successful_contract :
    ∃ r after, liftedCopy memory dst src destinationBacking sourceBacking 3 = some (r, after) ∧
      decodeResult (encodeResult r) = some r ∧
      ObservesCopy memory after dst src r (callerObservation 2 r) (fun _ => False) :=
  liftedCopy_total (valid_windows ⟨1, 3⟩ ⟨1, 2⟩ (by decide) (by decide)) 3 (by decide)

/-- Capacity is insufficient but the invocation is valid; no fuel is needed. -/
theorem short_zero_fuel :
    liftedCopy memory (destination ⟨1, 1⟩) src destinationBacking sourceBacking 0 =
      some (.Err .DestinationTooSmall, memory) :=
  liftedCopy_short (valid_windows ⟨1, 1⟩ ⟨1, 2⟩ (by decide) (by decide)) 0 (by decide)

/-- Both pointers are genuine one-past live nonempty allocations. Neither byte
at the pointer is mapped; empty success still leaves the whole memory equal. -/
theorem one_past_empty :
    Invocation allocations 8 (permissions ⟨5, 0⟩ ⟨4, 0⟩) memory
      (destination ⟨5, 0⟩) (source ⟨4, 0⟩) destinationBacking sourceBacking ∧
    memory (destination ⟨5, 0⟩).base = none ∧ memory (source ⟨4, 0⟩).base = none ∧
    liftedCopy memory (destination ⟨5, 0⟩) (source ⟨4, 0⟩)
      destinationBacking sourceBacking 1 = some (.Ok 0, memory) := by
  have h := valid_windows ⟨5, 0⟩ ⟨4, 0⟩ (by decide) (by decide)
  exact ⟨h, by decide, by decide, liftedCopy_empty h 0 rfl⟩

/-- The generic window relation also allows disjoint windows from the *same*
live owner, if the invocation's separate authority premises are supplied. -/
theorem same_owner_disjoint :
    Invocation allocations 8
      ⟨(destination ⟨0, 1⟩).contains, (destination ⟨2, 2⟩).contains⟩
      memory (destination ⟨2, 2⟩) (destination ⟨0, 1⟩)
      destinationBacking destinationBacking := by
  have hd := (valid_windows ⟨2, 2⟩ ⟨0, 0⟩ (by decide) (by decide)).destination
  have hs := (valid_windows ⟨0, 1⟩ ⟨0, 0⟩ (by decide) (by decide)).destination
  refine ⟨hd, hs, fun _ h => h, fun _ h => h, ?_⟩
  intro a ha hb
  simp only [ByteView.contains, ByteView.base, destination] at ha hb
  omega

/-- Separation has real force: even arbitrary grants cannot admit overlap. -/
theorem overlap_refused (p : Permissions) :
    ¬ Invocation allocations 8 p memory dst dst destinationBacking destinationBacking := by
  intro h
  exact h.disjoint 17 (by decide) (by decide)

/-- Zero length does not excuse an unknown/dangling owner. -/
theorem dangling_empty_refused (backing : Array UInt8) :
    ¬ RepresentsWindow allocations 8 memory ⟨2, 42, ⟨0, 0⟩⟩ backing := by
  intro h
  have := h.live
  simp [allocations] at this

/-- Unmapped bytes cannot be reinterpreted as zero-initialized backing. -/
theorem uninitialized_refused :
    ¬ RepresentsWindow allocations 8 (fun _ => none) dst destinationBacking := by
  intro h
  have := h.initialized 0 (by decide)
  contradiction

/-- Endpoints at the address modulus are excluded even for an empty window. -/
theorem wrapping_endpoint_refused (a : Allocations) (m : Memory) :
    ¬ RepresentsWindow a 8 m ⟨7, 255, ⟨1, 0⟩⟩ #[99] := by
  intro h
  have := h.endpoint
  contradiction

theorem malformed_result_refused :
    decodeResult ⟨2, 0⟩ = none ∧ decodeResult ⟨1, 1⟩ = none ∧
    decodeResult ⟨0, 4294967295⟩ = some (.Ok 4294967295) ∧
    decodeResult ⟨1, 0⟩ = some (.Err .DestinationTooSmall) := by decide

/-- Retaining the wrong caller value is observable, so the caller proof cannot
silently discard its length dependency. -/
theorem wrong_live_length : callerObservation 3 (.Ok 2) = false := by decide

/-- Insufficient extracted loop fuel is not success and is not the short error. -/
theorem success_fuel_exhaustion :
    liftedCopy memory dst src destinationBacking sourceBacking 2 = none := by rfl

/-- Independent final-state postconditions reject a corrupted copy byte. -/
theorem corrupt_copy_refused (r : Result_u32_CopyError) (caller : Bool) :
    ¬ ObservesCopy memory memory dst src r caller (fun _ => False) := by
  intro h
  have bad := h.destination 0 (by decide)
  contradiction

/-- An arbitrary observed success word with the wrong count cannot decode to
this return. This checks payload fidelity, not only encode/decode roundtrip. -/
theorem wrong_observed_count {after : Memory} {r : Result_u32_CopyError} {caller : Bool}
    (h : ObservesCopy memory after dst src r caller (fun _ => False)) :
    decodeResult ⟨0, 3⟩ ≠ some r := by
  have hr : r = .Ok 2 := h.result
  rw [hr]
  decide

/-- Scratch contents may change but the exact supplied frame cannot intersect
source/destination, and every non-frame byte still matches the canonical run. -/
def scratchAfter (canonical : Memory) : Memory :=
  fun a => if a = 100 then some 77 else canonical a

theorem scratch_frame_composition {r : Result_u32_CopyError} {canonical : Memory}
    {caller : Bool} (h : ObservesCopy memory canonical dst src r caller (fun _ => False)) :
    ObservesCopy memory (scratchAfter canonical) dst src r caller (inFrames [⟨100, 1⟩]) := by
  apply observes_with_frames h [⟨100, 1⟩]
  · intro a ha hf
    simp only [dst, destination, ByteView.contains, ByteView.base] at ha
    simp [inFrames] at hf
    omega
  · intro a ha hf
    simp only [src, source, ByteView.contains, ByteView.base] at ha
    simp [inFrames] at hf
    omega
  · intro a ha
    have : a ≠ 100 := by intro he; subst a; exact ha (by simp [inFrames])
    simp [scratchAfter, this]

end Oak.StatefulCopy.Controls
