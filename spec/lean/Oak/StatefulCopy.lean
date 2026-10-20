import Oak.Stdlib.BytesLaws
import Oak.ViewRefinement

/-!
# Stateful byte-copy representation adapter

This module lifts the *existing* extracted `bytes.copy_into` into partial byte
memory. `writeWindow` is generic representation writeback, not another copy loop.
The result/contents contract is independent of that lifted execution. Its proof
uses `copy_into_spec` and `copy_short_atomic`, with symbolic lengths and bytes.

`NativeResultWords` uses the concrete layout observed by
`TestStatefulCopyConcreteLayoutAndNativeCall`: Result tag at byte 0, payload at
byte 4; Ok = 0, Err = 1, DestinationTooSmall = 0. These tests bind the production
specialization/layout, not a Lean compiler-correctness theorem. This module
proves exact word-level encode/decode, not register or endian-byte transport.
`callerObservation` transliterates the frozen caller's match and retained length;
its source/extractor correspondence is still a separate obligation.

Allocation and permission maps describe invocation premises, not a production
borrow checker. A target must separately prove its execution realizes this
writeback and the supplied *exact* scratch frames. No instruction trace,
non-inlining, target fuel, machine/OS, frontend or external ISA/Core theorem is
introduced here. Empty windows have live owner-derived one-past pointers; they
do not require a byte mapped at that pointer.
-/

namespace Oak.StatefulCopy

open Oak.Stdlib.Bytes
open Oak.ViewRefinement

abbrev Memory := Nat → Option UInt8

structure Allocation where
  base : Nat
  size : Nat
  deriving DecidableEq, Repr

abbrev Allocations := Nat → Option Allocation

structure ByteView where
  owner : Nat
  ownerBase : Nat
  window : View
  deriving DecidableEq, Repr

def ByteView.base (v : ByteView) : Nat := v.ownerBase + v.window.start

def ByteView.contains (v : ByteView) (a : Nat) : Prop :=
  v.base ≤ a ∧ a < v.base + v.window.len

instance (v : ByteView) (a : Nat) : Decidable (v.contains a) :=
  inferInstanceAs (Decidable (_ ∧ _))

def logical (backing : Array UInt8) (v : ByteView) : Array UInt8 :=
  backing.extract v.window.start (v.window.start + v.window.len)

/-- The allocation map is live metadata. Every backing byte is initialized;
`none` is not read as zero. The conservative endpoint policy excludes wrap. -/
structure RepresentsWindow (allocs : Allocations) (bits : Nat) (mem : Memory)
    (v : ByteView) (backing : Array UInt8) : Prop where
  live : allocs v.owner = some ⟨v.ownerBase, backing.size⟩
  bounds : WellFormed v.window backing.size
  length : v.window.len < 2 ^ 32
  endpoint : v.ownerBase + backing.size < 2 ^ bits
  initialized : ∀ k, k < backing.size →
    mem (v.ownerBase + k) = some (backing.getD k 0)

/-- Permissions are external invocation metadata. Physical separation below is
independent of these grants; assigning a grant does not prove frontend ownership. -/
structure Permissions where
  readable : Nat → Prop
  exclusiveWrite : Nat → Prop

structure Invocation (allocs : Allocations) (bits : Nat) (permissions : Permissions)
    (mem : Memory) (dst src : ByteView) (db sb : Array UInt8) : Prop where
  destination : RepresentsWindow allocs bits mem dst db
  source : RepresentsWindow allocs bits mem src sb
  read : ∀ a, src.contains a → permissions.readable a
  write : ∀ a, dst.contains a → permissions.exclusiveWrite a
  disjoint : ∀ a, dst.contains a → ¬ src.contains a

@[simp] theorem logical_size (v : ByteView) (backing : Array UInt8)
    (h : WellFormed v.window backing.size) :
    (logical backing v).size = v.window.len := by
  unfold logical
  rw [Array.size_extract_of_le h]
  omega

theorem logical_get (v : ByteView) (backing : Array UInt8)
    (hw : WellFormed v.window backing.size) (k : Nat) (hk : k < v.window.len) :
    (logical backing v).getD k 0 = backing.getD (indexAt v.window k) 0 := by
  have hl : k < (logical backing v).size := by rw [logical_size _ _ hw]; exact hk
  rw [← Array.getElem_eq_getD (h := hl)]
  simp only [logical, Array.getElem_extract]
  exact (index_read_agrees backing v.window k 0 hw hk).symm

theorem represented_read {allocs : Allocations} {bits : Nat} {mem : Memory}
    {v : ByteView} {backing : Array UInt8}
    (h : RepresentsWindow allocs bits mem v backing) (k : Nat) (hk : k < v.window.len) :
    mem (v.base + k) = some ((logical backing v).getD k 0) := by
  rw [logical_get _ _ h.bounds k hk]
  simpa [ByteView.base, indexAt, Nat.add_assoc] using
    h.initialized (indexAt v.window k) (index_in_backing _ _ _ h.bounds hk)

/-- Both valid accesses and the derived one-past endpoint are representable. -/
theorem represented_address {allocs : Allocations} {bits : Nat} {mem : Memory}
    {v : ByteView} {backing : Array UInt8}
    (h : RepresentsWindow allocs bits mem v backing) (k : Nat) (hk : k ≤ v.window.len) :
    v.base + k < 2 ^ bits := by
  have hb := h.bounds
  have he := h.endpoint
  unfold WellFormed at hb
  unfold ByteView.base
  omega

/-- Exact in-backing stores use the existing ViewRefinement law; defaulting
array update cannot drop an accepted byte store. -/
theorem represented_store {allocs : Allocations} {bits : Nat} {mem : Memory}
    {v : ByteView} {backing : Array UInt8}
    (h : RepresentsWindow allocs bits mem v backing) (k : Nat) (hk : k < v.window.len)
    (byte : UInt8) :
    (backing.setIfInBounds (indexAt v.window k) byte).size = backing.size ∧
    (backing.setIfInBounds (indexAt v.window k) byte)[indexAt v.window k]'(by
      rw [Array.size_setIfInBounds]; exact index_in_backing _ _ _ h.bounds hk) = byte :=
  store_agrees backing v.window k byte h.bounds hk

structure NativeResultWords where
  tag : UInt32
  payload : UInt32
  deriving DecidableEq, Repr

def encodeResult : Result_u32_CopyError → NativeResultWords
  | .Ok n => ⟨0, n⟩
  | .Err .DestinationTooSmall => ⟨1, 0⟩

def decodeResult (words : NativeResultWords) : Option Result_u32_CopyError :=
  if words.tag = 0 then some (.Ok words.payload)
  else if words.tag = 1 ∧ words.payload = 0 then some (.Err .DestinationTooSmall)
  else none

@[simp] theorem decode_encode (r : Result_u32_CopyError) :
    decodeResult (encodeResult r) = some r := by
  cases r with
  | Ok n => simp [encodeResult, decodeResult]
  | Err e => cases e; decide

/-- Invalid outer tags and invalid nested error tags are not accepted as a Result. -/
theorem decode_exact (words : NativeResultWords) (r : Result_u32_CopyError) :
    decodeResult words = some r ↔ words = encodeResult r := by
  rcases words with ⟨tag, payload⟩
  cases r with
  | Ok n =>
    simp [decodeResult, encodeResult]
    split <;> simp_all
  | Err e =>
    cases e
    simp [decodeResult, encodeResult]
    split <;> simp_all

def callerObservation (savedLength : UInt32) : Result_u32_CopyError → Bool
  | .Ok count => decide (count = savedLength)
  | .Err _ => false

def expectedResult (dstLen srcLen : Nat) : Result_u32_CopyError :=
  if srcLen ≤ dstLen then .Ok srcLen.toUInt32 else .Err .DestinationTooSmall

def copiedLength (dstLen srcLen : Nat) : Nat :=
  if srcLen ≤ dstLen then srcLen else 0

/-- A shape independent of extracted execution: exact Result, size, prefix,
and suffix. Even out-of-range defaulting reads are characterized here. -/
def ArrayPost (dst src out : Array UInt8) (r : Result_u32_CopyError) : Prop :=
  r = expectedResult dst.size src.size ∧ out.size = dst.size ∧
  ∀ k, out.getD k 0 =
    if k < copiedLength dst.size src.size then src.getD k 0 else dst.getD k 0

private theorem toUInt32_toNat (n : Nat) (h : n < 2 ^ 32) :
    n.toUInt32.toNat = n := by
  rw [UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

/-- Termination and the independent array contract are derived from the actual
extracted copy, not assumed. Short destinations require no loop fuel. -/
theorem extracted_total (dst src : Array UInt8) (fuel : Nat)
    (hd : dst.size < 2 ^ 32) (hs : src.size < 2 ^ 32)
    (hf : src.size ≤ dst.size → src.size < fuel) :
    ∃ r out, copy_into dst src fuel = some (r, out) ∧ ArrayPost dst src out r := by
  by_cases hfit : src.size ≤ dst.size
  · obtain ⟨out, he, hsize, hget⟩ := copy_into_spec dst src fuel hd hfit (hf hfit)
    exact ⟨.Ok src.size.toUInt32, out, he,
      by simpa [ArrayPost, expectedResult, copiedLength, hfit] using And.intro hsize hget⟩
  · have hshort : dst.size.toUInt32 < src.size.toUInt32 := by
      rw [UInt32.lt_iff_toNat_lt, toUInt32_toNat _ hd, toUInt32_toNat _ hs]
      omega
    exact ⟨.Err .DestinationTooSmall, dst, copy_short_atomic dst src fuel hshort,
      by simp [ArrayPost, expectedResult, copiedLength, hfit]⟩

/-- Generic array-to-memory writeback. It does not choose copied bytes, run a
copy loop, or update allocation/permission metadata. -/
def writeWindow (mem : Memory) (dst : ByteView) (out : Array UInt8) : Memory :=
  fun a => if dst.contains a then some (out.getD (a - dst.base) 0) else mem a

@[simp] theorem writeWindow_inside (mem : Memory) (dst : ByteView) (out : Array UInt8)
    (k : Nat) (hk : k < dst.window.len) :
    writeWindow mem dst out (dst.base + k) = some (out.getD k 0) := by
  simp [writeWindow, ByteView.contains, hk]

theorem writeWindow_outside (mem : Memory) (dst : ByteView) (out : Array UInt8)
    (a : Nat) (h : ¬ dst.contains a) : writeWindow mem dst out a = mem a := by
  simp [writeWindow, h]

/-- Reinstalling the represented original array is extensionally the identity,
including outside the window and for zero-length windows. -/
theorem writeWindow_original {allocs : Allocations} {bits : Nat} {mem : Memory}
    {dst : ByteView} {backing : Array UInt8}
    (h : RepresentsWindow allocs bits mem dst backing) :
    writeWindow mem dst (logical backing dst) = mem := by
  funext a
  by_cases ha : dst.contains a
  · have hk : a - dst.base < dst.window.len := by
      unfold ByteView.contains at ha; omega
    have he : dst.base + (a - dst.base) = a := by
      unfold ByteView.contains at ha; omega
    rw [← he, writeWindow_inside _ _ _ _ hk, represented_read h _ hk]
  · exact writeWindow_outside _ _ _ _ ha

/-- Only this bridge runs the existing function. It is value-level extraction
plus generic writeback, not a new source/IR/machine evaluator. -/
def liftedCopy (mem : Memory) (dst src : ByteView) (db sb : Array UInt8) (fuel : Nat) :
    Option (Result_u32_CopyError × Memory) := do
  let (r, out) ← copy_into (logical db dst) (logical sb src) fuel
  pure (r, writeWindow mem dst out)

/-- The copied footprint is smaller than the admitted destination, including
zero bytes for the ordinary short-capacity error. -/
def inCopiedPrefix (dst src : ByteView) (a : Nat) : Prop :=
  dst.base ≤ a ∧ a < dst.base + copiedLength dst.window.len src.window.len

/-- Independent physical/caller observations; not defined as equality to a run. -/
structure ObservesCopy (before after : Memory) (dst src : ByteView)
    (r : Result_u32_CopyError) (caller : Bool) (scratch : Nat → Prop) : Prop where
  result : r = expectedResult dst.window.len src.window.len
  callerResult : caller = decide (src.window.len ≤ dst.window.len)
  destination : ∀ k, k < dst.window.len →
    after (dst.base + k) =
      if k < copiedLength dst.window.len src.window.len
      then before (src.base + k) else before (dst.base + k)
  source : ∀ k, k < src.window.len → after (src.base + k) = before (src.base + k)
  frame : ∀ a, ¬ inCopiedPrefix dst src a → ¬ scratch a → after a = before a

/-- For *arbitrary observed words*, successful decoding to the returned model
Result fixes both the outer tag and the complete payload, and determines the
caller's observation. A target still owes the `decoded` premise from its actual
register/memory transport; this is not that missing simulation theorem. -/
theorem observed_words_exact {before after : Memory} {dst src : ByteView}
    {r : Result_u32_CopyError} {caller : Bool} {scratch : Nat → Prop}
    (h : ObservesCopy before after dst src r caller scratch) (words : NativeResultWords)
    (decoded : decodeResult words = some r) :
    words = (if src.window.len ≤ dst.window.len
      then ⟨0, src.window.len.toUInt32⟩ else ⟨1, 0⟩) ∧
    (decodeResult words).map (callerObservation src.window.len.toUInt32) = some caller := by
  have hw := (decode_exact words r).mp decoded
  constructor
  · rw [hw, h.result]
    unfold expectedResult
    split <;> rfl
  · rw [decoded, Option.map_some, h.result, h.callerResult]
    unfold expectedResult
    split <;> simp [callerObservation, *]

private theorem copiedLength_le (d s : Nat) : copiedLength d s ≤ s := by
  unfold copiedLength; split <;> omega

/-- Window representation + the extracted array postcondition imply physical
source preservation, exact prefix/suffix, caller observation and external frame. -/
theorem writeback_observes {allocs : Allocations} {bits : Nat} {permissions : Permissions}
    {mem : Memory} {dst src : ByteView} {db sb : Array UInt8}
    (h : Invocation allocs bits permissions mem dst src db sb)
    (out : Array UInt8) (r : Result_u32_CopyError)
    (hp : ArrayPost (logical db dst) (logical sb src) out r) :
    ObservesCopy mem (writeWindow mem dst out) dst src r
      (callerObservation src.window.len.toUInt32 r) (fun _ => False) := by
  have hd := logical_size dst db h.destination.bounds
  have hs := logical_size src sb h.source.bounds
  rcases hp with ⟨hr, _, hg⟩
  rw [hd, hs] at hr
  simp only [hd, hs] at hg
  refine ⟨hr, ?_, ?_, ?_, ?_⟩
  · rw [hr]; unfold expectedResult; split <;> simp [callerObservation, *]
  · intro k hk
    rw [writeWindow_inside _ _ _ k hk, hg k]
    by_cases hc : k < copiedLength dst.window.len src.window.len
    · rw [if_pos hc, if_pos hc, represented_read h.source k
        (Nat.lt_of_lt_of_le hc (copiedLength_le _ _))]
    · rw [if_neg hc, if_neg hc, represented_read h.destination k hk]
  · intro k hk
    apply writeWindow_outside
    intro hc
    exact h.disjoint (src.base + k) hc ⟨by omega, by omega⟩
  · intro a ha _
    by_cases hac : dst.contains a
    · have hk : a - dst.base < dst.window.len := by
        unfold ByteView.contains at hac; omega
      have he : dst.base + (a - dst.base) = a := by
        unfold ByteView.contains at hac; omega
      have hn : ¬ a - dst.base < copiedLength dst.window.len src.window.len := by
        unfold inCopiedPrefix at ha
        unfold ByteView.contains at hac
        omega
      rw [← he, writeWindow_inside _ _ _ _ hk, hg _, if_neg hn,
        represented_read h.destination _ hk]
    · exact writeWindow_outside _ _ _ _ hac

/-- The main symbolic theorem. No returned execution is a premise. Success needs
`src.len + 1` extracted loop steps; short errors also work at fuel zero. -/
theorem liftedCopy_total {allocs : Allocations} {bits : Nat} {permissions : Permissions}
    {mem : Memory} {dst src : ByteView} {db sb : Array UInt8}
    (h : Invocation allocs bits permissions mem dst src db sb) (fuel : Nat)
    (hf : src.window.len ≤ dst.window.len → src.window.len < fuel) :
    ∃ r after, liftedCopy mem dst src db sb fuel = some (r, after) ∧
      decodeResult (encodeResult r) = some r ∧
      ObservesCopy mem after dst src r (callerObservation src.window.len.toUInt32 r)
        (fun _ => False) := by
  have hd := logical_size dst db h.destination.bounds
  have hs := logical_size src sb h.source.bounds
  obtain ⟨r, out, he, hp⟩ := extracted_total (logical db dst) (logical sb src) fuel
    (by rw [hd]; exact h.destination.length) (by rw [hs]; exact h.source.length)
    (by simpa only [hd, hs] using hf)
  exact ⟨r, writeWindow mem dst out, by simp [liftedCopy, he], decode_encode r,
    writeback_observes h out r hp⟩

/-- Valid short destinations return the real error and exactly unchanged data
memory even with zero fuel. This is not an admission refusal. -/
theorem liftedCopy_short {allocs : Allocations} {bits : Nat} {permissions : Permissions}
    {mem : Memory} {dst src : ByteView} {db sb : Array UInt8}
    (h : Invocation allocs bits permissions mem dst src db sb) (fuel : Nat)
    (hshort : dst.window.len < src.window.len) :
    liftedCopy mem dst src db sb fuel = some (.Err .DestinationTooSmall, mem) := by
  have hd := logical_size dst db h.destination.bounds
  have hs := logical_size src sb h.source.bounds
  have hc : (logical db dst).size.toUInt32 < (logical sb src).size.toUInt32 := by
    rw [UInt32.lt_iff_toNat_lt, hd, hs, toUInt32_toNat _ h.destination.length,
      toUInt32_toNat _ h.source.length]
    exact hshort
  simp [liftedCopy, copy_short_atomic _ _ fuel hc, writeWindow_original h.destination]

/-- Zero-length source has no data-memory change. Owner metadata, backing
bounds, and representable one-past pointer policy still apply through h. -/
theorem liftedCopy_empty {allocs : Allocations} {bits : Nat} {permissions : Permissions}
    {mem : Memory} {dst src : ByteView} {db sb : Array UInt8}
    (h : Invocation allocs bits permissions mem dst src db sb) (fuel : Nat)
    (hempty : src.window.len = 0) :
    liftedCopy mem dst src db sb (fuel + 1) = some (.Ok 0, mem) := by
  have hs : logical sb src = #[] := Array.eq_empty_of_size_eq_zero (by
    rw [logical_size _ _ h.source.bounds, hempty])
  simp [liftedCopy, hs, copy_empty, writeWindow_original h.destination]

/-! ## Explicit scratch-frame composition

A native target supplies its exact reserved caller/callee frame list and proves
agreement with the lifted memory outside it. That is an open simulation premise,
not implied by this adapter. Frames may change even on short/empty paths. SP,
return address and callee-saved register restoration are separate target duties.
-/

def inFrames (frames : List View) (a : Nat) : Prop :=
  ∃ frame ∈ frames, frame.start ≤ a ∧ a < frame.start + frame.len

/-- Compose independently justified scratch stores without weakening either
user window's guarantee. No existentially chosen "some scratch" footprint. -/
theorem observes_with_frames {before canonical after : Memory} {dst src : ByteView}
    {r : Result_u32_CopyError} {caller : Bool}
    (h : ObservesCopy before canonical dst src r caller (fun _ => False))
    (frames : List View)
    (hd : ∀ a, dst.contains a → ¬ inFrames frames a)
    (hs : ∀ a, src.contains a → ¬ inFrames frames a)
    (realizes : ∀ a, ¬ inFrames frames a → after a = canonical a) :
    ObservesCopy before after dst src r caller (inFrames frames) := by
  refine ⟨h.result, h.callerResult, ?_, ?_, ?_⟩
  · intro k hk
    rw [realizes _ (hd _ ⟨by omega, by omega⟩)]
    exact h.destination k hk
  · intro k hk
    rw [realizes _ (hs _ ⟨by omega, by omega⟩)]
    exact h.source k hk
  · intro a ha hf
    rw [realizes a hf]
    exact h.frame a ha (by simp)

end Oak.StatefulCopy
