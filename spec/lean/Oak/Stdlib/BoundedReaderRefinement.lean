import Oak.Stdlib.BoundedReaderExtracted
import Oak.Stdlib.BoundedReaderModel
import Init.Data.UInt.Lemmas
import Init.Data.UInt.Bitwise
import Init.Data.Nat.Bitwise.Lemmas
import Init.Data.Array.Lemmas
import Lean.Elab.Tactic.Omega

/-! Source-only uncompiled actual-extraction refinement candidate.
The exact generated implementation is imported unchanged. All propositions below
remain unelaborated until a separately granted bounded Lean and axiom gate. -/
set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000

/-! Source-only, uncompiled refinement candidate. The implementation is the exact
accepted generated import; the definitions below are lossless observations.
All complete equations quantify over every fuel, including zero. -/

namespace Oak.Stdlib.BoundedReaderRefinement
open Oak.Stdlib.BoundedReaderExtracted

abbrev GWindow := encoding_sreader__Window
abbrev GRange := encoding_sreader__RangeRead
abbrev GWord := encoding_sreader__WordRead
abbrev GError := encoding_sreader__Error
abbrev RWindow := Result_encoding_sreader__Window_encoding_sreader__Error
abbrev RRange := Result_encoding_sreader__RangeRead_encoding_sreader__Error
abbrev RWord := Result_encoding_sreader__WordRead_encoding_sreader__Error
abbrev RRemaining := Result_u32_encoding_sreader__Error

structure WordObs where
  value : Nat
  rest : ReaderModel.Window
  deriving DecidableEq, Repr

def liftError : GError → ReaderModel.Error
  | .InvalidWindow => .InvalidWindow
  | .InsufficientData => .InsufficientData

def liftWindow (s : GWindow) : ReaderModel.Window :=
  { next := s.next.toNat, endPos := s.end_.toNat }

def liftRange (p : GRange) : ReaderModel.RangeRead :=
  { offset := p.offset.toNat, length := p.length.toNat, rest := liftWindow p.rest }

def liftWord (r : GWord) : WordObs :=
  { value := r.value.toNat, rest := liftWindow r.rest }

def liftWindowResult : RWindow → ReaderModel.Result ReaderModel.Window
  | .Ok s => .Ok (liftWindow s)
  | .Err e => .Err (liftError e)

def liftRemainingResult : RRemaining → ReaderModel.Result Nat
  | .Ok n => .Ok n.toNat
  | .Err e => .Err (liftError e)

def liftRangeResult : RRange → ReaderModel.Result ReaderModel.RangeRead
  | .Ok p => .Ok (liftRange p)
  | .Err e => .Err (liftError e)

def liftWordResult : RWord → ReaderModel.Result WordObs
  | .Ok r => .Ok (liftWord r)
  | .Err e => .Err (liftError e)

theorem u8_toNat_injective : Function.Injective UInt8.toNat := by
  intro a b h; exact UInt8.toNat_inj.mp h

theorem u16_toNat_injective : Function.Injective UInt16.toNat := by
  intro a b h; exact UInt16.toNat_inj.mp h

theorem u32_toNat_injective : Function.Injective UInt32.toNat := by
  intro a b h; exact UInt32.toNat_inj.mp h

theorem liftError_injective : Function.Injective liftError := by
  intro a b h
  cases a <;> cases b <;> simp_all [liftError]

theorem liftWindow_injective : Function.Injective liftWindow := by
  intro a b h
  rcases a with ⟨an, ae⟩
  rcases b with ⟨bn, be⟩
  have hn : an.toNat = bn.toNat := congrArg ReaderModel.Window.next h
  have he : ae.toNat = be.toNat := congrArg ReaderModel.Window.endPos h
  have hn' := u32_toNat_injective hn
  have he' := u32_toNat_injective he
  cases hn'; cases he'; rfl

theorem liftRange_injective : Function.Injective liftRange := by
  intro a b h
  rcases a with ⟨ao, al, ar⟩
  rcases b with ⟨bo, bl, br⟩
  have ho : ao.toNat = bo.toNat := congrArg ReaderModel.RangeRead.offset h
  have hl : al.toNat = bl.toNat := congrArg ReaderModel.RangeRead.length h
  have hr : liftWindow ar = liftWindow br := congrArg ReaderModel.RangeRead.rest h
  have ho' := u32_toNat_injective ho
  have hl' := u32_toNat_injective hl
  have hr' := liftWindow_injective hr
  cases ho'; cases hl'; cases hr'; rfl

theorem liftWord_injective : Function.Injective liftWord := by
  intro a b h
  rcases a with ⟨av, ar⟩
  rcases b with ⟨bv, br⟩
  have hv : av.toNat = bv.toNat := congrArg WordObs.value h
  have hr : liftWindow ar = liftWindow br := congrArg WordObs.rest h
  have hv' := u16_toNat_injective hv
  have hr' := liftWindow_injective hr
  cases hv'; cases hr'; rfl

theorem liftWindowResult_injective : Function.Injective liftWindowResult := by
  intro a b h
  cases a with
  | Ok a =>
    cases b with
    | Ok b => exact congrArg Result_encoding_sreader__Window_encoding_sreader__Error.Ok (liftWindow_injective (ReaderModel.Result.Ok.inj h))
    | Err b => cases h
  | Err a =>
    cases b with
    | Ok b => cases h
    | Err b => exact congrArg Result_encoding_sreader__Window_encoding_sreader__Error.Err (liftError_injective (ReaderModel.Result.Err.inj h))

theorem liftRemainingResult_injective : Function.Injective liftRemainingResult := by
  intro a b h
  cases a with
  | Ok a =>
    cases b with
    | Ok b => exact congrArg Result_u32_encoding_sreader__Error.Ok (u32_toNat_injective (ReaderModel.Result.Ok.inj h))
    | Err b => cases h
  | Err a =>
    cases b with
    | Ok b => cases h
    | Err b => exact congrArg Result_u32_encoding_sreader__Error.Err (liftError_injective (ReaderModel.Result.Err.inj h))

theorem liftRangeResult_injective : Function.Injective liftRangeResult := by
  intro a b h
  cases a with
  | Ok a =>
    cases b with
    | Ok b => exact congrArg Result_encoding_sreader__RangeRead_encoding_sreader__Error.Ok (liftRange_injective (ReaderModel.Result.Ok.inj h))
    | Err b => cases h
  | Err a =>
    cases b with
    | Ok b => cases h
    | Err b => exact congrArg Result_encoding_sreader__RangeRead_encoding_sreader__Error.Err (liftError_injective (ReaderModel.Result.Err.inj h))

theorem liftWordResult_injective : Function.Injective liftWordResult := by
  intro a b h
  cases a with
  | Ok a =>
    cases b with
    | Ok b => exact congrArg Result_encoding_sreader__WordRead_encoding_sreader__Error.Ok (liftWord_injective (ReaderModel.Result.Ok.inj h))
    | Err b => cases h
  | Err a =>
    cases b with
    | Ok b => cases h
    | Err b => exact congrArg Result_encoding_sreader__WordRead_encoding_sreader__Error.Err (liftError_injective (ReaderModel.Result.Err.inj h))

theorem optionMap_injective {α β : Type} (f : α → β) (hf : Function.Injective f) :
    Function.Injective (Option.map f) := by
  intro x y h
  cases x with
  | none => cases y <;> simp_all
  | some a =>
    cases y with
    | none => simp at h
    | some b => exact congrArg some (hf (Option.some.inj h))

theorem optionMap_reflect {α β : Type} (f : α → β) (hf : Function.Injective f)
    (x : Option α) (a : α) :
    x = some a ↔ Option.map f x = some (f a) := by
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact optionMap_injective f hf h

theorem optionMap_some_witness {α β : Type} (f : α → β) (x : Option α) (b : β)
    (h : Option.map f x = some b) : ∃ a, x = some a ∧ f a = b := by
  cases x with
  | none => simp at h
  | some a => exact ⟨a, rfl, Option.some.inj h⟩

theorem optionMap_total {α β : Type} (f : α → β) (x : Option α) (b : β)
    (h : Option.map f x = some b) : x ≠ none := by
  intro hn; rw [hn] at h; cases h

theorem size_toNat (src : Array UInt8) (hSize : src.size < 2 ^ 32) :
    src.size.toUInt32.toNat = src.size := by
  show (UInt32.ofNat src.size).toNat = src.size
  rw [UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt hSize

theorem u32_sub_toNat (a b : UInt32) (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by
  rw [UInt32.toNat_sub_of_le]
  exact UInt32.le_iff_toNat_le.mpr h

theorem u32_add_toNat (a b : UInt32) (h : a.toNat + b.toNat < 2 ^ 32) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt32.toNat_add]
  exact Nat.mod_eq_of_lt h

theorem range_fits_eq (length offset width : UInt32) (fuel : Nat) :
    bytes__range_ufits length offset width fuel =
      some (ReaderModel.range_fits length.toNat offset.toNat width.toNat) := by
  by_cases h : offset.toNat > length.toNat
  · have hc : offset > length := UInt32.lt_iff_toNat_lt.mpr h
    simp [bytes__range_ufits, ReaderModel.range_fits, h, hc]
  · have hc : ¬ offset > length := by simpa only [UInt32.lt_iff_toNat_lt] using h
    have hle : offset.toNat ≤ length.toNat := by omega
    simp [bytes__range_ufits, ReaderModel.range_fits, h, hc,
      UInt32.le_iff_toNat_le, u32_sub_toNat length offset hle]

theorem window_eq (src : Array UInt8) (offset count : UInt32) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) :
    Option.map liftWindowResult (encoding_sreader__window src offset count fuel) =
      some (ReaderModel.window src.size offset.toNat count.toNat) := by
  have hr := range_fits_eq src.size.toUInt32 offset count fuel
  rw [size_toNat src hSize] at hr
  by_cases hFit : ReaderModel.range_fits src.size offset.toNat count.toNat = true
  · have hSum := (ReaderModel.range_fits_iff src.size offset.toNat count.toNat).mp hFit
    have hadd := u32_add_toNat offset count (by omega)
    simp [encoding_sreader__window, hr, hFit, ReaderModel.window,
      liftWindowResult, liftWindow, hadd]
  · have hFalse : ReaderModel.range_fits src.size offset.toNat count.toNat = false :=
      Bool.eq_false_iff.mpr hFit
    simp [encoding_sreader__window, hr, hFalse, ReaderModel.window,
      liftWindowResult, liftError]

theorem remaining_valid_raw (src : Array UInt8) (s : GWindow) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) (hValid : ReaderModel.Valid src.size (liftWindow s)) :
    encoding_sreader__remaining s src fuel = some (.Ok (s.end_ - s.next)) := by
  have hn : ¬ s.next.toNat > s.end_.toNat := by
    rcases hValid with ⟨hn, he⟩; dsimp [liftWindow] at hn he; omega
  have he : ¬ s.end_.toNat > src.size := by
    rcases hValid with ⟨hn, he⟩; dsimp [liftWindow] at hn he; omega
  simp [encoding_sreader__remaining, UInt32.lt_iff_toNat_lt, size_toNat src hSize, hn, he]

theorem remaining_invalid_raw (src : Array UInt8) (s : GWindow) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) (hInvalid : ¬ ReaderModel.Valid src.size (liftWindow s)) :
    encoding_sreader__remaining s src fuel = some (.Err .InvalidWindow) := by
  have h : s.next.toNat > s.end_.toNat ∨ s.end_.toNat > src.size := by
    unfold ReaderModel.Valid liftWindow at hInvalid
    simp only at hInvalid
    omega
  rcases h with h | h <;>
    simp [encoding_sreader__remaining, UInt32.lt_iff_toNat_lt, size_toNat src hSize, h]

theorem remaining_eq (src : Array UInt8) (s : GWindow) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) :
    Option.map liftRemainingResult (encoding_sreader__remaining s src fuel) =
      some (ReaderModel.remaining (liftWindow s) src.size) := by
  by_cases hValid : ReaderModel.Valid src.size (liftWindow s)
  · have hn : s.next.toNat ≤ s.end_.toNat := hValid.1
    rw [remaining_valid_raw src s fuel hSize hValid,
      ReaderModel.remaining_valid (liftWindow s) src.size hValid]
    simp [liftRemainingResult, liftWindow, u32_sub_toNat s.end_ s.next hn]
  · rw [remaining_invalid_raw src s fuel hSize hValid,
      ReaderModel.remaining_invalid (liftWindow s) src.size hValid]
    rfl

theorem take_invalid_raw (src : Array UInt8) (s : GWindow) (count : UInt32) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) (hInvalid : ¬ ReaderModel.Valid src.size (liftWindow s)) :
    encoding_sreader__take s src count fuel = some (.Err .InvalidWindow) := by
  simp [encoding_sreader__take, remaining_invalid_raw src s fuel hSize hInvalid]

theorem take_short_raw (src : Array UInt8) (s : GWindow) (count : UInt32) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) (hValid : ReaderModel.Valid src.size (liftWindow s))
    (hShort : count.toNat > s.end_.toNat - s.next.toNat) :
    encoding_sreader__take s src count fuel = some (.Err .InsufficientData) := by
  have hg : count > s.end_ - s.next := by
    change s.end_ - s.next < count
    apply UInt32.lt_iff_toNat_lt.mpr
    rw [u32_sub_toNat s.end_ s.next hValid.1]
    exact hShort
  simp [encoding_sreader__take, remaining_valid_raw src s fuel hSize hValid, hg]

theorem take_good_raw (src : Array UInt8) (s : GWindow) (count : UInt32) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) (hValid : ReaderModel.Valid src.size (liftWindow s))
    (hCount : count.toNat ≤ s.end_.toNat - s.next.toNat) :
    encoding_sreader__take s src count fuel =
      some (.Ok { offset := s.next, length := count, rest := { next := s.next + count, end_ := s.end_ } }) := by
  have hg : ¬ count > s.end_ - s.next := by
    change ¬ s.end_ - s.next < count
    intro hlt
    have hn := UInt32.lt_iff_toNat_lt.mp hlt
    rw [u32_sub_toNat s.end_ s.next hValid.1] at hn
    omega
  simp [encoding_sreader__take, remaining_valid_raw src s fuel hSize hValid, hg]

theorem take_eq (src : Array UInt8) (s : GWindow) (count : UInt32) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) :
    Option.map liftRangeResult (encoding_sreader__take s src count fuel) =
      some (ReaderModel.take (liftWindow s) src.size count.toNat) := by
  by_cases hValid : ReaderModel.Valid src.size (liftWindow s)
  · by_cases hCount : count.toNat ≤ s.end_.toNat - s.next.toNat
    · have hSum : s.next.toNat + count.toNat < 2 ^ 32 := by
        have hn : s.next.toNat ≤ s.end_.toNat := hValid.1
        have he : s.end_.toNat ≤ src.size := hValid.2
        omega
      have hm := (ReaderModel.take_ok_iff (liftWindow s) src.size count.toNat
        (ReaderModel.takeValue (liftWindow s) count.toNat)).mpr ⟨hValid, hCount, rfl⟩
      rw [take_good_raw src s count fuel hSize hValid hCount, hm]
      change some (ReaderModel.Result.Ok
        ({ offset := s.next.toNat, length := count.toNat, rest := { next := (s.next + count).toNat, endPos := s.end_.toNat } } : ReaderModel.RangeRead)) = _
      rw [u32_add_toNat s.next count hSum]
      rfl
    · have hShort : count.toNat > s.end_.toNat - s.next.toNat := by omega
      have hm := (ReaderModel.take_insufficient_iff (liftWindow s) src.size count.toNat).mpr
        ⟨hValid, hShort⟩
      rw [take_short_raw src s count fuel hSize hValid hShort, hm]
      rfl
  · rw [take_invalid_raw src s count fuel hSize hValid,
      ReaderModel.take_invalid_precedence (liftWindow s) src.size count.toNat hValid]
    rfl

theorem window_success_iff (src : Array UInt8) (offset count : UInt32) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) (r : GWindow) :
    encoding_sreader__window src offset count fuel = some (.Ok r) ↔
      offset.toNat + count.toNat ≤ src.size ∧
        liftWindow r = { next := offset.toNat, endPos := offset.toNat + count.toNat } := by
  rw [optionMap_reflect liftWindowResult liftWindowResult_injective,
    window_eq src offset count fuel hSize]
  simp only [liftWindowResult, Option.some.injEq]
  exact ReaderModel.window_ok_iff src.size offset.toNat count.toNat (liftWindow r)

theorem window_invalid_iff (src : Array UInt8) (offset count : UInt32) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) :
    encoding_sreader__window src offset count fuel = some (.Err .InvalidWindow) ↔
      ¬ offset.toNat + count.toNat ≤ src.size := by
  rw [optionMap_reflect liftWindowResult liftWindowResult_injective,
    window_eq src offset count fuel hSize]
  simp only [liftWindowResult, liftError, Option.some.injEq]
  exact ReaderModel.window_invalid_iff src.size offset.toNat count.toNat

theorem remaining_success_iff (src : Array UInt8) (s : GWindow) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) (n : UInt32) :
    encoding_sreader__remaining s src fuel = some (.Ok n) ↔
      ReaderModel.Valid src.size (liftWindow s) ∧ n.toNat = s.end_.toNat - s.next.toNat := by
  rw [optionMap_reflect liftRemainingResult liftRemainingResult_injective,
    remaining_eq src s fuel hSize]
  simp only [liftRemainingResult, Option.some.injEq]
  exact ReaderModel.remaining_ok_iff (liftWindow s) src.size n.toNat

theorem remaining_invalid_iff (src : Array UInt8) (s : GWindow) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) :
    encoding_sreader__remaining s src fuel = some (.Err .InvalidWindow) ↔
      ¬ ReaderModel.Valid src.size (liftWindow s) := by
  by_cases hv : ReaderModel.Valid src.size (liftWindow s)
  · simp [remaining_valid_raw src s fuel hSize hv, hv]
  · simp [remaining_invalid_raw src s fuel hSize hv, hv]

theorem take_success_iff (src : Array UInt8) (s : GWindow) (count : UInt32) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) (p : GRange) :
    encoding_sreader__take s src count fuel = some (.Ok p) ↔
      ReaderModel.Valid src.size (liftWindow s) ∧
      count.toNat ≤ s.end_.toNat - s.next.toNat ∧
      liftRange p = ReaderModel.takeValue (liftWindow s) count.toNat := by
  rw [optionMap_reflect liftRangeResult liftRangeResult_injective, take_eq src s count fuel hSize]
  simp only [liftRangeResult, Option.some.injEq]
  exact ReaderModel.take_ok_iff (liftWindow s) src.size count.toNat (liftRange p)

theorem take_invalid_iff (src : Array UInt8) (s : GWindow) (count : UInt32) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) :
    encoding_sreader__take s src count fuel = some (.Err .InvalidWindow) ↔
      ¬ ReaderModel.Valid src.size (liftWindow s) := by
  by_cases hv : ReaderModel.Valid src.size (liftWindow s)
  · by_cases hc : count.toNat ≤ s.end_.toNat - s.next.toNat
    · simp [take_good_raw src s count fuel hSize hv hc, hv]
    · have hs : count.toNat > s.end_.toNat - s.next.toNat := by omega
      simp [take_short_raw src s count fuel hSize hv hs, hv]
  · simp [take_invalid_raw src s count fuel hSize hv, hv]

theorem take_insufficient_iff (src : Array UInt8) (s : GWindow) (count : UInt32) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) :
    encoding_sreader__take s src count fuel = some (.Err .InsufficientData) ↔
      ReaderModel.Valid src.size (liftWindow s) ∧ count.toNat > s.end_.toNat - s.next.toNat := by
  rw [optionMap_reflect liftRangeResult liftRangeResult_injective, take_eq src s count fuel hSize]
  simp only [liftRangeResult, liftError, Option.some.injEq]
  exact ReaderModel.take_insufficient_iff (liftWindow s) src.size count.toNat

theorem core_total (src : Array UInt8) (s : GWindow) (offset count : UInt32) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) :
    encoding_sreader__window src offset count fuel ≠ none ∧
    encoding_sreader__remaining s src fuel ≠ none ∧
    encoding_sreader__take s src count fuel ≠ none := by
  exact ⟨optionMap_total _ _ _ (window_eq src offset count fuel hSize),
    optionMap_total _ _ _ (remaining_eq src s fuel hSize),
    optionMap_total _ _ _ (take_eq src s count fuel hSize)⟩

def rangeReturnedRest : RRange → Option ReaderModel.Window
  | .Ok p => some (liftWindow p.rest)
  | .Err _ => none

def wordReturnedRest : RWord → Option ReaderModel.Window
  | .Ok r => some (liftWindow r.rest)
  | .Err _ => none

theorem error_no_rest (e : GError) :
    rangeReturnedRest (.Err e) = none ∧ wordReturnedRest (.Err e) = none := by
  exact ⟨rfl, rfl⟩

theorem take_error_keeps_committed_cursor (src : Array UInt8) (s : GWindow)
    (count : UInt32) (fuel : Nat) (hSize : src.size < 2 ^ 32) (e : GError)
    (h : encoding_sreader__take s src count fuel = some (.Err e)) :
    ReaderModel.commitRest (liftWindow s) (ReaderModel.take (liftWindow s) src.size count.toNat) = liftWindow s := by
  have hm := take_eq src s count fuel hSize
  rw [h] at hm
  have he : ReaderModel.take (liftWindow s) src.size count.toNat = .Err (liftError e) :=
    (Option.some.inj hm).symm
  exact ReaderModel.take_failure_keeps_committed_cursor _ _ _ _ he


theorem window_error_distinction (src : Array UInt8) (offset count : UInt32) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) :
    encoding_sreader__window src offset count fuel ≠ some (.Err .InsufficientData) := by
  intro h
  have hm := window_eq src offset count fuel hSize
  rw [h] at hm
  by_cases hg : ReaderModel.range_fits src.size offset.toNat count.toNat = true <;>
    simp [ReaderModel.window, hg, liftWindowResult, liftError] at hm

theorem remaining_error_distinction (src : Array UInt8) (s : GWindow) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) :
    encoding_sreader__remaining s src fuel ≠ some (.Err .InsufficientData) := by
  by_cases hv : ReaderModel.Valid src.size (liftWindow s)
  · simp [remaining_valid_raw src s fuel hSize hv]
  · simp [remaining_invalid_raw src s fuel hSize hv]

theorem window_success_bounds (src : Array UInt8) (offset count : UInt32) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) (r : GWindow)
    (h : encoding_sreader__window src offset count fuel = some (.Ok r)) :
    ReaderModel.Valid src.size (liftWindow r) ∧
    r.end_.toNat - r.next.toNat = count.toNat ∧
    r.end_.toNat < 2 ^ 32 := by
  have hm := window_eq src offset count fuel hSize
  rw [h] at hm
  have he : ReaderModel.window src.size offset.toNat count.toNat = .Ok (liftWindow r) :=
    (Option.some.inj hm).symm
  have hb := ReaderModel.window_ok_bounds _ _ _ _ he
  exact ⟨hb.1, hb.2, r.end_.toNat_lt⟩

theorem take_success_bounds (src : Array UInt8) (s : GWindow) (count : UInt32) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) (p : GRange)
    (h : encoding_sreader__take s src count fuel = some (.Ok p)) :
    p.offset.toNat = s.next.toNat ∧
    p.length.toNat = count.toNat ∧
    p.rest.next.toNat = s.next.toNat + count.toNat ∧
    p.rest.end_.toNat = s.end_.toNat ∧
    ReaderModel.Valid src.size (liftWindow p.rest) ∧
    p.offset.toNat + p.length.toNat ≤ s.end_.toNat ∧
    p.offset.toNat + p.length.toNat ≤ src.size ∧
    p.rest.end_.toNat - p.rest.next.toNat = s.end_.toNat - s.next.toNat - count.toNat := by
  have hm := take_eq src s count fuel hSize
  rw [h] at hm
  have he : ReaderModel.take (liftWindow s) src.size count.toNat = .Ok (liftRange p) :=
    (Option.some.inj hm).symm
  exact ReaderModel.take_ok_bounds _ _ _ _ he

theorem take_success_representable (src : Array UInt8) (s : GWindow) (count : UInt32) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) (p : GRange)
    (h : encoding_sreader__take s src count fuel = some (.Ok p)) :
    ReaderModel.FitsU32 p.offset.toNat ∧ ReaderModel.FitsU32 p.length.toNat ∧
    ReaderModel.FitsU32 p.rest.next.toNat ∧ ReaderModel.FitsU32 p.rest.end_.toNat := by
  have hm := take_eq src s count fuel hSize
  rw [h] at hm
  have he : ReaderModel.take (liftWindow s) src.size count.toNat = .Ok (liftRange p) :=
    (Option.some.inj hm).symm
  exact ReaderModel.take_ok_fits_u32 _ _ _ _ hSize he

theorem projection_constructors (s : GWindow) (p : GRange) (r : GWord) (n : UInt32) (e : GError) :
    liftWindowResult (.Ok s) = .Ok (liftWindow s) ∧
    liftWindowResult (.Err e) = .Err (liftError e) ∧
    liftRangeResult (.Ok p) = .Ok (liftRange p) ∧
    liftRangeResult (.Err e) = .Err (liftError e) ∧
    liftWordResult (.Ok r) = .Ok (liftWord r) ∧
    liftWordResult (.Err e) = .Err (liftError e) ∧
    liftRemainingResult (.Ok n) = .Ok n.toNat ∧
    liftRemainingResult (.Err e) = .Err (liftError e) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem projection_error_distinct :
    liftError .InvalidWindow ≠ liftError .InsufficientData := by decide

theorem projection_options {α β : Type} (f : α → β) (a : α) :
    Option.map f none = none ∧ Option.map f (some a) = some (f a) := by
  exact ⟨rfl, rfl⟩


theorem projection_fields (s : GWindow) (p : GRange) (r : GWord) :
    (liftWindow s).next = s.next.toNat ∧ (liftWindow s).endPos = s.end_.toNat ∧
    (liftRange p).offset = p.offset.toNat ∧ (liftRange p).length = p.length.toNat ∧
    (liftRange p).rest = liftWindow p.rest ∧
    (liftWord r).value = r.value.toNat ∧ (liftWord r).rest = liftWindow r.rest := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem projection_ok_err_disjoint (s : GWindow) (p : GRange) (r : GWord) (n : UInt32) (e : GError) :
    liftWindowResult (.Ok s) ≠ liftWindowResult (.Err e) ∧
    liftRangeResult (.Ok p) ≠ liftRangeResult (.Err e) ∧
    liftWordResult (.Ok r) ≠ liftWordResult (.Err e) ∧
    liftRemainingResult (.Ok n) ≠ liftRemainingResult (.Err e) := by
  simp [liftWindowResult, liftRangeResult, liftWordResult, liftRemainingResult]

theorem result_option_maps_injective :
    Function.Injective (Option.map liftWindowResult) ∧
    Function.Injective (Option.map liftRemainingResult) ∧
    Function.Injective (Option.map liftRangeResult) ∧
    Function.Injective (Option.map liftWordResult) := by
  exact ⟨optionMap_injective _ liftWindowResult_injective,
    optionMap_injective _ liftRemainingResult_injective,
    optionMap_injective _ liftRangeResult_injective,
    optionMap_injective _ liftWordResult_injective⟩

theorem u32_comparison_nat (a b : UInt32) :
    (a < b ↔ a.toNat < b.toNat) ∧ (a ≤ b ↔ a.toNat ≤ b.toNat) ∧
    (a > b ↔ a.toNat > b.toNat) ∧ (a ≥ b ↔ a.toNat ≥ b.toNat) ∧
    decide (a < b) = decide (a.toNat < b.toNat) ∧
    decide (a ≤ b) = decide (a.toNat ≤ b.toNat) := by
  exact ⟨UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le,
    UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le,
    decide_eq_decide.mpr UInt32.lt_iff_toNat_lt,
    decide_eq_decide.mpr UInt32.le_iff_toNat_le⟩

theorem range_fits_total (length offset width : UInt32) (fuel : Nat) :
    bytes__range_ufits length offset width fuel ≠ none := by
  rw [range_fits_eq]; intro h; cases h

theorem take_failure_no_rest (src : Array UInt8) (s : GWindow) (count : UInt32) (fuel : Nat)
    (e : GError) (h : encoding_sreader__take s src count fuel = some (.Err e)) :
    Option.map rangeReturnedRest (encoding_sreader__take s src count fuel) = some none := by
  rw [h]; rfl

end Oak.Stdlib.BoundedReaderRefinement

namespace Oak.Stdlib.BoundedReaderRefinement

/-
Source-only draft for Lean 4.33.1. This file has not been compiled.

The following abbreviation is exactly the three `value` bindings in
`Oak.Stdlib.BoundedReaderExtracted.endian__read_uu16_ube`, with `hi` and `lo`
substituted for its first and second `src.getD` expressions respectively.
It contains no array reads, range checks, result constructors, or decoder.

Extracted source SHA-256:
94f44f3e034bd421c1653304d5b8cb6558a2440f595854af962a2088fe08a335
-/
abbrev be16ValueExpr (hi lo : UInt8) : UInt16 :=
  let value : UInt16 := (0 : UInt16)
  let value := (value ||| ((hi.toUInt16) <<< (8 : UInt16)))
  let value := (value ||| ((lo.toUInt16) <<< (0 : UInt16)))
  value

/-- The generated word-value expression denotes the mathematical BE16 value. -/
theorem be16ValueExpr_toNat (hi lo : UInt8) :
    (be16ValueExpr hi lo).toNat = 256 * hi.toNat + lo.toNat := by
  have hi_lt : hi.toNat < 256 := UInt8.toNat_lt_size hi
  have lo_lt : lo.toNat < 256 := UInt8.toNat_lt_size lo
  have hi_shift_lt : hi.toNat <<< 8 < 2 ^ 16 := by
    rw [Nat.shiftLeft_eq]
    change hi.toNat * 256 < 65536
    omega
  have hi_shift_toNat :
      (hi.toUInt16 <<< (8 : UInt16)).toNat = hi.toNat <<< 8 := by
    rw [UInt16.toNat_shiftLeft, UInt8.toNat_toUInt16]
    change (hi.toNat <<< 8) % 65536 = hi.toNat <<< 8
    exact Nat.mod_eq_of_lt hi_shift_lt
  have lo_lt_pow : lo.toNat < 2 ^ (8 : Nat) := lo_lt
  calc
    (be16ValueExpr hi lo).toNat =
        (hi.toUInt16 <<< (8 : UInt16)).toNat ||| lo.toUInt16.toNat := by
      simp only [be16ValueExpr, UInt16.zero_or, UInt16.shiftLeft_zero,
        UInt16.toNat_or]
    _ = (hi.toNat <<< 8) ||| lo.toNat := by
      rw [hi_shift_toNat, UInt8.toNat_toUInt16]
    _ = (hi.toNat <<< 8) + lo.toNat :=
      (Nat.shiftLeft_add_eq_or_of_lt (i := 8) lo_lt_pow hi.toNat).symm
    _ = 256 * hi.toNat + lo.toNat := by
      rw [Nat.shiftLeft_eq]
      change hi.toNat * 256 + lo.toNat = 256 * hi.toNat + lo.toNat
      rw [Nat.mul_comm hi.toNat 256]

/-- Every generated BE16 value is at most 65535. -/
theorem be16ValueExpr_le_65535 (hi lo : UInt8) :
    (be16ValueExpr hi lo).toNat ≤ 65535 := by
  rw [be16ValueExpr_toNat]
  have hi_lt : hi.toNat < 256 := UInt8.toNat_lt_size hi
  have lo_lt : lo.toNat < 256 := UInt8.toNat_lt_size lo
  omega

/-- Every generated BE16 value is strictly below 65536. -/
theorem be16ValueExpr_lt_65536 (hi lo : UInt8) :
    (be16ValueExpr hi lo).toNat < 65536 := by
  have value_le := be16ValueExpr_le_65535 hi lo
  omega

end Oak.Stdlib.BoundedReaderRefinement

/-! Uncompiled source candidate. These theorems refer to the exact generated
functions. They concern pure Array values, not an operational load/write trace. -/

namespace Oak.Stdlib.BoundedReaderRefinement
open Oak.Stdlib.BoundedReaderExtracted

def Good (src : Array UInt8) (w : ReaderModel.Window) : Prop :=
  ReaderModel.Valid src.size w ∧ 2 ≤ w.endPos - w.next

theorem good_window_bounds (src : Array UInt8) (w : ReaderModel.Window) (h : Good src w) :
    w.next < w.endPos ∧ w.next + 1 < w.endPos ∧ w.next + 2 ≤ w.endPos := by
  rcases h with ⟨⟨hn, he⟩, hc⟩
  omega

theorem good_index0 (src : Array UInt8) (w : ReaderModel.Window) (h : Good src w) :
    w.next < src.size := by
  have hb := good_window_bounds src w h
  have he := h.1.2
  omega

theorem good_index1 (src : Array UInt8) (w : ReaderModel.Window) (h : Good src w) :
    w.next + 1 < src.size := by
  have hb := good_window_bounds src w h
  have he := h.1.2
  omega

theorem good_no_wrap (src : Array UInt8) (w : ReaderModel.Window)
    (hSize : src.size < 2 ^ 32) (h : Good src w) :
    w.next + 2 < 2 ^ 32 := by
  have hb := good_window_bounds src w h
  have he := h.1.2
  omega

theorem u32_two_indices (src : Array UInt8) (s : GWindow)
    (hSize : src.size < 2 ^ 32) (h : Good src (liftWindow s)) :
    (s.next + (0 : UInt32)).toNat = s.next.toNat ∧
    (s.next + (1 : UInt32)).toNat = s.next.toNat + 1 ∧
    (s.next + (2 : UInt32)).toNat = s.next.toNat + 2 := by
  have hb : s.next.toNat + 2 < 2 ^ 32 := good_no_wrap src (liftWindow s) hSize h
  have h0 := u32_add_toNat s.next (0 : UInt32) (by simpa using s.next.toNat_lt)
  have h1 := u32_add_toNat s.next (1 : UInt32) (by simpa using (show s.next.toNat + 1 < 2 ^ 32 by omega))
  have h2 := u32_add_toNat s.next (2 : UInt32) (by simpa using hb)
  simpa using And.intro h0 (And.intro h1 h2)

theorem getD_checked (src : Array UInt8) (i : Nat) (zero : UInt8) (h : i < src.size) :
    src.getD i zero = src[i]'h := by
  simp [Array.getD, h]

def checkedHi (src : Array UInt8) (w : ReaderModel.Window) (h : Good src w) : UInt8 :=
  src[w.next]'(good_index0 src w h)

def checkedLo (src : Array UInt8) (w : ReaderModel.Window) (h : Good src w) : UInt8 :=
  src[w.next + 1]'(good_index1 src w h)

def checkedBE16 (src : Array UInt8) (w : ReaderModel.Window) (h : Good src w) : Nat :=
  256 * (checkedHi src w h).toNat + (checkedLo src w h).toNat

def wordValue (src : Array UInt8) (w : ReaderModel.Window) (h : Good src w) : WordObs :=
  { value := checkedBE16 src w h, rest := { next := w.next + 2, endPos := w.endPos } }

/-- Full mathematical specification. Invalid states take precedence over short
windows. Successful bytes use proofs of source containment, never defaults. -/
def wordSpec (src : Array UInt8) (w : ReaderModel.Window) : ReaderModel.Result WordObs := by
  letI : Decidable (ReaderModel.Valid src.size w) :=
    inferInstanceAs (Decidable (w.next ≤ w.endPos ∧ w.endPos ≤ src.size))
  exact if hv : ReaderModel.Valid src.size w then
    if hc : 2 ≤ w.endPos - w.next then .Ok (wordValue src w ⟨hv, hc⟩)
    else .Err .InsufficientData
  else .Err .InvalidWindow

theorem checked_bytes_proof_irrelevant (src : Array UInt8) (w : ReaderModel.Window)
    (h1 h2 : Good src w) :
    checkedHi src w h1 = checkedHi src w h2 ∧
    checkedLo src w h1 = checkedLo src w h2 ∧
    checkedBE16 src w h1 = checkedBE16 src w h2 := by
  exact ⟨rfl, rfl, rfl⟩

theorem endian_range_after_good (src : Array UInt8) (s : GWindow) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) (hg : Good src (liftWindow s)) :
    bytes__range_ufits src.size.toUInt32 s.next (2 : UInt32) fuel = some true := by
  rw [range_fits_eq, size_toNat src hSize]
  have hb := good_window_bounds src (liftWindow s) hg
  have he : s.end_.toNat ≤ src.size := hg.1.2
  have hFit := (ReaderModel.range_fits_iff src.size s.next.toNat 2).mpr (by
    dsimp [liftWindow] at hb
    omega)
  simpa using congrArg some hFit

theorem generated_reads_checked (src : Array UInt8) (s : GWindow)
    (hSize : src.size < 2 ^ 32) (hg : Good src (liftWindow s)) :
    src.getD (s.next + (0 : UInt32)).toNat (0 : UInt8) = checkedHi src (liftWindow s) hg ∧
    src.getD (s.next + (1 : UInt32)).toNat (0 : UInt8) = checkedLo src (liftWindow s) hg := by
  have hi := u32_two_indices src s hSize hg
  rw [hi.1, hi.2.1]
  exact ⟨getD_checked src s.next.toNat 0 (good_index0 src (liftWindow s) hg),
    getD_checked src (s.next.toNat + 1) 0 (good_index1 src (liftWindow s) hg)⟩

theorem endian_good_raw (src : Array UInt8) (s : GWindow) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) (hg : Good src (liftWindow s)) :
    endian__read_uu16_ube src s.next fuel =
      some (.Ok (be16ValueExpr (checkedHi src (liftWindow s) hg) (checkedLo src (liftWindow s) hg))) := by
  have hGuard := endian_range_after_good src s fuel hSize hg
  have hRead := generated_reads_checked src s hSize hg
  unfold endian__read_uu16_ube
  rw [hGuard]
  change some (Result_u16_endian__Error.Ok
    (be16ValueExpr (src.getD (s.next + (0 : UInt32)).toNat (0 : UInt8))
      (src.getD (s.next + (1 : UInt32)).toNat (0 : UInt8)))) = _
  rw [hRead.1, hRead.2]

theorem endian_total (src : Array UInt8) (offset : UInt32) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) :
    endian__read_uu16_ube src offset fuel ≠ none := by
  have hr := range_fits_eq src.size.toUInt32 offset (2 : UInt32) fuel
  rw [size_toNat src hSize] at hr
  change bytes__range_ufits src.size.toUInt32 offset (2 : UInt32) fuel =
    some (ReaderModel.range_fits src.size offset.toNat 2) at hr
  cases hb : ReaderModel.range_fits src.size offset.toNat 2
  · rw [hb] at hr
    simp [endian__read_uu16_ube, hr]
  · rw [hb] at hr
    simp [endian__read_uu16_ube, hr]

theorem read_invalid_raw (src : Array UInt8) (s : GWindow) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) (hInvalid : ¬ ReaderModel.Valid src.size (liftWindow s)) :
    encoding_sreader__read_uu16_ube s src fuel = some (.Err .InvalidWindow) := by
  simp [encoding_sreader__read_uu16_ube, take_invalid_raw src s 2 fuel hSize hInvalid]

theorem read_short_raw (src : Array UInt8) (s : GWindow) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) (hValid : ReaderModel.Valid src.size (liftWindow s))
    (hShort : s.end_.toNat - s.next.toNat < 2) :
    encoding_sreader__read_uu16_ube s src fuel = some (.Err .InsufficientData) := by
  have ht := take_short_raw src s 2 fuel hSize hValid (by simpa using hShort)
  simp [encoding_sreader__read_uu16_ube, ht]

theorem read_good_raw (src : Array UInt8) (s : GWindow) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) (hg : Good src (liftWindow s)) :
    encoding_sreader__read_uu16_ube s src fuel =
      some (.Ok { value := be16ValueExpr (checkedHi src (liftWindow s) hg) (checkedLo src (liftWindow s) hg), rest := { next := s.next + (2 : UInt32), end_ := s.end_ } }) := by
  have ht := take_good_raw src s 2 fuel hSize hg.1 (by simpa [liftWindow] using hg.2)
  have he := endian_good_raw src s fuel hSize hg
  simp [encoding_sreader__read_uu16_ube, ht, he]

theorem read_eq (src : Array UInt8) (s : GWindow) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) :
    Option.map liftWordResult (encoding_sreader__read_uu16_ube s src fuel) =
      some (wordSpec src (liftWindow s)) := by
  by_cases hv : ReaderModel.Valid src.size (liftWindow s)
  · by_cases hc : 2 ≤ s.end_.toNat - s.next.toNat
    · have hg : Good src (liftWindow s) := ⟨hv, hc⟩
      have hi := u32_two_indices src s hSize hg
      have hc' : 2 ≤ (liftWindow s).endPos - (liftWindow s).next := hc
      rw [read_good_raw src s fuel hSize hg, wordSpec, dif_pos hv, dif_pos hc']
      change some (ReaderModel.Result.Ok
        ({ value := (be16ValueExpr (checkedHi src (liftWindow s) hg) (checkedLo src (liftWindow s) hg)).toNat, rest := { next := (s.next + (2 : UInt32)).toNat, endPos := s.end_.toNat } } : WordObs)) = _
      rw [be16ValueExpr_toNat, hi.2.2]
      rfl
    · have hs : s.end_.toNat - s.next.toNat < 2 := by omega
      have hc' : ¬ 2 ≤ (liftWindow s).endPos - (liftWindow s).next := hc
      rw [read_short_raw src s fuel hSize hv hs, wordSpec, dif_pos hv, dif_neg hc']
      rfl
  · rw [read_invalid_raw src s fuel hSize hv, wordSpec, dif_neg hv]
    rfl

theorem read_invalid_iff (src : Array UInt8) (s : GWindow) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) :
    encoding_sreader__read_uu16_ube s src fuel = some (.Err .InvalidWindow) ↔
      ¬ ReaderModel.Valid src.size (liftWindow s) := by
  rw [optionMap_reflect liftWordResult liftWordResult_injective, read_eq src s fuel hSize]
  simp only [liftWordResult, liftError, Option.some.injEq]
  by_cases hv : ReaderModel.Valid src.size (liftWindow s)
  · by_cases hc : 2 ≤ (liftWindow s).endPos - (liftWindow s).next
    · rw [wordSpec, dif_pos hv, dif_pos hc]
      constructor
      · intro h; cases h
      · intro hn; exact False.elim (hn hv)
    · rw [wordSpec, dif_pos hv, dif_neg hc]
      constructor
      · intro h; cases h
      · intro hn; exact False.elim (hn hv)
  · rw [wordSpec, dif_neg hv]
    exact ⟨fun _ => hv, fun _ => rfl⟩

theorem read_insufficient_iff (src : Array UInt8) (s : GWindow) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) :
    encoding_sreader__read_uu16_ube s src fuel = some (.Err .InsufficientData) ↔
      ReaderModel.Valid src.size (liftWindow s) ∧ s.end_.toNat - s.next.toNat < 2 := by
  rw [optionMap_reflect liftWordResult liftWordResult_injective, read_eq src s fuel hSize]
  simp only [liftWordResult, liftError, Option.some.injEq]
  by_cases hv : ReaderModel.Valid src.size (liftWindow s)
  · by_cases hc : 2 ≤ (liftWindow s).endPos - (liftWindow s).next
    · rw [wordSpec, dif_pos hv, dif_pos hc]
      constructor
      · intro h; cases h
      · rintro ⟨_, hs⟩
        have hn : 2 ≤ s.end_.toNat - s.next.toNat := hc
        exfalso
        omega
    · rw [wordSpec, dif_pos hv, dif_neg hc]
      have hn : ¬ 2 ≤ s.end_.toNat - s.next.toNat := hc
      have hs : s.end_.toNat - s.next.toNat < 2 := by omega
      exact ⟨fun _ => ⟨hv, hs⟩, fun _ => rfl⟩
  · rw [wordSpec, dif_neg hv]
    constructor
    · intro h; cases h
    · rintro ⟨hv', _⟩; exact False.elim (hv hv')

theorem read_success_iff (src : Array UInt8) (s : GWindow) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) (r : GWord) :
    encoding_sreader__read_uu16_ube s src fuel = some (.Ok r) ↔
      ∃ hg : Good src (liftWindow s), liftWord r = wordValue src (liftWindow s) hg := by
  rw [optionMap_reflect liftWordResult liftWordResult_injective, read_eq src s fuel hSize]
  simp only [liftWordResult, Option.some.injEq]
  by_cases hv : ReaderModel.Valid src.size (liftWindow s)
  · by_cases hc : 2 ≤ (liftWindow s).endPos - (liftWindow s).next
    · rw [wordSpec, dif_pos hv, dif_pos hc]
      simp only [ReaderModel.Result.Ok.injEq]
      constructor
      · intro h; exact ⟨⟨hv, hc⟩, h.symm⟩
      · rintro ⟨hg, h⟩; exact h.symm
    · rw [wordSpec, dif_pos hv, dif_neg hc]
      constructor
      · intro h; cases h
      · rintro ⟨hg, _⟩; exact False.elim (hc hg.2)
  · rw [wordSpec, dif_neg hv]
    constructor
    · intro h; cases h
    · rintro ⟨hg, _⟩; exact False.elim (hv hg.1)

theorem read_total (src : Array UInt8) (s : GWindow) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) : encoding_sreader__read_uu16_ube s src fuel ≠ none :=
  optionMap_total _ _ _ (read_eq src s fuel hSize)

theorem read_success_unique (src : Array UInt8) (s : GWindow) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) (hg : Good src (liftWindow s)) :
    ∃ r : GWord, encoding_sreader__read_uu16_ube s src fuel = some (.Ok r) ∧
      ∀ y : GWord, encoding_sreader__read_uu16_ube s src fuel = some (.Ok y) → y = r := by
  let r : GWord := { value := be16ValueExpr (checkedHi src (liftWindow s) hg) (checkedLo src (liftWindow s) hg), rest := { next := s.next + (2 : UInt32), end_ := s.end_ } }
  have hr : encoding_sreader__read_uu16_ube s src fuel = some (.Ok r) :=
    read_good_raw src s fuel hSize hg
  refine ⟨r, hr, ?_⟩
  intro y hy
  exact Result_encoding_sreader__WordRead_encoding_sreader__Error.Ok.inj
    (Option.some.inj (hy.symm.trans hr))

theorem read_success_implies_good (src : Array UInt8) (s : GWindow) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) (r : GWord)
    (h : encoding_sreader__read_uu16_ube s src fuel = some (.Ok r)) : Good src (liftWindow s) := by
  rcases (read_success_iff src s fuel hSize r).mp h with ⟨hg, hr⟩
  exact hg

theorem read_cases_disjoint_complete (src : Array UInt8) (s : GWindow) :
    (¬ ReaderModel.Valid src.size (liftWindow s) ∨
      (ReaderModel.Valid src.size (liftWindow s) ∧ s.end_.toNat - s.next.toNat < 2) ∨
      Good src (liftWindow s)) ∧
    ¬ (¬ ReaderModel.Valid src.size (liftWindow s) ∧ Good src (liftWindow s)) ∧
    ¬ ((ReaderModel.Valid src.size (liftWindow s) ∧ s.end_.toNat - s.next.toNat < 2) ∧
      Good src (liftWindow s)) ∧
    ¬ (¬ ReaderModel.Valid src.size (liftWindow s) ∧
      (ReaderModel.Valid src.size (liftWindow s) ∧ s.end_.toNat - s.next.toNat < 2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases hv : ReaderModel.Valid src.size (liftWindow s)
    · by_cases hc : 2 ≤ s.end_.toNat - s.next.toNat
      · exact Or.inr (Or.inr ⟨hv, hc⟩)
      · exact Or.inr (Or.inl ⟨hv, by omega⟩)
    · exact Or.inl hv
  · rintro ⟨hn, hg⟩
    exact hn hg.1
  · rintro ⟨⟨_, hs⟩, hg⟩
    have hc : 2 ≤ s.end_.toNat - s.next.toNat := hg.2
    omega
  · rintro ⟨hn, hv, _⟩
    exact hn hv

theorem endian_error_unreachable_after_take (src : Array UInt8) (s : GWindow) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) (p : GRange)
    (ht : encoding_sreader__take s src (2 : UInt32) fuel = some (.Ok p)) :
    endian__read_uu16_ube src p.offset fuel ≠ some (.Err .BufferTooSmall) := by
  rcases (take_success_iff src s 2 fuel hSize p).mp ht with ⟨hv, hc, hp⟩
  have hg : Good src (liftWindow s) := by
    refine ⟨hv, ?_⟩
    change 2 ≤ s.end_.toNat - s.next.toNat
    exact hc
  have ho : p.offset.toNat = s.next.toNat := congrArg ReaderModel.RangeRead.offset hp
  have ho' : p.offset = s.next := u32_toNat_injective ho
  rw [ho', endian_good_raw src s fuel hSize hg]
  intro h; cases h

theorem read_same_take_rest (src : Array UInt8) (s : GWindow) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) (p : GRange) (r : GWord)
    (ht : encoding_sreader__take s src (2 : UInt32) fuel = some (.Ok p))
    (hr : encoding_sreader__read_uu16_ube s src fuel = some (.Ok r)) :
    r.rest = p.rest ∧ liftWindow r.rest = (ReaderModel.takeValue (liftWindow s) 2).rest ∧
    ReaderModel.take (liftWindow s) src.size 2 = .Ok (ReaderModel.takeValue (liftWindow s) 2) := by
  rcases (take_success_iff src s 2 fuel hSize p).mp ht with ⟨hv, hc, hp⟩
  rcases (read_success_iff src s fuel hSize r).mp hr with ⟨hg, hrp⟩
  have hpRest : liftWindow p.rest = (ReaderModel.takeValue (liftWindow s) 2).rest :=
    congrArg ReaderModel.RangeRead.rest hp
  have hrRest : liftWindow r.rest = (ReaderModel.takeValue (liftWindow s) 2).rest :=
    congrArg WordObs.rest hrp
  have hRest := liftWindow_injective (hrRest.trans hpRest.symm)
  exact ⟨hRest, hrRest, (ReaderModel.take_ok_iff _ _ _ _).mpr ⟨hv, hc, rfl⟩⟩

theorem read_success_value_and_access (src : Array UInt8) (s : GWindow) (fuel : Nat)
    (hSize : src.size < 2 ^ 32) (r : GWord)
    (hr : encoding_sreader__read_uu16_ube s src fuel = some (.Ok r)) :
    ∃ hg : Good src (liftWindow s),
      r.value.toNat = checkedBE16 src (liftWindow s) hg ∧ r.value.toNat ≤ 65535 ∧
      r.value.toNat < 65536 ∧ s.next.toNat < s.end_.toNat ∧
      s.next.toNat + 1 < s.end_.toNat ∧ s.next.toNat + 1 < src.size ∧
      r.rest.next.toNat = s.next.toNat + 2 ∧ r.rest.end_.toNat = s.end_.toNat ∧
      s.next.toNat + 2 < 2 ^ 32 := by
  rcases (read_success_iff src s fuel hSize r).mp hr with ⟨hg, hp⟩
  have hv : r.value.toNat = checkedBE16 src (liftWindow s) hg := congrArg WordObs.value hp
  have hrest := congrArg WordObs.rest hp
  have hn : r.rest.next.toNat = s.next.toNat + 2 := congrArg ReaderModel.Window.next hrest
  have he : r.rest.end_.toNat = s.end_.toNat := congrArg ReaderModel.Window.endPos hrest
  have hb := good_window_bounds src (liftWindow s) hg
  have hi := good_index1 src (liftWindow s) hg
  have hnw := good_no_wrap src (liftWindow s) hSize hg
  have hval : r.value.toNat ≤ 65535 := by
    rw [hv, checkedBE16, ← be16ValueExpr_toNat]
    exact be16ValueExpr_le_65535 _ _
  exact ⟨hg, hv, hval, by omega, hb.1, hb.2.1, hi, hn, he, hnw⟩

theorem read_failure_no_rest (src : Array UInt8) (s : GWindow) (fuel : Nat) (e : GError)
    (h : encoding_sreader__read_uu16_ube s src fuel = some (.Err e)) :
    Option.map wordReturnedRest (encoding_sreader__read_uu16_ube s src fuel) = some none := by
  rw [h]; rfl


theorem read_fuel_irrelevant (src : Array UInt8) (s : GWindow) (fuelA fuelB : Nat)
    (hSize : src.size < 2 ^ 32) :
    encoding_sreader__read_uu16_ube s src fuelA = encoding_sreader__read_uu16_ube s src fuelB := by
  apply optionMap_injective liftWordResult liftWordResult_injective
  rw [read_eq src s fuelA hSize, read_eq src s fuelB hSize]

end Oak.Stdlib.BoundedReaderRefinement

/-! Finite future kernel-reduction controls. These are source-only and unrun;
none substitutes for the universal theorems in the imported modules. -/

namespace Oak.Stdlib.BoundedReaderRefinement.Controls
open Oak.Stdlib.BoundedReaderExtracted

theorem window_empty : encoding_sreader__window #[] 0 0 0 =
    some (.Ok { next := 0, end_ := 0 }) := by decide

theorem window_empty_at_end : encoding_sreader__window #[0x12, 0x34] 2 0 0 =
    some (.Ok { next := 2, end_ := 2 }) := by decide

theorem window_offset_past_end : encoding_sreader__window #[0x12, 0x34] 3 0 0 =
    some (.Err .InvalidWindow) := by decide

theorem window_wrapping_endpoint_refused :
    encoding_sreader__window #[] (4294967295 : UInt32) 2 0 =
    some (.Err .InvalidWindow) := by decide

theorem take_invalid_precedes_short :
    encoding_sreader__take { next := 3, end_ := 2 } #[0x12, 0x34] 4 0 =
    some (.Err .InvalidWindow) := by decide

theorem take_end_past_source :
    encoding_sreader__take { next := 0, end_ := 3 } #[0x12, 0x34] 0 0 =
    some (.Err .InvalidWindow) := by decide

theorem take_short :
    encoding_sreader__take { next := 1, end_ := 2 } #[0x12, 0x34] 2 0 =
    some (.Err .InsufficientData) := by decide

theorem take_zero_at_end :
    encoding_sreader__take { next := 2, end_ := 2 } #[0x12, 0x34] 0 0 =
    some (.Ok { offset := 2, length := 0, rest := { next := 2, end_ := 2 } }) := by decide

theorem read_0000 : encoding_sreader__read_uu16_ube { next := 0, end_ := 2 } #[0, 0] 0 =
    some (.Ok { value := 0, rest := { next := 2, end_ := 2 } }) := by decide

theorem read_0001 : encoding_sreader__read_uu16_ube { next := 0, end_ := 2 } #[0, 1] 0 =
    some (.Ok { value := 1, rest := { next := 2, end_ := 2 } }) := by decide

theorem read_00ff : encoding_sreader__read_uu16_ube { next := 0, end_ := 2 } #[0, 255] 0 =
    some (.Ok { value := 255, rest := { next := 2, end_ := 2 } }) := by decide

theorem read_0100 : encoding_sreader__read_uu16_ube { next := 0, end_ := 2 } #[1, 0] 0 =
    some (.Ok { value := 256, rest := { next := 2, end_ := 2 } }) := by decide

theorem read_ffff : encoding_sreader__read_uu16_ube { next := 0, end_ := 2 } #[255, 255] 0 =
    some (.Ok { value := 65535, rest := { next := 2, end_ := 2 } }) := by decide

theorem read_invalid_precedes_short :
    encoding_sreader__read_uu16_ube { next := 3, end_ := 2 } #[0x12, 0x34] 0 =
    some (.Err .InvalidWindow) := by decide

theorem read_source_bound_refused :
    encoding_sreader__read_uu16_ube { next := 0, end_ := 3 } #[0x12, 0x34] 0 =
    some (.Err .InvalidWindow) := by decide

theorem read_short_window :
    encoding_sreader__read_uu16_ube { next := 1, end_ := 2 } #[0x12, 0x34] 0 =
    some (.Err .InsufficientData) := by decide

theorem read_empty_at_end :
    encoding_sreader__read_uu16_ube { next := 2, end_ := 2 } #[0x12, 0x34] 0 =
    some (.Err .InsufficientData) := by decide

theorem read_narrow_subwindow :
    encoding_sreader__read_uu16_ube { next := 1, end_ := 3 } #[0xaa, 0x12, 0x34, 0xbb] 7 =
    some (.Ok { value := 0x1234, rest := { next := 3, end_ := 3 } }) := by decide

end Oak.Stdlib.BoundedReaderRefinement.Controls
