import Lean.Elab.Tactic.Omega

/-!
# Oak.Stdlib.ReaderModel — UNCOMPILED abstract bounded-reader model

Hand-written source draft, not generated extraction, a checked proof artifact,
or an Oak-to-Lean refinement. No Lean invocation has been performed.

Arithmetic observations use `Nat`. The intended `u32` correspondence domain is
explicit: source length, incoming cursor fields and counts are below `2 ^ 32`.
The functions are total outside that domain, but no Oak correspondence is
claimed there. Successful additions are shown below to remain below the limit
when the source length does. No storage, bytes, pointers, or aliases are modeled.

Source authority: reader.oak SHA-256
262a8e1571054f5ffd0ec6231571bd8265fbac7b08463a3058c1de86907576d6.
See CORRESPONDENCE.md for scope and outstanding checks.
-/

set_option autoImplicit false

namespace Oak.Stdlib.ReaderModel

def u32Limit : Nat := 2 ^ 32

def FitsU32 (value : Nat) : Prop := value < u32Limit

structure Window where
  next : Nat
  endPos : Nat
  deriving Repr, DecidableEq

inductive Error where
  | InvalidWindow
  | InsufficientData
  deriving Repr, DecidableEq

inductive Result (α : Type) where
  | Ok (value : α)
  | Err (reason : Error)
  deriving Repr, DecidableEq

structure RangeRead where
  offset : Nat
  length : Nat
  rest : Window
  deriving Repr, DecidableEq

/-- Arithmetic validity is separate from the representation-domain assumption. -/
def Valid (length : Nat) (state : Window) : Prop :=
  state.next ≤ state.endPos ∧ state.endPos ≤ length

/-- Preconditions for comparing arbitrary incoming `take` calls with Oak u32s. -/
def U32Inputs (length : Nat) (state : Window) (count : Nat) : Prop :=
  FitsU32 length ∧ FitsU32 state.next ∧ FitsU32 state.endPos ∧ FitsU32 count

/-- This preserves the source's order: reject the offset, then subtract. -/
def range_fits (length offset width : Nat) : Bool :=
  if offset > length then false else decide (width ≤ length - offset)

def window (length offset count : Nat) : Result Window :=
  if range_fits length offset count = true then
    .Ok { next := offset, endPos := offset + count }
  else .Err .InvalidWindow

def remaining (state : Window) (length : Nat) : Result Nat :=
  if state.next > state.endPos ∨ state.endPos > length then
    .Err .InvalidWindow
  else .Ok (state.endPos - state.next)

/-- A pure constructor for the successful branch of `take`. -/
def takeValue (state : Window) (count : Nat) : RangeRead :=
  { offset := state.next, length := count,
    rest := { next := state.next + count, endPos := state.endPos } }

def take (state : Window) (length count : Nat) : Result RangeRead :=
  match remaining state length with
  | .Err reason => .Err reason
  | .Ok available =>
    if count > available then .Err .InsufficientData
    else .Ok (takeValue state count)

/-- The subtraction-first guard is exactly the mathematical range bound. -/
theorem range_fits_iff (length offset width : Nat) :
    range_fits length offset width = true ↔ offset + width ≤ length := by
  by_cases h : offset > length
  · simp [range_fits, h]
    omega
  · simp only [range_fits, if_neg h, decide_eq_true_eq]
    omega

theorem range_fits_empty_at_end (length : Nat) :
    range_fits length length 0 = true := by
  simp [range_fits]

theorem range_fits_offset_past_end (length offset width : Nat)
    (h : offset > length) :
    range_fits length offset width = false := by
  simp [range_fits, h]

/-- The guard justifies a non-wrapping mathematical addition in the u32 domain. -/
theorem range_fits_sum_fits_u32 (length offset width : Nat)
    (hLength : FitsU32 length)
    (hFit : range_fits length offset width = true) :
    FitsU32 (offset + width) := by
  have hSum := (range_fits_iff length offset width).mp hFit
  unfold FitsU32 at *
  omega

theorem window_ok_iff (length offset count : Nat) (state : Window) :
    window length offset count = .Ok state ↔
      offset + count ≤ length ∧
      state = { next := offset, endPos := offset + count } := by
  by_cases hFit : range_fits length offset count = true
  · have hSum := (range_fits_iff length offset count).mp hFit
    simp [window, hFit, hSum, eq_comm]
  · have hSum : ¬ offset + count ≤ length := by
      intro h
      exact hFit ((range_fits_iff length offset count).mpr h)
    simp [window, hFit, hSum]

theorem window_invalid_iff (length offset count : Nat) :
    window length offset count = .Err .InvalidWindow ↔
      ¬ offset + count ≤ length := by
  by_cases hFit : range_fits length offset count = true
  · have hSum := (range_fits_iff length offset count).mp hFit
    simp [window, hFit, hSum]
  · have hSum : ¬ offset + count ≤ length := by
      intro h
      exact hFit ((range_fits_iff length offset count).mpr h)
    simp [window, hFit, hSum]

theorem window_ok_bounds (length offset count : Nat) (state : Window)
    (h : window length offset count = .Ok state) :
    Valid length state ∧ state.endPos - state.next = count := by
  rcases (window_ok_iff length offset count state).mp h with ⟨hFit, hState⟩
  subst state
  dsimp [Valid]
  constructor
  · constructor <;> omega
  · omega

theorem remaining_valid (state : Window) (length : Nat)
    (h : Valid length state) :
    remaining state length = .Ok (state.endPos - state.next) := by
  have hGuard : ¬ (state.next > state.endPos ∨ state.endPos > length) := by
    rcases h with ⟨hNext, hEnd⟩
    omega
  simp [remaining, hGuard]

theorem remaining_invalid (state : Window) (length : Nat)
    (h : ¬ Valid length state) :
    remaining state length = .Err .InvalidWindow := by
  have hGuard : state.next > state.endPos ∨ state.endPos > length := by
    unfold Valid at h
    omega
  simp [remaining, hGuard]

theorem remaining_ok_iff (state : Window) (length available : Nat) :
    remaining state length = .Ok available ↔
      Valid length state ∧ available = state.endPos - state.next := by
  by_cases h : Valid length state
  · rw [remaining_valid state length h]
    simp [h, eq_comm]
  · rw [remaining_invalid state length h]
    simp [h]

/-- Exact success conditions and the complete successful result value. -/
theorem take_ok_iff (state : Window) (length count : Nat) (part : RangeRead) :
    take state length count = .Ok part ↔
      Valid length state ∧ count ≤ state.endPos - state.next ∧
      part = takeValue state count := by
  by_cases hValid : Valid length state
  · by_cases hCount : count ≤ state.endPos - state.next
    · have hShort : ¬ count > state.endPos - state.next := by omega
      simp [take, remaining_valid state length hValid,
        hShort, hValid, hCount, eq_comm]
    · have hShort : count > state.endPos - state.next := by omega
      simp [take, remaining_valid state length hValid,
        hShort, hValid, hCount]
  · simp [take, remaining_invalid state length hValid, hValid]

/-- InvalidWindow wins even if the requested count would also be too large. -/
theorem take_invalid_precedence (state : Window) (length count : Nat)
    (h : ¬ Valid length state) :
    take state length count = .Err .InvalidWindow := by
  simp [take, remaining_invalid state length h]

theorem take_insufficient_iff (state : Window) (length count : Nat) :
    take state length count = .Err .InsufficientData ↔
      Valid length state ∧ count > state.endPos - state.next := by
  by_cases hValid : Valid length state
  · by_cases hShort : count > state.endPos - state.next
    · simp [take, remaining_valid state length hValid, hValid, hShort]
    · simp [take, remaining_valid state length hValid, hValid, hShort]
  · simp [take, remaining_invalid state length hValid, hValid]

/-- Exact advancement, preserved end, source containment and remaining budget. -/
theorem take_ok_bounds (state : Window) (length count : Nat) (part : RangeRead)
    (h : take state length count = .Ok part) :
    part.offset = state.next ∧
    part.length = count ∧
    part.rest.next = state.next + count ∧
    part.rest.endPos = state.endPos ∧
    Valid length part.rest ∧
    part.offset + part.length ≤ state.endPos ∧
    part.offset + part.length ≤ length ∧
    part.rest.endPos - part.rest.next = state.endPos - state.next - count := by
  rcases (take_ok_iff state length count part).mp h with ⟨hValid, hCount, hPart⟩
  subst part
  rcases hValid with ⟨hNext, hEnd⟩
  dsimp [takeValue, Valid]
  refine ⟨rfl, rfl, rfl, rfl, ⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;> omega

/-- A successful result has representable cursor/range fields when length does. -/
theorem take_ok_fits_u32 (state : Window) (length count : Nat) (part : RangeRead)
    (hLength : FitsU32 length)
    (h : take state length count = .Ok part) :
    FitsU32 part.offset ∧ FitsU32 part.length ∧
    FitsU32 part.rest.next ∧ FitsU32 part.rest.endPos := by
  rcases (take_ok_iff state length count part).mp h with ⟨hValid, hCount, hPart⟩
  subst part
  rcases hValid with ⟨hNext, hEnd⟩
  dsimp [takeValue, FitsU32]
  unfold FitsU32 at hLength
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- This observation does not manufacture a cursor for an error variant. -/
def returnedRest (result : Result RangeRead) : Option Window :=
  match result with
  | .Ok part => some part.rest
  | .Err _ => none

theorem take_failure_no_rest (state : Window) (length count : Nat) (reason : Error)
    (h : take state length count = .Err reason) :
    returnedRest (take state length count) = none := by
  rw [h]
  rfl

/-- Ghost frame wrapper: it explicitly returns unchanged inputs. This is only
an immutable-value model, not a theorem about physical memory or aliases. -/
def framedTake {σ : Type} (frame : σ) (state : Window) (length count : Nat) :
    Result RangeRead × (Window × σ) :=
  (take state length count, (state, frame))

theorem take_frame_unchanged {σ : Type} (frame : σ) (state : Window)
    (length count : Nat) :
    (framedTake frame state length count).2 = (state, frame) := by
  rfl

/-- A separate caller policy: publish `rest` only on success. -/
def commitRest (state : Window) (result : Result RangeRead) : Window :=
  match result with
  | .Ok part => part.rest
  | .Err _ => state

theorem take_failure_keeps_committed_cursor (state : Window) (length count : Nat)
    (reason : Error) (h : take state length count = .Err reason) :
    commitRest state (take state length count) = state := by
  rw [h]
  rfl

end Oak.Stdlib.ReaderModel
