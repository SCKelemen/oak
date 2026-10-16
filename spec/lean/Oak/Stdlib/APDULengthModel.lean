import Lean.Elab.Tactic.Omega
import Oak.Stdlib.BoundedReaderModel

/-!
# Pure APDU length model — UNCOMPILED proof candidate

Handwritten specification of the seven structural cases in the pinned Oak
decoder. This is NOT generated/extracted Oak and is NOT an implementation
refinement proof. `observe` is a total mathematical projection, not an access
trace: its default values outside a list are irrelevant only under the stated
case/guard obligations. Native memory, aliases, machine arithmetic and protocol
semantics remain separate obligations. No Lean invocation has checked this file.
-/

set_option autoImplicit false

namespace Oak.Stdlib.APDUModel

abbrev Byte := Fin 256
abbrev Word := Fin 65536

inductive CommandCase where
  | case1 | case2Short | case3Short | case4Short
  | case2Extended | case3Extended | case4Extended
  deriving DecidableEq, Repr

inductive Error where
  | tooLong | truncatedHeader | truncatedLength
  | zeroDataLength | truncatedData | trailingBytes
  deriving DecidableEq, Repr

/-- Observed length fields. `word` is bytes 5/6, shortLe the last byte, and
extendedLe the last two bytes. A decoder branch may ignore any of these fields.
The four uninterpreted header bytes are outside this length-only result. -/
structure Input where
  n : Nat
  first : Byte
  word : Word
  shortLe : Byte
  extendedLe : Word
  deriving DecidableEq, Repr

structure Lengths where
  form : CommandCase
  dataAt : Nat
  dataLength : Nat
  responseLength : Option Nat
  consumed : Nat
  deriving DecidableEq, Repr

def beWord (hi lo : Byte) : Word :=
  ⟨256 * hi.val + lo.val, by
    have hhi := hi.isLt
    have hlo := lo.isLt
    omega⟩

def byteAt (src : List Byte) (offset : Nat) : Byte := src.getD offset 0

/-- A mathematical summary; not claimed to use the Oak access order. -/
def observe (src : List Byte) : Input :=
  { n := src.length
    first := byteAt src 4
    word := beWord (byteAt src 5) (byteAt src 6)
    shortLe := byteAt src (src.length - 1)
    extendedLe := beWord (byteAt src (src.length - 2))
      (byteAt src (src.length - 1)) }

def shortResponse (v : Byte) : Nat := if v.val = 0 then 256 else v.val
def extendedResponse (v : Word) : Nat := if v.val = 0 then 65536 else v.val

def layout (x : Input) (form : CommandCase) : Lengths :=
  match form with
  | .case1 => ⟨form, 4, 0, none, x.n⟩
  | .case2Short => ⟨form, 5, 0, some (shortResponse x.first), x.n⟩
  | .case3Short => ⟨form, 5, x.first.val, none, x.n⟩
  | .case4Short => ⟨form, 5, x.first.val, some (shortResponse x.shortLe), x.n⟩
  | .case2Extended => ⟨form, 7, 0, some (extendedResponse x.word), x.n⟩
  | .case3Extended => ⟨form, 7, x.word.val, none, x.n⟩
  | .case4Extended => ⟨form, 7, x.word.val, some (extendedResponse x.extendedLe), x.n⟩

/-- Declarative seven-case grammar, independent of the decoder branch order.
Payload bytes are arbitrary; byte/word widths are carried by `Input`. -/
def Shape (x : Input) (form : CommandCase) : Prop :=
  match form with
  | .case1 => x.n = 4
  | .case2Short => x.n = 5
  | .case3Short => 0 < x.first.val ∧ x.n = 5 + x.first.val
  | .case4Short => 0 < x.first.val ∧ x.n = 6 + x.first.val
  | .case2Extended => x.first.val = 0 ∧ x.n = 7
  | .case3Extended => x.first.val = 0 ∧ 0 < x.word.val ∧ x.n = 7 + x.word.val
  | .case4Extended => x.first.val = 0 ∧ 0 < x.word.val ∧ x.n = 9 + x.word.val

def shortData (x : Input) : Except Error Lengths :=
  if x.first.val > x.n - 5 then .error .truncatedData
  else if x.n - (5 + x.first.val) = 0 then .ok (layout x .case3Short)
  else if x.n - (5 + x.first.val) = 1 then .ok (layout x .case4Short)
  else .error .trailingBytes

def extendedData (x : Input) : Except Error Lengths :=
  if x.word.val > x.n - 7 then .error .truncatedData
  else if x.n - (7 + x.word.val) = 0 then .ok (layout x .case3Extended)
  else if x.n - (7 + x.word.val) = 1 then .error .truncatedLength
  else if x.n - (7 + x.word.val) = 2 then .ok (layout x .case4Extended)
  else .error .trailingBytes

/-- Exact rejection priority of the pinned decoder, after abstracting checked
reader operations to arithmetic on their validated windows. -/
def decode (x : Input) : Except Error Lengths :=
  if x.n > 65544 then .error .tooLong
  else if x.n < 4 then .error .truncatedHeader
  else if x.n = 4 then .ok (layout x .case1)
  else if x.n = 5 then .ok (layout x .case2Short)
  else if x.first.val = 0 then
    if x.n < 7 then .error .truncatedLength
    else if x.n = 7 then .ok (layout x .case2Extended)
    else if x.word.val = 0 then .error .zeroDataLength
    else extendedData x
  else shortData x

def decodeBytes (src : List Byte) : Except Error Lengths := decode (observe src)

/-- Arithmetic bridge between the two handwritten models. For the APDU helper
entries `offset` is 5 or 7 and the checked reader window ends at the frame length.
This is not a theorem about the extracted Oak reader. -/
theorem data_window_take_iff (n offset count : Nat) (h : offset ≤ n) :
    ReaderModel.take ⟨offset, n⟩ n count =
      .Ok (ReaderModel.takeValue ⟨offset, n⟩ count) ↔ count ≤ n - offset := by
  rw [ReaderModel.take_ok_iff]
  simp [ReaderModel.Valid, h]

theorem short_response_bounds (v : Byte) :
    1 ≤ shortResponse v ∧ shortResponse v ≤ 256 := by
  have h := v.isLt
  unfold shortResponse
  split <;> omega

theorem extended_response_bounds (v : Word) :
    1 ≤ extendedResponse v ∧ extendedResponse v ≤ 65536 := by
  have h := v.isLt
  unfold extendedResponse
  split <;> omega

theorem short_zero_sentinel : shortResponse 0 = 256 := by rfl
theorem extended_zero_sentinel : extendedResponse 0 = 65536 := by rfl

/-- No input can simultaneously satisfy two different structural cases. -/
theorem shape_unique (x : Input) (a b : CommandCase)
    (ha : Shape x a) (hb : Shape x b) : a = b := by
  cases a <;> cases b <;> simp_all [Shape] <;> omega

theorem shape_frame_bound (x : Input) (k : CommandCase) (h : Shape x k) :
    4 ≤ x.n ∧ x.n ≤ 65544 := by
  have hf := x.first.isLt
  have hw := x.word.isLt
  cases k <;> simp_all [Shape] <;> omega

/-- Bounds use subtraction first, matching reader acceptance. -/
theorem shape_payload_bounds (x : Input) (k : CommandCase) (h : Shape x k) :
    (layout x k).dataAt ≤ x.n ∧
    (layout x k).dataLength ≤ x.n - (layout x k).dataAt := by
  cases k <;> simp_all [Shape, layout] <;> omega

theorem shape_payload_sum_no_u32_wrap (x : Input) (k : CommandCase)
    (h : Shape x k) :
    (layout x k).dataAt + (layout x k).dataLength ≤ x.n ∧
    (layout x k).dataAt + (layout x k).dataLength < 4294967296 := by
  have hb := shape_payload_bounds x k h
  have hn := shape_frame_bound x k h
  omega

theorem layout_consumed (x : Input) (k : CommandCase) :
    (layout x k).consumed = x.n := by
  cases k <;> rfl

theorem layout_response_bounds (x : Input) (k : CommandCase) (r : Nat)
    (h : (layout x k).responseLength = some r) :
    1 ≤ r ∧ r ≤ 65536 ∧ r < 4294967296 := by
  have h1 := short_response_bounds x.first
  have h2 := short_response_bounds x.shortLe
  have h3 := extended_response_bounds x.word
  have h4 := extended_response_bounds x.extendedLe
  cases k <;> simp_all [layout] <;> omega

private theorem short_data_sound (x : Input) (r : Lengths)
    (hn : 5 < x.n) (hc : 0 < x.first.val)
    (h : shortData x = .ok r) :
    Shape x r.form ∧ r = layout x r.form := by
  unfold shortData at h
  split at h
  · cases h
  · split at h
    · cases h
      constructor
      · simp only [layout, Shape]
        omega
      · rfl
    · split at h
      · cases h
        constructor
        · simp only [layout, Shape]
          omega
        · rfl
      · cases h

private theorem extended_data_sound (x : Input) (r : Lengths)
    (hn : 7 < x.n) (hm : x.first.val = 0) (hc : 0 < x.word.val)
    (h : extendedData x = .ok r) :
    Shape x r.form ∧ r = layout x r.form := by
  unfold extendedData at h
  split at h
  · cases h
  · split at h
    · cases h
      constructor
      · simp only [layout, Shape]
        omega
      · rfl
    · split at h
      · cases h
      · split at h
        · cases h
          constructor
          · simp only [layout, Shape]
            omega
          · rfl
        · cases h

/-- Soundness is only for this handwritten pure model. -/
theorem decode_sound (x : Input) (r : Lengths) (h : decode x = .ok r) :
    Shape x r.form ∧ r = layout x r.form := by
  unfold decode at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
        exact ⟨by simp_all [Shape, layout], rfl⟩
      · split at h
        · cases h
          exact ⟨by simp_all [Shape, layout], rfl⟩
        · split at h
          · split at h
            · cases h
            · split at h
              · cases h
                exact ⟨by simp_all [Shape, layout], rfl⟩
              · split at h
                · cases h
                · exact extended_data_sound x r (by omega) (by assumption) (by omega) h
          · exact short_data_sound x r (by omega) (by omega) h

/-- Completeness of the declarative grammar for the pure branch model. -/
theorem decode_of_shape (x : Input) (k : CommandCase) (h : Shape x k) :
    decode x = .ok (layout x k) := by
  have hframe := shape_frame_bound x k h
  have hmax : ¬ 65544 < x.n := by omega
  have hheader : ¬ x.n < 4 := by omega
  cases k with
  | case1 =>
    have hn : x.n = 4 := h
    unfold decode
    rw [if_neg hmax, if_neg hheader, if_pos hn]
  | case2Short =>
    have hn : x.n = 5 := h
    have h4 : x.n ≠ 4 := by omega
    unfold decode
    rw [if_neg hmax, if_neg hheader, if_neg h4, if_pos hn]
  | case3Short =>
    rcases h with ⟨hc, hn⟩
    have h4 : x.n ≠ 4 := by omega
    have h5 : x.n ≠ 5 := by omega
    have hm : x.first.val ≠ 0 := by omega
    have hd : ¬ x.n - 5 < x.first.val := by omega
    have hr : x.n - (5 + x.first.val) = 0 := by omega
    unfold decode
    rw [if_neg hmax, if_neg hheader, if_neg h4, if_neg h5, if_neg hm]
    unfold shortData
    rw [if_neg hd, if_pos hr]
  | case4Short =>
    rcases h with ⟨hc, hn⟩
    have h4 : x.n ≠ 4 := by omega
    have h5 : x.n ≠ 5 := by omega
    have hm : x.first.val ≠ 0 := by omega
    have hd : ¬ x.n - 5 < x.first.val := by omega
    have hr0 : x.n - (5 + x.first.val) ≠ 0 := by omega
    have hr1 : x.n - (5 + x.first.val) = 1 := by omega
    unfold decode
    rw [if_neg hmax, if_neg hheader, if_neg h4, if_neg h5, if_neg hm]
    unfold shortData
    rw [if_neg hd, if_neg hr0, if_pos hr1]
  | case2Extended =>
    rcases h with ⟨hm, hn⟩
    have h4 : x.n ≠ 4 := by omega
    have h5 : x.n ≠ 5 := by omega
    have h7 : ¬ x.n < 7 := by omega
    unfold decode
    rw [if_neg hmax, if_neg hheader, if_neg h4, if_neg h5, if_pos hm,
      if_neg h7, if_pos hn]
  | case3Extended =>
    rcases h with ⟨hm, hc, hn⟩
    have h4 : x.n ≠ 4 := by omega
    have h5 : x.n ≠ 5 := by omega
    have h7 : ¬ x.n < 7 := by omega
    have hn7 : x.n ≠ 7 := by omega
    have hw : x.word.val ≠ 0 := by omega
    have hd : ¬ x.n - 7 < x.word.val := by omega
    have hr : x.n - (7 + x.word.val) = 0 := by omega
    unfold decode
    rw [if_neg hmax, if_neg hheader, if_neg h4, if_neg h5, if_pos hm,
      if_neg h7, if_neg hn7, if_neg hw]
    unfold extendedData
    rw [if_neg hd, if_pos hr]
  | case4Extended =>
    rcases h with ⟨hm, hc, hn⟩
    have h4 : x.n ≠ 4 := by omega
    have h5 : x.n ≠ 5 := by omega
    have h7 : ¬ x.n < 7 := by omega
    have hn7 : x.n ≠ 7 := by omega
    have hw : x.word.val ≠ 0 := by omega
    have hd : ¬ x.n - 7 < x.word.val := by omega
    have hr0 : x.n - (7 + x.word.val) ≠ 0 := by omega
    have hr1 : x.n - (7 + x.word.val) ≠ 1 := by omega
    have hr2 : x.n - (7 + x.word.val) = 2 := by omega
    unfold decode
    rw [if_neg hmax, if_neg hheader, if_neg h4, if_neg h5, if_pos hm,
      if_neg h7, if_neg hn7, if_neg hw]
    unfold extendedData
    rw [if_neg hd, if_neg hr0, if_neg hr1, if_pos hr2]

theorem decode_success_iff (x : Input) (k : CommandCase) :
    decode x = .ok (layout x k) ↔ Shape x k := by
  constructor
  · intro h
    have hs := (decode_sound x (layout x k) h).1
    cases k <;> simpa [layout] using hs
  · exact decode_of_shape x k

theorem decode_payload_safe (x : Input) (r : Lengths) (h : decode x = .ok r) :
    r.dataAt ≤ x.n ∧ r.dataLength ≤ x.n - r.dataAt ∧
    r.dataAt + r.dataLength < 4294967296 ∧ r.consumed = x.n := by
  rcases decode_sound x r h with ⟨hs, hr⟩
  have hb := shape_payload_bounds x r.form hs
  have hn := shape_payload_sum_no_u32_wrap x r.form hs
  have hc := layout_consumed x r.form
  have hat := congrArg Lengths.dataAt hr
  have hlen := congrArg Lengths.dataLength hr
  have hconsumed := (congrArg Lengths.consumed hr).trans hc
  rw [hat, hlen]
  exact ⟨hb.1, hb.2, hn.2, hconsumed⟩

/-- Logical positions used by the corresponding successful Oak branch. This
list is not an instrumented load trace and may contain duplicate positions. -/
def positions (x : Input) (k : CommandCase) : List Nat :=
  [0, 1, 2, 3] ++ match k with
  | .case1 => []
  | .case2Short | .case3Short => [4]
  | .case4Short => [4, x.n - 1]
  | .case2Extended | .case3Extended => [4, 5, 6]
  | .case4Extended => [4, 5, 6, x.n - 2, x.n - 1]

theorem positions_in_bounds (x : Input) (k : CommandCase)
    (h : Shape x k) (i : Nat) (hi : i ∈ positions x k) : i < x.n := by
  cases k <;> simp_all [Shape, positions] <;> omega

theorem positions_count (x : Input) (k : CommandCase) :
    (positions x k).length ≤ 9 := by
  cases k <;> simp [positions]

theorem reject_too_long (x : Input) (h : 65544 < x.n) :
    decode x = .error .tooLong := by simp [decode, h]

theorem reject_header (x : Input) (h : x.n < 4) :
    decode x = .error .truncatedHeader := by
  have hmax : ¬ 65544 < x.n := by omega
  unfold decode
  rw [if_neg hmax, if_pos h]

theorem reject_six_byte_marker (x : Input) (hn : x.n = 6)
    (hm : x.first.val = 0) : decode x = .error .truncatedLength := by
  simp [decode, hn, hm]

theorem reject_extended_zero_lc (x : Input) (hn : 7 < x.n)
    (hmax : x.n ≤ 65544) (hm : x.first.val = 0) (hw : x.word.val = 0) :
    decode x = .error .zeroDataLength := by
  have hmax' : ¬ 65544 < x.n := by omega
  have hheader : ¬ x.n < 4 := by omega
  have h4 : x.n ≠ 4 := by omega
  have h5 : x.n ≠ 5 := by omega
  have h7 : ¬ x.n < 7 := by omega
  have hn7 : x.n ≠ 7 := by omega
  unfold decode
  rw [if_neg hmax', if_neg hheader, if_neg h4, if_neg h5, if_pos hm,
    if_neg h7, if_neg hn7, if_pos hw]

theorem reject_short_data (x : Input) (hn : 5 < x.n) (hmax : x.n ≤ 65544)
    (hm : 0 < x.first.val) (hc : x.n - 5 < x.first.val) :
    decode x = .error .truncatedData := by
  have hmax' : ¬ 65544 < x.n := by omega
  have hheader : ¬ x.n < 4 := by omega
  have h4 : x.n ≠ 4 := by omega
  have h5 : x.n ≠ 5 := by omega
  have hm0 : x.first.val ≠ 0 := by omega
  unfold decode
  rw [if_neg hmax', if_neg hheader, if_neg h4, if_neg h5, if_neg hm0]
  unfold shortData
  rw [if_pos hc]

theorem reject_short_trailing (x : Input) (hn : 5 < x.n)
    (hmax : x.n ≤ 65544) (hm : 0 < x.first.val)
    (hc : 5 + x.first.val + 2 ≤ x.n) : decode x = .error .trailingBytes := by
  have hmax' : ¬ 65544 < x.n := by omega
  have hheader : ¬ x.n < 4 := by omega
  have h4 : x.n ≠ 4 := by omega
  have h5 : x.n ≠ 5 := by omega
  have hm0 : x.first.val ≠ 0 := by omega
  have hd : ¬ x.n - 5 < x.first.val := by omega
  have hr0 : x.n - (5 + x.first.val) ≠ 0 := by omega
  have hr1 : x.n - (5 + x.first.val) ≠ 1 := by omega
  unfold decode
  rw [if_neg hmax', if_neg hheader, if_neg h4, if_neg h5, if_neg hm0]
  unfold shortData
  rw [if_neg hd, if_neg hr0, if_neg hr1]

theorem reject_extended_data (x : Input) (hn : 7 < x.n)
    (hmax : x.n ≤ 65544) (hm : x.first.val = 0)
    (hc : 0 < x.word.val) (hd : x.n - 7 < x.word.val) :
    decode x = .error .truncatedData := by
  have hmax' : ¬ 65544 < x.n := by omega
  have hheader : ¬ x.n < 4 := by omega
  have h4 : x.n ≠ 4 := by omega
  have h5 : x.n ≠ 5 := by omega
  have h7 : ¬ x.n < 7 := by omega
  have hn7 : x.n ≠ 7 := by omega
  have hw0 : x.word.val ≠ 0 := by omega
  unfold decode
  rw [if_neg hmax', if_neg hheader, if_neg h4, if_neg h5, if_pos hm,
    if_neg h7, if_neg hn7, if_neg hw0]
  unfold extendedData
  rw [if_pos hd]

theorem reject_one_byte_extended_le (x : Input) (hm : x.first.val = 0)
    (hc : 0 < x.word.val) (hn : x.n = 8 + x.word.val) :
    decode x = .error .truncatedLength := by
  have hw := x.word.isLt
  have hmax' : ¬ 65544 < x.n := by omega
  have hheader : ¬ x.n < 4 := by omega
  have h4 : x.n ≠ 4 := by omega
  have h5 : x.n ≠ 5 := by omega
  have h7 : ¬ x.n < 7 := by omega
  have hn7 : x.n ≠ 7 := by omega
  have hw0 : x.word.val ≠ 0 := by omega
  have hd : ¬ x.n - 7 < x.word.val := by omega
  have hr0 : x.n - (7 + x.word.val) ≠ 0 := by omega
  have hr1 : x.n - (7 + x.word.val) = 1 := by omega
  unfold decode
  rw [if_neg hmax', if_neg hheader, if_neg h4, if_neg h5, if_pos hm,
    if_neg h7, if_neg hn7, if_neg hw0]
  unfold extendedData
  rw [if_neg hd, if_neg hr0, if_pos hr1]

theorem reject_extended_trailing (x : Input) (hmax : x.n ≤ 65544)
    (hm : x.first.val = 0) (hc : 0 < x.word.val)
    (hn : 7 + x.word.val + 3 ≤ x.n) : decode x = .error .trailingBytes := by
  have hmax' : ¬ 65544 < x.n := by omega
  have hheader : ¬ x.n < 4 := by omega
  have h4 : x.n ≠ 4 := by omega
  have h5 : x.n ≠ 5 := by omega
  have h7 : ¬ x.n < 7 := by omega
  have hn7 : x.n ≠ 7 := by omega
  have hw0 : x.word.val ≠ 0 := by omega
  have hd : ¬ x.n - 7 < x.word.val := by omega
  have hr0 : x.n - (7 + x.word.val) ≠ 0 := by omega
  have hr1 : x.n - (7 + x.word.val) ≠ 1 := by omega
  have hr2 : x.n - (7 + x.word.val) ≠ 2 := by omega
  unfold decode
  rw [if_neg hmax', if_neg hheader, if_neg h4, if_neg h5, if_pos hm,
    if_neg h7, if_neg hn7, if_neg hw0]
  unfold extendedData
  rw [if_neg hd, if_neg hr0, if_neg hr1, if_neg hr2]

/-- Pure frame preservation, by construction. This says nothing about the
Oak implementation's borrowed-view aliasing or compiled store behavior. -/
def decodeWithFrame (src : List Byte) : Except Error Lengths × List Byte :=
  (decodeBytes src, src)

theorem frame_unchanged (src : List Byte) : (decodeWithFrame src).2 = src := by rfl

theorem rejection_returns_no_command (src : List Byte) (e : Error)
    (h : decodeBytes src = .error e) : decodeWithFrame src = (.error e, src) := by
  simp [decodeWithFrame, h]

/- Concrete model controls. These declarations have NOT been checked. Their
expected fields are literal goldens, not calls to the layout constructor. -/
example : decode ⟨4, 0, 0, 0, 0⟩ = .ok ⟨.case1, 4, 0, none, 4⟩ := by rfl
example : decode ⟨5, 0, 0, 0, 0⟩ = .ok ⟨.case2Short, 5, 0, some 256, 5⟩ := by rfl
example : decode ⟨6, 1, 0, 0, 0⟩ = .ok ⟨.case3Short, 5, 1, none, 6⟩ := by rfl
example : decode ⟨7, 1, 0, 0, 0⟩ = .ok ⟨.case4Short, 5, 1, some 256, 7⟩ := by rfl
example : decode ⟨7, 0, 0, 0, 0⟩ = .ok ⟨.case2Extended, 7, 0, some 65536, 7⟩ := by rfl
example : decode ⟨8, 0, 1, 0, 0⟩ = .ok ⟨.case3Extended, 7, 1, none, 8⟩ := by rfl
example : decode ⟨10, 0, 1, 0, 0⟩ = .ok ⟨.case4Extended, 7, 1, some 65536, 10⟩ := by rfl
example : decode ⟨65544, 0, 65535, 0, 65535⟩ =
    .ok ⟨.case4Extended, 7, 65535, some 65535, 65544⟩ := by rfl
example : decode ⟨65545, 0, 0, 0, 0⟩ = .error .tooLong := by rfl
example : decode ⟨3, 0, 0, 0, 0⟩ = .error .truncatedHeader := by rfl
example : decode ⟨6, 0, 0, 0, 0⟩ = .error .truncatedLength := by rfl
example : decode ⟨8, 0, 0, 0, 0⟩ = .error .zeroDataLength := by rfl
example : decode ⟨6, 2, 0, 0, 0⟩ = .error .truncatedData := by rfl
example : decode ⟨8, 1, 0, 0, 0⟩ = .error .trailingBytes := by rfl
example : decode ⟨9, 0, 1, 0, 0⟩ = .error .truncatedLength := by rfl

end Oak.Stdlib.APDUModel
