import Std.Tactic

/-!
# Core Wasm LEB prefixes

Mathematical prefix grammar and executable decoder for the integer encodings
in WebAssembly/spec@779957d81feca2ec6a372c40a9130e28ef390645,
document/core/binary/values.rst. Padded encodings within the width budget are
legal. Signed values are mathematical integers, not unsigned accumulator bits.

This is not yet a refinement of wasm/check/read.go's OR/shift accumulator,
mutable cursor, error positions, or the full module decoder/type validator.
Production-generated finite examples pin the successful word/cursor results
and failure decisions separately. No source-to-Wasm verdict follows from this.
-/

namespace Oak.WasmLEB

def inRange (width : Nat) (signed : Bool) (value : Int) : Prop :=
  if signed then
    -(2 ^ (width - 1) : Int) ≤ value ∧ value < (2 ^ (width - 1) : Int)
  else
    0 ≤ value ∧ value < (2 ^ width : Int)

instance (width : Nat) (signed : Bool) (value : Int) :
    Decidable (inRange width signed value) := by unfold inRange; infer_instance

def terminalValue (signed : Bool) (b : UInt8) : Int :=
  if signed && decide (64 ≤ b.toNat) then (b.toNat : Int) - 128
  else (b.toNat : Int)

/-- Declarative grammar for exactly one integer (no trailing bytes).
The terminal range condition expresses the unused-bit rule; continuation
decreases the remaining width by seven. -/
inductive Encoding : Nat → Bool → List UInt8 → Int → Prop where
  | terminal {width signed b}
      (positive : 0 < width) (stop : b.toNat < 128)
      (range : inRange width signed (terminalValue signed b)) :
      Encoding width signed [b] (terminalValue signed b)
  | continuation {width signed b bytes value}
      (budget : 7 < width) (more : 128 ≤ b.toNat)
      (tail : Encoding (width - 7) signed bytes value) :
      Encoding width signed (b :: bytes) ((b.toNat % 128 : Nat) + 128 * value)

/-- Executable prefix decoder. Recursion consumes a byte; width also decreases
on every continuation, so even arbitrarily long lists cannot extend the budget. -/
def decode (width : Nat) (signed : Bool) (bytes : List UInt8) :
    Option (Int × List UInt8) :=
  match bytes with
  | [] => none
  | b :: rest =>
    if width = 0 then none
    else if b.toNat < 128 then
      if inRange width signed (terminalValue signed b) then
        some (terminalValue signed b, rest)
      else none
    else if width ≤ 7 then none
    else do
      let (value, suffix) ← decode (width - 7) signed rest
      pure ((b.toNat % 128 : Nat) + 128 * value, suffix)

theorem decode_complete {width signed bytes value}
    (h : Encoding width signed bytes value) (suffix : List UInt8) :
    decode width signed (bytes ++ suffix) = some (value, suffix) := by
  induction h with
  | terminal positive stop range =>
    simp [decode, Nat.ne_of_gt positive, stop, range]
  | @continuation w s b bs v budget more tail ih =>
    simp [decode, show w ≠ 0 from by omega,
      show ¬ b.toNat < 128 from by omega, show ¬ w ≤ 7 from by omega, ih]

theorem decode_sound {width signed bytes value suffix}
    (h : decode width signed bytes = some (value, suffix)) :
    ∃ front, bytes = front ++ suffix ∧ Encoding width signed front value := by
  induction bytes generalizing width value suffix with
  | nil => simp [decode] at h
  | cons b rest ih =>
    simp only [decode] at h
    split at h
    next => simp at h
    next positive =>
      split at h
      next stop =>
        split at h
        next range =>
          cases h
          exact ⟨[b], rfl, .terminal (by omega) stop range⟩
        next => simp at h
      next more =>
        split at h
        next => simp at h
        next budget =>
          cases hd : decode (width - 7) signed rest with
          | none => simp [hd] at h
          | some result =>
            obtain ⟨v, s⟩ := result
            simp only [hd, pure] at h
            cases h
            obtain ⟨front, hp, he⟩ := ih hd
            exact ⟨b :: front, by simp [hp], .continuation (by omega) (by omega) he⟩

theorem decode_iff {width signed bytes value suffix} :
    decode width signed bytes = some (value, suffix) ↔
      ∃ front, bytes = front ++ suffix ∧ Encoding width signed front value := by
  constructor
  · exact decode_sound
  · rintro ⟨front, rfl, h⟩
    exact decode_complete h suffix

theorem Encoding.nonempty {width signed bytes value}
    (h : Encoding width signed bytes value) : bytes ≠ [] := by
  cases h <;> simp

/-- Equivalent to the usual ceiling(width/7) byte budget, without division. -/
theorem Encoding.byte_budget {width signed bytes value}
    (h : Encoding width signed bytes value) : 7 * bytes.length ≤ width + 6 := by
  induction h with
  | terminal positive => simp; omega
  | continuation budget more tail ih => simp only [List.length_cons]; omega

private theorem pow_seven (width : Nat) (h : 7 ≤ width) :
    (2 ^ width : Int) = 128 * 2 ^ (width - 7) := by
  calc
    (2 ^ width : Int) = 2 ^ (7 + (width - 7)) := by
      congr 1; omega
    _ = 128 * 2 ^ (width - 7) := by rw [Int.pow_add]; rfl

theorem Encoding.range {width signed bytes value}
    (h : Encoding width signed bytes value) : inRange width signed value := by
  induction h with
  | terminal positive stop range => exact range
  | @continuation width signed b bytes value budget more tail ih =>
    have hlo : 0 ≤ ((b.toNat % 128 : Nat) : Int) := Int.natCast_nonneg _
    have hhi : ((b.toNat % 128 : Nat) : Int) < 128 := by
      have := Nat.mod_lt b.toNat (by decide : 0 < 128)
      omega
    cases signed with
    | false =>
      simp only [inRange, Bool.false_eq_true, ↓reduceIte] at ih ⊢
      rw [pow_seven width (by omega)]
      omega
    | true =>
      simp only [inRange, ↓reduceIte] at ih ⊢
      have he : width - 1 - 7 = width - 7 - 1 := by omega
      rw [pow_seven (width - 1) (by omega), he]
      omega

/-- The decoded suffix is genuinely untouched: appending any bytes after it
does not alter either the value or the already-consumed prefix. -/
theorem decode_append {width signed bytes value suffix}
    (h : decode width signed bytes = some (value, suffix)) (extra : List UInt8) :
    decode width signed (bytes ++ extra) = some (value, suffix ++ extra) := by
  obtain ⟨front, rfl, he⟩ := decode_sound h
  simpa [List.append_assoc] using decode_complete he (suffix ++ extra)

/-- Boundary observed by the Go oracle: sign-extended 64-bit word and number
of bytes consumed on success. A refusal deliberately models no error cursor. -/
def decodeWord (width : Nat) (signed : Bool) (bytes : List UInt8) :
    Option (Nat × Nat) := do
  let (value, suffix) ← decode width signed bytes
  pure ((BitVec.ofInt 64 value).toNat, bytes.length - suffix.length)

example : decodeWord 32 false [128, 0, 42] = some (0, 2) := by decide
example : decodeWord 32 true [255, 255, 255, 255, 127] =
    some (18446744073709551615, 5) := by decide
example : decodeWord 32 false [128, 128, 128, 128, 16] = none := by decide
example : decodeWord 64 true [128, 128, 128, 128, 128, 128, 128, 128, 128, 127] =
    some (9223372036854775808, 10) := by decide

end Oak.WasmLEB
