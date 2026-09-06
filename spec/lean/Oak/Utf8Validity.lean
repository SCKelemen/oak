import Oak.SourcePosition

namespace Oak.Utf8Validity

set_option maxRecDepth 8192

/-! # UTF-8 validity

Model for `docs/spec/70-strings.md`: `string` values are valid UTF-8, and
validity enters the system at the source decoder. `Seq` is the Unicode
standard's Table 3-7, one constructor per well-formed lead-byte class:
truncated sequences, stray continuations, overlong encodings, surrogates,
and values above U+10FFFF are unrepresentable — the specification fails
closed by construction.

The compiler's `source.ValidateUTF8` is the executable transliteration of
these brackets, differentially tested against an independent validator. The
length theorem ties this byte model to `Oak.SourcePosition.utf8Width`: a
sequence's byte count equals the canonical width of the scalar it encodes,
which is precisely the absence of overlong encodings — one fact, two
projections. -/

def scalar2 (b0 b1 : Nat) : Nat := (b0 - 0xC0) * 0x40 + (b1 - 0x80)

def scalar3 (b0 b1 b2 : Nat) : Nat :=
  ((b0 - 0xE0) * 0x40 + (b1 - 0x80)) * 0x40 + (b2 - 0x80)

def scalar4 (b0 b1 b2 b3 : Nat) : Nat :=
  (((b0 - 0xF0) * 0x40 + (b1 - 0x80)) * 0x40 + (b2 - 0x80)) * 0x40 + (b3 - 0x80)

/-- `Seq bytes scalar`: `bytes` is one complete well-formed UTF-8 sequence
    encoding `scalar` (Unicode Table 3-7). -/
inductive Seq : List Nat → Nat → Prop
  | ascii {b0 : Nat} :
      b0 ≤ 0x7F → Seq [b0] b0
  | two {b0 b1 : Nat} :
      0xC2 ≤ b0 → b0 ≤ 0xDF → 0x80 ≤ b1 → b1 ≤ 0xBF →
      Seq [b0, b1] (scalar2 b0 b1)
  | threeE0 {b1 b2 : Nat} :
      0xA0 ≤ b1 → b1 ≤ 0xBF → 0x80 ≤ b2 → b2 ≤ 0xBF →
      Seq [0xE0, b1, b2] (scalar3 0xE0 b1 b2)
  | threeMid {b0 b1 b2 : Nat} :
      0xE1 ≤ b0 → b0 ≤ 0xEC → 0x80 ≤ b1 → b1 ≤ 0xBF → 0x80 ≤ b2 → b2 ≤ 0xBF →
      Seq [b0, b1, b2] (scalar3 b0 b1 b2)
  | threeED {b1 b2 : Nat} :
      0x80 ≤ b1 → b1 ≤ 0x9F → 0x80 ≤ b2 → b2 ≤ 0xBF →
      Seq [0xED, b1, b2] (scalar3 0xED b1 b2)
  | threeHigh {b0 b1 b2 : Nat} :
      0xEE ≤ b0 → b0 ≤ 0xEF → 0x80 ≤ b1 → b1 ≤ 0xBF → 0x80 ≤ b2 → b2 ≤ 0xBF →
      Seq [b0, b1, b2] (scalar3 b0 b1 b2)
  | fourF0 {b1 b2 b3 : Nat} :
      0x90 ≤ b1 → b1 ≤ 0xBF → 0x80 ≤ b2 → b2 ≤ 0xBF → 0x80 ≤ b3 → b3 ≤ 0xBF →
      Seq [0xF0, b1, b2, b3] (scalar4 0xF0 b1 b2 b3)
  | fourMid {b0 b1 b2 b3 : Nat} :
      0xF1 ≤ b0 → b0 ≤ 0xF3 → 0x80 ≤ b1 → b1 ≤ 0xBF → 0x80 ≤ b2 → b2 ≤ 0xBF →
      0x80 ≤ b3 → b3 ≤ 0xBF →
      Seq [b0, b1, b2, b3] (scalar4 b0 b1 b2 b3)
  | fourF4 {b1 b2 b3 : Nat} :
      0x80 ≤ b1 → b1 ≤ 0x8F → 0x80 ≤ b2 → b2 ≤ 0xBF → 0x80 ≤ b3 → b3 ≤ 0xBF →
      Seq [0xF4, b1, b2, b3] (scalar4 0xF4 b1 b2 b3)

/-- Unicode scalar values: at most U+10FFFF and never a surrogate. -/
def ScalarValue (n : Nat) : Prop :=
  n ≤ 0x10FFFF ∧ ¬(0xD800 ≤ n ∧ n ≤ 0xDFFF)

/-- **Fail-closed by construction**: every well-formed sequence encodes a
    Unicode scalar value — surrogates and out-of-range values are
    unrepresentable. -/
theorem seq_yields_scalar {bytes : List Nat} {s : Nat}
    (h : Seq bytes s) : ScalarValue s := by
  cases h <;> simp only [ScalarValue, scalar2, scalar3, scalar4] <;> omega

/-- **No overlong encodings**: a sequence's byte count equals the canonical
    UTF-8 width of its scalar (`Oak.SourcePosition.utf8Width`), tying this
    byte-level model to the width model used for source positions. -/
theorem seq_length_canonical {bytes : List Nat} {s : Nat}
    (h : Seq bytes s) : bytes.length = Oak.SourcePosition.utf8Width s := by
  cases h with
  | ascii hb =>
    rw [Oak.SourcePosition.ascii_utf8_width _ hb]
    rfl
  | two h0 h0' h1 h1' =>
    rw [Oak.SourcePosition.two_byte_utf8_width _
      (by unfold scalar2; omega) (by unfold scalar2; omega)]
    rfl
  | threeE0 h1 h1' h2 h2' =>
    rw [Oak.SourcePosition.three_byte_utf8_width _
      (by unfold scalar3; omega) (by unfold scalar3; omega)]
    rfl
  | threeMid h0 h0' h1 h1' h2 h2' =>
    rw [Oak.SourcePosition.three_byte_utf8_width _
      (by unfold scalar3; omega) (by unfold scalar3; omega)]
    rfl
  | threeED h1 h1' h2 h2' =>
    rw [Oak.SourcePosition.three_byte_utf8_width _
      (by unfold scalar3; omega) (by unfold scalar3; omega)]
    rfl
  | threeHigh h0 h0' h1 h1' h2 h2' =>
    rw [Oak.SourcePosition.three_byte_utf8_width _
      (by unfold scalar3; omega) (by unfold scalar3; omega)]
    rfl
  | fourF0 h1 h1' h2 h2' h3 h3' =>
    rw [Oak.SourcePosition.four_byte_utf8_width _
      (by unfold scalar4; omega)]
    rfl
  | fourMid h0 h0' h1 h1' h2 h2' h3 h3' =>
    rw [Oak.SourcePosition.four_byte_utf8_width _
      (by unfold scalar4; omega)]
    rfl
  | fourF4 h1 h1' h2 h2' h3 h3' =>
    rw [Oak.SourcePosition.four_byte_utf8_width _
      (by unfold scalar4; omega)]
    rfl

/-- Sequences are 1..4 bytes long. -/
theorem seq_length_bounds {bytes : List Nat} {s : Nat}
    (h : Seq bytes s) : 1 ≤ bytes.length ∧ bytes.length ≤ 4 := by
  cases h <;> simp

/-- A byte string is valid UTF-8 when it is a concatenation of well-formed
    sequences. -/
inductive Valid : List Nat → Prop
  | nil : Valid []
  | app {seq rest : List Nat} {s : Nat} :
      Seq seq s → Valid rest → Valid (seq ++ rest)

/-- ASCII text is valid UTF-8. -/
theorem ascii_valid (bytes : List Nat) (h : ∀ b ∈ bytes, b ≤ 0x7F) :
    Valid bytes := by
  induction bytes with
  | nil => exact Valid.nil
  | cons b rest ih =>
    have hb : b ≤ 0x7F := h b (by simp)
    have hrest : ∀ x ∈ rest, x ≤ 0x7F := fun x hx => h x (by simp [hx])
    exact Valid.app (Seq.ascii hb) (ih hrest)

/-- Every scalar of a valid string is a Unicode scalar value: validity is
    compositional, so downstream string operations can rely on scalar
    validity without re-validating. -/
theorem valid_pieces_are_scalars {seq rest : List Nat} {s : Nat}
    (hseq : Seq seq s) (_ : Valid rest) : ScalarValue s :=
  seq_yields_scalar hseq

end Oak.Utf8Validity
