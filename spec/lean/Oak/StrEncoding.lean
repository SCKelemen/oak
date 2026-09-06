import Oak.Utf8Validity

namespace Oak.StrEncoding

/-! # Phantom-encoded strings

Model for `docs/spec/70-strings.md`: `string = Str[Utf8]`, and encoding tags
are phantom — they change static identity while every `Str[E]` shares one
unit representation. Well-formedness is the per-encoding validity obligation
carried by the tag, so an unvalidated bytes-to-string construction is
unrepresentable in safe code, and the only implicit zero-copy retyping is
the direction proven validity-preserving (`Ascii → Utf8`).

This is the string instance of the phantom law proven generally in
`Oak.PhantomRepresentation`: retagging rebinds identity and preserves the
representation exactly. The v1 vocabulary carries the encodings the compiler
enforces today. -/

/-- Phantom encoding tags the compiler enforces today. -/
inductive Encoding where
  | utf8
  | ascii
  deriving DecidableEq, Repr

/-- A typed string value: code units plus the phantom tag. -/
structure Str where
  encoding : Encoding
  units : List Nat
  deriving Repr

/-- The validity obligation each encoding imposes on its units. -/
def UnitsValid : Encoding → List Nat → Prop
  | .utf8, units => Oak.Utf8Validity.Valid units
  | .ascii, units => ∀ b ∈ units, b ≤ 0x7F

/-- A well-formed string satisfies its own tag's obligation. Constructing
    `Str` with the utf8 tag therefore requires `Oak.Utf8Validity.Valid` —
    the forbidden unvalidated `from_bytes` has no well-formed image. -/
def WF (s : Str) : Prop := UnitsValid s.encoding s.units

/-- Retagging: the phantom conversion. -/
def retag (s : Str) (e : Encoding) : Str := { s with encoding := e }

/-- **Phantom identity preserves representation**: retagging changes the tag
    and nothing else — zero-copy by construction. -/
theorem retag_preserves_units (s : Str) (e : Encoding) :
    (retag s e).units = s.units := rfl

/-- **Retyping into utf8 is exactly a validity proof**: a retagged string is
    well-formed iff its unchanged units are valid UTF-8. -/
theorem retag_utf8_wf_iff (s : Str) :
    WF (retag s .utf8) ↔ Oak.Utf8Validity.Valid s.units := Iff.rfl

/-- **The one legal implicit widening**: ASCII units are valid UTF-8, so the
    `Ascii → Utf8` retype is validity-preserving — zero-copy and safe. -/
theorem ascii_retag_utf8_wf (s : Str) (h : WF s) (henc : s.encoding = .ascii) :
    WF (retag s .utf8) := by
  have hascii : ∀ b ∈ s.units, b ≤ 0x7F := by
    have := h
    unfold WF at this
    rw [henc] at this
    exact this
  exact Oak.Utf8Validity.ascii_valid s.units hascii

/-- The reverse direction is not validity-preserving: a well-formed utf8
    string with any non-ASCII unit has no well-formed ascii retype. -/
theorem utf8_retag_ascii_needs_ascii (s : Str) {b : Nat}
    (hmem : b ∈ s.units) (hbig : 0x7F < b) :
    ¬ WF (retag s .ascii) := by
  intro hwf
  exact absurd (hwf b hmem) (by omega)

end Oak.StrEncoding
