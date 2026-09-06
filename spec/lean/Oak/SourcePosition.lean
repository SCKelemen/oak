namespace Oak.SourcePosition

/-- UTF-8 width for a valid Unicode scalar value, modeled by scalar range. -/
def utf8Width (scalar : Nat) : Nat :=
  if scalar ≤ 127 then 1
  else if scalar ≤ 2047 then 2
  else if scalar ≤ 65535 then 3
  else 4

/-- UTF-16 code-unit width for a valid Unicode scalar value. -/
def utf16Width (scalar : Nat) : Nat :=
  if scalar ≤ 65535 then 1 else 2

structure Position where
  byteOffset : Nat
  utf16Column : Nat
  deriving DecidableEq, Repr

def advance (p : Position) (scalar : Nat) : Position :=
  { byteOffset := p.byteOffset + utf8Width scalar
    utf16Column := p.utf16Column + utf16Width scalar }

def advanceText : Position -> List Nat -> Position
  | p, [] => p
  | p, scalar :: rest => advanceText (advance p scalar) rest

def utf8Bytes : List Nat -> Nat
  | [] => 0
  | scalar :: rest => utf8Width scalar + utf8Bytes rest

def utf16Units : List Nat -> Nat
  | [] => 0
  | scalar :: rest => utf16Width scalar + utf16Units rest

theorem ascii_utf8_width (scalar : Nat) (h : scalar ≤ 127) :
    utf8Width scalar = 1 := by
  simp [utf8Width, h]

theorem two_byte_utf8_width (scalar : Nat)
    (hlo : 127 < scalar) (hhi : scalar ≤ 2047) :
    utf8Width scalar = 2 := by
  have hn : ¬ scalar ≤ 127 := Nat.not_le_of_lt hlo
  simp [utf8Width, hn, hhi]

theorem three_byte_utf8_width (scalar : Nat)
    (hlo : 2047 < scalar) (hhi : scalar ≤ 65535) :
    utf8Width scalar = 3 := by
  have h127 : ¬ scalar ≤ 127 := by omega
  have h2047 : ¬ scalar ≤ 2047 := Nat.not_le_of_lt hlo
  simp [utf8Width, h127, h2047, hhi]

theorem four_byte_utf8_width (scalar : Nat)
    (hlo : 65535 < scalar) :
    utf8Width scalar = 4 := by
  have h127 : ¬ scalar ≤ 127 := by omega
  have h2047 : ¬ scalar ≤ 2047 := by omega
  have h65535 : ¬ scalar ≤ 65535 := Nat.not_le_of_lt hlo
  simp [utf8Width, h127, h2047, h65535]

theorem bmp_utf16_width (scalar : Nat) (h : scalar ≤ 65535) :
    utf16Width scalar = 1 := by
  simp [utf16Width, h]

theorem supplementary_utf16_width (scalar : Nat) (h : 65535 < scalar) :
    utf16Width scalar = 2 := by
  have hn : ¬ scalar ≤ 65535 := Nat.not_le_of_lt h
  simp [utf16Width, hn]

theorem advanceText_append (p : Position) (left right : List Nat) :
    advanceText p (left ++ right) = advanceText (advanceText p left) right := by
  induction left generalizing p with
  | nil => rfl
  | cons scalar rest ih =>
      simp [advanceText, ih]

theorem advanceText_byteOffset (p : Position) (text : List Nat) :
    (advanceText p text).byteOffset = p.byteOffset + utf8Bytes text := by
  induction text generalizing p with
  | nil => simp [advanceText, utf8Bytes]
  | cons scalar rest ih =>
      simp [advanceText, advance, utf8Bytes, ih, Nat.add_assoc]

theorem advanceText_utf16Column (p : Position) (text : List Nat) :
    (advanceText p text).utf16Column = p.utf16Column + utf16Units text := by
  induction text generalizing p with
  | nil => simp [advanceText, utf16Units]
  | cons scalar rest ih =>
      simp [advanceText, advance, utf16Units, ih, Nat.add_assoc]

theorem byteOffset_monotone (p : Position) (text : List Nat) :
    p.byteOffset ≤ (advanceText p text).byteOffset := by
  rw [advanceText_byteOffset]
  exact Nat.le_add_right p.byteOffset (utf8Bytes text)

theorem utf16Column_monotone (p : Position) (text : List Nat) :
    p.utf16Column ≤ (advanceText p text).utf16Column := by
  rw [advanceText_utf16Column]
  exact Nat.le_add_right p.utf16Column (utf16Units text)

/-- ASCII prefixes have identical byte and UTF-16 widths. -/
def AllAscii : List Nat -> Prop
  | [] => True
  | scalar :: rest => scalar ≤ 127 ∧ AllAscii rest

theorem ascii_widths_equal (text : List Nat) (h : AllAscii text) :
    utf8Bytes text = utf16Units text := by
  induction text with
  | nil => rfl
  | cons scalar rest ih =>
      simp [AllAscii] at h
      simp [utf8Bytes, utf16Units, ascii_utf8_width scalar h.1,
        bmp_utf16_width scalar (Nat.le_trans h.1 (by decide : 127 ≤ 65535)),
        ih h.2]

end Oak.SourcePosition
