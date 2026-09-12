import Std.Tactic.BVDecide

/-!
# Word-parallel decimal digits

`stdlib/json.oak` scans integers a word at a time (docs/spec/71-codecs.md
section 19): a mask marks the bytes that are not decimal digits, the run of
digit bytes at the front of the word is counted with no branch and no
count-trailing-zeros instruction, and eight digits — or the run, moved to
the high bytes over ASCII zeros — become a number in three multiply-and-add
steps. Every one of those is a fact about one 64-bit word, decided here by
bit-blasting, with the carries between lanes that the additive tricks
produce included in the statement.
-/

namespace Oak.JsonDigits

/-- `json_non_digit_mask`: bit 7 of every byte that is not an ASCII digit. -/
def nonDigitMask (w : BitVec 64) : BitVec 64 :=
  ((w + 0x4646464646464646#64) ||| (w - 0x3030303030303030#64)) &&& 0x8080808080808080#64

/-- Byte `i` of a word, the first digit in the low byte. -/
def byteAt (w : BitVec 64) (i : Nat) : BitVec 8 := BitVec.extractLsb' (8 * i) 8 w

def isDigit (b : BitVec 8) : Bool := 0x30#8 ≤ b && b ≤ 0x39#8

/-- **Soundness of the mask.** A lane the mask leaves clear holds a digit,
whatever the other lanes carry into it. (The converse fails: a carry can
mark a digit lane, which only shortens a run.) -/
theorem non_digit_mask_sound (w : BitVec 64) :
    ((nonDigitMask w).getLsbD 7 = false → isDigit (byteAt w 0) = true) ∧
    ((nonDigitMask w).getLsbD 15 = false → isDigit (byteAt w 1) = true) ∧
    ((nonDigitMask w).getLsbD 23 = false → isDigit (byteAt w 2) = true) ∧
    ((nonDigitMask w).getLsbD 31 = false → isDigit (byteAt w 3) = true) ∧
    ((nonDigitMask w).getLsbD 39 = false → isDigit (byteAt w 4) = true) ∧
    ((nonDigitMask w).getLsbD 47 = false → isDigit (byteAt w 5) = true) ∧
    ((nonDigitMask w).getLsbD 55 = false → isDigit (byteAt w 6) = true) ∧
    ((nonDigitMask w).getLsbD 63 = false → isDigit (byteAt w 7) = true) := by
  unfold nonDigitMask byteAt isDigit
  bv_decide

/-- `json_word_value`: eight ASCII digits to their value. -/
def wordValue (w : BitVec 64) : BitVec 64 :=
  let digits := w &&& 0x0F0F0F0F0F0F0F0F#64
  let pairs := ((digits * 10) + (digits >>> 8)) &&& 0x00FF00FF00FF00FF#64
  let quads := ((pairs * 100) + (pairs >>> 16)) &&& 0x0000FFFF0000FFFF#64
  ((quads * 10000) + (quads >>> 32)) &&& 0xFFFFFFFF#64

/-- The decimal value of byte `i`. -/
def digitValue (w : BitVec 64) (i : Nat) : BitVec 64 := (byteAt w i - 0x30#8).setWidth 64

/-- **Eight digits.** A word the mask clears entirely reads as its eight
digits, most significant first. -/
theorem word_value (w : BitVec 64) (h : nonDigitMask w = 0) :
    wordValue w = (((((((digitValue w 0) * 10 + digitValue w 1) * 10 + digitValue w 2) * 10 + digitValue w 3) * 10 + digitValue w 4) * 10 + digitValue w 5) * 10 + digitValue w 6) * 10 + digitValue w 7 := by
  unfold wordValue digitValue byteAt nonDigitMask at *
  bv_decide (config := { timeout := 300 })

/-- The partial word of `json_scan_integer`: the first `k` bytes moved to
the high end, ASCII zeros below them. -/
def partialWord (w : BitVec 64) (k : Nat) : BitVec 64 :=
  (w <<< (8 * (8 - k))) ||| (0x3030303030303030#64 >>> (8 * k))

/-! **The run's value.** For a run of `k` digits, `1 ≤ k ≤ 7`, the partial
word reads as exactly those digits. -/

theorem partial_value_1 (w : BitVec 64) (h0 : isDigit (byteAt w 0) = true) :
    wordValue (partialWord w 1) = digitValue w 0 := by
  unfold wordValue partialWord digitValue byteAt isDigit at *
  bv_decide (config := { timeout := 300 })

theorem partial_value_2 (w : BitVec 64) (h0 : isDigit (byteAt w 0) = true) (h1 : isDigit (byteAt w 1) = true) :
    wordValue (partialWord w 2) = (digitValue w 0) * 10 + digitValue w 1 := by
  unfold wordValue partialWord digitValue byteAt isDigit at *
  bv_decide (config := { timeout := 300 })

theorem partial_value_3 (w : BitVec 64) (h0 : isDigit (byteAt w 0) = true) (h1 : isDigit (byteAt w 1) = true) (h2 : isDigit (byteAt w 2) = true) :
    wordValue (partialWord w 3) = ((digitValue w 0) * 10 + digitValue w 1) * 10 + digitValue w 2 := by
  unfold wordValue partialWord digitValue byteAt isDigit at *
  bv_decide (config := { timeout := 300 })

theorem partial_value_4 (w : BitVec 64) (h0 : isDigit (byteAt w 0) = true) (h1 : isDigit (byteAt w 1) = true) (h2 : isDigit (byteAt w 2) = true) (h3 : isDigit (byteAt w 3) = true) :
    wordValue (partialWord w 4) = (((digitValue w 0) * 10 + digitValue w 1) * 10 + digitValue w 2) * 10 + digitValue w 3 := by
  unfold wordValue partialWord digitValue byteAt isDigit at *
  bv_decide (config := { timeout := 300 })

theorem partial_value_5 (w : BitVec 64) (h0 : isDigit (byteAt w 0) = true) (h1 : isDigit (byteAt w 1) = true) (h2 : isDigit (byteAt w 2) = true) (h3 : isDigit (byteAt w 3) = true) (h4 : isDigit (byteAt w 4) = true) :
    wordValue (partialWord w 5) = ((((digitValue w 0) * 10 + digitValue w 1) * 10 + digitValue w 2) * 10 + digitValue w 3) * 10 + digitValue w 4 := by
  unfold wordValue partialWord digitValue byteAt isDigit at *
  bv_decide (config := { timeout := 300 })

theorem partial_value_6 (w : BitVec 64) (h0 : isDigit (byteAt w 0) = true) (h1 : isDigit (byteAt w 1) = true) (h2 : isDigit (byteAt w 2) = true) (h3 : isDigit (byteAt w 3) = true) (h4 : isDigit (byteAt w 4) = true) (h5 : isDigit (byteAt w 5) = true) :
    wordValue (partialWord w 6) = (((((digitValue w 0) * 10 + digitValue w 1) * 10 + digitValue w 2) * 10 + digitValue w 3) * 10 + digitValue w 4) * 10 + digitValue w 5 := by
  unfold wordValue partialWord digitValue byteAt isDigit at *
  bv_decide (config := { timeout := 300 })

theorem partial_value_7 (w : BitVec 64) (h0 : isDigit (byteAt w 0) = true) (h1 : isDigit (byteAt w 1) = true) (h2 : isDigit (byteAt w 2) = true) (h3 : isDigit (byteAt w 3) = true) (h4 : isDigit (byteAt w 4) = true) (h5 : isDigit (byteAt w 5) = true) (h6 : isDigit (byteAt w 6) = true) :
    wordValue (partialWord w 7) = ((((((digitValue w 0) * 10 + digitValue w 1) * 10 + digitValue w 2) * 10 + digitValue w 3) * 10 + digitValue w 4) * 10 + digitValue w 5) * 10 + digitValue w 6 := by
  unfold wordValue partialWord digitValue byteAt isDigit at *
  bv_decide (config := { timeout := 300 })

/-! ## The four-byte tail

`json_scan_integer` takes a tail of four to seven bytes through one 32-bit
word with the same three functions. -/

def nonDigitMask32 (w : BitVec 32) : BitVec 32 :=
  ((w + 0x46464646#32) ||| (w - 0x30303030#32)) &&& 0x80808080#32

def byteAt32 (w : BitVec 32) (i : Nat) : BitVec 8 := BitVec.extractLsb' (8 * i) 8 w

theorem non_digit_mask32_sound (w : BitVec 32) :
    ((nonDigitMask32 w).getLsbD 7 = false → isDigit (byteAt32 w 0) = true) ∧
    ((nonDigitMask32 w).getLsbD 15 = false → isDigit (byteAt32 w 1) = true) ∧
    ((nonDigitMask32 w).getLsbD 23 = false → isDigit (byteAt32 w 2) = true) ∧
    ((nonDigitMask32 w).getLsbD 31 = false → isDigit (byteAt32 w 3) = true) := by
  unfold nonDigitMask32 byteAt32 isDigit
  bv_decide

def wordValue32 (w : BitVec 32) : BitVec 32 :=
  let digits := w &&& 0x0F0F0F0F#32
  let pairs := ((digits * 10) + (digits >>> 8)) &&& 0x00FF00FF#32
  ((pairs * 100) + (pairs >>> 16)) &&& 0xFFFF#32

def digitValue32 (w : BitVec 32) (i : Nat) : BitVec 32 := (byteAt32 w i - 0x30#8).setWidth 32

theorem word_value32 (w : BitVec 32) (h : nonDigitMask32 w = 0) :
    wordValue32 w = (((digitValue32 w 0) * 10 + digitValue32 w 1) * 10 + digitValue32 w 2) * 10 + digitValue32 w 3 := by
  unfold wordValue32 digitValue32 byteAt32 nonDigitMask32 at *
  bv_decide

def partialWord32 (w : BitVec 32) (k : Nat) : BitVec 32 :=
  (w <<< (8 * (4 - k))) ||| (0x30303030#32 >>> (8 * k))

theorem partial_value32_1 (w : BitVec 32) (h0 : isDigit (byteAt32 w 0) = true) :
    wordValue32 (partialWord32 w 1) = digitValue32 w 0 := by
  unfold wordValue32 partialWord32 digitValue32 byteAt32 isDigit at *
  bv_decide

theorem partial_value32_2 (w : BitVec 32) (h0 : isDigit (byteAt32 w 0) = true) (h1 : isDigit (byteAt32 w 1) = true) :
    wordValue32 (partialWord32 w 2) = (digitValue32 w 0) * 10 + digitValue32 w 1 := by
  unfold wordValue32 partialWord32 digitValue32 byteAt32 isDigit at *
  bv_decide

theorem partial_value32_3 (w : BitVec 32) (h0 : isDigit (byteAt32 w 0) = true) (h1 : isDigit (byteAt32 w 1) = true) (h2 : isDigit (byteAt32 w 2) = true) :
    wordValue32 (partialWord32 w 3) = ((digitValue32 w 0) * 10 + digitValue32 w 1) * 10 + digitValue32 w 2 := by
  unfold wordValue32 partialWord32 digitValue32 byteAt32 isDigit at *
  bv_decide

/-! **Digits at a known extent** (`json_digits_at`). When a structural
index gives a number's extent, the reader parses it from its own bytes:
`n ≤ 8` digits are the partial word `partialWord w n` (the theorems above
give its value); nine to sixteen digits are one full word and a partial
word combined as `wordValue w * 10^(n-8) + wordValue (partialWord w2 (n-8))`
in 64-bit arithmetic. The bound below is what makes that arithmetic exact:
a word of eight digits reads below 10^8, so the combination stays below
10^16 < 2^64 and no operation wraps. -/
theorem word_value_bound (w : BitVec 64) (h : nonDigitMask w = 0) :
    wordValue w ≤ 99999999#64 := by
  unfold wordValue nonDigitMask at *
  bv_decide (config := { timeout := 300 })

theorem two_words_fit (a b : BitVec 64) (ha : a ≤ 99999999#64) (hb : b ≤ 99999999#64) (k : Nat) (hk : k ≤ 8) :
    a.toNat * 10 ^ k + b.toNat < 2 ^ 64 := by
  have ha' : a.toNat ≤ 99999999 := by
    have := BitVec.le_def.mp ha
    simpa using this
  have hb' : b.toNat ≤ 99999999 := by
    have := BitVec.le_def.mp hb
    simpa using this
  have hp : 10 ^ k ≤ 10 ^ 8 := Nat.pow_le_pow_right (by decide) hk
  have : a.toNat * 10 ^ k ≤ 99999999 * 10 ^ 8 := Nat.mul_le_mul ha' hp
  omega

end Oak.JsonDigits
