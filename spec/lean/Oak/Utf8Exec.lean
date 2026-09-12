/-
Executable UTF-8 validity for the extraction (docs/spec/95-extraction.md
section 3). `Oak.Utf8Validity.Valid` states well-formedness as a relation
over byte lists; the compiler's `is_valid_utf8` intrinsic decides it over a
view. The extraction renders the intrinsic as `Oak.Utf8Exec.valid`, the
same decision procedure over the `Array UInt8` carrier: Unicode Table 3-7
(one to four bytes, no overlongs, no surrogates, nothing above U+10FFFF),
one scalar per step, stopping at the first ill-formed sequence.

The relation between this procedure and `Oak.Utf8Validity.Valid` is listed
in `docs/spec/95-extraction.md` section 7 as remaining work; the
faithfulness harness compares this definition with the compiled intrinsic
on random inputs.
-/

namespace Oak.Utf8Exec

/-- The byte at `i`, or zero past the end (the extraction's read choice). -/
@[inline] def at? (bytes : Array UInt8) (i : Nat) : UInt8 := bytes.getD i 0

/-- Whether `b` is a continuation byte `10xxxxxx`. -/
@[inline] def isCont (b : UInt8) : Bool := b &&& 0xC0 == 0x80

/--
The width of the well-formed sequence starting at `i`, or `0` when the bytes
there are ill-formed or the input ends inside the sequence. Table 3-7 rows:
`00..7F`; `C2..DF 80..BF`; `E0 A0..BF 80..BF`, `E1..EC 80..BF 80..BF`,
`ED 80..9F 80..BF`, `EE..EF 80..BF 80..BF`; `F0 90..BF 80..BF 80..BF`,
`F1..F3 80..BF 80..BF 80..BF`, `F4 80..8F 80..BF 80..BF`.
-/
def width (bytes : Array UInt8) (i : Nat) : Nat :=
  let n := bytes.size
  let b0 := at? bytes i
  if b0 < 0x80 then 1
  else if b0 < 0xC2 then 0
  else if b0 < 0xE0 then
    if i + 1 < n && isCont (at? bytes (i + 1)) then 2 else 0
  else if b0 < 0xF0 then
    if i + 2 < n then
      let b1 := at? bytes (i + 1)
      let b2 := at? bytes (i + 2)
      let lo : UInt8 := if b0 == 0xE0 then 0xA0 else 0x80
      let hi : UInt8 := if b0 == 0xED then 0x9F else 0xBF
      if lo ≤ b1 && b1 ≤ hi && isCont b2 then 3 else 0
    else 0
  else if b0 < 0xF5 then
    if i + 3 < n then
      let b1 := at? bytes (i + 1)
      let b2 := at? bytes (i + 2)
      let b3 := at? bytes (i + 3)
      let lo : UInt8 := if b0 == 0xF0 then 0x90 else 0x80
      let hi : UInt8 := if b0 == 0xF4 then 0x8F else 0xBF
      if lo ≤ b1 && b1 ≤ hi && isCont b2 && isCont b3 then 4 else 0
    else 0
  else 0

/-- Validity from position `i` to the end. -/
def validFrom (bytes : Array UInt8) (i : Nat) : Bool :=
  if _h : i < bytes.size then
    let w := width bytes i
    if _hw : 0 < w then validFrom bytes (i + w) else false
  else true
termination_by bytes.size - i
decreasing_by omega

/-- `is_valid_utf8` over the carrier. -/
def valid (bytes : Array UInt8) : Bool := validFrom bytes 0

end Oak.Utf8Exec
