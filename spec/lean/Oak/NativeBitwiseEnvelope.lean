import Oak.NativeBitwiseEnvelopeLayout

/-! Actual extracted full-writer composition and its field-specification join. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
namespace Oak.BitwiseELFProducer
open Oak.WasmAssembler (writeBytes writeBytes_size writeBytes_suffix)
open Oak.NativeBitwiseEnvelope
open Oak.MinimalELF (Machine)

def archTag : Machine → UInt32 | .arm64 => 1 | .rv64 => 2

/-- Exact ordered stores after the actual zero pass, including both opaque
copies. This proof normal form is independently joined to the field-based E. -/
def nativePatches (m : Machine) (name text : List UInt8) : List Patch :=
  let stub := Oak.NativeBitwiseImage.stubSize m
  let body := Oak.NativeBitwiseImage.bodySize m
  let load := Oak.NativeBitwiseImage.loadSize m
  let sym := Oak.NativeBitwiseImage.symOffset m
  let str := Oak.NativeBitwiseImage.strOffset m
  let shstr := Oak.NativeBitwiseImage.shstrOffset m (Oak.NativeBitwiseObject.fromUInt8 name)
  let sections := Oak.NativeBitwiseImage.shOffset m (Oak.NativeBitwiseObject.fromUInt8 name)
  let machine := 2 + 65536 * m.number
  let flags := m.abiFlags
  [
    (0, word32Bytes 1179403647),
    (4, word32Bytes 65794),
    (16, word32Bytes machine),
    (20, word32Bytes 1),
    (24, word32Bytes 65536),
    (32, word32Bytes 64),
    (40, word32Bytes sections),
    (48, word32Bytes flags),
    (52, word32Bytes 3670080),
    (56, word32Bytes 4194305),
    (60, word32Bytes 327686),
    (64, word32Bytes 1),
    (68, word32Bytes 5),
    (72, word32Bytes 4096),
    (80, word32Bytes 65536),
    (88, word32Bytes 65536),
    (96, word32Bytes load),
    (104, word32Bytes load),
    (112, word32Bytes 4096),
    (4096, text),
    ((sym + 24), word32Bytes 1),
    ((sym + 28), word32Bytes 65554),
    ((sym + 32), word32Bytes 65536),
    ((sym + 40), word32Bytes stub),
    ((sym + 48), word32Bytes 8),
    ((sym + 52), word32Bytes 65554),
    ((sym + 56), word32Bytes (65536 + stub)),
    ((sym + 64), word32Bytes body),
    (str, word32Bytes 1953718016),
    ((str + 4), word32Bytes 7631457),
    ((str + 8), word32Bytes 1600872815),
    (str + 12, name),
    (shstr, word32Bytes 1702112768),
    ((shstr + 4), word32Bytes 771781752),
    ((shstr + 8), word32Bytes 1633972082),
    ((shstr + 12), word32Bytes 771776884),
    ((shstr + 16), word32Bytes 1953331571),
    ((shstr + 20), word32Bytes 771777121),
    ((shstr + 24), word32Bytes 1953657971),
    ((shstr + 28), word32Bytes 771777121),
    ((shstr + 32), word32Bytes 1953720435),
    ((shstr + 36), word32Bytes 1650553970),
    ((sections + 64), word32Bytes 1),
    ((sections + 68), word32Bytes 1),
    ((sections + 72), word32Bytes 6),
    ((sections + 80), word32Bytes 65536),
    ((sections + 88), word32Bytes 4096),
    ((sections + 96), word32Bytes (stub + body)),
    ((sections + 112), word32Bytes 4),
    ((sections + 128), word32Bytes 7),
    ((sections + 132), word32Bytes 1),
    ((sections + 136), word32Bytes 2),
    ((sections + 144), word32Bytes (65536 + load)),
    ((sections + 152), word32Bytes sym),
    ((sections + 176), word32Bytes 16),
    ((sections + 192), word32Bytes 15),
    ((sections + 196), word32Bytes 2),
    ((sections + 216), word32Bytes sym),
    ((sections + 224), word32Bytes 72),
    ((sections + 232), word32Bytes 4),
    ((sections + 236), word32Bytes 1),
    ((sections + 240), word32Bytes 8),
    ((sections + 248), word32Bytes 24),
    ((sections + 256), word32Bytes 23),
    ((sections + 260), word32Bytes 3),
    ((sections + 280), word32Bytes str),
    ((sections + 288), word32Bytes (name.length + 13)),
    ((sections + 304), word32Bytes 1),
    ((sections + 320), word32Bytes 31),
    ((sections + 324), word32Bytes 3),
    ((sections + 344), word32Bytes shstr),
    ((sections + 352), word32Bytes 41),
    ((sections + 368), word32Bytes 1)]

theorem nativePatches_ordered (m : Machine) (name text : List UInt8)
    (ht : text.length = Oak.NativeBitwiseImage.textSize m) :
    OrderedPatches 0 (Oak.NativeBitwiseImage.shOffset m (Oak.NativeBitwiseObject.fromUInt8 name) + 384) (nativePatches m name text) := by
  have hs := (shOffset_bounds m name).1
  cases m <;> simp_all [nativePatches, OrderedPatches,
    Oak.NativeBitwiseImage.stubSize, Oak.NativeBitwiseImage.bodySize, Oak.NativeBitwiseImage.loadSize, Oak.NativeBitwiseImage.symOffset, Oak.NativeBitwiseImage.strOffset,
    Oak.NativeBitwiseImage.textOffset, Oak.NativeBitwiseImage.shstrOffset, Oak.NativeBitwiseImage.textSize] <;> omega

private theorem zeroGap65 (n : Nat) : List.replicate (n+65) (0 : UInt8) =
    0 :: (List.replicate n 0 ++ List.replicate 64 0) := by
  rw [List.replicate_append_replicate]
  change List.replicate ((n+64)+1) (0 : UInt8) = _
  rfl

private theorem zeros3980 : List.replicate 3980 (0 : UInt8) = [0,0,0,0] ++ List.replicate 3976 0 := rfl
private theorem zeros0 : List.replicate 0 (0 : UInt8) = [] := rfl
private theorem zeros1 : List.replicate 1 (0 : UInt8) = [0] := rfl
private theorem zeros2 : List.replicate 2 (0 : UInt8) = [0,0] := rfl
private theorem zeros3 : List.replicate 3 (0 : UInt8) = [0,0,0] := rfl
private theorem zeros4 : List.replicate 4 (0 : UInt8) = [0,0,0,0] := rfl
private theorem zeros5 : List.replicate 5 (0 : UInt8) = [0,0,0,0,0] := rfl
private theorem zeros6 : List.replicate 6 (0 : UInt8) = [0,0,0,0,0,0] := rfl
private theorem zeros7 : List.replicate 7 (0 : UInt8) = [0,0,0,0,0,0,0] := rfl
private theorem zeros8 : List.replicate 8 (0 : UInt8) = [0,0,0,0,0,0,0,0] := rfl
private theorem zeros9 : List.replicate 9 (0 : UInt8) = [0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros10 : List.replicate 10 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros11 : List.replicate 11 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros12 : List.replicate 12 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros13 : List.replicate 13 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros14 : List.replicate 14 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros15 : List.replicate 15 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros16 : List.replicate 16 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros17 : List.replicate 17 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros18 : List.replicate 18 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros19 : List.replicate 19 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros20 : List.replicate 20 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros21 : List.replicate 21 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros22 : List.replicate 22 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros23 : List.replicate 23 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros24 : List.replicate 24 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros25 : List.replicate 25 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros26 : List.replicate 26 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros27 : List.replicate 27 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros28 : List.replicate 28 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros29 : List.replicate 29 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros30 : List.replicate 30 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros31 : List.replicate 31 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros32 : List.replicate 32 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros33 : List.replicate 33 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros34 : List.replicate 34 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros35 : List.replicate 35 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros36 : List.replicate 36 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros37 : List.replicate 37 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros38 : List.replicate 38 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros39 : List.replicate 39 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros40 : List.replicate 40 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros41 : List.replicate 41 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros42 : List.replicate 42 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros43 : List.replicate 43 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros44 : List.replicate 44 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros45 : List.replicate 45 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros46 : List.replicate 46 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros47 : List.replicate 47 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros48 : List.replicate 48 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros49 : List.replicate 49 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros50 : List.replicate 50 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros51 : List.replicate 51 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros52 : List.replicate 52 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros53 : List.replicate 53 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros54 : List.replicate 54 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros55 : List.replicate 55 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros56 : List.replicate 56 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros57 : List.replicate 57 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros58 : List.replicate 58 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros59 : List.replicate 59 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros60 : List.replicate 60 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros61 : List.replicate 61 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros62 : List.replicate 62 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros63 : List.replicate 63 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl
private theorem zeros64 : List.replicate 64 (0 : UInt8) = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl

/-- The store normal form equals the independently serialized ELF fields. -/
theorem nativePatches_bytes (m : Machine) (name body : List UInt8)
    (hb : body.length = Oak.NativeBitwiseImage.bodySize m) :
    patchBytes 0 (Oak.NativeBitwiseImage.shOffset m (Oak.NativeBitwiseObject.fromUInt8 name) + 384)
      (nativePatches m name (Oak.NativeBitwiseObject.toUInt8 (Oak.NativeBitwiseImage.startup m) ++ body)) =
      E m name body := by
  have hs := (shOffset_bounds m name).1
  cases m <;> simp_all +arith [nativePatches, patchBytes, E, header, programBytes, symbols, symbolBytes,
    stringTable, sections, sectionBytes, dwordBytes, word32Bytes, wordBytes,
    Oak.NativeBitwiseImage.stubSize, Oak.NativeBitwiseImage.bodySize, Oak.NativeBitwiseImage.loadSize,
    Oak.NativeBitwiseImage.symOffset, Oak.NativeBitwiseImage.strOffset, Oak.NativeBitwiseImage.textOffset,
    Oak.NativeBitwiseImage.shstrOffset, Oak.NativeBitwiseImage.textSize, Oak.NativeBitwiseImage.base,
    Oak.NativeBitwiseImage.startup, Oak.NativeBitwiseImage.sectionNames,
    Oak.NativeBitwiseImage.nullSymbol, Oak.NativeBitwiseImage.startSymbol, Oak.NativeBitwiseImage.functionSymbol,
    Oak.NativeBitwiseImage.bodyAddress, Oak.NativeBitwiseImage.nullSection, Oak.NativeBitwiseImage.textSection,
    Oak.NativeBitwiseImage.dataSection, Oak.NativeBitwiseImage.symSection, Oak.NativeBitwiseImage.strSection,
    Oak.NativeBitwiseImage.shstrSection, Oak.NativeBitwiseObject.toUInt8, Oak.MinimalELF.Machine.number,
    Oak.MinimalELF.Machine.abiFlags, List.append_assoc, -List.reduceReplicate, zeros3980, zeros0, zeros1, zeros2, zeros3, zeros4, zeros5, zeros6, zeros7, zeros8, zeros9, zeros10, zeros11, zeros12, zeros13, zeros14, zeros15, zeros16, zeros17, zeros18, zeros19, zeros20, zeros21, zeros22, zeros23, zeros24, zeros25, zeros26, zeros27, zeros28, zeros29, zeros30, zeros31, zeros32, zeros33, zeros34, zeros35, zeros36, zeros37, zeros38, zeros39, zeros40, zeros41, zeros42, zeros43, zeros44, zeros45, zeros46, zeros47, zeros48, zeros49, zeros50, zeros51, zeros52, zeros53, zeros54, zeros55, zeros56, zeros57, zeros58, zeros59, zeros60, zeros61, zeros62, zeros63, zeros64]
  all_goals
    first
    | rw [show Oak.NativeBitwiseImage.shOffset .rv64 (Oak.NativeBitwiseObject.fromUInt8 name) - (name.length+4221) =
        (Oak.NativeBitwiseImage.shOffset .rv64 (Oak.NativeBitwiseObject.fromUInt8 name) - (name.length+4286))+65 by omega]
    | rw [show Oak.NativeBitwiseImage.shOffset .arm64 (Oak.NativeBitwiseObject.fromUInt8 name) - (name.length+4189) =
        (Oak.NativeBitwiseImage.shOffset .arm64 (Oak.NativeBitwiseObject.fromUInt8 name) - (name.length+4254))+65 by omega]
    simp only [zeroGap65, List.cons_append, List.append_assoc, zeros64]
    rfl

end Oak.BitwiseELFProducer
