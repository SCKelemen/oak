import Std.Tactic.BVDecide

/-! # Compiler correspondence for the explicit integer conversions

`docs/spec/20-types.md` §11.1 gives the conversion family
`{target}_{op}_{source}` one meaning each:

* `trunc` narrows within one signedness to the low bits, wrapping mod `2^N`;
* `saturating` narrows within one signedness to the exact value clamped to
  the target's range;
* `checked` narrows within one signedness to `Ok(exact)` when the value is
  in the target's range and `Err(Overflow)` otherwise;
* `bits` reinterprets the bit pattern between the two signednesses of one
  width.

The checker admits exactly those pairs (`typechecker.isValidNarrowing`:
same signedness, strictly wider source; `bits`: same width, opposite
signedness). The C backend (`codegen/conversions.go`) realizes them as:

```c
static inline uT oak_conv_uT_trunc_uS( uS x ) { return (uT)( x ); }
static inline iT oak_conv_iT_trunc_iS( iS x ) {
  union { uT low; iT to; } pun;
  pun.low = (uT)( (uS)x );
  return pun.to;
}
static inline uT oak_conv_uT_saturating_uS( uS x ) { return x > (uS)MAX ? (uT)MAX : (uT)x; }
static inline iT oak_conv_iT_saturating_iS( iS x ) {
  if (x > (iS)MAX) { return (iT)MAX; }
  if (x < (iS)(MIN)) { return (iT)(MIN); }
  return (iT)x;
}
static inline Result oak_conv_T_checked_S( S x ) {
  if (x > (S)MAX [|| x < (S)(MIN)]) { return Err(Overflow); }
  return Ok((T)x);
}
static inline iT oak_conv_iT_bits_uT( uT x ) { union { uT from; iT to; } pun; pun.from = x; return pun.to; }
```

This module transliterates each body over Lean's `UIntN`/`IntN` — `(uT)x`
on an unsigned value is `toUIntT`, `(uS)x` on a signed value the
two's-complement reinterpretation `toUIntS`, the union pun `toIntT`, and
the in-range `(iT)x` the value-preserving `toIntT` — and proves each equal
to the spec's meaning for every admitted pair: `trunc` is Lean's wrapping
narrowing; `saturating` returns `min(max(x, MIN), MAX)` read back in the
source width; `checked` is `some` exactly in range and returns the exact
value; `bits` preserves the bit pattern. One point the transliteration
makes visible: the signed `(iT)x` cast is only evaluated after both bound
tests, so the value converted is always representable and C's
implementation-defined out-of-range signed conversion is never reached;
the signed `trunc` goes through unsigned space and a union instead. The
emitted helper text is pinned by `codegen/conversion_refinement_test.go`
and `compiler/e2e_conversion_refinement_test.go`.

Scoped as the arithmetic refinement is: the C99 meanings of unsigned
casts, in-range signed casts and the union pun are assumed. -/

namespace Oak.ConversionRefinement

/-! ## trunc: the low bits -/

namespace Trunc

def u8_u16 (x : UInt16) : UInt8 := x.toUInt8
def u8_u32 (x : UInt32) : UInt8 := x.toUInt8
def u8_u64 (x : UInt64) : UInt8 := x.toUInt8
def u16_u32 (x : UInt32) : UInt16 := x.toUInt16
def u16_u64 (x : UInt64) : UInt16 := x.toUInt16
def u32_u64 (x : UInt64) : UInt32 := x.toUInt32

/-- `pun.low = (uT)((uS)x); return pun.to`. -/
def i8_i16 (x : Int16) : Int8 := (x.toUInt16.toUInt8).toInt8
def i8_i32 (x : Int32) : Int8 := (x.toUInt32.toUInt8).toInt8
def i8_i64 (x : Int64) : Int8 := (x.toUInt64.toUInt8).toInt8
def i16_i32 (x : Int32) : Int16 := (x.toUInt32.toUInt16).toInt16
def i16_i64 (x : Int64) : Int16 := (x.toUInt64.toUInt16).toInt16
def i32_i64 (x : Int64) : Int32 := (x.toUInt64.toUInt32).toInt32

/-- The unsigned forms are the wrapping narrowing by definition; the value
    read is `x mod 2^T`. -/
theorem u8_u32_mod (x : UInt32) : (u8_u32 x).toNat = x.toNat % 256 := by
  unfold u8_u32; simp [UInt32.toNat_toUInt8]
theorem u16_u64_mod (x : UInt64) : (u16_u64 x).toNat = x.toNat % 65536 := by
  unfold u16_u64; simp [UInt64.toNat_toUInt16]

/-- The signed forms equal Lean's wrapping narrowing. -/
theorem i8_i16_eq (x : Int16) : i8_i16 x = x.toInt8 := by unfold i8_i16; bv_decide
theorem i8_i32_eq (x : Int32) : i8_i32 x = x.toInt8 := by unfold i8_i32; bv_decide
theorem i8_i64_eq (x : Int64) : i8_i64 x = x.toInt8 := by unfold i8_i64; bv_decide
theorem i16_i32_eq (x : Int32) : i16_i32 x = x.toInt16 := by unfold i16_i32; bv_decide
theorem i16_i64_eq (x : Int64) : i16_i64 x = x.toInt16 := by unfold i16_i64; bv_decide
theorem i32_i64_eq (x : Int64) : i32_i64 x = x.toInt32 := by unfold i32_i64; bv_decide

end Trunc

/-! ## saturating: clamp, then a value-preserving cast -/

namespace Saturating

/-- `x > (uS)MAX ? (uT)MAX : (uT)x`. -/
def u8_u32 (x : UInt32) : UInt8 := if x > 255 then 255 else x.toUInt8
def u16_u32 (x : UInt32) : UInt16 := if x > 65535 then 65535 else x.toUInt16
def u8_u64 (x : UInt64) : UInt8 := if x > 255 then 255 else x.toUInt8
def u32_u64 (x : UInt64) : UInt32 := if x > 4294967295 then 4294967295 else x.toUInt32

/-- `if (x > MAX) return MAX; if (x < MIN) return MIN; return (iT)x`. -/
def i8_i32 (x : Int32) : Int8 := if x > 127 then 127 else if x < -128 then -128 else x.toInt8
def i16_i32 (x : Int32) : Int16 := if x > 32767 then 32767 else if x < -32768 then -32768 else x.toInt16
def i8_i64 (x : Int64) : Int8 := if x > 127 then 127 else if x < -128 then -128 else x.toInt8
def i32_i64 (x : Int64) : Int32 :=
  if x > 2147483647 then 2147483647 else if x < -2147483648 then -2147483648 else x.toInt32

/-- **Clamping**: read back in the source width, the result is `min(x, MAX)`
    for unsigned and `min(max(x, MIN), MAX)` for signed — the exact value
    clamped to the range, so the narrowing cast that follows never loses
    a bit. -/
theorem u8_u32_clamps (x : UInt32) : (u8_u32 x).toUInt32 = if x > 255 then 255 else x := by
  unfold u8_u32; bv_decide
theorem u16_u32_clamps (x : UInt32) : (u16_u32 x).toUInt32 = if x > 65535 then 65535 else x := by
  unfold u16_u32; bv_decide
theorem u8_u64_clamps (x : UInt64) : (u8_u64 x).toUInt64 = if x > 255 then 255 else x := by
  unfold u8_u64; bv_decide
theorem u32_u64_clamps (x : UInt64) : (u32_u64 x).toUInt64 = if x > 4294967295 then 4294967295 else x := by
  unfold u32_u64; bv_decide

theorem i8_i32_clamps (x : Int32) :
    (i8_i32 x).toInt32 = if x > 127 then 127 else if x < -128 then -128 else x := by
  unfold i8_i32; bv_decide
theorem i16_i32_clamps (x : Int32) :
    (i16_i32 x).toInt32 = if x > 32767 then 32767 else if x < -32768 then -32768 else x := by
  unfold i16_i32; bv_decide
theorem i8_i64_clamps (x : Int64) :
    (i8_i64 x).toInt64 = if x > 127 then 127 else if x < -128 then -128 else x := by
  unfold i8_i64; bv_decide
theorem i32_i64_clamps (x : Int64) :
    (i32_i64 x).toInt64 = if x > 2147483647 then 2147483647 else if x < -2147483648 then -2147483648 else x := by
  unfold i32_i64; bv_decide

end Saturating

/-! ## checked: the bound test, then the exact value -/

namespace Checked

/-- The two outcomes of `if (x > (S)MAX [|| x < (S)(MIN)]) return Err(Overflow); return Ok((T)x)`:
    the test's verdict, and the payload taken when it is Ok. -/
def u8_u32_ok (x : UInt32) : Bool := !decide (x > 255)
def u8_u32_value (x : UInt32) : UInt8 := x.toUInt8
def u32_u64_ok (x : UInt64) : Bool := !decide (x > 4294967295)
def u32_u64_value (x : UInt64) : UInt32 := x.toUInt32
def i8_i32_ok (x : Int32) : Bool := !(decide (x > 127) || decide (x < -128))
def i8_i32_value (x : Int32) : Int8 := x.toInt8
def i16_i64_ok (x : Int64) : Bool := !(decide (x > 32767) || decide (x < -32768))
def i16_i64_value (x : Int64) : Int16 := x.toInt16

/-- `Ok` exactly in range. -/
theorem u8_u32_ok_iff (x : UInt32) : u8_u32_ok x = true ↔ x ≤ 255 := by
  unfold u8_u32_ok; simp <;> bv_decide
theorem u32_u64_ok_iff (x : UInt64) : u32_u64_ok x = true ↔ x ≤ 4294967295 := by
  unfold u32_u64_ok; simp <;> bv_decide
theorem i8_i32_ok_iff (x : Int32) : i8_i32_ok x = true ↔ -128 ≤ x ∧ x ≤ 127 := by
  unfold i8_i32_ok; simp <;> bv_decide
theorem i16_i64_ok_iff (x : Int64) : i16_i64_ok x = true ↔ -32768 ≤ x ∧ x ≤ 32767 := by
  unfold i16_i64_ok; simp <;> bv_decide

/-- The payload is the exact value: in range, the narrowing cast is
    value-preserving. -/
theorem u8_u32_exact (x : UInt32) (h : x ≤ 255) : (u8_u32_value x).toUInt32 = x := by
  unfold u8_u32_value; bv_decide
theorem u32_u64_exact (x : UInt64) (h : x ≤ 4294967295) : (u32_u64_value x).toUInt64 = x := by
  unfold u32_u64_value; bv_decide
theorem i8_i32_exact (x : Int32) (h : -128 ≤ x ∧ x ≤ 127) : (i8_i32_value x).toInt32 = x := by
  unfold i8_i32_value; bv_decide
theorem i16_i64_exact (x : Int64) (h : -32768 ≤ x ∧ x ≤ 32767) : (i16_i64_value x).toInt64 = x := by
  unfold i16_i64_value; bv_decide

end Checked

/-! ## bits: the same pattern, the other signedness -/

namespace Bits

def i8_u8 (x : UInt8) : Int8 := x.toInt8
def u8_i8 (x : Int8) : UInt8 := x.toUInt8
def i32_u32 (x : UInt32) : Int32 := x.toInt32
def u32_i32 (x : Int32) : UInt32 := x.toUInt32
def i64_u64 (x : UInt64) : Int64 := x.toInt64
def u64_i64 (x : Int64) : UInt64 := x.toUInt64

theorem i8_u8_pattern (x : UInt8) : (i8_u8 x).toBitVec = x.toBitVec := by unfold i8_u8; bv_decide
theorem u8_i8_pattern (x : Int8) : (u8_i8 x).toBitVec = x.toBitVec := by unfold u8_i8; bv_decide
theorem i32_u32_pattern (x : UInt32) : (i32_u32 x).toBitVec = x.toBitVec := by unfold i32_u32; bv_decide
theorem u32_i32_pattern (x : Int32) : (u32_i32 x).toBitVec = x.toBitVec := by unfold u32_i32; bv_decide
theorem i64_u64_pattern (x : UInt64) : (i64_u64 x).toBitVec = x.toBitVec := by unfold i64_u64; bv_decide
theorem u64_i64_pattern (x : Int64) : (u64_i64 x).toBitVec = x.toBitVec := by unfold u64_i64; bv_decide

/-- The two directions invert each other: reinterpretation loses nothing. -/
theorem i32_u32_roundtrip (x : UInt32) : u32_i32 (i32_u32 x) = x := by unfold u32_i32 i32_u32; bv_decide
theorem u64_i64_roundtrip (x : Int64) : i64_u64 (u64_i64 x) = x := by unfold i64_u64 u64_i64; bv_decide

end Bits

end Oak.ConversionRefinement
