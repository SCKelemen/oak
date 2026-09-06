namespace Oak.CInterop

/-! # C interface conversion table

Model for `docs/spec/92-ffi.md` §2.2: the fixed-width conversion rows
between Oak integer types and the `c` library's fixed-width types. The
table is a bijection — every fixed-width Oak integer names exactly one
`c.*` type and back, and both directions round-trip — so an explicit
conversion pair `c.Int32(x)` / `i32(y)` can never change which abstract
value crosses the boundary. Width and signedness are preserved by
construction, which is the "ABI honesty" rule: an extern signature over
`c.*` types pins the foreign ABI exactly. -/

/-- The fixed-width Oak integer types admitted at the boundary. -/
inductive OakTy
  | i8 | i16 | i32 | i64
  | u8 | u16 | u32 | u64
  deriving DecidableEq, Repr

/-- The fixed-width members of the `c` library. -/
inductive CTy
  | int8 | int16 | int32 | int64
  | uint8 | uint16 | uint32 | uint64
  deriving DecidableEq, Repr

/-- The conversion table, Oak → C. -/
def cOf : OakTy → CTy
  | .i8 => .int8 | .i16 => .int16 | .i32 => .int32 | .i64 => .int64
  | .u8 => .uint8 | .u16 => .uint16 | .u32 => .uint32 | .u64 => .uint64

/-- The conversion table, C → Oak. -/
def oakOf : CTy → OakTy
  | .int8 => .i8 | .int16 => .i16 | .int32 => .i32 | .int64 => .i64
  | .uint8 => .u8 | .uint16 => .u16 | .uint32 => .u32 | .uint64 => .u64

/-- Bit width of an Oak boundary type. -/
def oakWidth : OakTy → Nat
  | .i8 => 8 | .i16 => 16 | .i32 => 32 | .i64 => 64
  | .u8 => 8 | .u16 => 16 | .u32 => 32 | .u64 => 64

/-- Bit width of a fixed-width `c` type. -/
def cWidth : CTy → Nat
  | .int8 => 8 | .int16 => 16 | .int32 => 32 | .int64 => 64
  | .uint8 => 8 | .uint16 => 16 | .uint32 => 32 | .uint64 => 64

/-- Signedness of an Oak boundary type. -/
def oakSigned : OakTy → Bool
  | .i8 | .i16 | .i32 | .i64 => true
  | .u8 | .u16 | .u32 | .u64 => false

/-- Signedness of a fixed-width `c` type. -/
def cSigned : CTy → Bool
  | .int8 | .int16 | .int32 | .int64 => true
  | .uint8 | .uint16 | .uint32 | .uint64 => false

/-- **Round trip, Oak side**: converting to C and back is the identity. -/
theorem oakOf_cOf (t : OakTy) : oakOf (cOf t) = t := by
  cases t <;> rfl

/-- **Round trip, C side**: converting to Oak and back is the identity. -/
theorem cOf_oakOf (t : CTy) : cOf (oakOf t) = t := by
  cases t <;> rfl

/-- **Injectivity**: distinct Oak types never share a `c` spelling, so a
    boundary signature identifies its Oak-side types uniquely. -/
theorem cOf_injective : Function.Injective cOf := by
  intro a b h
  have := congrArg oakOf h
  rwa [oakOf_cOf, oakOf_cOf] at this

/-- **Width preservation**: the table never changes representation size. -/
theorem width_preserved (t : OakTy) : cWidth (cOf t) = oakWidth t := by
  cases t <;> rfl

/-- **Signedness preservation**: the table never changes signedness, so
    no conversion pair can reinterpret a value's sign. -/
theorem sign_preserved (t : OakTy) : cSigned (cOf t) = oakSigned t := by
  cases t <;> rfl

end Oak.CInterop
