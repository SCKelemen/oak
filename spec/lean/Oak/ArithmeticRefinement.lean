import Std.Tactic.BVDecide

/-! # Compiler correspondence for total fixed-width arithmetic

`docs/spec/20-types.md` §11.1 gives `+ - * / %` and unary minus on
`u8..u64`, `i8..i64` one meaning: the result wraps mod `2^N` in the operand
width, division by zero traps, `MIN / -1` is `MIN` and `x % -1` is `0`.
The Lean extraction (`95-extraction.md` §2) realizes that meaning as Lean's
`UInt8..UInt64` and `Int8..Int64` operators. The C backend realizes it as
the macro families `OAK_ARITH_U(T)` and `OAK_ARITH_I(T, U, MIN)` in the
generated prelude (`codegen/codegen.go`), whose bodies compute in `u64`
space and truncate — signed operands through an unsigned reinterpretation
and back, so C never evaluates a signed overflow — with the divisor checks
spelled out.

This module states the correspondence in refinement form, the way
`Oak.ModulesRefinement` does for the module system: each macro body is
transliterated line for line as a Lean function over the fixed-width types
(`(T)((u64)a + (u64)b)` becomes `(a.toUInt64 + b.toUInt64).toUInt8`;
`oak_pun_T((U)((u64)(U)a + (u64)(U)b))` becomes
`((a.toUInt8.toUInt64 + b.toUInt8.toUInt64).toUInt8).toInt8`), and a theorem
proves it equal to the extraction's operator on every input. Division and
remainder take the nonzero divisor as a hypothesis: the C helper traps
there, and the extraction's operators are total with a different
convention at zero, so zero is outside the refined domain by the spec's
own rule.

The correspondence is scoped: it covers the arithmetic the macros define,
over the C99 meanings the backend relies on (`(u64)` of an unsigned value
zero-extends; `(T)` to a narrower unsigned type reduces mod `2^N`; a union
pun between `U` and `T` of one width reinterprets the bits; `/` and `%`
on nonzero divisors compute the truncated quotient and its remainder). It
does not cover C's integer promotions inside the bodies beyond those
meanings, nor the checked, saturating and trapping family
(`codegen/arithmetic.go`), which is verified by execution at every width's
boundaries (`compiler/e2e_checked_arithmetic_test.go`). The emitted macro
text is pinned to this transliteration by
`codegen/arithmetic_refinement_test.go`. -/

namespace Oak.ArithmeticRefinement

/-! ## OAK_ARITH_U(T)

```c
static inline T oak_add_##T(T a, T b) { return (T)((u64)a + (u64)b); }
static inline T oak_sub_##T(T a, T b) { return (T)((u64)a - (u64)b); }
static inline T oak_neg_##T(T a)      { return (T)(0u - (u64)a); }
static inline T oak_mul_##T(T a, T b) { return (T)((u64)a * (u64)b); }
static inline T oak_div_##T(T a, T b) { if (b == 0) { __builtin_trap(); } return (T)(a / b); }
static inline T oak_rem_##T(T a, T b) { if (b == 0) { __builtin_trap(); } return (T)(a % b); }
```
-/

namespace U8

def add (a b : UInt8) : UInt8 := (a.toUInt64 + b.toUInt64).toUInt8
def sub (a b : UInt8) : UInt8 := (a.toUInt64 - b.toUInt64).toUInt8
def neg (a : UInt8) : UInt8 := (0 - a.toUInt64).toUInt8
def mul (a b : UInt8) : UInt8 := (a.toUInt64 * b.toUInt64).toUInt8
def div (a b : UInt8) (_ : b ≠ 0) : UInt8 := a / b
def rem (a b : UInt8) (_ : b ≠ 0) : UInt8 := a % b

theorem add_eq (a b : UInt8) : add a b = a + b := by unfold add; bv_decide
theorem sub_eq (a b : UInt8) : sub a b = a - b := by unfold sub; bv_decide
theorem neg_eq (a : UInt8) : neg a = -a := by unfold neg; bv_decide
theorem mul_eq (a b : UInt8) : mul a b = a * b := by unfold mul; bv_decide
theorem div_eq (a b : UInt8) (h : b ≠ 0) : div a b h = a / b := rfl
theorem rem_eq (a b : UInt8) (h : b ≠ 0) : rem a b h = a % b := rfl

end U8

namespace U16

def add (a b : UInt16) : UInt16 := (a.toUInt64 + b.toUInt64).toUInt16
def sub (a b : UInt16) : UInt16 := (a.toUInt64 - b.toUInt64).toUInt16
def neg (a : UInt16) : UInt16 := (0 - a.toUInt64).toUInt16
def mul (a b : UInt16) : UInt16 := (a.toUInt64 * b.toUInt64).toUInt16
def div (a b : UInt16) (_ : b ≠ 0) : UInt16 := a / b
def rem (a b : UInt16) (_ : b ≠ 0) : UInt16 := a % b

theorem add_eq (a b : UInt16) : add a b = a + b := by unfold add; bv_decide
theorem sub_eq (a b : UInt16) : sub a b = a - b := by unfold sub; bv_decide
theorem neg_eq (a : UInt16) : neg a = -a := by unfold neg; bv_decide
theorem mul_eq (a b : UInt16) : mul a b = a * b := by unfold mul; bv_decide
theorem div_eq (a b : UInt16) (h : b ≠ 0) : div a b h = a / b := rfl
theorem rem_eq (a b : UInt16) (h : b ≠ 0) : rem a b h = a % b := rfl

end U16

namespace U32

def add (a b : UInt32) : UInt32 := (a.toUInt64 + b.toUInt64).toUInt32
def sub (a b : UInt32) : UInt32 := (a.toUInt64 - b.toUInt64).toUInt32
def neg (a : UInt32) : UInt32 := (0 - a.toUInt64).toUInt32
def mul (a b : UInt32) : UInt32 := (a.toUInt64 * b.toUInt64).toUInt32
def div (a b : UInt32) (_ : b ≠ 0) : UInt32 := a / b
def rem (a b : UInt32) (_ : b ≠ 0) : UInt32 := a % b

theorem add_eq (a b : UInt32) : add a b = a + b := by unfold add; bv_decide
theorem sub_eq (a b : UInt32) : sub a b = a - b := by unfold sub; bv_decide
theorem neg_eq (a : UInt32) : neg a = -a := by unfold neg; bv_decide
theorem mul_eq (a b : UInt32) : mul a b = a * b := by unfold mul; bv_decide
theorem div_eq (a b : UInt32) (h : b ≠ 0) : div a b h = a / b := rfl
theorem rem_eq (a b : UInt32) (h : b ≠ 0) : rem a b h = a % b := rfl

end U32

namespace U64

/-- At the widest width the `(u64)` casts are the identity, so the body is
    the operator itself. -/
def add (a b : UInt64) : UInt64 := a + b
def sub (a b : UInt64) : UInt64 := a - b
def neg (a : UInt64) : UInt64 := 0 - a
def mul (a b : UInt64) : UInt64 := a * b
def div (a b : UInt64) (_ : b ≠ 0) : UInt64 := a / b
def rem (a b : UInt64) (_ : b ≠ 0) : UInt64 := a % b

theorem add_eq (a b : UInt64) : add a b = a + b := rfl
theorem sub_eq (a b : UInt64) : sub a b = a - b := rfl
theorem neg_eq (a : UInt64) : neg a = -a := by unfold neg; bv_decide
theorem mul_eq (a b : UInt64) : mul a b = a * b := rfl
theorem div_eq (a b : UInt64) (h : b ≠ 0) : div a b h = a / b := rfl
theorem rem_eq (a b : UInt64) (h : b ≠ 0) : rem a b h = a % b := rfl

end U64

/-! ## OAK_ARITH_I(T, U, MIN)

```c
static inline T oak_pun_##T(U bits) { union { U from; T to; } pun; pun.from = bits; return pun.to; }
static inline T oak_add_##T(T a, T b) { return oak_pun_##T((U)((u64)(U)a + (u64)(U)b)); }
static inline T oak_sub_##T(T a, T b) { return oak_pun_##T((U)((u64)(U)a - (u64)(U)b)); }
static inline T oak_neg_##T(T a)      { return oak_pun_##T((U)(0u - (u64)(U)a)); }
static inline T oak_mul_##T(T a, T b) { return oak_pun_##T((U)((u64)(U)a * (u64)(U)b)); }
static inline T oak_div_##T(T a, T b) { if (b == 0) { __builtin_trap(); } if (a == MIN && b == -1) { return a; } return (T)(a / b); }
static inline T oak_rem_##T(T a, T b) { if (b == 0) { __builtin_trap(); } if (b == -1) { return 0; } return (T)(a % b); }
```

`(U)a` on a signed `a` is the two's-complement reinterpretation
(`Int8.toUInt8`), `(u64)` of the unsigned value zero-extends
(`UInt8.toUInt64`), `(U)` back reduces mod `2^N` (`UInt64.toUInt8`), and
the pun reinterprets the bits as `T` (`UInt8.toInt8`). Lean's `Int8.div`
and `Int8.mod` are `BitVec.sdiv` and `BitVec.srem`, which already yield
`MIN` for `MIN / -1` and `0` for `x % -1`, so the guarded C branches agree
with the unguarded operator. -/

namespace I8

def add (a b : Int8) : Int8 := ((a.toUInt8.toUInt64 + b.toUInt8.toUInt64).toUInt8).toInt8
def sub (a b : Int8) : Int8 := ((a.toUInt8.toUInt64 - b.toUInt8.toUInt64).toUInt8).toInt8
def neg (a : Int8) : Int8 := ((0 - a.toUInt8.toUInt64).toUInt8).toInt8
def mul (a b : Int8) : Int8 := ((a.toUInt8.toUInt64 * b.toUInt8.toUInt64).toUInt8).toInt8
def div (a b : Int8) (_ : b ≠ 0) : Int8 := if a = Int8.minValue ∧ b = -1 then a else a / b
def rem (a b : Int8) (_ : b ≠ 0) : Int8 := if b = -1 then 0 else a % b

theorem add_eq (a b : Int8) : add a b = a + b := by unfold add; bv_decide
theorem sub_eq (a b : Int8) : sub a b = a - b := by unfold sub; bv_decide
theorem neg_eq (a : Int8) : neg a = -a := by unfold neg; bv_decide
theorem mul_eq (a b : Int8) : mul a b = a * b := by unfold mul; bv_decide
theorem div_eq (a b : Int8) (h : b ≠ 0) : div a b h = a / b := by
  unfold div; split
  · rename_i hc; obtain ⟨ha, hb⟩ := hc; subst ha; subst hb; decide
  · rfl
theorem rem_eq (a b : Int8) (h : b ≠ 0) : rem a b h = a % b := by
  unfold rem; split
  · rename_i hb; subst hb; bv_decide
  · rfl

end I8

namespace I16

def add (a b : Int16) : Int16 := ((a.toUInt16.toUInt64 + b.toUInt16.toUInt64).toUInt16).toInt16
def sub (a b : Int16) : Int16 := ((a.toUInt16.toUInt64 - b.toUInt16.toUInt64).toUInt16).toInt16
def neg (a : Int16) : Int16 := ((0 - a.toUInt16.toUInt64).toUInt16).toInt16
def mul (a b : Int16) : Int16 := ((a.toUInt16.toUInt64 * b.toUInt16.toUInt64).toUInt16).toInt16
def div (a b : Int16) (_ : b ≠ 0) : Int16 := if a = Int16.minValue ∧ b = -1 then a else a / b
def rem (a b : Int16) (_ : b ≠ 0) : Int16 := if b = -1 then 0 else a % b

theorem add_eq (a b : Int16) : add a b = a + b := by unfold add; bv_decide
theorem sub_eq (a b : Int16) : sub a b = a - b := by unfold sub; bv_decide
theorem neg_eq (a : Int16) : neg a = -a := by unfold neg; bv_decide
theorem mul_eq (a b : Int16) : mul a b = a * b := by unfold mul; bv_decide
theorem div_eq (a b : Int16) (h : b ≠ 0) : div a b h = a / b := by
  unfold div; split
  · rename_i hc; obtain ⟨ha, hb⟩ := hc; subst ha; subst hb; decide
  · rfl
theorem rem_eq (a b : Int16) (h : b ≠ 0) : rem a b h = a % b := by
  unfold rem; split
  · rename_i hb; subst hb; bv_decide
  · rfl

end I16

namespace I32

def add (a b : Int32) : Int32 := ((a.toUInt32.toUInt64 + b.toUInt32.toUInt64).toUInt32).toInt32
def sub (a b : Int32) : Int32 := ((a.toUInt32.toUInt64 - b.toUInt32.toUInt64).toUInt32).toInt32
def neg (a : Int32) : Int32 := ((0 - a.toUInt32.toUInt64).toUInt32).toInt32
def mul (a b : Int32) : Int32 := ((a.toUInt32.toUInt64 * b.toUInt32.toUInt64).toUInt32).toInt32
def div (a b : Int32) (_ : b ≠ 0) : Int32 := if a = Int32.minValue ∧ b = -1 then a else a / b
def rem (a b : Int32) (_ : b ≠ 0) : Int32 := if b = -1 then 0 else a % b

theorem add_eq (a b : Int32) : add a b = a + b := by unfold add; bv_decide
theorem sub_eq (a b : Int32) : sub a b = a - b := by unfold sub; bv_decide
theorem neg_eq (a : Int32) : neg a = -a := by unfold neg; bv_decide
theorem mul_eq (a b : Int32) : mul a b = a * b := by unfold mul; bv_decide
theorem div_eq (a b : Int32) (h : b ≠ 0) : div a b h = a / b := by
  unfold div; split
  · rename_i hc; obtain ⟨ha, hb⟩ := hc; subst ha; subst hb; decide
  · rfl
theorem rem_eq (a b : Int32) (h : b ≠ 0) : rem a b h = a % b := by
  unfold rem; split
  · rename_i hb; subst hb; bv_decide
  · rfl

end I32

namespace I64

def add (a b : Int64) : Int64 := (a.toUInt64 + b.toUInt64).toInt64
def sub (a b : Int64) : Int64 := (a.toUInt64 - b.toUInt64).toInt64
def neg (a : Int64) : Int64 := (0 - a.toUInt64).toInt64
def mul (a b : Int64) : Int64 := (a.toUInt64 * b.toUInt64).toInt64
def div (a b : Int64) (_ : b ≠ 0) : Int64 := if a = Int64.minValue ∧ b = -1 then a else a / b
def rem (a b : Int64) (_ : b ≠ 0) : Int64 := if b = -1 then 0 else a % b

theorem add_eq (a b : Int64) : add a b = a + b := by unfold add; bv_decide
theorem sub_eq (a b : Int64) : sub a b = a - b := by unfold sub; bv_decide
theorem neg_eq (a : Int64) : neg a = -a := by unfold neg; bv_decide
theorem mul_eq (a b : Int64) : mul a b = a * b := by unfold mul; bv_decide
theorem div_eq (a b : Int64) (h : b ≠ 0) : div a b h = a / b := by
  unfold div; split
  · rename_i hc; obtain ⟨ha, hb⟩ := hc; subst ha; subst hb; decide
  · rfl
theorem rem_eq (a b : Int64) (h : b ≠ 0) : rem a b h = a % b := by
  unfold rem; split
  · rename_i hb; subst hb; bv_decide
  · rfl

end I64

end Oak.ArithmeticRefinement
