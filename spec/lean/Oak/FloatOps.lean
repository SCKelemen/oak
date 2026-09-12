/-!
# Oak.FloatOps — bit-exact carriers for the float intrinsics Lean lacks

`docs/spec/20-types.md` section 11.3.5 names `fma`, `copysign`, and
`round_even` among the correctly rounded intrinsics. Lean's `Float` and
`Float32` carry `sqrt`, `abs`, `floor`, `ceil`, `round` (ties away) and the
classifications with the same contract, so the extraction
(`docs/spec/95-extraction.md` section 2) maps those directly. The three
below have no counterpart in the core library, so this file defines them
from the bit pattern, where every step is integer arithmetic and therefore
exact:

* `copysign x y` replaces the sign bit of `x` with that of `y`: a bit
  operation, total on NaN, exactly the C `copysign` the backend emits.
* `roundEven x` is round to nearest, ties to even (C `rint` under the
  default rounding mode). It starts from Lean's `round` (ties away), which
  is correct except on ties; a tie is detected exactly because `x - round x`
  is exact (Sterbenz for `|x| ≥ 1/2`, and `x` itself below), and the tie is
  moved one unit toward even. A zero result takes the sign of `x`, as
  `rint` does.
* `fma a b c` is one rounding of the exact `a * b + c`: the operands are
  decoded into `±m · 2^e` with `m : Nat`, the product and sum are formed
  exactly over `Int`, and the result is rounded once to the format (round to
  nearest, ties to even, subnormals and overflow to infinity included) by
  `encode`. The special cases (NaN, infinities, `0 · ∞`, exact zero sums)
  follow IEEE 754-2019 §7.2 and §6.3. NaN payloads are not modeled: any NaN
  result is the canonical quiet NaN, which is the one modeling choice this
  file makes beyond IEEE (stated in `95-extraction.md` section 3).

Both widths share the code through `Fmt`; `Float` and `Float32` wrappers
convert through `toBits`/`ofBits`, which are exact.
-/

namespace Oak.FloatOps

/-- A binary interchange format: the total width, the significand precision
`prec` (with the implicit bit), and the exponent field width. -/
structure Fmt where
  width : Nat
  prec : Nat
  expBits : Nat

def binary64 : Fmt := ⟨64, 53, 11⟩
def binary32 : Fmt := ⟨32, 24, 8⟩

namespace Fmt

def fracBits (f : Fmt) : Nat := f.prec - 1
def bias (f : Fmt) : Nat := 2 ^ (f.expBits - 1) - 1
def expMax (f : Fmt) : Nat := 2 ^ f.expBits - 1
/-- The exponent of the least subnormal quantum (`-1074` for binary64). -/
def emin (f : Fmt) : Int := 1 - (f.bias : Int) - (f.fracBits : Int)
def signBit (f : Fmt) : Nat := 2 ^ (f.width - 1)
def sign (f : Fmt) (b : Nat) : Bool := b.testBit (f.width - 1)
def expField (f : Fmt) (b : Nat) : Nat := (b >>> f.fracBits) % 2 ^ f.expBits
def frac (f : Fmt) (b : Nat) : Nat := b % 2 ^ f.fracBits
def isNaN (f : Fmt) (b : Nat) : Bool := f.expField b = f.expMax && f.frac b ≠ 0
def isInf (f : Fmt) (b : Nat) : Bool := f.expField b = f.expMax && f.frac b = 0
def isZero (f : Fmt) (b : Nat) : Bool := f.expField b = 0 && f.frac b = 0
def signOnly (f : Fmt) (neg : Bool) : Nat := if neg then f.signBit else 0
def inf (f : Fmt) (neg : Bool) : Nat := f.signOnly neg + (f.expMax <<< f.fracBits)
/-- The canonical quiet NaN: exponent all ones, top fraction bit set. -/
def qnan (f : Fmt) : Nat := (f.expMax <<< f.fracBits) + 2 ^ (f.fracBits - 1)

/-- A finite value as `(negative, m, e)` meaning `±m · 2^e`. -/
def finite (f : Fmt) (b : Nat) : Bool × Nat × Int :=
  let ex := f.expField b
  if ex = 0 then (f.sign b, f.frac b, f.emin)
  else (f.sign b, f.frac b + 2 ^ f.fracBits, (ex : Int) - f.bias - f.fracBits)

/-- `n / 2^s` rounded to nearest, ties to even, for `s ≥ 1`. -/
def roundShift (n s : Nat) : Nat :=
  let q := n >>> s
  let r := n % 2 ^ s
  let half := 2 ^ (s - 1)
  if r > half || (r = half && q % 2 = 1) then q + 1 else q

/-- Round `±n · 2^e` (`n ≠ 0`) once to the format, to nearest, ties to
even; overflow yields the infinity of that sign, small values the
subnormal encoding. -/
def encode (f : Fmt) (neg : Bool) (n : Nat) (e : Int) : Nat :=
  if n = 0 then f.signOnly neg else
  let len : Nat := Nat.log2 n + 1
  let eu : Int := max (e + len - f.prec) f.emin
  let q0 : Nat :=
    if e ≥ eu then n <<< (e - eu).toNat else roundShift n (eu - e).toNat
  let (q, eu) : Nat × Int :=
    if q0 = 2 ^ f.prec then (q0 / 2, eu + 1) else (q0, eu)
  if q < 2 ^ f.fracBits then f.signOnly neg + q
  else
    let expF : Int := eu + f.fracBits + f.bias
    if expF ≥ f.expMax then f.inf neg
    else f.signOnly neg + (expF.toNat <<< f.fracBits) + (q - 2 ^ f.fracBits)

def copysign (f : Fmt) (x y : Nat) : Nat :=
  (x % f.signBit) + (if f.sign y then f.signBit else 0)

/-- One rounding of `a * b + c` over the bit patterns. -/
def fma (f : Fmt) (a b c : Nat) : Nat :=
  if f.isNaN a || f.isNaN b || f.isNaN c then f.qnan
  else if f.isInf a || f.isInf b then
    if f.isZero a || f.isZero b then f.qnan
    else
      let ps := f.sign a != f.sign b
      if f.isInf c && (f.sign c != ps) then f.qnan else f.inf ps
  else if f.isInf c then c
  else
    let (sa, ma, ea) := f.finite a
    let (sb, mb, eb) := f.finite b
    let (sc, mc, ec) := f.finite c
    let ps := sa != sb
    if ma = 0 || mb = 0 then
      -- An exact zero product: the sum is c, except that two zeros of
      -- different signs give +0 under round to nearest.
      if mc = 0 then (if ps = sc then f.signOnly ps else 0) else c
    else
      let eP : Int := ea + eb
      let emin : Int := min eP ec
      let P : Int := (if ps then -1 else 1) * (ma * mb : Nat) * ((2 : Int) ^ (eP - emin).toNat)
      let Z : Int := (if sc then -1 else 1) * (mc : Nat) * ((2 : Int) ^ (ec - emin).toNat)
      let N : Int := P + Z
      if N = 0 then 0 else f.encode (N < 0) N.natAbs emin

end Fmt

def copysign64 (x y : Float) : Float :=
  Float.ofBits (UInt64.ofNat (binary64.copysign x.toBits.toNat y.toBits.toNat))

def copysign32 (x y : Float32) : Float32 :=
  Float32.ofBits (UInt32.ofNat (binary32.copysign x.toBits.toNat y.toBits.toNat))

def fma64 (a b c : Float) : Float :=
  Float.ofBits (UInt64.ofNat (binary64.fma a.toBits.toNat b.toBits.toNat c.toBits.toNat))

def fma32 (a b c : Float32) : Float32 :=
  Float32.ofBits (UInt32.ofNat (binary32.fma a.toBits.toNat b.toBits.toNat c.toBits.toNat))

/-- Round to nearest, ties to even (C `rint`). -/
def roundEven64 (x : Float) : Float :=
  if x.isNaN || x.isInf then x else
  let t := x.round
  let d := x - t
  let tie := d == 0.5 || d == -0.5
  let odd := (t * 0.5).floor * 2.0 != t
  let r := if tie && odd then (if x < 0.0 then t + 1.0 else t - 1.0) else t
  if r == 0.0 then copysign64 r x else r

def roundEven32 (x : Float32) : Float32 :=
  if x.isNaN || x.isInf then x else
  let t := x.round
  let d := x - t
  let tie := d == 0.5 || d == -0.5
  let odd := (t * 0.5).floor * 2.0 != t
  let r := if tie && odd then (if x < 0.0 then t + 1.0 else t - 1.0) else t
  if r == 0.0 then copysign32 r x else r

end Oak.FloatOps
