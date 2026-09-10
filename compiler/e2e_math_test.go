package compiler

// The fourth witness for the math library (docs/spec/20-types.md section
// 11.3.6): every function of stdlib/math.oak is evaluated by the compiled C
// program and by the interpreter over a corpus of arguments, both results
// must be bit-identical (the library is written in Oak over correctly
// rounded primitives, so there is no libm variance), and both must lie
// within the documented ulp bound of an arbitrary-precision reference
// computed here with math/big.

import (
	"fmt"
	"math"
	"math/big"
	"math/rand"
	"os"
	"strconv"
	"strings"
	"sync"
	"testing"

	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

const referencePrecision = 320

// reductionPrecision covers the argument reduction of the trigonometric
// functions for the largest f64: x 2/pi needs about 1024 bits before the
// binary point plus the reference precision after it.
const reductionPrecision = 1700

// ln2 to 100 digits.
const ln2Digits = "0.6931471805599453094172321214581765680755001343602552541206800094933936219696947156058633269964186875"

func bigLn2() *big.Float {
	v, _, err := big.ParseFloat(ln2Digits, 10, referencePrecision, big.ToNearestEven)
	if err != nil {
		panic(err)
	}
	return v
}

func newBig(v float64) *big.Float { return new(big.Float).SetPrec(referencePrecision).SetFloat64(v) }

func bigAt(prec uint) *big.Float { return new(big.Float).SetPrec(prec) }

// atanInverse is atan(1/n) by its Taylor series at the given precision.
func atanInverse(n int64, prec uint) *big.Float {
	x := bigAt(prec).Quo(bigAt(prec).SetInt64(1), bigAt(prec).SetInt64(n))
	x2 := bigAt(prec).Mul(x, x)
	sum := bigAt(prec).Set(x)
	power := bigAt(prec).Set(x)
	for k := int64(1); ; k++ {
		power.Mul(power, x2)
		term := bigAt(prec).Quo(power, bigAt(prec).SetInt64(2*k+1))
		if term.Sign() == 0 || term.MantExp(nil)-sum.MantExp(nil) < -int(prec)-8 {
			break
		}
		if k%2 == 1 {
			sum.Sub(sum, term)
		} else {
			sum.Add(sum, term)
		}
	}
	return sum
}

var (
	bigPiOnce  sync.Once
	bigPiValue *big.Float
)

// bigPi is pi at reductionPrecision by Machin's formula
// pi = 16 atan(1/5) - 4 atan(1/239).
func bigPi() *big.Float {
	bigPiOnce.Do(func() {
		a := atanInverse(5, reductionPrecision)
		b := atanInverse(239, reductionPrecision)
		pi := bigAt(reductionPrecision).Mul(a, bigAt(reductionPrecision).SetInt64(16))
		pi.Sub(pi, bigAt(reductionPrecision).Mul(b, bigAt(reductionPrecision).SetInt64(4)))
		bigPiValue = pi
	})
	return bigPiValue
}

// refExp is e^x by argument reduction with the high-precision ln 2 and a
// Taylor series on the remainder.
func refExp(x *big.Float) *big.Float {
	ln2 := bigLn2()
	// n = round(x / ln2)
	q := new(big.Float).SetPrec(referencePrecision).Quo(x, ln2)
	qf, _ := q.Float64()
	n := math.Round(qf)
	r := new(big.Float).SetPrec(referencePrecision).Sub(x, new(big.Float).SetPrec(referencePrecision).Mul(ln2, newBig(n)))
	// Taylor series for exp(r), |r| <= ln2/2.
	sum := newBig(1)
	term := newBig(1)
	for k := 1; k < 200; k++ {
		term.Mul(term, r)
		term.Quo(term, newBig(float64(k)))
		sum.Add(sum, term)
		if term.Sign() == 0 || term.MantExp(nil)-sum.MantExp(nil) < -referencePrecision-8 {
			break
		}
	}
	return sum.SetMantExp(sum, int(n))
}

// refLog is ln x for x > 0: x = m 2^e with m in [0.5, 1), ln m by the
// atanh series, plus e ln 2.
func refLog(x *big.Float) *big.Float {
	m := new(big.Float).SetPrec(referencePrecision)
	e := x.MantExp(m) // x = m * 2^e, m in [0.5, 1)
	// t = (m - 1) / (m + 1), |t| <= 1/3
	num := new(big.Float).SetPrec(referencePrecision).Sub(m, newBig(1))
	den := new(big.Float).SetPrec(referencePrecision).Add(m, newBig(1))
	t := new(big.Float).SetPrec(referencePrecision).Quo(num, den)
	t2 := new(big.Float).SetPrec(referencePrecision).Mul(t, t)
	sum := new(big.Float).SetPrec(referencePrecision).Set(t)
	power := new(big.Float).SetPrec(referencePrecision).Set(t)
	for k := 3; k < 2000; k += 2 {
		power.Mul(power, t2)
		term := new(big.Float).SetPrec(referencePrecision).Quo(power, newBig(float64(k)))
		sum.Add(sum, term)
		if term.Sign() == 0 || term.MantExp(nil)-sum.MantExp(nil) < -referencePrecision-8 {
			break
		}
	}
	sum.Mul(sum, newBig(2))
	return sum.Add(sum, new(big.Float).SetPrec(referencePrecision).Mul(bigLn2(), newBig(float64(e))))
}

// refSinCos is (sin x, cos x) for finite x: x is reduced by the nearest
// multiple of pi/2 at reductionPrecision, the remainder's sine and cosine
// come from their Taylor series, and the quadrant selects and signs them.
func refSinCos(x float64) (*big.Float, *big.Float) {
	bx := bigAt(reductionPrecision).SetFloat64(x)
	halfPi := bigAt(reductionPrecision).Quo(bigPi(), bigAt(reductionPrecision).SetInt64(2))
	q := bigAt(reductionPrecision).Quo(bx, halfPi)
	// k = round(q)
	half := bigAt(reductionPrecision).SetFloat64(0.5)
	if q.Sign() < 0 {
		half.Neg(half)
	}
	k := new(big.Int)
	bigAt(reductionPrecision).Add(q, half).Int(k)
	r := bigAt(reductionPrecision).Sub(bx, bigAt(reductionPrecision).Mul(halfPi, bigAt(reductionPrecision).SetInt(k)))
	r = bigAt(referencePrecision).Set(r)
	r2 := bigAt(referencePrecision).Mul(r, r)
	// sin r = r - r^3/3! + ..., cos r = 1 - r^2/2! + ...
	sinR := bigAt(referencePrecision).Set(r)
	cosR := bigAt(referencePrecision).SetInt64(1)
	sinTerm := bigAt(referencePrecision).Set(r)
	cosTerm := bigAt(referencePrecision).SetInt64(1)
	for n := 1; n < 400; n++ {
		cosTerm.Mul(cosTerm, r2)
		cosTerm.Quo(cosTerm, bigAt(referencePrecision).SetInt64(int64((2*n-1)*(2*n))))
		cosTerm.Neg(cosTerm)
		cosR.Add(cosR, cosTerm)
		sinTerm.Mul(sinTerm, r2)
		sinTerm.Quo(sinTerm, bigAt(referencePrecision).SetInt64(int64((2*n)*(2*n+1))))
		sinTerm.Neg(sinTerm)
		sinR.Add(sinR, sinTerm)
		if sinTerm.Sign() == 0 || sinTerm.MantExp(nil) < -referencePrecision-8 {
			break
		}
	}
	quadrant := new(big.Int).Mod(k, big.NewInt(4)).Int64()
	negSin := bigAt(referencePrecision).Neg(sinR)
	negCos := bigAt(referencePrecision).Neg(cosR)
	switch quadrant {
	case 0:
		return sinR, cosR
	case 1:
		return cosR, negSin
	case 2:
		return negSin, negCos
	default:
		return negCos, sinR
	}
}

// refPi is pi at the reference precision.
func refPi() *big.Float { return bigAt(referencePrecision).Set(bigPi()) }

// refAtan is atan x: |x| > 1 goes through pi/2 - atan(1/|x|), the argument
// is halved by atan t = 2 atan(t / (1 + sqrt(1 + t^2))) until |t| < 2^-8,
// and the Taylor series finishes.
func refAtan(x *big.Float) *big.Float {
	t := bigAt(referencePrecision).Abs(x)
	invert := t.Cmp(bigAt(referencePrecision).SetInt64(1)) > 0
	if invert {
		t.Quo(bigAt(referencePrecision).SetInt64(1), t)
	}
	halvings := 0
	threshold := bigAt(referencePrecision).SetMantExp(bigAt(referencePrecision).SetInt64(1), -8)
	for t.Sign() != 0 && t.Cmp(threshold) > 0 {
		t2 := bigAt(referencePrecision).Mul(t, t)
		root := bigAt(referencePrecision).Sqrt(t2.Add(t2, bigAt(referencePrecision).SetInt64(1)))
		t.Quo(t, root.Add(root, bigAt(referencePrecision).SetInt64(1)))
		halvings++
	}
	t2 := bigAt(referencePrecision).Mul(t, t)
	sum := bigAt(referencePrecision).Set(t)
	power := bigAt(referencePrecision).Set(t)
	for k := 1; k < 400; k++ {
		power.Mul(power, t2)
		term := bigAt(referencePrecision).Quo(power, bigAt(referencePrecision).SetInt64(int64(2*k+1)))
		if k%2 == 1 {
			sum.Sub(sum, term)
		} else {
			sum.Add(sum, term)
		}
		if term.Sign() == 0 || term.MantExp(nil)-sum.MantExp(nil) < -referencePrecision-8 {
			break
		}
	}
	sum.SetMantExp(sum, halvings)
	if invert {
		halfPi := refPi()
		halfPi.Quo(halfPi, bigAt(referencePrecision).SetInt64(2))
		sum.Sub(halfPi, sum)
	}
	if x.Sign() < 0 {
		sum.Neg(sum)
	}
	return sum
}

// refPow is x^y for finite x > 0 and finite y as exp(y ln x); results
// beyond every format's range are reported exactly.
func refPow(x, y float64) (exact float64, ref *big.Float, isExact bool) {
	l := bigAt(referencePrecision).Mul(newBig(y), refLog(newBig(x)))
	lf, _ := l.Float64()
	if lf > 1100 {
		return math.Inf(1), nil, true
	}
	if lf < -1100 {
		return 0, nil, true
	}
	return 0, refExp(l), false
}

// isOddInteger reports whether y is an odd integer (IEEE 754 pow rules).
func isOddInteger(y float64) bool {
	if y != math.Trunc(y) || math.IsInf(y, 0) {
		return false
	}
	return math.Abs(math.Mod(y, 2)) == 1
}

// mathReference evaluates one library function at (x, y) in high
// precision, or reports the exact special-value result as a float64 (NaN,
// infinities, exact zeros) when the mathematics is not a finite non-zero
// real.
func mathReference(name string, x, y float64) (exact float64, ref *big.Float, isExact bool) {
	if name == "pow" {
		return powReference(x, y)
	}
	if name == "atan2" {
		return atan2Reference(x, y)
	}
	if math.IsNaN(x) {
		return math.NaN(), nil, true
	}
	bx := newBig(x)
	// For |x| below 2^-60 the correctly rounded expm1, tanh, log1p, sin,
	// and tan of x are x itself (the next series term is below half an
	// ulp), and cos x is 1.
	if x != 0 && math.Abs(x) < 0x1p-60 {
		switch name {
		case "expm1", "tanh", "log1p", "sin", "tan", "atan", "asin", "sinh", "asinh", "atanh":
			return x, nil, true
		case "cos", "cosh":
			return 1, nil, true
		}
	}
	switch name {
	case "exp", "exp2", "expm1":
		if math.IsInf(x, 1) {
			return math.Inf(1), nil, true
		}
		if math.IsInf(x, -1) {
			if name == "expm1" {
				return -1, nil, true
			}
			return 0, nil, true
		}
		arg := bx
		if name == "exp2" {
			arg = new(big.Float).SetPrec(referencePrecision).Mul(bx, bigLn2())
		}
		v := refExp(arg)
		if name == "expm1" {
			v.Sub(v, newBig(1))
			if v.Sign() == 0 {
				return math.Copysign(0, x), nil, true
			}
		}
		return 0, v, false
	case "log", "log2":
		if x == 0 {
			return math.Inf(-1), nil, true
		}
		if x < 0 {
			return math.NaN(), nil, true
		}
		if math.IsInf(x, 1) {
			return math.Inf(1), nil, true
		}
		if x == 1 {
			return 0, nil, true
		}
		v := refLog(bx)
		if name == "log2" {
			v.Quo(v, bigLn2())
		}
		return 0, v, false
	case "log1p":
		if x == -1 {
			return math.Inf(-1), nil, true
		}
		if x < -1 {
			return math.NaN(), nil, true
		}
		if math.IsInf(x, 1) {
			return math.Inf(1), nil, true
		}
		if x == 0 {
			return x, nil, true
		}
		return 0, refLog(new(big.Float).SetPrec(referencePrecision).Add(bx, newBig(1))), false
	case "tanh":
		if math.IsInf(x, 0) {
			return math.Copysign(1, x), nil, true
		}
		if x == 0 {
			return x, nil, true
		}
		if math.Abs(x) > 40 {
			return math.Copysign(1, x), nil, true
		}
		e2 := refExp(new(big.Float).SetPrec(referencePrecision).Mul(bx, newBig(2)))
		num := new(big.Float).SetPrec(referencePrecision).Sub(e2, newBig(1))
		den := new(big.Float).SetPrec(referencePrecision).Add(e2, newBig(1))
		return 0, num.Quo(num, den), false
	case "sin", "cos", "tan":
		if math.IsInf(x, 0) {
			return math.NaN(), nil, true
		}
		if x == 0 {
			if name == "cos" {
				return 1, nil, true
			}
			return x, nil, true
		}
		s, c := refSinCos(x)
		switch name {
		case "sin":
			return 0, s, false
		case "cos":
			return 0, c, false
		default:
			return 0, bigAt(referencePrecision).Quo(s, c), false
		}
	case "atan":
		if math.IsInf(x, 0) {
			half := refPi()
			half.Quo(half, bigAt(referencePrecision).SetInt64(2))
			if x < 0 {
				half.Neg(half)
			}
			return 0, half, false
		}
		if x == 0 {
			return x, nil, true
		}
		return 0, refAtan(bx), false
	case "asin", "acos":
		if math.Abs(x) > 1 {
			return math.NaN(), nil, true
		}
		if name == "acos" && x == 1 {
			return 0, nil, true
		}
		if name == "asin" && x == 0 {
			return x, nil, true
		}
		// asin x = atan(x / sqrt(1 - x^2)); acos x = pi/2 - asin x
		var asin *big.Float
		if math.Abs(x) == 1 {
			asin = refPi()
			asin.Quo(asin, bigAt(referencePrecision).SetInt64(2))
			if x < 0 {
				asin.Neg(asin)
			}
		} else {
			one := bigAt(referencePrecision).SetInt64(1)
			den := bigAt(referencePrecision).Sqrt(one.Sub(one, bigAt(referencePrecision).Mul(bx, bx)))
			asin = refAtan(bigAt(referencePrecision).Quo(bx, den))
		}
		if name == "asin" {
			return 0, asin, false
		}
		half := refPi()
		half.Quo(half, bigAt(referencePrecision).SetInt64(2))
		return 0, half.Sub(half, asin), false
	case "sinh", "cosh":
		if math.IsInf(x, 0) {
			if name == "sinh" {
				return x, nil, true
			}
			return math.Inf(1), nil, true
		}
		if x == 0 {
			if name == "sinh" {
				return x, nil, true
			}
			return 1, nil, true
		}
		if math.Abs(x) > 712 {
			if name == "sinh" {
				return math.Copysign(math.Inf(1), x), nil, true
			}
			return math.Inf(1), nil, true
		}
		e := refExp(bx)
		inverse := bigAt(referencePrecision).Quo(bigAt(referencePrecision).SetInt64(1), e)
		v := bigAt(referencePrecision)
		if name == "sinh" {
			v.Sub(e, inverse)
		} else {
			v.Add(e, inverse)
		}
		return 0, v.Quo(v, bigAt(referencePrecision).SetInt64(2)), false
	case "asinh":
		if math.IsInf(x, 0) || x == 0 {
			return x, nil, true
		}
		ax := bigAt(referencePrecision).Abs(bx)
		root := bigAt(referencePrecision).Mul(ax, ax)
		root.Sqrt(root.Add(root, bigAt(referencePrecision).SetInt64(1)))
		v := refLog(root.Add(root, ax))
		if x < 0 {
			v.Neg(v)
		}
		return 0, v, false
	case "acosh":
		if x < 1 {
			return math.NaN(), nil, true
		}
		if x == 1 {
			return 0, nil, true
		}
		if math.IsInf(x, 1) {
			return math.Inf(1), nil, true
		}
		root := bigAt(referencePrecision).Mul(bx, bx)
		root.Sqrt(root.Sub(root, bigAt(referencePrecision).SetInt64(1)))
		return 0, refLog(root.Add(root, bx)), false
	case "atanh":
		if math.Abs(x) > 1 {
			return math.NaN(), nil, true
		}
		if math.Abs(x) == 1 {
			return math.Copysign(math.Inf(1), x), nil, true
		}
		if x == 0 {
			return x, nil, true
		}
		one := bigAt(referencePrecision).SetInt64(1)
		num := bigAt(referencePrecision).Add(one, bx)
		den := bigAt(referencePrecision).Sub(one, bx)
		v := refLog(num.Quo(num, den))
		return 0, v.Quo(v, bigAt(referencePrecision).SetInt64(2)), false
	}
	panic("unknown function " + name)
}

// atan2Reference applies the C99 Annex F.9.1.4 special cases of atan2(y, x)
// before delegating to refAtan; the arguments arrive as (x=y, y=x) in the
// case's field order, that is, the case's x is the first argument y.
func atan2Reference(y, x float64) (exact float64, ref *big.Float, isExact bool) {
	pi := func(scale float64, sign float64) (float64, *big.Float, bool) {
		v := refPi()
		v.Mul(v, bigAt(referencePrecision).SetFloat64(scale))
		if sign < 0 || (sign == 0 && math.Signbit(sign)) {
			v.Neg(v)
		}
		return 0, v, false
	}
	switch {
	case math.IsNaN(x) || math.IsNaN(y):
		return math.NaN(), nil, true
	case y == 0:
		if x > 0 || (x == 0 && !math.Signbit(x)) {
			return y, nil, true
		}
		return pi(1, y)
	case x == 0:
		return pi(0.5, y)
	case math.IsInf(x, 1):
		if math.IsInf(y, 0) {
			return pi(0.25, y)
		}
		return math.Copysign(0, y), nil, true
	case math.IsInf(x, -1):
		if math.IsInf(y, 0) {
			return pi(0.75, y)
		}
		return pi(1, y)
	case math.IsInf(y, 0):
		return pi(0.5, y)
	}
	ratio := bigAt(referencePrecision).Quo(bigAt(referencePrecision).SetFloat64(math.Abs(y)), bigAt(referencePrecision).SetFloat64(math.Abs(x)))
	a := refAtan(ratio)
	if x < 0 {
		a.Sub(refPi(), a)
	}
	if y < 0 {
		a.Neg(a)
	}
	return 0, a, false
}

// powReference applies the IEEE 754-2019 / C99 Annex F.9.4.4 special cases
// of pow before delegating finite positive bases to refPow.
func powReference(x, y float64) (exact float64, ref *big.Float, isExact bool) {
	switch {
	case y == 0 || x == 1:
		return 1, nil, true
	case math.IsNaN(x) || math.IsNaN(y):
		return math.NaN(), nil, true
	case x == 0:
		if y < 0 {
			if isOddInteger(y) {
				return math.Copysign(math.Inf(1), x), nil, true
			}
			return math.Inf(1), nil, true
		}
		if isOddInteger(y) {
			return x, nil, true
		}
		return 0, nil, true
	case math.IsInf(y, 0):
		if x == -1 {
			return 1, nil, true
		}
		if (math.Abs(x) < 1) == (y < 0) {
			return math.Inf(1), nil, true
		}
		return 0, nil, true
	case math.IsInf(x, -1):
		if y < 0 {
			if isOddInteger(y) {
				return math.Copysign(0, -1), nil, true
			}
			return 0, nil, true
		}
		if isOddInteger(y) {
			return math.Inf(-1), nil, true
		}
		return math.Inf(1), nil, true
	case math.IsInf(x, 1):
		if y < 0 {
			return 0, nil, true
		}
		return math.Inf(1), nil, true
	case x < 0 && y != math.Trunc(y):
		return math.NaN(), nil, true
	}
	exact, ref, isExact = refPow(math.Abs(x), y)
	if x < 0 && isOddInteger(y) {
		if isExact {
			return -exact, nil, true
		}
		return 0, ref.Neg(ref), false
	}
	return exact, ref, isExact
}

// ulpError measures |got - ref| in units of the last place of the target
// width at the reference's magnitude. Results that overflow or underflow
// the format are compared as the format's rounding of the reference.
func ulpError(got float64, ref *big.Float, width int) float64 {
	var nearest float64
	if width == 32 {
		r32, _ := ref.Float32()
		nearest = float64(r32)
	} else {
		nearest, _ = ref.Float64()
	}
	if math.IsInf(nearest, 0) {
		if got == nearest {
			return 0
		}
		return math.Inf(1)
	}
	var ulp float64
	if width == 32 {
		a := float32(math.Abs(nearest))
		ulp = float64(math.Nextafter32(a, float32(math.Inf(1))) - a)
	} else {
		a := math.Abs(nearest)
		ulp = math.Nextafter(a, math.Inf(1)) - a
	}
	diff := new(big.Float).SetPrec(referencePrecision).Sub(newBig(got), ref)
	diff.Abs(diff)
	// The ratio is formed in high precision: a difference at subnormal
	// scale would itself round if converted to float64 first.
	ratio, _ := diff.Quo(diff, newBig(ulp)).Float64()
	return ratio
}

type mathCase struct {
	function string
	width    int
	x        float64
	y        float64 // second argument of the two-argument functions only
}

// twoArgument names the library functions of two arguments; for pow the
// arguments are (x, y), for atan2 they are (y, x) in that order.
var twoArgument = map[string]bool{"pow": true, "atan2": true}

// nearestMultipleOfHalfPi is the f64 nearest to k pi/2: the hardest
// arguments for the reduction, whose true remainders are far smaller than
// the argument's ulp.
func nearestMultipleOfHalfPi(k float64) float64 {
	halfPi := bigAt(reductionPrecision).Quo(bigPi(), bigAt(reductionPrecision).SetInt64(2))
	v, _ := bigAt(reductionPrecision).Mul(halfPi, bigAt(reductionPrecision).SetFloat64(k)).Float64()
	return v
}

// mathCorpus: the special points of each function plus log-uniform random
// arguments over each function's domain.
func mathCorpus(rng *rand.Rand) []mathCase {
	var cases []mathCase
	add := func(function string, width int, xs ...float64) {
		for _, x := range xs {
			if width == 32 {
				// The f32 functions receive the f32 nearest to x; the
				// reference must see exactly that argument.
				x = float64(float32(x))
			}
			cases = append(cases, mathCase{function: function, width: width, x: x})
		}
	}
	addPow := func(width int, x, y float64) {
		if width == 32 {
			x = float64(float32(x))
			y = float64(float32(y))
		}
		cases = append(cases, mathCase{function: "pow", width: width, x: x, y: y})
	}
	nan := math.NaN()
	inf := math.Inf(1)
	negZero := math.Copysign(0, -1)
	tiny := 1e-300
	// Kahan's hardest f64 for pi/2 reduction: 6381956970095103 2^797 lies
	// within 4.7e-19 of a multiple of pi/2.
	kahan := math.Ldexp(6381956970095103, 797)
	for _, width := range []int{64, 32} {
		expPoints := []float64{0, negZero, 1, -1, 0.5, -0.5, 0.1, 2, 10, -10, 100, -100, 0.6931471805599453, 1.0397207708399179,
			709.7, -708, -745, 710, 1e-10, -1e-10, tiny, nan, inf, -inf, 3.5, 20.25, -37.9}
		if width == 32 {
			expPoints = append(expPoints, 88.7, -87.3, -103.9)
		}
		add("exp", width, expPoints...)
		add("expm1", width, expPoints...)
		add("exp2", width, 0, 0.5, -0.5, 1, 3, -3, 10.75, -10.75, 0.1, 1023.5, -1074, 1025, 1e-9, nan, inf, -inf, 127.5, -149.5)
		logPoints := []float64{1, 2, 0.5, 10, 0.1, 1e-300, 1e300, 5e-324, 1.0000001, 0.9999999, 4, 0.75, 1.4142135623730951, 0.7071067811865476,
			0, negZero, -1, nan, inf, 1e-45, 3.4028234663852886e38, 123456.789}
		add("log", width, logPoints...)
		add("log2", width, logPoints...)
		add("log1p", width, 0, negZero, 1e-10, -1e-10, 1e-20, 0.5, -0.5, 1, -0.9999999, -1, -2, 0.29, -0.29, 0.42, 0.41421356, 3, 1e10, 1e300,
			nan, inf, -inf, 2.220446049250313e-16, -2.220446049250313e-16, 5e-324, 1e-45, 3.4e38)
		add("tanh", width, 0, negZero, 1e-10, -1e-10, 0.25, -0.25, 0.5, 1, 2, -2, 10, 22, -22, 30, nan, inf, -inf, 1e-30)
		trigPoints := []float64{0, negZero, 1e-10, -1e-10, 1e-20, 0.25, 0.5, 0.67, 0.68, 0.6744, 0.7853981633974483, 0.7853981633974484,
			1, -1, 1.5707963267948966, 2, 3, 3.141592653589793, 4.71238898038469, 6.283185307179586, 10, 100, -100, 1e6, 1647099.3, 1.7e6,
			1e10, 1e16, 4.5e15, 1e22, -1e22, 1e100, 1e300, 1.7976931348623157e308, kahan, -kahan, 5e-324, nan, inf, -inf, 2.5e-8, 1e-8}
		if width == 32 {
			trigPoints = append(trigPoints, 3.4028234663852886e38, 1e30, 16777215, 33554430)
		}
		add("sin", width, trigPoints...)
		add("cos", width, trigPoints...)
		add("tan", width, trigPoints...)
		powPairs := [][2]float64{{2, 10}, {2, -1074}, {2, 0.5}, {10, 308}, {10, -320}, {0.5, 1075}, {-2, 3}, {-2, 4}, {-2, 0.5}, {-8, 1.0 / 3},
			{0, -1}, {negZero, -1}, {negZero, -2}, {0, 0.5}, {0, 3}, {negZero, 3}, {negZero, 4}, {inf, -1}, {inf, 2}, {-inf, 3}, {-inf, 2}, {-inf, -3}, {-inf, -2},
			{1, nan}, {nan, 0}, {nan, 1}, {1, inf}, {2, inf}, {0.5, inf}, {-1, inf}, {-1, -inf}, {0.5, -inf}, {2, -inf}, {-0.5, inf},
			{1.0000001, 1e9}, {0.9999999, -1e9}, {1.0000001, 2.5e9}, {1 + 0x1p-40, 1e15}, {1e-300, 2}, {1e300, 2}, {3, 0.3333333333333333},
			{7.5, 2.5}, {1.5, 1e5}, {2, 1023.5}, {2, 1024}, {2, -1075}, {2.5, -1070}, {-3, 7}, {-3, 8}, {-1.5, -3}, {10, 22}, {10, -22},
			{3, 40}, {0.1, 3}, {1e-5, -60}, {123.456, 7.89}, {0.9, 5000}, {1.1, -5000}, {2, 1e100}, {0.5, 1e100}, {-2, 1e100}, {1e-320, 0.5}, {1e-320, 2}}
		for _, p := range powPairs {
			addPow(width, p[0], p[1])
		}
		atanPoints := []float64{0, negZero, 1e-10, -1e-10, 1e-20, 0.4374, 0.4375, 0.4376, 0.6875, 0.6874, 1, -1, 1.1875, 1.1874, 2.4375, 2.4374, 3, 10, 1e6,
			1e10, 7.378697629483821e19, 1e300, inf, -inf, nan, 5e-324, 0.5, 1.5, -2.5}
		add("atan", width, atanPoints...)
		asinPoints := []float64{0, negZero, 1e-10, -1e-10, 1e-20, 0.25, -0.25, 0.5, -0.5, 0.4999999, 0.75, 0.975, 0.9750001, 0.9749999, 0.99, 0.999999, 0.9999999999999999,
			-0.9999999999999999, 1, -1, 1.0000001, -1.5, inf, -inf, nan, 5e-324, 6.938893903907228e-18, 0.7071067811865476}
		add("asin", width, asinPoints...)
		add("acos", width, asinPoints...)
		atan2Pairs := [][2]float64{{0, 1}, {negZero, 1}, {0, -1}, {negZero, -1}, {0, 0}, {0, negZero}, {negZero, 0}, {negZero, negZero}, {1, 0}, {-1, 0}, {1, negZero}, {-1, negZero},
			{1, inf}, {-1, inf}, {1, -inf}, {-1, -inf}, {inf, 1}, {-inf, 1}, {inf, -1}, {inf, inf}, {-inf, inf}, {inf, -inf}, {-inf, -inf}, {nan, 1}, {1, nan},
			{1, 1}, {-1, 1}, {1, -1}, {-1, -1}, {3, 4}, {-3, 4}, {3, -4}, {-3, -4}, {1e-300, 1}, {1, 1e-300}, {1e300, 1e-300}, {1e-300, -1}, {1e-20, -1e10}, {2, 1},
			{0.5, 2}, {7, -0.001}, {-1e10, 1e-10}, {1e-320, 1e-320}, {1, 1.0000000000000002}, {0.1, 0.3}}
		for _, p := range atan2Pairs {
			x, y := p[0], p[1]
			if width == 32 {
				x = float64(float32(x))
				y = float64(float32(y))
			}
			cases = append(cases, mathCase{function: "atan2", width: width, x: x, y: y})
		}
		hyperbolicPoints := []float64{0, negZero, 1e-10, -1e-10, 1e-20, 0.1, -0.1, 0.5, 0.6931471805599453, 0.7, 1, -1, 2, 10, 22, 22.5, 30, -30, 100, 700, 709.7, 710.4, 710.5, 711, -711,
			1000, inf, -inf, nan, 5e-324, 1.4901161193847656e-08}
		if width == 32 {
			hyperbolicPoints = append(hyperbolicPoints, 88.7, 89.5, -89.5, 90)
		}
		add("sinh", width, hyperbolicPoints...)
		add("cosh", width, hyperbolicPoints...)
		add("asinh", width, 0, negZero, 1e-10, -1e-10, 1e-20, 0.1, 0.125, 0.3, 0.5, -0.5, 1, -1, 1.5, 2, 3, 10, 67108864, 67108863, 1e10, 1e300, -1e300, inf, -inf, nan, 5e-324, 1.4901161193847656e-08)
		add("acosh", width, 1, 1.0000001, 1.0000000000000002, 1.05, 1.125, 1.126, 1.5, 2, 3, 10, 67108864, 67108863, 1e10, 1e300, inf, 0.5, 0, -1, -inf, nan)
		add("atanh", width, 0, negZero, 1e-10, -1e-10, 1e-20, 0.1, 0.25, 0.4999999, 0.5, 0.5000001, 0.75, 0.9, 0.999, 0.9999999, 0.9999999999999999, 1, -1, 1.5, -1.5, inf, nan, 5e-324, 2.3283064365386963e-10)
		for i := 0; i < 40; i++ {
			// log-uniform magnitudes with random sign
			mag := math.Pow(10, rng.Float64()*8-4)
			if rng.Intn(2) == 1 {
				mag = -mag
			}
			add("exp", width, mag*math.Min(1, 700/math.Abs(mag)))
			add("expm1", width, mag*math.Min(1, 700/math.Abs(mag)))
			add("exp2", width, mag*math.Min(1, 1000/math.Abs(mag)))
			logRange := 600.0
			if width == 32 {
				logRange = 74 // 10^-37 .. 10^37 stays within f32
			}
			add("log", width, math.Pow(10, rng.Float64()*logRange-logRange/2))
			add("log2", width, math.Pow(10, rng.Float64()*logRange-logRange/2))
			if mag > -1 {
				add("log1p", width, mag)
			}
			add("tanh", width, mag*math.Min(1, 25/math.Abs(mag)))
			// trigonometric: medium arguments, huge arguments through the
			// Payne-Hanek path, and near-multiples of pi/2
			trigRange := 300.0
			if width == 32 {
				trigRange = 38
			}
			huge := math.Pow(10, 8+rng.Float64()*(trigRange-8))
			near := nearestMultipleOfHalfPi(float64(1 + rng.Intn(1000000)))
			if width == 32 {
				near = nearestMultipleOfHalfPi(float64(1 + rng.Intn(4000)))
			}
			for _, function := range []string{"sin", "cos", "tan"} {
				add(function, width, mag*math.Min(1, 1e8/math.Abs(mag)), huge, near)
			}
			// pow: bases around 1 with exponents kept inside the format
			base := math.Pow(10, rng.Float64()*6-3)
			limit := 700.0
			if width == 32 {
				limit = 85
			}
			maxExponent := math.Min(60, limit/math.Abs(math.Log(base)))
			exponent := (rng.Float64()*2 - 1) * maxExponent
			addPow(width, base, exponent)
			addPow(width, -base, math.Trunc(exponent))
			addPow(width, 1+(rng.Float64()*2-1)*1e-6, (rng.Float64()*2-1)*1e6)
			// inverse trigonometric and hyperbolic
			add("atan", width, mag)
			unit := rng.Float64()*2 - 1
			nearOne := math.Copysign(1-math.Pow(10, -rng.Float64()*15), unit)
			if width == 32 {
				nearOne = math.Copysign(1-math.Pow(10, -rng.Float64()*7), unit)
			}
			add("asin", width, unit, nearOne)
			add("acos", width, unit, nearOne)
			add("atanh", width, unit, nearOne)
			other := math.Pow(10, rng.Float64()*8-4)
			if rng.Intn(2) == 1 {
				other = -other
			}
			second := other
			if width == 32 {
				second = float64(float32(other))
			}
			cases = append(cases, mathCase{function: "atan2", width: width, x: magAsWidth(mag, width), y: second})
			add("sinh", width, mag*math.Min(1, 700/math.Abs(mag)))
			add("cosh", width, mag*math.Min(1, 700/math.Abs(mag)))
			add("asinh", width, mag)
			add("acosh", width, 1+math.Abs(mag))
		}
	}
	return cases
}

// magAsWidth rounds an argument to the case's width.
func magAsWidth(v float64, width int) float64 {
	if width == 32 {
		return float64(float32(v))
	}
	return v
}

func (c mathCase) call() string {
	if twoArgument[c.function] {
		if c.width == 32 {
			return fmt.Sprintf("math.%s_f32(f32_bits_u32(u32(%d)), f32_bits_u32(u32(%d)))", c.function, math.Float32bits(float32(c.x)), math.Float32bits(float32(c.y)))
		}
		return fmt.Sprintf("math.%s(f64_bits_u64(u64(%d)), f64_bits_u64(u64(%d)))", c.function, math.Float64bits(c.x), math.Float64bits(c.y))
	}
	if c.width == 32 {
		return fmt.Sprintf("math.%s_f32(f32_bits_u32(u32(%d)))", c.function, math.Float32bits(float32(c.x)))
	}
	return fmt.Sprintf("math.%s(f64_bits_u64(u64(%d)))", c.function, math.Float64bits(c.x))
}

func (c mathCase) bitsExpression() string {
	if c.width == 32 {
		return "u64(u32_bits_f32(" + c.call() + "))"
	}
	return "u64_bits_f64(" + c.call() + ")"
}

func (c mathCase) String() string {
	if twoArgument[c.function] {
		return fmt.Sprintf("%s/f%d(%v, %v)", c.function, c.width, c.x, c.y)
	}
	return fmt.Sprintf("%s/f%d(%v)", c.function, c.width, c.x)
}

// mathBounds are the documented error bounds in ulps (stdlib/math.oak).
// tanh composes expm1 with a division and reaches about 1.5 ulp in the
// |x| < 1 path (fdlibm), so its contract is 2; atan2 adds the pi correction
// to atan's error and is observed near 1 ulp; the hyperbolics and their
// inverses are compositions of exp, expm1, log, and log1p.
var mathBounds = map[string]float64{
	"exp": 1, "exp2": 1, "expm1": 1, "log": 1, "log2": 1, "log1p": 1, "tanh": 2,
	"sin": 1, "cos": 1, "tan": 1, "pow": 1,
	"atan": 1, "atan2": 2, "asin": 1, "acos": 1,
	"sinh": 2, "cosh": 2, "asinh": 2, "acosh": 2, "atanh": 2,
}

func TestMathLibraryFourthWitness(t *testing.T) {
	seed := int64(20260910)
	if env := os.Getenv("OAK_MATH_SEED"); env != "" {
		parsed, err := strconv.ParseInt(env, 10, 64)
		if err != nil {
			t.Fatalf("OAK_MATH_SEED: %v", err)
		}
		seed = parsed
	}
	t.Logf("seed %d", seed)
	cases := mathCorpus(rand.New(rand.NewSource(seed)))

	var src strings.Builder
	src.WriteString("import(\"math\")\n\nputchar: (ch: c.Int): c.Int = c.extern(\"putchar\")\n\n")
	src.WriteString(`hex: (v: u64): () {
  shift: u64 = 64
  i: u32 = 0
  while i < 16 {
    shift = shift - 4
    d: u64 = (v >> shift) & 15
    ch: u64 = d < 10 ? d + 48 | d + 87
    _ = putchar(c.Int(i32_bits_u32(u32_trunc_u64(ch))))
    i = i + 1
  }
  _ = putchar(c.Int(10))
}

`)
	for k, c := range cases {
		fmt.Fprintf(&src, "case_%d: (): u64 {\n  %s\n}\n\n", k, c.bitsExpression())
	}
	src.WriteString("main: (): i32 {\n")
	for k := range cases {
		fmt.Fprintf(&src, "  hex(case_%d())\n", k)
	}
	src.WriteString("  0\n}\n")

	// Library packages resolve through the module loader, so the program is
	// a module root.
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/mathwitness\noak 0.1.0\n",
		"main.oak": "package main\n" + src.String(),
	})
	stdout, code, abnormal := buildAndRunFrom(t, "mathwitness", New().WithPackageDir(root))
	if abnormal || code != 0 {
		t.Fatalf("compiled math program exited (%d, abnormal=%v)", code, abnormal)
	}
	lines := strings.Fields(stdout)
	if len(lines) != len(cases) {
		t.Fatalf("compiled program printed %d results, want %d", len(lines), len(cases))
	}

	model, err := New().WithPackageDir(root).Check().Get()
	if err != nil {
		t.Fatalf("check failed: %v", err)
	}
	env := object.NewEnvironment()
	env.SetArithmeticWidths(model.TypeChecker.ArithmeticType)
	if result := evaluator.Eval(model.Tree.Root, env); result != nil {
		if e, isErr := result.(*object.Error); isErr {
			t.Fatalf("interpreter error evaluating program: %s", e.Message)
		}
	}

	worst := map[string]float64{}
	worstCase := map[string]mathCase{}
	failures := 0
	for k, c := range cases {
		compiled, err := strconv.ParseUint(lines[k], 16, 64)
		if err != nil {
			t.Fatalf("case %d: bad hex %q", k, lines[k])
		}
		call := parser.New(layout.New(scanner.New(fmt.Sprintf("case_%d()", k)))).ParseProgram()
		result := evaluator.Eval(call, env)
		if e, isErr := result.(*object.Error); isErr {
			t.Fatalf("interpreter error in case %d (%s): %s", k, c, e.Message)
		}
		integer, ok := result.(*object.Integer)
		if !ok {
			t.Fatalf("case %d returned %s", k, result.Inspect())
		}
		interpreted := uint64(integer.Value)
		key := fmt.Sprintf("%s/f%d", c.function, c.width)

		got := fromBits(compiled, c.width)
		if !sameFloatBits(compiled, interpreted, c.width) {
			failures++
			t.Errorf("%s: compiled %016x, interpreter %016x differ", c, compiled, interpreted)
			continue
		}
		exact, ref, isExact := mathReference(c.function, c.x, c.y)
		if isExact {
			want := toBits(exact, c.width)
			if !sameFloatBits(want, compiled, c.width) {
				failures++
				t.Errorf("%s: got %v (%016x), want exactly %v", c, got, compiled, exact)
			}
			continue
		}
		errUlps := ulpError(got, ref, c.width)
		if errUlps > worst[key] {
			worst[key] = errUlps
			worstCase[key] = c
		}
		if errUlps > mathBounds[c.function] {
			failures++
			refValue, _ := ref.Float64()
			t.Errorf("%s: got %v, reference %v, error %.3f ulp exceeds the bound of %g", c, got, refValue, errUlps, mathBounds[c.function])
		}
	}
	if failures != 0 {
		t.Fatalf("%d of %d math cases failed", failures, len(cases))
	}
	for key, w := range worst {
		t.Logf("%-10s worst error %.3f ulp at %s", key, w, worstCase[key])
	}
}
