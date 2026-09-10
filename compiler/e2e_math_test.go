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
	"testing"

	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

const referencePrecision = 320

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

// mathReference evaluates one library function at x in high precision, or
// reports the exact special-value result as a float64 (NaN, infinities,
// exact zeros) when the mathematics is not a finite non-zero real.
func mathReference(name string, x float64) (exact float64, ref *big.Float, isExact bool) {
	switch {
	case math.IsNaN(x):
		return math.NaN(), nil, true
	}
	bx := newBig(x)
	// For |x| below 2^-60 the correctly rounded expm1(x) and tanh(x) are x
	// itself (the next series term is below half an ulp), and the
	// high-precision evaluation would lose x against 1.
	if (name == "expm1" || name == "tanh") && x != 0 && math.Abs(x) < 0x1p-60 {
		return x, nil, true
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
	}
	panic("unknown function " + name)
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
	d, _ := diff.Float64()
	return d / ulp
}

type mathCase struct {
	function string
	width    int
	x        float64
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
			cases = append(cases, mathCase{function, width, x})
		}
	}
	nan := math.NaN()
	inf := math.Inf(1)
	tiny := 1e-300
	for _, width := range []int{64, 32} {
		expPoints := []float64{0, math.Copysign(0, -1), 1, -1, 0.5, -0.5, 0.1, 2, 10, -10, 100, -100, 0.6931471805599453, 1.0397207708399179,
			709.7, -708, -745, 710, 1e-10, -1e-10, tiny, nan, inf, -inf, 3.5, 20.25, -37.9}
		if width == 32 {
			expPoints = append(expPoints, 88.7, -87.3, -103.9)
		}
		add("exp", width, expPoints...)
		add("expm1", width, expPoints...)
		add("exp2", width, 0, 0.5, -0.5, 1, 3, -3, 10.75, -10.75, 0.1, 1023.5, -1074, 1025, 1e-9, nan, inf, -inf, 127.5, -149.5)
		logPoints := []float64{1, 2, 0.5, 10, 0.1, 1e-300, 1e300, 5e-324, 1.0000001, 0.9999999, 4, 0.75, 1.4142135623730951, 0.7071067811865476,
			0, math.Copysign(0, -1), -1, nan, inf, 1e-45, 3.4028234663852886e38, 123456.789}
		add("log", width, logPoints...)
		add("log2", width, logPoints...)
		add("tanh", width, 0, math.Copysign(0, -1), 1e-10, -1e-10, 0.25, -0.25, 0.5, 1, 2, -2, 10, 22, -22, 30, nan, inf, -inf, 1e-30)
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
			add("tanh", width, mag*math.Min(1, 25/math.Abs(mag)))
		}
	}
	return cases
}

func (c mathCase) call() string {
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

// mathBounds are the documented error bounds in ulps (stdlib/math.oak).
// tanh composes expm1 with a division and reaches about 1.5 ulp in the
// |x| < 1 path (fdlibm), so its contract is 2.
var mathBounds = map[string]float64{"exp": 1, "exp2": 1, "expm1": 1, "log": 1, "log2": 1, "tanh": 2}

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
	failures := 0
	for k, c := range cases {
		compiled, err := strconv.ParseUint(lines[k], 16, 64)
		if err != nil {
			t.Fatalf("case %d: bad hex %q", k, lines[k])
		}
		call := parser.New(layout.New(scanner.New(fmt.Sprintf("case_%d()", k)))).ParseProgram()
		result := evaluator.Eval(call, env)
		if e, isErr := result.(*object.Error); isErr {
			t.Fatalf("interpreter error in case %d (%s %d %v): %s", k, c.function, c.width, c.x, e.Message)
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
			t.Errorf("%s(%v): compiled %016x, interpreter %016x differ", key, c.x, compiled, interpreted)
			continue
		}
		exact, ref, isExact := mathReference(c.function, c.x)
		if isExact {
			want := toBits(exact, c.width)
			if !sameFloatBits(want, compiled, c.width) {
				failures++
				t.Errorf("%s(%v): got %v (%016x), want exactly %v", key, c.x, got, compiled, exact)
			}
			continue
		}
		err32 := ulpError(got, ref, c.width)
		if err32 > worst[key] {
			worst[key] = err32
		}
		if err32 > mathBounds[c.function] {
			failures++
			refValue, _ := ref.Float64()
			t.Errorf("%s(%v): got %v, reference %v, error %.3f ulp exceeds the bound of %g", key, c.x, got, refValue, err32, mathBounds[c.function])
		}
	}
	if failures != 0 {
		t.Fatalf("%d of %d math cases failed", failures, len(cases))
	}
	for key, w := range worst {
		t.Logf("%-10s worst error %.3f ulp", key, w)
	}
}
