package compiler

// Differential fuzz for floating point (docs/spec/20-types.md section
// 11.3.3, reproducibility): random f32 and f64 expression trees — every
// grouping of + - * /, unary minus, and the correctly rounded intrinsics
// over a pool of IEEE special values — must produce bit-identical results
// in three witnesses: an independent Go reference, the compiled C program
// (libc's fmaf/sqrtf/... and the plain operators under FP_CONTRACT OFF),
// and the interpreter. NaN results compare as a class, since the payload of
// a NaN is unspecified. The seed is fixed so a failure is reproducible.

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

type floatNode struct {
	kind  string // "leaf", "neg", "op", "call"
	op    string // + - * / for "op"; intrinsic name for "call"
	bits  uint64 // leaf value as the width's bit pattern
	args  []*floatNode
	width int
}

// floatPool are the leaf values, chosen for their rounding behavior:
// non-representable decimals, the 2^53 boundary, signed zeros, infinities,
// NaN, a subnormal, and the largest finite value.
func floatPool(width int) []float64 {
	if width == 32 {
		return []float64{0, math.Copysign(0, -1), 0.1, 0.2, 0.3, 1, -1, 3, 0.5, 2.5, -2.5, 7.9,
			1.0 / 3.0, 16777216, 16777218, 1e10, 1e30, 1e-40, math.MaxFloat32, math.Inf(1), math.Inf(-1), math.NaN()}
	}
	return []float64{0, math.Copysign(0, -1), 0.1, 0.2, 0.3, 1, -1, 3, 0.5, 2.5, -2.5, 7.9,
		1.0 / 3.0, 9007199254740992, 9007199254740994, 1e16, 1e300, 5e-324, math.MaxFloat64, math.Inf(1), math.Inf(-1), math.NaN()}
}

var floatUnaryCalls = []string{"sqrt", "abs", "floor", "ceil", "trunc", "round", "round_even"}
var floatBinaryCalls = []string{"copysign", "min", "max", "min_num", "max_num"}

func toBits(v float64, width int) uint64 {
	if width == 32 {
		return uint64(math.Float32bits(float32(v)))
	}
	return math.Float64bits(v)
}

func fromBits(bits uint64, width int) float64 {
	if width == 32 {
		return float64(math.Float32frombits(uint32(bits)))
	}
	return math.Float64frombits(bits)
}

func genFloatNode(rng *rand.Rand, width, depth int) *floatNode {
	if depth == 0 || rng.Intn(4) == 0 {
		pool := floatPool(width)
		return &floatNode{kind: "leaf", bits: toBits(pool[rng.Intn(len(pool))], width), width: width}
	}
	switch rng.Intn(11) {
	case 0:
		return &floatNode{kind: "neg", args: []*floatNode{genFloatNode(rng, width, depth-1)}, width: width}
	case 10:
		if width == 32 {
			// A round trip through a storage format (section 11.3.1):
			// f32(f16_round_f32(x)) or f32(bf16_round_f32(x)).
			format := "f16"
			if rng.Intn(2) == 1 {
				format = "bf16"
			}
			return &floatNode{kind: "via", op: format, args: []*floatNode{genFloatNode(rng, width, depth-1)}, width: width}
		}
	case 1:
		return &floatNode{kind: "call", op: floatUnaryCalls[rng.Intn(len(floatUnaryCalls))],
			args: []*floatNode{genFloatNode(rng, width, depth-1)}, width: width}
	case 2:
		return &floatNode{kind: "call", op: floatBinaryCalls[rng.Intn(len(floatBinaryCalls))],
			args: []*floatNode{genFloatNode(rng, width, depth-1), genFloatNode(rng, width, depth-1)}, width: width}
	case 3:
		return &floatNode{kind: "call", op: "fma",
			args: []*floatNode{genFloatNode(rng, width, depth-1), genFloatNode(rng, width, depth-1), genFloatNode(rng, width, depth-1)}, width: width}
	}
	ops := []string{"+", "-", "*", "/"}
	return &floatNode{kind: "op", op: ops[rng.Intn(len(ops))],
		args: []*floatNode{genFloatNode(rng, width, depth-1), genFloatNode(rng, width, depth-1)}, width: width}
}

// render writes the node as Oak source; leaves enter as exact bit patterns
// through the bits conversions, so no decimal conversion is involved.
func (n *floatNode) render() string {
	switch n.kind {
	case "leaf":
		if n.width == 32 {
			return fmt.Sprintf("f32_bits_u32(u32(%d))", n.bits)
		}
		return fmt.Sprintf("f64_bits_u64(u64(%d))", n.bits)
	case "neg":
		return "(-" + n.args[0].render() + ")"
	case "op":
		return "(" + n.args[0].render() + " " + n.op + " " + n.args[1].render() + ")"
	case "via":
		return "f32(" + n.op + "_round_f32(" + n.args[0].render() + "))"
	}
	parts := make([]string, len(n.args))
	for i, arg := range n.args {
		parts[i] = arg.render()
	}
	return n.op + "(" + strings.Join(parts, ", ") + ")"
}

// reference evaluates the node in Go with IEEE semantics at the width:
// float32 arithmetic for f32 (Go rounds each operation to float32), Go
// math for the intrinsics, exact arbitrary-precision fma for f32.
func (n *floatNode) reference() float64 {
	round := func(v float64) float64 {
		if n.width == 32 {
			return float64(float32(v))
		}
		return v
	}
	switch n.kind {
	case "leaf":
		return fromBits(n.bits, n.width)
	case "neg":
		return -n.args[0].reference()
	case "via":
		return referenceStorageRoundTrip(n.op, float32(n.args[0].reference()))
	case "op":
		a, b := n.args[0].reference(), n.args[1].reference()
		if n.width == 32 {
			fa, fb := float32(a), float32(b)
			switch n.op {
			case "+":
				return float64(fa + fb)
			case "-":
				return float64(fa - fb)
			case "*":
				return float64(fa * fb)
			default:
				return float64(fa / fb)
			}
		}
		switch n.op {
		case "+":
			return a + b
		case "-":
			return a - b
		case "*":
			return a * b
		default:
			return a / b
		}
	}
	values := make([]float64, len(n.args))
	for i, arg := range n.args {
		values[i] = arg.reference()
	}
	switch n.op {
	case "fma":
		if n.width == 32 {
			return referenceFMA32(float32(values[0]), float32(values[1]), float32(values[2]))
		}
		return math.FMA(values[0], values[1], values[2])
	case "sqrt":
		return round(math.Sqrt(values[0]))
	case "abs":
		return math.Abs(values[0])
	case "floor":
		return math.Floor(values[0])
	case "ceil":
		return math.Ceil(values[0])
	case "trunc":
		return math.Trunc(values[0])
	case "round":
		return math.Round(values[0])
	case "round_even":
		return math.RoundToEven(values[0])
	case "copysign":
		return math.Copysign(values[0], values[1])
	case "min":
		return referenceMinimum(values[0], values[1])
	case "max":
		return referenceMaximum(values[0], values[1])
	case "min_num":
		if math.IsNaN(values[0]) {
			return values[1]
		}
		if math.IsNaN(values[1]) {
			return values[0]
		}
		return referenceMinimum(values[0], values[1])
	case "max_num":
		if math.IsNaN(values[0]) {
			return values[1]
		}
		if math.IsNaN(values[1]) {
			return values[0]
		}
		return referenceMaximum(values[0], values[1])
	}
	panic("unknown intrinsic " + n.op)
}

func referenceMinimum(a, b float64) float64 {
	switch {
	case math.IsNaN(a) || math.IsNaN(b):
		return math.NaN()
	case a == b:
		if math.Signbit(a) {
			return a
		}
		return b
	case a < b:
		return a
	}
	return b
}

func referenceMaximum(a, b float64) float64 {
	switch {
	case math.IsNaN(a) || math.IsNaN(b):
		return math.NaN()
	case a == b:
		if math.Signbit(a) {
			return b
		}
		return a
	case a > b:
		return a
	}
	return b
}

// referenceFMA32 forms a*b + c exactly and rounds once to float32.
func referenceFMA32(a, b, c float32) float64 {
	for _, v := range []float32{a, b, c} {
		if math.IsNaN(float64(v)) || math.IsInf(float64(v), 0) {
			return float64(float32(math.FMA(float64(a), float64(b), float64(c))))
		}
	}
	const precision = 2048
	product := new(big.Float).SetPrec(precision).SetFloat64(float64(a))
	product.Mul(product, new(big.Float).SetPrec(precision).SetFloat64(float64(b)))
	sum := new(big.Float).SetPrec(precision).Add(product, new(big.Float).SetPrec(precision).SetFloat64(float64(c)))
	if sum.Sign() == 0 {
		return float64(float32(math.FMA(float64(a), float64(b), float64(c))))
	}
	rounded, _ := sum.Float32()
	return float64(rounded)
}

// bitsExpression wraps the node so the program observes its bit pattern
// as a u64.
func (n *floatNode) bitsExpression() string {
	if n.width == 32 {
		return "u64(u32_bits_f32(" + n.render() + "))"
	}
	return "u64_bits_f64(" + n.render() + ")"
}

func sameFloatBits(want, got uint64, width int) bool {
	wantValue, gotValue := fromBits(want, width), fromBits(got, width)
	if math.IsNaN(wantValue) {
		return math.IsNaN(gotValue) // payload is unspecified
	}
	return want == got
}

func TestDifferentialFloatExpressions(t *testing.T) {
	// Deterministic by default; OAK_FLOAT_SEED and OAK_FLOAT_CASES widen the
	// hunt locally (a failure prints the seed and the offending trees).
	seed := int64(20260910)
	if env := os.Getenv("OAK_FLOAT_SEED"); env != "" {
		parsed, err := strconv.ParseInt(env, 10, 64)
		if err != nil {
			t.Fatalf("OAK_FLOAT_SEED: %v", err)
		}
		seed = parsed
	}
	count := 200
	if env := os.Getenv("OAK_FLOAT_CASES"); env != "" {
		parsed, err := strconv.Atoi(env)
		if err != nil || parsed < 1 {
			t.Fatalf("OAK_FLOAT_CASES: %v", err)
		}
		count = parsed
	}
	t.Logf("seed %d, %d cases", seed, count)
	rng := rand.New(rand.NewSource(seed))
	cases := make([]*floatNode, 0, count)
	for i := 0; i < count; i++ {
		width := 32
		if i%2 == 1 {
			width = 64
		}
		cases = append(cases, genFloatNode(rng, width, 1+rng.Intn(4)))
	}

	// Witness two: the compiled program prints every result's bits.
	var src strings.Builder
	src.WriteString(`putchar: (ch: c.Int): c.Int = c.extern("putchar")

hex: (v: u64): () {
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
	for k, node := range cases {
		fmt.Fprintf(&src, "case_%d: (): u64 {\n  %s\n}\n\n", k, node.bitsExpression())
	}
	src.WriteString("main: (): i32 {\n")
	for k := range cases {
		fmt.Fprintf(&src, "  hex(case_%d())\n", k)
	}
	src.WriteString("  0\n}\n")
	stdout, code, abnormal := buildAndRunOutput(t, "floatdiff", src.String())
	if abnormal || code != 0 {
		t.Fatalf("compiled float program exited (%d, abnormal=%v)", code, abnormal)
	}
	lines := strings.Fields(stdout)
	if len(lines) != count {
		t.Fatalf("compiled program printed %d results, want %d:\n%s", len(lines), count, stdout)
	}
	mismatches := 0
	for k, node := range cases {
		want := toBits(node.reference(), node.width)
		got, err := strconv.ParseUint(lines[k], 16, 64)
		if err != nil {
			t.Fatalf("case %d: bad hex %q", k, lines[k])
		}
		if !sameFloatBits(want, got, node.width) {
			mismatches++
			if mismatches <= 10 {
				t.Errorf("compiled case %d (f%d): %s\n  reference %016x (%v)\n  compiled  %016x (%v)",
					k, node.width, node.render(), want, fromBits(want, node.width), got, fromBits(got, node.width))
			}
		}
	}

	// Witness three: the interpreter evaluates the same checked program once
	// and each case_k() is called for its u64 bit pattern.
	model, err := New().WithSource("floatdiff.oak", src.String()).Check().Get()
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
	for k, node := range cases {
		want := toBits(node.reference(), node.width)
		call := parser.New(layout.New(scanner.New(fmt.Sprintf("case_%d()", k)))).ParseProgram()
		result := evaluator.Eval(call, env)
		if e, isErr := result.(*object.Error); isErr {
			t.Fatalf("interpreter error in case %d: %s", k, e.Message)
		}
		integer, ok := result.(*object.Integer)
		if !ok {
			t.Fatalf("case %d returned %s", k, result.Inspect())
		}
		got := uint64(integer.Value)
		if !sameFloatBits(want, got, node.width) {
			mismatches++
			if mismatches <= 10 {
				t.Errorf("interpreted case %d (f%d): %s\n  reference   %016x (%v)\n  interpreter %016x (%v)",
					k, node.width, node.render(), want, fromBits(want, node.width), got, fromBits(got, node.width))
			}
		}
	}
	if mismatches != 0 {
		t.Fatalf("%d of %d differential float cases disagree", mismatches, 2*count)
	}
	t.Logf("floating point: %d expression trees agree bit for bit across reference, compiled C, and interpreter", count)
}

// referenceStorageRoundTrip is the reference for f32(<format>_round_f32(x)):
// round to nearest even into the 16-bit format and widen exactly. The C
// helpers in the emitted preamble are the independent witness.
func referenceStorageRoundTrip(format string, x float32) float64 {
	u := math.Float32bits(x)
	if format == "bf16" {
		if (u>>23)&0xFF == 0xFF && u&0x7FFFFF != 0 {
			return float64(math.Float32frombits((u>>16 | 0x40) << 16))
		}
		upper := u >> 16
		rem := u & 0xFFFF
		if rem > 0x8000 || (rem == 0x8000 && upper&1 == 1) {
			upper++
		}
		return float64(math.Float32frombits(upper << 16))
	}
	// binary16
	sign := uint32(u>>16) & 0x8000
	exp := (u >> 23) & 0xFF
	mant := u & 0x7FFFFF
	var half uint32
	switch {
	case exp == 0xFF:
		half = sign | 0x7C00
		if mant != 0 {
			half |= 0x200 | mant>>13
		}
	default:
		e := int32(exp) - 127 + 15
		switch {
		case e >= 0x1F:
			half = sign | 0x7C00
		case e < -10:
			half = sign
		case e <= 0:
			mant |= 0x800000
			shift := uint32(14 - e)
			h := mant >> shift
			rem := mant & (1<<shift - 1)
			midpoint := uint32(1) << (shift - 1)
			if rem > midpoint || (rem == midpoint && h&1 == 1) {
				h++
			}
			half = sign | h
		default:
			h := uint32(e)<<10 | mant>>13
			rem := mant & 0x1FFF
			if rem > 0x1000 || (rem == 0x1000 && h&1 == 1) {
				h++
			}
			half = sign | h
		}
	}
	// widen
	hs := half & 0x8000
	he := (half >> 10) & 0x1F
	hm := half & 0x3FF
	switch {
	case he == 0x1F:
		return float64(math.Float32frombits(hs<<16 | 0x7F800000 | hm<<13))
	case he == 0:
		if hm == 0 {
			return float64(math.Float32frombits(hs << 16))
		}
		e := int32(1)
		for hm&0x400 == 0 {
			hm <<= 1
			e--
		}
		hm &= 0x3FF
		return float64(math.Float32frombits(hs<<16 | uint32(e+112)<<23 | hm<<13))
	}
	return float64(math.Float32frombits(hs<<16 | (he+112)<<23 | hm<<13))
}
