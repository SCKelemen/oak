package compiler

import (
	"fmt"
	"math"
	"math/big"
	"math/rand"
	"strconv"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

// The float package (stdlib/float.oak): shortest round-trip and fixed-digit
// decimal text for f64/f32 and correctly rounded parsing, through an exact
// 800-digit decimal. Every expectation here is Go's strconv, the reference
// implementation of the same algorithm.

// floatTestPrelude declares the helpers the check programs use: each helper
// renders or parses through the package and compares with an expected view
// or bit pattern.
const floatTestPrelude = `import(std)

fmt_is: (v: f64, expected: []u8): Bool {
  out: [400]u8
  n: u32 = 0
  true ? {
    dst: [*]u8 = span(&out)
    n = float_written(float_format(dst, v))
  }
  whole: []u8 = view(&out)
  n > u32(0) && bytes_equal(whole[u32(0):n], expected)
}

fixed_is: (v: f64, digits: u32, expected: []u8): Bool {
  out: [400]u8
  n: u32 = 0
  true ? {
    dst: [*]u8 = span(&out)
    n = float_written(float_format_fixed(dst, v, digits))
  }
  whole: []u8 = view(&out)
  n > u32(0) && bytes_equal(whole[u32(0):n], expected)
}

exp_is: (v: f64, digits: u32, expected: []u8): Bool {
  out: [400]u8
  n: u32 = 0
  true ? {
    dst: [*]u8 = span(&out)
    n = float_written(float_format_exp(dst, v, digits))
  }
  whole: []u8 = view(&out)
  n > u32(0) && bytes_equal(whole[u32(0):n], expected)
}

fmt32_is: (v: f32, expected: []u8): Bool {
  out: [64]u8
  n: u32 = 0
  true ? {
    dst: [*]u8 = span(&out)
    n = float_written(float_format_f32(dst, v))
  }
  whole: []u8 = view(&out)
  n > u32(0) && bytes_equal(whole[u32(0):n], expected)
}

// fmt_short: formatting into a span one byte too short is DestinationTooSmall
// and leaves the span untouched.
fmt_short: (v: f64, room: u32): Bool {
  out: [64]u8
  code: u32 = 0
  true ? {
    whole: [*]u8 = span(&out)
    dst: [*]u8 = whole[u32(0):room]
    code = float_failure(float_format(dst, v))
  }
  code == u32(3) && out[0] == u8(0) && out[room - u32(1)] == u8(0)
}

parse_is: (text: []u8, bits: u64): Bool {
  r: Result[f64, FloatError] = float_parse(text)
  r ? | .Ok(v) => { u64_bits_f64(v) == bits } | .Err(e) => { false }
}

parse_code: (text: []u8): u32 = float_parse_failure(float_parse(text))

parse_sat_is: (text: []u8, bits: u64): Bool {
  r: Result[f64, FloatError] = float_parse_saturating(text)
  r ? | .Ok(v) => { u64_bits_f64(v) == bits } | .Err(e) => { false }
}

parse32_is: (text: []u8, bits: u32): Bool {
  r: Result[f32, FloatError] = float_parse_f32(text)
  r ? | .Ok(v) => { u32_bits_f32(v) == bits } | .Err(e) => { false }
}

parse32_code: (text: []u8): u32 = float_parse_failure_f32(float_parse_f32(text))

parse_nan: (text: []u8): Bool {
  r: Result[f64, FloatError] = float_parse(text)
  r ? | .Ok(v) => { (u64_bits_f64(v) & u64(9218868437227405312)) == u64(9218868437227405312) && (u64_bits_f64(v) & u64(4503599627370495)) != u64(0) } | .Err(e) => { false }
}
`

// floatChecks accumulates numbered Bool checks; program(chunk) renders a
// slice of them into an Oak main that returns 42 when every check holds
// and otherwise the id of the first failure (ids start at 100 and stay
// below 256 so the exit status carries them).
type floatChecks struct {
	entries []floatCheck
	pending strings.Builder
	arrays  int
}

type floatCheck struct {
	decls string
	cond  string
}

const floatChunk = 120

func (b *floatChecks) text(s string) string {
	b.arrays++
	name := fmt.Sprintf("t%d", b.arrays)
	fmt.Fprintf(&b.pending, "  %s: [%d]u8 = %s\n", name, len(s), oakByteArrayLiteral([]byte(s)))
	return "view(&" + name + ")"
}

func (b *floatChecks) check(cond string) {
	b.entries = append(b.entries, floatCheck{decls: b.pending.String(), cond: cond})
	b.pending.Reset()
}

func (b *floatChecks) chunks() int { return (len(b.entries) + floatChunk - 1) / floatChunk }

func (b *floatChecks) chunk(n int) []floatCheck {
	lo := n * floatChunk
	hi := lo + floatChunk
	if hi > len(b.entries) {
		hi = len(b.entries)
	}
	return b.entries[lo:hi]
}

func (b *floatChecks) program(n int) string {
	var body strings.Builder
	for i, e := range b.chunk(n) {
		body.WriteString(e.decls)
		fmt.Fprintf(&body, "  fail = fail == u32(0) && !(%s) ? { u32(%d) } | { fail }\n", e.cond, 100+i)
	}
	return floatTestPrelude + "\nmain: (): i32 {\n  fail: u32 = 0\n" + body.String() +
		"  fail == u32(0) ? { i32(42) } | { i32_bits_u32(fail) }\n}\n"
}

func (b *floatChecks) describe(n int, code int) string {
	entries := b.chunk(n)
	index := code - 100
	if index < 0 || index >= len(entries) {
		return fmt.Sprintf("exit code %d (not a check id)", code)
	}
	decls := entries[index].decls
	if len(decls) > 300 {
		decls = decls[:300] + "..."
	}
	return fmt.Sprintf("check %d of chunk %d: %s\n%s", code, n, entries[index].cond, decls)
}

func oakByteArrayLiteral(data []byte) string {
	var sb strings.Builder
	fmt.Fprintf(&sb, "[%d]u8{", len(data))
	for i, b := range data {
		if i > 0 {
			sb.WriteString(",")
		}
		fmt.Fprintf(&sb, "%d", b)
	}
	sb.WriteString("}")
	return sb.String()
}

func oakF64(bits uint64) string { return fmt.Sprintf("f64_bits_u64(u64(%d))", bits) }
func oakF32(bits uint32) string { return fmt.Sprintf("f32_bits_u32(u32(%d))", bits) }

// runFloatChecks compiles and runs each chunk; with interpret, the same
// program is also evaluated by the interpreter.
func runFloatChecks(t *testing.T, name string, b *floatChecks, interpret bool) {
	t.Helper()
	for n := 0; n < b.chunks(); n++ {
		src := b.program(n)
		root := writeModule(t, map[string]string{
			"oak.mod":  "module example.com/" + name + "\noak 0.1.0\n",
			"main.oak": "package main\n" + src,
		})
		code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
		if abnormal || code != 42 {
			t.Fatalf("compiled float program failed: %s (abnormal=%v)", b.describe(n, code), abnormal)
		}
		if !interpret {
			continue
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
		call := parser.New(layout.New(scanner.New("main()"))).ParseProgram()
		result := evaluator.Eval(call, env)
		if e, isErr := result.(*object.Error); isErr {
			t.Fatalf("interpreter error in main(): %s", e.Message)
		}
		integer, ok := result.(*object.Integer)
		if !ok {
			t.Fatalf("interpreter returned %s", result.Inspect())
		}
		if integer.Value != 42 {
			t.Fatalf("interpreted float program failed: %s", b.describe(n, int(integer.Value)))
		}
	}
}

func goShortest(v float64) string      { return strconv.FormatFloat(v, 'g', -1, 64) }
func goShortest32(v float32) string    { return strconv.FormatFloat(float64(v), 'g', -1, 32) }
func goFixed(v float64, d int) string  { return strconv.FormatFloat(v, 'f', d, 64) }
func goExp(v float64, d int) string    { return strconv.FormatFloat(v, 'e', d, 64) }
func goParse64(s string) (uint64, int) { return goParseBits(s, 64) }

// goParseBits returns Go's parse result as bits plus the package's error
// code (0 ok, 1 syntax, 2 range).
func goParseBits(s string, size int) (uint64, int) {
	// Go accepts digit-separating underscores and hexadecimal floats; the
	// package accepts neither.
	if strings.Contains(s, "_") || strings.Contains(strings.ToLower(s), "0x") {
		return 0, 1
	}
	v, err := strconv.ParseFloat(s, size)
	if err != nil {
		if numErr, ok := err.(*strconv.NumError); ok && numErr.Err == strconv.ErrRange {
			if size == 32 {
				return uint64(math.Float32bits(float32(v))), 2
			}
			return math.Float64bits(v), 2
		}
		return 0, 1
	}
	if size == 32 {
		return uint64(math.Float32bits(float32(v))), 0
	}
	return math.Float64bits(v), 0
}

// TestE2EStdlibFloatHardCases: the values that break naive conversions,
// formatted and parsed both ways, compiled and interpreted.
func TestE2EStdlibFloatHardCases(t *testing.T) {
	b := &floatChecks{}
	values := []float64{
		0.1, 1.0 / 3, 5e-324, 2.2250738585072011e-308, 2.2250738585072012e-308, 2.2250738585072014e-308,
		1.7976931348623157e308, 9007199254740992, 0.3, 0.30000000000000004, 1e23, 9.999999999999999e22,
		123456789012345680, 1e21, 1e20, 1e6, 999999, 1234567, 0.0001, 0.00001, 100, 1.5, 2.5, 0.125,
		math.Copysign(0, -1), 0, 1, -1, 3.14159, 1e-7, 4.9406564584124654e-324, 2.2250738585072009e-308,
		math.MaxFloat64, math.SmallestNonzeroFloat64, 1e-320, 123e-320, 6.02214076e23, 1.602176634e-19,
	}
	for _, v := range values {
		bits := math.Float64bits(v)
		b.check(fmt.Sprintf("fmt_is(%s, %s)", oakF64(bits), b.text(goShortest(v))))
		b.check(fmt.Sprintf("parse_is(%s, u64(%d))", b.text(goShortest(v)), bits))
		for _, d := range []int{0, 1, 2, 5, 17} {
			b.check(fmt.Sprintf("fixed_is(%s, u32(%d), %s)", oakF64(bits), d, b.text(goFixed(v, d))))
			b.check(fmt.Sprintf("exp_is(%s, u32(%d), %s)", oakF64(bits), d, b.text(goExp(v, d))))
		}
		f := float32(v)
		fbits := math.Float32bits(f)
		b.check(fmt.Sprintf("fmt32_is(%s, %s)", oakF32(fbits), b.text(goShortest32(f))))
		b.check(fmt.Sprintf("parse32_is(%s, u32(%d))", b.text(goShortest32(f)), fbits))
	}
	// Specials.
	b.check(fmt.Sprintf("fmt_is(%s, %s)", oakF64(math.Float64bits(math.Inf(1))), b.text("+Inf")))
	b.check(fmt.Sprintf("fmt_is(%s, %s)", oakF64(math.Float64bits(math.Inf(-1))), b.text("-Inf")))
	b.check(fmt.Sprintf("fmt_is(%s, %s)", oakF64(math.Float64bits(math.NaN())), b.text("NaN")))
	b.check(fmt.Sprintf("fmt_is(%s, %s)", oakF64(0x7FF0000000000001), b.text("NaN")))
	b.check(fmt.Sprintf("fmt32_is(%s, %s)", oakF32(math.Float32bits(float32(math.Inf(1)))), b.text("+Inf")))
	for _, s := range []string{"inf", "+Inf", "INFINITY", "+infinity", "Infinity"} {
		b.check(fmt.Sprintf("parse_is(%s, u64(%d))", b.text(s), math.Float64bits(math.Inf(1))))
	}
	for _, s := range []string{"-inf", "-Infinity", "-INF"} {
		b.check(fmt.Sprintf("parse_is(%s, u64(%d))", b.text(s), math.Float64bits(math.Inf(-1))))
	}
	for _, s := range []string{"nan", "NaN", "NAN"} {
		b.check(fmt.Sprintf("parse_nan(%s)", b.text(s)))
	}
	// Parsing: exact decimal inputs with hard rounding.
	parses := []string{
		"9007199254740993", "9007199254740993.0", "9007199254740992.5", "9007199254740993.5",
		"2.2250738585072011e-308", "2.2250738585072012e-308", "4.9406564584124654e-324",
		"2.4703282292062327e-324", "2.4703282292062328e-324", "1e-400", "1e-324", "3e-324",
		"1.7976931348623157e308", "1.7976931348623158e308", "0.1", ".5", "5.", "1e", "+.5e-2",
		"000000.0000001", "1_0", "0x1p3", "1e+", "e5", "", ".", "-", "+", " 1", "1 ", "1.2.3", "1e5e5",
		"--1", "1e100000", "1e-100000", "0.000e5", "-0", "-0.0e-5", "1" + strings.Repeat("0", 400),
		"0." + strings.Repeat("0", 400) + "1", "1." + strings.Repeat("0", 900) + "1", "1" + strings.Repeat("0", 900),
		"7.038531e-26", "1.00000005960464477550", "1.0000000596046448", "3.4028235677973366e38", "3.4028235e38", "1e39",
		"1e-46", "1.4e-45", "7e-46", "0.7e-45", "infi", "+nan", "nan1", "9999999999999999999999999999",
	}
	for _, s := range parses {
		bits, code := goParse64(s)
		if code == 0 {
			b.check(fmt.Sprintf("parse_is(%s, u64(%d))", b.text(s), bits))
		} else {
			b.check(fmt.Sprintf("parse_code(%s) == u32(%d)", b.text(s), code))
			if code == 2 {
				b.check(fmt.Sprintf("parse_sat_is(%s, u64(%d))", b.text(s), bits))
			}
		}
		bits32, code32 := goParseBits(s, 32)
		if code32 == 0 {
			b.check(fmt.Sprintf("parse32_is(%s, u32(%d))", b.text(s), bits32))
		} else {
			b.check(fmt.Sprintf("parse32_code(%s) == u32(%d)", b.text(s), code32))
		}
	}
	// Destination too small: one byte short of the shortest spelling.
	for _, v := range []float64{0.1, 1e23, math.MaxFloat64, 5e-324, 100} {
		b.check(fmt.Sprintf("fmt_short(%s, u32(%d))", oakF64(math.Float64bits(v)), len(goShortest(v))-1))
	}
	runFloatChecks(t, "float_hard", b, true)
}

// TestE2EStdlibFloatQualifiedImport: the package through the module loader.
func TestE2EStdlibFloatQualifiedImport(t *testing.T) {
	src := `package main
import("float")
main: (): i32 {
  out: [32]u8
  n: u32 = 0
  true ? {
    dst: [*]u8 = span(&out)
    n = float.float_written(float.float_format(dst, 0.1))
  }
  whole: []u8 = view(&out)
  back: f64 = float.float_parse_value(float.float_parse(whole[u32(0):n]), 7.0)
  n == u32(3) && back == 0.1 && float.float_error_code(.InvalidSyntax) == u32(1) ? { 42 } | { 0 }
}
`
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/float_qualified\noak 0.1.0\n",
		"main.oak": src,
	})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

// floatDiffPrelude: one compiled program prints every result, one per line
// (text for formats, 16 hex digits for parsed bits, "!<code>" for errors).
const floatDiffPrelude = `import(std)
putchar: (ch: c.Int): c.Int = c.extern("putchar")

emit_bytes: (src: []u8): () {
  i: u32 = 0
  while i < len(src) {
    _ = putchar(c.Int(i32_bits_u32(u32(src[i]))))
    i = i + 1
  }
  _ = putchar(c.Int(10))
}

emit_code: (code: u32): () {
  _ = putchar(c.Int(33))
  _ = putchar(c.Int(i32_bits_u32(u32(48) + code)))
  _ = putchar(c.Int(10))
}

emit_hex: (v: u64): () {
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

show: (r: Result[u32, FloatError], out: []u8): () {
  r ? | .Ok(n) => { emit_bytes(out[u32(0):n]) } | .Err(e) => { emit_code(float_error_code(e)) }
}

f64_all: (v: f64): () {
  out: [400]u8
  r0: Result[u32, FloatError] = .Ok(u32(0))
  r1: Result[u32, FloatError] = .Ok(u32(0))
  r2: Result[u32, FloatError] = .Ok(u32(0))
  r3: Result[u32, FloatError] = .Ok(u32(0))
  true ? {
    dst: [*]u8 = span(&out)
    r0 = float_format(dst, v)
  }
  show(r0, view(&out))
  true ? {
    dst2: [*]u8 = span(&out)
    r1 = float_format_fixed(dst2, v, u32(3))
  }
  show(r1, view(&out))
  true ? {
    dst3: [*]u8 = span(&out)
    r2 = float_format_exp(dst3, v, u32(6))
  }
  show(r2, view(&out))
  true ? {
    dst4: [*]u8 = span(&out)
    r3 = float_format_fixed(dst4, v, u32(0))
  }
  show(r3, view(&out))
}

f32_all: (v: f32): () {
  out: [64]u8
  r0: Result[u32, FloatError] = .Ok(u32(0))
  true ? {
    dst: [*]u8 = span(&out)
    r0 = float_format_f32(dst, v)
  }
  show(r0, view(&out))
}

p64: (text: []u8): () {
  r: Result[f64, FloatError] = float_parse(text)
  r ? | .Ok(v) => { emit_hex(u64_bits_f64(v)) } | .Err(e) => { emit_code(float_error_code(e)) }
}

p32: (text: []u8): () {
  r: Result[f32, FloatError] = float_parse_f32(text)
  r ? | .Ok(v) => { emit_hex(u64(u32_bits_f32(v))) } | .Err(e) => { emit_code(float_error_code(e)) }
}
`

// floatDiff collects expected lines alongside the Oak statements producing them.
type floatDiff struct {
	body     strings.Builder
	expected []string
	arrays   int
	cases    int
}

func (d *floatDiff) text(s string) string {
	d.arrays++
	name := fmt.Sprintf("s%d", d.arrays)
	fmt.Fprintf(&d.body, "  %s: [%d]u8 = %s\n", name, len(s), oakByteArrayLiteral([]byte(s)))
	return "view(&" + name + ")"
}

func (d *floatDiff) f64(bits uint64) {
	v := math.Float64frombits(bits)
	fmt.Fprintf(&d.body, "  f64_all(%s)\n", oakF64(bits))
	d.expected = append(d.expected, goShortest(v), goFixed(v, 3), goExp(v, 6), goFixed(v, 0))
	d.cases++
}

func (d *floatDiff) f32(bits uint32) {
	fmt.Fprintf(&d.body, "  f32_all(%s)\n", oakF32(bits))
	d.expected = append(d.expected, goShortest32(math.Float32frombits(bits)))
	d.cases++
}

func expectedParse(s string, size int) string {
	bits, code := goParseBits(s, size)
	if code != 0 {
		return fmt.Sprintf("!%d", code)
	}
	return fmt.Sprintf("%016x", bits)
}

func (d *floatDiff) parse(s string) {
	name := d.text(s)
	fmt.Fprintf(&d.body, "  p64(%s)\n  p32(%s)\n", name, name)
	d.expected = append(d.expected, expectedParse(s, 64), expectedParse(s, 32))
	d.cases++
}

func (d *floatDiff) run(t *testing.T, name string) {
	t.Helper()
	src := floatDiffPrelude + "\nmain: (): i32 {\n" + d.body.String() + "  0\n}\n"
	stdout, code, abnormal := buildAndRunOutput(t, name, src)
	if abnormal || code != 0 {
		t.Fatalf("%s: compiled program exited (%d, abnormal=%v)", name, code, abnormal)
	}
	lines := strings.Split(strings.TrimRight(stdout, "\n"), "\n")
	if len(lines) != len(d.expected) {
		t.Fatalf("%s: %d lines printed, %d expected", name, len(lines), len(d.expected))
	}
	mismatches := 0
	for i, want := range d.expected {
		if lines[i] != want {
			mismatches++
			if mismatches <= 10 {
				t.Errorf("%s: line %d: got %q, want %q", name, i, lines[i], want)
			}
		}
	}
	if mismatches > 0 {
		t.Fatalf("%s: %d of %d lines differ from strconv", name, mismatches, len(d.expected))
	}
}

// randomF64Bits draws bit patterns from several distributions so exponents
// near both ends, subnormals, and integers all appear; NaN is excluded (its
// text is checked in the hard cases and its payload is not comparable).
func randomF64Bits(rng *rand.Rand) uint64 {
	var bits uint64
	for {
		switch rng.Intn(6) {
		case 0:
			bits = rng.Uint64()
		case 1: // subnormal or tiny
			bits = rng.Uint64() & ((1 << 52) - 1)
			if rng.Intn(2) == 0 {
				bits |= 1 << 63
			}
		case 2: // moderate exponent, dense mantissa
			exp := uint64(1023 - 60 + rng.Intn(120))
			bits = exp<<52 | rng.Uint64()&((1<<52)-1)
		case 3: // integers and simple fractions
			v := float64(rng.Int63n(1<<53)) / float64(uint64(1)<<uint(rng.Intn(20)))
			bits = math.Float64bits(v)
		case 4: // powers of ten and neighbours
			p := rng.Intn(600) - 300
			v := math.Pow(10, float64(p))
			for k := rng.Intn(3); k > 0; k-- {
				v = math.Nextafter(v, math.Inf(1))
			}
			bits = math.Float64bits(v)
		default: // random exponent, sparse mantissa
			exp := uint64(rng.Intn(2046) + 1)
			bits = exp<<52 | uint64(rng.Intn(1<<20))<<32 | uint64(rng.Intn(4))
		}
		v := math.Float64frombits(bits)
		if !math.IsNaN(v) {
			return bits
		}
	}
}

func randomF32Bits(rng *rand.Rand) uint32 {
	for {
		var bits uint32
		switch rng.Intn(3) {
		case 0:
			bits = rng.Uint32()
		case 1:
			bits = rng.Uint32() & ((1 << 23) - 1)
		default:
			bits = math.Float32bits(float32(rng.Int63n(1<<24)) / float32(uint32(1)<<uint(rng.Intn(10))))
		}
		if !math.IsNaN(float64(math.Float32frombits(bits))) {
			return bits
		}
	}
}

// randomDecimal spells a random decimal: digits with an optional fraction
// and exponent, sometimes long enough to exercise truncation, sometimes
// exactly at a rounding boundary of a random double.
func randomDecimal(rng *rand.Rand) string {
	var sb strings.Builder
	switch rng.Intn(4) {
	case 0: // the exact midpoint between two doubles, to force the tie rule
		bits := randomF64Bits(rng)
		v := math.Float64frombits(bits)
		next := math.Nextafter(v, math.Inf(1))
		if math.IsInf(next, 0) || math.IsInf(v, 0) {
			return "1e308"
		}
		return exactMidpoint(v, next)
	case 1: // long digit strings
		if rng.Intn(2) == 0 {
			sb.WriteByte('-')
		}
		n := 1 + rng.Intn(60)
		for i := 0; i < n; i++ {
			sb.WriteByte(byte('0' + rng.Intn(10)))
		}
		if rng.Intn(2) == 0 {
			sb.WriteByte('.')
			m := rng.Intn(60)
			for i := 0; i < m; i++ {
				sb.WriteByte(byte('0' + rng.Intn(10)))
			}
		}
		if rng.Intn(2) == 0 {
			fmt.Fprintf(&sb, "e%d", rng.Intn(700)-350)
		}
		return sb.String()
	case 2: // short numbers around the ends of the range
		fmt.Fprintf(&sb, "%d.%de%d", rng.Intn(100), rng.Intn(1000), []int{-330, -324, -320, -310, -308, -300, 300, 305, 308, 309, 310, 38, 39, -38, -45, -46}[rng.Intn(16)])
		return sb.String()
	default: // a random double's shortest text with a digit appended
		s := goShortest(math.Float64frombits(randomF64Bits(rng)))
		if i := strings.IndexByte(s, 'e'); i >= 0 {
			return s[:i] + string(rune('0'+rng.Intn(10))) + s[i:]
		}
		return s + string(rune('0'+rng.Intn(10)))
	}
}

// exactMidpoint spells (v + next) / 2 exactly: the denominator is a power of
// two, so the decimal expansion is finite and FloatString with as many
// places as that power is exact (over a thousand digits near the subnormal
// range, which also exercises the parser's truncation flag).
func exactMidpoint(v, next float64) string {
	sum := new(big.Rat).Add(new(big.Rat).SetFloat64(v), new(big.Rat).SetFloat64(next))
	mid := sum.Quo(sum, big.NewRat(2, 1))
	places := mid.Denom().BitLen() - 1
	return mid.FloatString(places)
}

func TestE2EStdlibFloatDifferential(t *testing.T) {
	rng := rand.New(rand.NewSource(20260911))
	const perProgram = 400
	// Formatting of random f64 bit patterns and parsing of their shortest text.
	for chunk := 0; chunk < 6; chunk++ {
		d := &floatDiff{}
		for i := 0; i < perProgram; i++ {
			bits := randomF64Bits(rng)
			d.f64(bits)
			d.parse(goShortest(math.Float64frombits(bits)))
		}
		d.run(t, fmt.Sprintf("float_diff_f64_%d", chunk))
	}
	// f32 shortest text and its parse.
	for chunk := 0; chunk < 3; chunk++ {
		d := &floatDiff{}
		for i := 0; i < perProgram; i++ {
			bits := randomF32Bits(rng)
			d.f32(bits)
			d.parse(goShortest32(math.Float32frombits(bits)))
		}
		d.run(t, fmt.Sprintf("float_diff_f32_%d", chunk))
	}
	// Random decimal spellings, parsed at both sizes.
	for chunk := 0; chunk < 4; chunk++ {
		d := &floatDiff{}
		for i := 0; i < perProgram; i++ {
			d.parse(randomDecimal(rng))
		}
		d.run(t, fmt.Sprintf("float_diff_parse_%d", chunk))
	}
}
