package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

// Trapping arithmetic (docs/spec/20-types.md section 11.1a):
// `{type}_trapping_{add|sub|mul}` is the exact result when it fits and a
// located trap otherwise — the overflow-loud spelling for hot paths that
// would rather stop than branch. Every boundary the wrapping operators
// cross silently is exercised in range here; the overflow itself is a
// separate program per realization.
const trappingArithmeticProgram = `
main: (): i32 {
  full: u8 = 255
  assert(u8_trapping_add(full, 0) == 255)
  assert(u8_trapping_add(u8(254), u8(1)) == 255)
  assert(u8_trapping_sub(u8(3), u8(3)) == 0)
  assert(u8_trapping_mul(u8(15), u8(17)) == 255)
  top: u32 = 4294967295
  assert(u32_trapping_add(top, 0) == top)
  assert(u32_trapping_sub(top, top) == 0)
  assert(u32_trapping_mul(u32(65535), u32(65537)) == top)
  big: u64 = 18446744073709551615
  half: u64 = 9223372036854775808
  assert(u64_trapping_add(half, half - 1) == big)
  assert(u64_trapping_sub(big, half) == half - 1)
  assert(u64_trapping_mul(u64(4294967295), u64(4294967297)) == big)
  assert(i8_trapping_add(i8(127), i8(-128)) == -1)
  assert(i8_trapping_sub(i8(-128), i8(-1)) == -127)
  assert(i8_trapping_mul(i8(-64), i8(2)) == -128)
  imax: i32 = 2147483647
  imin: i32 = -2147483648
  assert(i32_trapping_add(imax, -1) == 2147483646)
  assert(i32_trapping_sub(imin, -1) == imin + 1)
  assert(i32_trapping_mul(i32(-46341), i32(46340)) == -2147441940)
  lmax: i64 = 9223372036854775807
  lmin: i64 = -9223372036854775807 - 1
  assert(i64_trapping_add(lmax, 0) == lmax)
  assert(i64_trapping_sub(lmin, -1) == lmin + 1)
  assert(i64_trapping_mul(i64(3037000499), i64(3037000499)) == 9223372030926249001)
  42
}
`

func TestE2ETrappingArithmeticInRange(t *testing.T) {
	output, err := New().WithSource("trapping.oak", trappingArithmeticProgram).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"static inline void oak_overflow_trap(const char *file, u32 line)",
		"oak: arithmetic overflow at %s:%u",
		"static inline u8 oak_arith_u8_trapping_add( u8 a, u8 b, const char *file, u32 line )",
		"if (__builtin_mul_overflow(a, b, &r)) { oak_overflow_trap(file, line); }",
		`oak_arith_u8_trapping_add( full, 0, "trapping.oak", 4 )`,
	} {
		if !strings.Contains(output, want) {
			t.Fatalf("generated C lacks %q:\n%s", want, output)
		}
	}
	code, abnormal := buildAndRun(t, "trapping", trappingArithmeticProgram)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if interpreted := interpretChecked(t, trappingArithmeticProgram); interpreted != 42 {
		t.Fatalf("interpreter returned %d", interpreted)
	}
}

// Each overflow is a program of its own: the compiled binary traps
// (abnormal exit), and the interpreter reports the overflow as an error.
func TestE2ETrappingArithmeticOverflowTraps(t *testing.T) {
	cases := map[string]string{
		"u8 add":  "u8_trapping_add(u8(255), u8(1))",
		"u32 sub": "u32_trapping_sub(u32(0), u32(1))",
		"u64 mul": "u64_trapping_mul(u64(4294967296), u64(4294967296))",
		"i8 mul":  "i8_trapping_mul(i8(-128), i8(-1))",
		"i32 add": "i32_trapping_add(i32(2147483647), i32(1))",
		"i64 sub": "i64_trapping_sub(i64(-9223372036854775807) - 1, i64(1))",
	}
	for name, expr := range cases {
		src := "main: (): i32 {\n  x := " + expr + "\n  0\n}\n"
		if _, abnormal := buildAndRun(t, "trap_"+strings.ReplaceAll(name, " ", "_"), src); !abnormal {
			t.Errorf("%s: the compiled program must trap", name)
		}
		model, err := New().WithSource("trap.oak", src).Check().Get()
		if err != nil {
			t.Fatalf("%s: check failed: %v", name, err)
		}
		env := object.NewEnvironment()
		env.SetArithmeticWidths(model.TypeChecker.ArithmeticType)
		if result := evaluator.Eval(model.Tree.Root, env); isEvalError(result) {
			t.Fatalf("%s: program definition failed: %s", name, result.(*object.Error).Message)
		}
		call := parser.New(layout.New(scanner.New("main()"))).ParseProgram()
		result := evaluator.Eval(call, env)
		e, isErr := result.(*object.Error)
		if !isErr || !strings.Contains(e.Message, "arithmetic overflow") {
			t.Errorf("%s: interpreter result = %v, want an arithmetic overflow error", name, result)
		}
	}
}

func isEvalError(result object.Object) bool {
	_, isErr := result.(*object.Error)
	return isErr
}

// The trapping grammar keeps one width per call like the other forms.
func TestTrappingArithmeticRejections(t *testing.T) {
	cases := []struct{ name, src, want string }{
		{"mixed widths", "main: (): i32 {\n  a: u32 = 1\n  b: u8 = 2\n  c: u32 = u32_trapping_add(a, b)\n  0\n}", "expects operand 2 of type u32"},
		{"one argument", "main: (): i32 {\n  a: i64 = 1\n  c: i64 = i64_trapping_mul(a)\n  0\n}", "expects 2 arguments"},
	}
	for _, c := range cases {
		_, err := New().WithSource("reject.oak", c.src).Check().Get()
		if err == nil || !strings.Contains(err.Error(), c.want) {
			t.Fatalf("%s: err = %v, want %q", c.name, err, c.want)
		}
	}
}
