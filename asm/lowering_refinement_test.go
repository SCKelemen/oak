package asm

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

// The verifier's Oak lowering is transliterated in
// spec/lean/Oak/LoweringRefinement.lean as `lowerT`, and `lowerT_eval`
// proves it agrees with the Lean extraction's embedding of the same
// expression in every agreeing scope (docs/spec/126-verification-chain.md
// §4, the seam). That proof is about `lowerT`; these tests pin
// `oakLowering.lower` to it: every expression below is lowered at its own
// width and its `term.String()` must be the render `lowerT` gives, stated
// as an `example` in the Lean file. A change to either side has to visit
// the other.
var loweringRenders = []struct {
	decl, body, want string
}{
	{"f: (a, b: u32) -> u32", "a + b", "(a add b)"},
	{"f: (a, b: u32) -> u32", "a - b", "(a sub b)"},
	{"f: (a: u32) -> u32", "a * 3", "(a mul 3)"},
	{"f: (a: u32) -> u32", "a / 8", "(a shr 3)"},
	{"f: (a: u32) -> u32", "a % 8", "(a and 7)"},
	{"f: (a: u32) -> u32", "-a", "(0 sub a)"},
	{"f: (a: u32) -> u32", "^a", "(a xor 4294967295)"},
	{"f: (a, b: u32) -> u32", "(a << 3) | (b >> 5)", "((a shl 3) or (b shr 5))"},
	{"f: (a, b: u32) -> u32", "(a & b) ^ b", "((a and b) xor b)"},
	{"f: (a: u8) -> u32", "u32(a)", "(a and 255)"},
	{"f: (a: i8) -> i32", "i32(a)", "(((a and 255) shl 24) sar 24)"},
	{"f: (a: i32) -> i64", "i64(a) + 1", "((((a and 4294967295) shl 32) sar 32) add 1)"},
	{"f: (a: u32) -> u8", "u8_trunc_u32(a)", "a"},
	{"f: (a, b: u16) -> u32", "u32(a) * u32(b)", "((a and 65535) mul (b and 65535))"},
	{"f: (a, b: u32) -> Bool", "a < b", "(a lo b)"},
	{"f: (a, b: u32) -> Bool", "a <= b", "(a ls b)"},
	{"f: (a, b: u32) -> Bool", "a > b", "(a hi b)"},
	{"f: (a, b: u32) -> Bool", "a >= b", "(a hs b)"},
	{"f: (a, b: u32) -> Bool", "a == b", "(a eq b)"},
	{"f: (a, b: u32) -> Bool", "a != b", "(a ne b)"},
	{"f: (a, b: i32) -> Bool", "a < b", "(a lt b)"},
	{"f: (a, b: i32) -> Bool", "a <= b", "(a le b)"},
	{"f: (a, b: i32) -> Bool", "a > b", "(a gt b)"},
	{"f: (a, b: i32) -> Bool", "a >= b", "(a ge b)"},
	{"f: (a, b, c: u32) -> Bool", "a < b && b < c", "((a lo b) and (b lo c))"},
	{"f: (a, b: u32) -> Bool", "a < b || a == b", "((a lo b) or (a eq b))"},
	{"f: (a, b: u32) -> Bool", "!(a < b)", "((a lo b) xor 1)"},
	{"f: (a, b: u32) -> u32", "a < b ? a | b", "((a lo b) ? a : b)"},
	{"f: (a, b: i64) -> i64", "a < b ? b - a | a - b", "((a lt b) ? (b sub a) : (a sub b))"},
}

// Locals and calls (LoweringRefinement.lean, `letIn` and `call`): a local
// is lowered once and substituted, a rebinding replaces its term, a call
// binds the callee's parameters to the lowered arguments and inlines the
// body, so the renders are the terms the source would have without them.
// Each program's last function is the one lowered; the others are its
// callees.
var loweringProgramRenders = []struct {
	program, want string
}{
	{"f: (a, b: u32) -> u32 = {\n  y: u32 = a + b\n  y * y\n}\n", "((a add b) mul (a add b))"},
	{"f: (a: u32) -> u32 = {\n  y: u32 = a\n  y = y + 1\n  y * 2\n}\n", "((a add 1) mul 2)"},
	{"f: (a: u32) -> u32 = {\n  y: u8 = u8_trunc_u32(a)\n  u32(y)\n}\n", "(a and 255)"},
	{"g: (x: u32) -> u32 = x * x\n\nf: (a: u32) -> u32 = g(a + 1)\n", "((a add 1) mul (a add 1))"},
	{"h: (x, y: u32) -> u32 = {\n  d: u32 = x - y\n  d & 255\n}\n\nf: (a, b: u32) -> u32 = h(b, a)\n", "((b sub a) and 255)"},
}

func TestLoweringProgramsMatchLeanTransliteration(t *testing.T) {
	for _, c := range loweringProgramRenders {
		p := parser.New(layout.New(scanner.New(c.program)))
		program := p.ParseProgram()
		if errs := p.Errors(); len(errs) != 0 {
			t.Fatalf("%s: %v", c.program, errs)
		}
		var fns []*ast.FunctionStatement
		for _, stmt := range program.Statements {
			if fn, ok := stmt.(*ast.FunctionStatement); ok && fn.Name != nil {
				fns = append(fns, fn)
			}
		}
		if len(fns) == 0 {
			t.Fatalf("%s: no functions", c.program)
		}
		spec := fns[len(fns)-1]
		lo := newLowering(spec)
		lo.functions = map[string]*ast.FunctionStatement{}
		for _, fn := range fns[:len(fns)-1] {
			lo.functions[fn.Name.Value] = fn
		}
		width, _, ok := contractBits(spec.ReturnType)
		if !ok {
			t.Fatalf("%s: no contract width", c.program)
		}
		term, reason, ok := lo.lower(spec.Body, width)
		if !ok {
			t.Fatalf("%s: not lowered (%s)", c.program, reason)
		}
		if got := term.String(); got != c.want {
			t.Errorf("%s\n  lowered: %s\n  lowerT:  %s\n— update spec/lean/Oak/LoweringRefinement.lean or the lowering", c.program, got, c.want)
		}
	}
}

func TestLoweringMatchesLeanTransliteration(t *testing.T) {
	for _, c := range loweringRenders {
		spec, err := parseSignatureWithBody(c.decl + " = " + c.body)
		if err != nil {
			t.Fatalf("%s = %s: %v", c.decl, c.body, err)
		}
		lo := newLowering(spec)
		width, _, ok := contractBits(spec.ReturnType)
		if !ok {
			t.Fatalf("%s: no contract width", c.decl)
		}
		term, reason, ok := lo.lower(spec.Body, width)
		if !ok {
			t.Fatalf("%s = %s: not lowered (%s)", c.decl, c.body, reason)
		}
		if got := term.String(); got != c.want {
			t.Errorf("%s = %s\n  lowered: %s\n  lowerT:  %s\n— update spec/lean/Oak/LoweringRefinement.lean or the lowering", c.decl, c.body, got, c.want)
		}
		if term.width != width {
			t.Errorf("%s = %s: lowered at width %d, the contract is %d", c.decl, c.body, term.width, width)
		}
	}
}
