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
// §4, the seam). Oak.FloatLoweringRefinement does the same for its first
// exact-f32 slice. These tests pin `oakLowering.lower` to the two models:
// every expression below is lowered at its own width and its `term.String()`
// must be the render stated as an `example` in the corresponding Lean file.
// A change to either side has to visit the other.
var loweringRenders = []struct {
	decl, body, want string
}{
	{"f: (a, b: u32) -> u32", "a + b", "(a add b)"},
	{"f: (a, b: u32) -> u32", "a - b", "(a sub b)"},
	{"f: (a: u32) -> u32", "a * 3", "(a mul 3)"},
	{"f: (a: u32) -> u32", "a / 8", "(a shr 3)"},
	{"f: (a: u32) -> u32", "a % 8", "(a and 7)"},
	// Division by a variable: the uninterpreted quotient, the remainder
	// a - (a / b) * b, then the type's identity extension (Term.uop, divT).
	{"f: (a, b: u32) -> u32", "a / b", "(udiv32(a, b) and 4294967295)"},
	{"f: (a, b: u32) -> u32", "a % b", "((a sub (udiv32(a, b) mul b)) and 4294967295)"},
	{"f: (a, b: i32) -> i32", "a / b", "(((sdiv32(a, b) and 4294967295) shl 0) sar 0)"},
	{"f: (a, b: i8) -> i8", "a % b", "((((a sub (sdiv8(a, b) mul b)) and 255) shl 0) sar 0)"},
	// Exact binary32 arithmetic (FloatLoweringRefinement.lowerF): the
	// extraction's add32/sub32/mul32 and the verifier's width-32 termFloat
	// keep the same operation and operand order. Multiplication followed by
	// addition stays two operations; it is never contracted implicitly.
	{"f: (a, b: f32) -> f32", "a + b", "fadd32(a, b)"},
	{"f: (a, b: f32) -> f32", "a - b", "fsub32(a, b)"},
	{"f: (a, b: f32) -> f32", "a * b", "fmul32(a, b)"},
	{"f: (a, b, c: f32) -> f32", "a * b + c", "fadd32(fmul32(a, b), c)"},
	// Exact sign operations (FloatLoweringRefinement): negation flips the
	// sign bit, abs clears it, and copysign combines the magnitude and sign.
	{"f: (a: f32) -> f32", "-a", "(a xor 2147483648)"},
	{"f: (a: f32) -> f32", "abs(a)", "(a and 2147483647)"},
	{"f: (a, b: f32) -> f32", "copysign(-a, b)", "(((a xor 2147483648) and 2147483647) or (b and 2147483648))"},
	// IEEE comparisons (FloatLoweringRefinement.lowerCondition): NaNs are
	// unordered, signed zeros compare equal, and finite nonzero values use
	// the sign-magnitude order.  The deliberately explicit renders pin the
	// production floatCompare expansion to that model.
	{"f: (a, b: f32) -> Bool", "a == b", "((((((a and 2139095040) eq 2139095040) and ((a and 8388607) ne 0)) or (((b and 2139095040) eq 2139095040) and ((b and 8388607) ne 0))) xor 1) and ((a eq b) or (((a and 2147483647) or (b and 2147483647)) eq 0)))"},
	{"f: (a, b: f32) -> Bool", "a != b", "(((((((a and 2139095040) eq 2139095040) and ((a and 8388607) ne 0)) or (((b and 2139095040) eq 2139095040) and ((b and 8388607) ne 0))) xor 1) and ((a eq b) or (((a and 2147483647) or (b and 2147483647)) eq 0))) xor 1)"},
	{"f: (a, b: f32) -> Bool", "a < b", "((((((a and 2139095040) eq 2139095040) and ((a and 8388607) ne 0)) or (((b and 2139095040) eq 2139095040) and ((b and 8388607) ne 0))) xor 1) and (((((a and 2147483647) or (b and 2147483647)) eq 0) xor 1) and ((((a shr 31) and 1) and (((b shr 31) and 1) xor 1)) or (((((a shr 31) and 1) and ((b shr 31) and 1)) and ((a and 2147483647) hi (b and 2147483647))) or (((((a shr 31) and 1) xor 1) and (((b shr 31) and 1) xor 1)) and ((a and 2147483647) lo (b and 2147483647)))))))"},
	{"f: (a, b: f32) -> Bool", "a <= b", "(((((((a and 2139095040) eq 2139095040) and ((a and 8388607) ne 0)) or (((b and 2139095040) eq 2139095040) and ((b and 8388607) ne 0))) xor 1) and (((((a and 2147483647) or (b and 2147483647)) eq 0) xor 1) and ((((a shr 31) and 1) and (((b shr 31) and 1) xor 1)) or (((((a shr 31) and 1) and ((b shr 31) and 1)) and ((a and 2147483647) hi (b and 2147483647))) or (((((a shr 31) and 1) xor 1) and (((b shr 31) and 1) xor 1)) and ((a and 2147483647) lo (b and 2147483647))))))) or ((((((a and 2139095040) eq 2139095040) and ((a and 8388607) ne 0)) or (((b and 2139095040) eq 2139095040) and ((b and 8388607) ne 0))) xor 1) and ((a eq b) or (((a and 2147483647) or (b and 2147483647)) eq 0))))"},
	{"f: (a, b: f32) -> Bool", "a > b", "((((((a and 2139095040) eq 2139095040) and ((a and 8388607) ne 0)) or (((b and 2139095040) eq 2139095040) and ((b and 8388607) ne 0))) xor 1) and (((((a and 2147483647) or (b and 2147483647)) eq 0) xor 1) and ((((b shr 31) and 1) and (((a shr 31) and 1) xor 1)) or (((((b shr 31) and 1) and ((a shr 31) and 1)) and ((b and 2147483647) hi (a and 2147483647))) or (((((b shr 31) and 1) xor 1) and (((a shr 31) and 1) xor 1)) and ((b and 2147483647) lo (a and 2147483647)))))))"},
	{"f: (a, b: f32) -> Bool", "a >= b", "(((((((a and 2139095040) eq 2139095040) and ((a and 8388607) ne 0)) or (((b and 2139095040) eq 2139095040) and ((b and 8388607) ne 0))) xor 1) and (((((a and 2147483647) or (b and 2147483647)) eq 0) xor 1) and ((((b shr 31) and 1) and (((a shr 31) and 1) xor 1)) or (((((b shr 31) and 1) and ((a shr 31) and 1)) and ((b and 2147483647) hi (a and 2147483647))) or (((((b shr 31) and 1) xor 1) and (((a shr 31) and 1) xor 1)) and ((b and 2147483647) lo (a and 2147483647))))))) or ((((((a and 2139095040) eq 2139095040) and ((a and 8388607) ne 0)) or (((b and 2139095040) eq 2139095040) and ((b and 8388607) ne 0))) xor 1) and ((a eq b) or (((a and 2147483647) or (b and 2147483647)) eq 0))))"},
	// One value-position Bool conditional composes the comparison and float
	// expression refinements, matching the verifier's iteTerm.
	{"f: (a, b: f32) -> f32", "a < b ? a + 1.0 | b * 2.0", "(((((((a and 2139095040) eq 2139095040) and ((a and 8388607) ne 0)) or (((b and 2139095040) eq 2139095040) and ((b and 8388607) ne 0))) xor 1) and (((((a and 2147483647) or (b and 2147483647)) eq 0) xor 1) and ((((a shr 31) and 1) and (((b shr 31) and 1) xor 1)) or (((((a shr 31) and 1) and ((b shr 31) and 1)) and ((a and 2147483647) hi (b and 2147483647))) or (((((a shr 31) and 1) xor 1) and (((b shr 31) and 1) xor 1)) and ((a and 2147483647) lo (b and 2147483647))))))) ? fadd32(a, 1065353216) : fmul32(b, 1073741824))"},
	// A float literal is rounded to its binary32 bits before it enters the
	// term language.  1.5 is 0x3fc00000 (1069547520).
	{"f: (a: f32) -> f32", "a + 1.5", "fadd32(a, 1069547520)"},
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
	// Span elements (`elem`, `len`): a symbolic index is a select, a constant
	// index the element parameter under the same name; a select is masked to
	// its own width by zeroExtend, so a widening masks twice.
	{"f: (v: []u32, i: u32) -> u32", "v[i]", "v[i]"},
	{"f: (v: []u32, i: u32) -> u32", "v[i + 1] * v[0]", "(v[(i add 1)] mul v[0])"},
	{"f: (b: []u8, i: u32) -> u32", "u32(b[i])", "((b[i] and 255) and 255)"},
	{"f: (v: []u32, i: u32) -> Bool", "i < len(v)", "(i lo len(v))"},
	// Folding (`Term.binary`, `iteT`): constant operands fold, `x + 0` is `x`.
	{"f: (a: u32) -> u32", "a + 2 * 3", "(a add 6)"},
	{"f: (a: u32) -> u32", "a + 0", "a"},
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
	// Exact-f32 locals (FloatLoweringRefinement.lowerWith): declaration and
	// rebinding substitute the initializer term into the remaining body.
	{"f: (a: f32) -> f32 = {\n  y: f32 = a + 1.5\n  y * y\n}\n", "fmul32(fadd32(a, 1069547520), fadd32(a, 1069547520))"},
	{"f: (a: f32) -> f32 = {\n  y: f32 = a\n  y = y + 1.0\n  y * 2.0\n}\n", "fmul32(fadd32(a, 1065353216), 1073741824)"},
	{"f: (a, b: u32) -> u32 = {\n  y: u32 = a + b\n  y * y\n}\n", "((a add b) mul (a add b))"},
	{"f: (a: u32) -> u32 = {\n  y: u32 = a\n  y = y + 1\n  y * 2\n}\n", "((a add 1) mul 2)"},
	{"f: (a: u32) -> u32 = {\n  y: u8 = u8_trunc_u32(a)\n  u32(y)\n}\n", "(a and 255)"},
	{"g: (x: u32) -> u32 = x * x\n\nf: (a: u32) -> u32 = g(a + 1)\n", "((a add 1) mul (a add 1))"},
	{"h: (x, y: u32) -> u32 = {\n  d: u32 = x - y\n  d & 255\n}\n\nf: (a, b: u32) -> u32 = h(b, a)\n", "((b sub a) and 255)"},
	// Statement-level conditionals (`condSet`): a local an arm assigns becomes
	// a select between the arms' terms; an untouched local keeps its term.
	{"f: (a, b: u32) -> u32 = {\n  m: u32 = a\n  a < b ? { m = b } | { }\n  m * 2\n}\n", "(((a lo b) ? b : a) mul 2)"},
	{"f: (a, b: u32) -> u32 = {\n  x: u32 = a\n  y: u32 = b\n  a < b ? { x = b\n  y = a } | { x = x + 1 }\n  x - y\n}\n", "(((a lo b) ? b : (a add 1)) sub ((a lo b) ? a : b))"},
	// Counted loops (`whileLoop`): the condition folds to a constant each
	// iteration, so the loop lowers to its unrolled body.
	{"f: (n: u32) -> u32 = {\n  s: u32 = 0\n  i: u32 = 0\n  while i < 3 {\n    s = s + n\n    i = i + 1\n  }\n  s\n}\n", "((n add n) add n)"},
	{"f: (n: u32) -> u32 = {\n  s: u32 = 0\n  i: u32 = 0\n  while i < 4 {\n    i % 2 == 0 ? { s = s + n } | { }\n    i = i + 1\n  }\n  s\n}\n", "(n add n)"},
	// Integer-constant matches (`matchInt`, `matchSet`): an if-chain of
	// equality selects, the first case outermost, the wildcard the fallback.
	{"f: (op, a, b: u32) -> u32 = op ? | 0 => a | 1 => b | _ => a + b\n", "((op eq 0) ? a : ((op eq 1) ? b : (a add b)))"},
	{"f: (op, a: u32) -> u32 = {\n  r: u32 = a\n  op ? | 0 => { r = a + 1 } | 1 => { r = a * 2 } | _ => { }\n  r\n}\n", "((op eq 0) ? (a add 1) : ((op eq 1) ? (a mul 2) : a))"},
	// Owned arrays (`arrDecl`, `arrGet`, `arrSetE`): a read at a symbolic
	// index selects element by element, a write at one selects at every
	// element, literal indices fold to the one element.
	{"f: (i, v: u32) -> u32 = {\n  a: [3]u32\n  a[0] = v\n  a[1] = v + 1\n  a[2] = v * 2\n  a[i]\n}\n", "((i eq 0) ? v : ((i eq 1) ? (v add 1) : (v mul 2)))"},
	{"f: (i, v: u32) -> u32 = {\n  a: [2]u32\n  a[i] = v\n  a[1]\n}\n", "((i eq 1) ? v : 0)"},
	// Records (`recDecl`): a record is its field leaves `r.f`, a field read
	// the variable, a field write its rebinding; a record parameter is its
	// field leaves as parameters (`paramAggregate`).
	{"P: type = struct {\n  x: u32\n  y: u32\n}\n\nf: (a, b: u32) -> u32 = {\n  p: P = P { x: a, y: b }\n  p.x = p.x + 1\n  p.x * p.y\n}\n", "((a add 1) mul b)"},
	{"P: type = struct {\n  x: u32\n  y: u32\n}\n\nf: (p: P) -> u32 = p.x + p.y\n", "(p.x add p.y)"},
	// Sum types: a tagged union is its tag leaf and one payload leaf per
	// carrying variant (`u.tag`, `u.B`); a variant match is the constant
	// match on the tag with the arm's binding an alias of the payload leaf.
	{"U: type = A | B: u32\n\nf: (v: u32) -> u32 = {\n  u: U = .B(v)\n  u ? | B(x) => x + 1 | A => 0\n}\n", "(v add 1)"},
	{"U: type = A | B: u32\n\nf: (u: U) -> u32 = u ? | B(x) => x + 1 | A => 0\n", "((u.tag eq 1) ? (u.B add 1) : 0)"},
	// Nested aggregates and array literals (`arrLit`, leaf naming): a
	// record's array field `r.h[k]`, an array's record elements `a[k].x`,
	// each the same leaves under longer names; a literal binds its elements.
	{"f: (v, i: u32) -> u32 = {\n  a: [3]u32 = [v, 5, v + 1]\n  a[i]\n}\n", "((i eq 0) ? v : ((i eq 1) ? 5 : (v add 1)))"},
	{"R: type = struct {\n  h: [2]u32\n  n: u32\n}\n\nf: (i, v: u32) -> u32 = {\n  r: R = R { h: [v, v + 1], n: 3 }\n  r.h[i] + r.n\n}\n", "(((i eq 0) ? v : (v add 1)) add 3)"},
	{"P: type = struct {\n  x: u32\n  y: u32\n}\n\nf: (i, v: u32) -> u32 = {\n  a: [2]P = [P { x: v, y: 1 }, P { x: v + 1, y: 2 }]\n  a[i].x\n}\n", "((i eq 0) ? v : (v add 1))"},
	{"R: type = struct {\n  h: [2]u32\n  n: u32\n}\n\nf: (r: R, i: u32) -> u32 = r.h[i]\n", "((i eq 0) ? r.h[0] : r.h[1])"},
	// Calls that borrow (`callX`): the callee's span leaves are copies of
	// the owner's, written back on return; a record result binds its
	// leaves in the caller.
	{"g: (s: [*]u32, v: u32) -> u32 = {\n  s[1] = v\n  s[0] + s[1]\n}\n\nf: (v: u32) -> u32 = {\n  a: [2]u32\n  a[0] = v\n  r: u32 = g(span(&a), v + 1)\n  r + a[1]\n}\n", "((v add (v add 1)) add (v add 1))"},
	{"P: type = struct {\n  x: u32\n  y: u32\n}\n\nshift: (p: P, dx: u32) -> P = P { x: p.x + dx, y: p.y }\n\nf: (a, b: u32) -> u32 = {\n  p: P = P { x: a, y: b }\n  q: P = shift(p, 1)\n  q.x * q.y\n}\n", "((a add 1) mul b)"},
	// A local declared inside a loop body (redeclared each iteration) or an
	// arm: its declaration binds the initializer's term, exactly as an
	// assignment to a pre-declared local does, so the model's pre-declared
	// local gives the same terms.
	{"f: (n: u32) -> u32 = {\n  s: u32 = 0\n  i: u32 = 0\n  while i < 2 {\n    d: u32 = n * 2\n    s = s + d\n    i = i + 1\n  }\n  s\n}\n", "((n mul 2) add (n mul 2))"},
	{"f: (a, b: u32) -> u32 = {\n  r: u32 = a\n  a < b ? {\n    t: u32 = b - a\n    r = t\n  } | { }\n  r\n}\n", "((a lo b) ? (b sub a) : a)"},
	// Data-dependent loops (`whileEvent`): the carried locals stand as the
	// fresh symbols `loop<index>.<var>` after the loop (`loopEvent`).
	{"f: (n: u32) -> u32 = {\n  s: u32 = 0\n  i: u32 = 0\n  while i < n {\n    s = s + i\n    i = i + 1\n  }\n  s + i\n}\n", "(loop1.s add loop1.i)"},
	{"f: (n: u32) -> u32 = {\n  s: u32 = 0\n  i: u32 = 0\n  while i < n {\n    s = s + i\n    i = i + 1\n  }\n  s * 2\n}\n", "(loop1.s mul 2)"},
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
		// Record declarations (`P: type = struct { ... }`), as prepareLowering
		// takes them from the unit's declarations.
		lo.records = map[string]*ast.RecordLiteral{}
		lo.adts = map[string]*ast.ADTType{}
		for _, stmt := range program.Statements {
			adt, isADT := stmt.(*ast.ADTType)
			if !isADT || adt.Name == nil || len(adt.TypeParams) != 0 {
				continue
			}
			if len(adt.Variants) == 1 {
				if literal, isRecord := adt.Variants[0].Literal.(*ast.RecordLiteral); isRecord {
					lo.records[adt.Name.Value] = literal
					continue
				}
			}
			lo.adts[adt.Name.Value] = adt
		}
		lo.bindAggregateParams(spec)
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
