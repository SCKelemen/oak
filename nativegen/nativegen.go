// Package nativegen is the native AArch64 backend for Oak bodies
// (docs/spec/94-assembler.md §9): it lowers a type-checked Oak function to
// an asm.Function — the same checked, verifiable, encodable object an
// `.oakasm` unit yields — so the compiler's own output is held to the seam
// checker's disciplines, proved against the Oak body by the verifier where
// the verifier reaches, and encoded by the Oak assembler into the companion
// object. The C backend stays the portable realization and the differential
// oracle.
//
// First increment — the fixed-width integer subset: parameters, locals,
// and results of u8/u16/u32/u64/i8/i16/i32/i64/Bool (or a unit result);
// literals, arithmetic (wrapping, as 20-types.md §11.1 states; division by
// zero traps), shifts (a count at or beyond the width traps), comparisons,
// `&&`/`||` (short-circuit), `!`/`-`/`^`, the primitive conversions
// `u32(x)`, the Bool conditional `c ? a | b` in value and statement
// position, typed locals and assignment, `while`/`break`, `assert`, and
// calls to program functions with scalar signatures. Anything else leaves
// the function to the C backend, with the reason.
//
// Values live in the frame: every parameter and local has an 8-byte slot;
// expressions evaluate into the scratch registers x9–x15 as a small operand
// stack, spilled around calls (the checker forbids reading a caller-saved
// register after `bl`). A value of a narrow type is kept normalized in its
// register — zero-extended when unsigned, sign-extended when signed — so
// comparisons and divisions read it as C does.
package nativegen

import (
	"fmt"
	"strconv"
	"strings"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// scalar is a fixed-width integer type of the subset.
type scalar struct {
	name   string
	bits   int
	signed bool
	isBool bool
}

var scalars = map[string]scalar{
	"u8": {"u8", 8, false, false}, "u16": {"u16", 16, false, false}, "u32": {"u32", 32, false, false}, "u64": {"u64", 64, false, false},
	"i8": {"i8", 8, true, false}, "i16": {"i16", 16, true, false}, "i32": {"i32", 32, true, false}, "i64": {"i64", 64, true, false},
	"Bool": {"Bool", 8, false, true}, "byte": {"u8", 8, false, false},
}

// scalarOf reads a type expression of the subset.
func scalarOf(expr ast.Expression) (scalar, bool) {
	if expr == nil {
		return scalar{}, false
	}
	s, ok := scalars[expr.String()]
	return s, ok
}

// wide reports a type held in an x register (64-bit); the rest use w.
func (s scalar) wide() bool { return s.bits == 64 }

// Unsupported reports why a function is left to the C backend.
type Unsupported struct{ Reason string }

func (u Unsupported) Error() string { return u.Reason }

func unsupported(format string, args ...interface{}) Unsupported {
	return Unsupported{fmt.Sprintf(format, args...)}
}

// generator holds one function's lowering.
type generator struct {
	fn        *ast.FunctionStatement
	tc        *typechecker.TypeChecker
	functions map[string]*ast.FunctionStatement
	result    *scalar

	items    []asm.Item
	slots    map[string]int64  // variable → frame offset (relative to the frame base after the prologue)
	types    map[string]scalar // variable → type
	scopes   []map[string]slotBinding
	nslots   int64
	spill    map[int]int64 // scratch register → its spill slot offset
	free     []int         // free scratch registers
	live     []int         // allocated scratch registers, allocation order
	labels   int
	loops    []string // break targets
	hasCalls bool
	line     int
	trap     string // the trap block's label (division by zero, shift overflow, assert)
	usedTrap bool
	// terminated: an unconditional jump was emitted and no label has
	// followed — instructions there are unreachable and are not emitted (the
	// checker refuses them).
	terminated bool
}

type slotBinding struct {
	offset int64
	typ    scalar
}

const scratchLow, scratchHigh = 9, 15

// Compile lowers one Oak function. functions maps every program function by
// name (callees' signatures); tc is the checker that typed the program.
func Compile(fn *ast.FunctionStatement, functions map[string]*ast.FunctionStatement, tc *typechecker.TypeChecker) (*asm.Function, error) {
	if fn.Body == nil || fn.ExternSymbol != "" || fn.Receiver != nil || len(fn.TypeParams) > 0 || fn.AsmBacked {
		return nil, unsupported("not an ordinary function body")
	}
	if len(fn.Parameters) > 8 {
		return nil, unsupported("more than eight parameters")
	}
	g := &generator{fn: fn, tc: tc, functions: functions, slots: map[string]int64{}, types: map[string]scalar{}, spill: map[int]int64{}, line: fn.Token.Line}
	for r := scratchHigh; r >= scratchLow; r-- {
		g.free = append(g.free, r)
	}
	for _, p := range fn.Parameters {
		if p.Variadic {
			return nil, unsupported("variadic parameter %s", p.Name.Value)
		}
		if _, ok := scalarOf(p.Type); !ok {
			return nil, unsupported("parameter %s of type %s", p.Name.Value, p.Type.String())
		}
	}
	if fn.ReturnType != nil {
		if fn.ReturnType.String() != "()" {
			s, ok := scalarOf(fn.ReturnType)
			if !ok {
				return nil, unsupported("result of type %s", fn.ReturnType.String())
			}
			g.result = &s
		}
	}
	g.hasCalls = mentionsCall(fn.Body)
	// Parameters occupy the first slots, in order.
	g.pushScope()
	for _, p := range fn.Parameters {
		s, _ := scalarOf(p.Type)
		g.declare(p.Name.Value, s)
	}
	body, err := g.lowerBody(fn.Body)
	if err != nil {
		return nil, err
	}
	// The frame: [x29, x30] when the body calls, then the slots, rounded to
	// 16 bytes; sp moves once at entry and once before ret.
	frame := g.frameSize()
	if frame > 4080 {
		return nil, unsupported("a frame of %d bytes", frame)
	}
	out := &asm.Function{Name: fn.Name.Value, Signature: fn, Line: fn.Token.Line, Fallback: true}
	g.line = fn.Token.Line
	var prologue []asm.Item
	if frame > 0 {
		out.Frame = frame
		prologue = append(prologue, g.ins("sub", sp(), sp(), imm(frame)))
	}
	if g.hasCalls {
		prologue = append(prologue, g.ins("stp", xr(29), xr(30), mem(0)))
	}
	// Bind and store the parameters (narrow ones normalized: the caller's
	// upper bits are unspecified under AAPCS64).
	for i, p := range fn.Parameters {
		s, _ := scalarOf(p.Type)
		bound := wr(i)
		if s.wide() {
			bound = xr(i)
		}
		out.Bindings = append(out.Bindings, asm.Binding{Register: bound, Param: p.Name.Value, Line: fn.Token.Line})
		prologue = append(prologue, g.normalizeInto(i, s)...)
		prologue = append(prologue, g.ins("str", reg(i, s), g.slotMem(g.slots[p.Name.Value])))
	}
	out.Items = append(prologue, body...)
	// Clobbers: the scratch registers, the argument registers a call
	// writes beyond the bound parameters, and the link register.
	for r := scratchLow; r <= scratchHigh; r++ {
		out.Clobbers = append(out.Clobbers, xr(r))
	}
	if g.hasCalls {
		for r := len(fn.Parameters); r <= 7; r++ {
			if !(g.result != nil && r == 0) {
				out.Clobbers = append(out.Clobbers, xr(r))
			}
		}
		out.Clobbers = append(out.Clobbers, xr(29), xr(30)) // saved by the prologue's stp, restored by ldp
	}
	return out, nil
}

// frameSize is the frame in bytes: the [x29, x30] pair when the body
// calls, the slots, rounded up to 16.
func (g *generator) frameSize() int64 {
	base := int64(0)
	if g.hasCalls {
		base = 16
	}
	return (base + 8*g.nslots + 15) / 16 * 16
}

// ---- items ------------------------------------------------------------

func xr(n int) asm.Register {
	if n == 31 {
		return asm.Register{Text: "xzr", Class: asm.ClassX, Num: 31, Lane: -1}
	}
	return asm.Register{Text: "x" + strconv.Itoa(n), Class: asm.ClassX, Num: n, Lane: -1}
}

func wr(n int) asm.Register {
	if n == 31 {
		return asm.Register{Text: "wzr", Class: asm.ClassW, Num: 31, Lane: -1}
	}
	return asm.Register{Text: "w" + strconv.Itoa(n), Class: asm.ClassW, Num: n, Lane: -1}
}

func sp() asm.Register { return asm.Register{Text: "sp", Class: asm.ClassSP, Num: -1, Lane: -1} }

func imm(v int64) asm.Immediate { return asm.Immediate{Value: v} }

func mem(offset int64) asm.Memory { return asm.Memory{Base: sp(), Offset: offset} }

func (g *generator) ins(mnemonic string, operands ...asm.Operand) asm.Instruction {
	return asm.Instruction{Mnemonic: mnemonic, Operands: operands, Line: g.line}
}

func (g *generator) emit(mnemonic string, operands ...asm.Operand) {
	if g.terminated {
		return
	}
	g.items = append(g.items, g.ins(mnemonic, operands...))
	if mnemonic == "b" || mnemonic == "ret" || mnemonic == "brk" {
		g.terminated = true
	}
}

func (g *generator) branch(cond, label string) {
	if g.terminated {
		return
	}
	g.items = append(g.items, asm.Instruction{Mnemonic: "b.", Cond: cond, Operands: []asm.Operand{asm.Symbol{Name: label}}, Line: g.line})
}

func (g *generator) label(name string) {
	g.items = append(g.items, asm.Label{Name: name, Line: g.line})
	g.terminated = false
}

func (g *generator) newLabel(hint string) string {
	g.labels++
	return fmt.Sprintf("%s_%d", hint, g.labels)
}

// reg spells scratch register r at the type's width.
func reg(r int, s scalar) asm.Register {
	if s.wide() {
		return xr(r)
	}
	return wr(r)
}

// ---- scratch registers and slots --------------------------------------

func (g *generator) alloc() (int, error) {
	if len(g.free) == 0 {
		return 0, unsupported("an expression deeper than the scratch registers")
	}
	r := g.free[len(g.free)-1]
	g.free = g.free[:len(g.free)-1]
	g.live = append(g.live, r)
	return r, nil
}

func (g *generator) release(r int) {
	for i, live := range g.live {
		if live == r {
			g.live = append(g.live[:i], g.live[i+1:]...)
			break
		}
	}
	g.free = append(g.free, r)
}

func (g *generator) pushScope() { g.scopes = append(g.scopes, map[string]slotBinding{}) }

func (g *generator) popScope() {
	top := g.scopes[len(g.scopes)-1]
	g.scopes = g.scopes[:len(g.scopes)-1]
	for name := range top {
		delete(g.slots, name)
		delete(g.types, name)
		// A shadowed outer binding comes back into view.
		for i := len(g.scopes) - 1; i >= 0; i-- {
			if b, ok := g.scopes[i][name]; ok {
				g.slots[name], g.types[name] = b.offset, b.typ
				break
			}
		}
	}
}

// declare gives a variable a fresh slot in the current scope.
func (g *generator) declare(name string, s scalar) int64 {
	offset := 8 * g.nslots
	g.nslots++
	g.slots[name], g.types[name] = offset, s
	g.scopes[len(g.scopes)-1][name] = slotBinding{offset, s}
	return offset
}

// slotMem is the frame address of a slot; the prologue's [x29, x30] pair
// sits below the slots when the body calls.
func (g *generator) slotMem(offset int64) asm.Memory {
	if g.hasCalls {
		return mem(offset + 16)
	}
	return mem(offset)
}

// ---- types --------------------------------------------------------------

// typeOf infers an expression's type in the subset; hint is the type the
// context expects (a literal takes it).
func (g *generator) typeOf(expr ast.Expression, hint *scalar) (scalar, error) {
	switch e := expr.(type) {
	case *ast.IntegerLiteral:
		if hint != nil {
			return *hint, nil
		}
		return scalars["i32"], nil
	case *ast.Boolean:
		return scalars["Bool"], nil
	case *ast.Identifier:
		if s, ok := g.types[e.Value]; ok {
			return s, nil
		}
		return scalar{}, unsupported("identifier %s", e.Value)
	case *ast.InfixExpression:
		switch e.Operator {
		case "==", "!=", "<", "<=", ">", ">=", "&&", "||":
			return scalars["Bool"], nil
		case "<<", ">>":
			if width, known := g.tc.ShiftWidth(e.Token); known {
				return scalars["u"+strconv.Itoa(width)], nil
			}
			return g.typeOf(e.Left, hint)
		}
		if name, known := g.tc.ArithmeticType(e.Token); known {
			if s, ok := scalars[name]; ok {
				return s, nil
			}
			return scalar{}, unsupported("arithmetic on %s", name)
		}
		// A literal-only expression carries no record: the context types it.
		left, err := g.typeOf(e.Left, hint)
		if err == nil {
			return left, nil
		}
		return g.typeOf(e.Right, hint)
	case *ast.PrefixExpression:
		if e.Operator == "!" {
			return scalars["Bool"], nil
		}
		if name, known := g.tc.ArithmeticType(e.Token); known {
			if s, ok := scalars[name]; ok {
				return s, nil
			}
		}
		return g.typeOf(e.Right, hint)
	case *ast.InvocationExpression:
		ident, isIdent := e.Function.(*ast.Identifier)
		if !isIdent {
			return scalar{}, unsupported("a call through a value")
		}
		if s, isConv := scalars[ident.Value]; isConv && len(e.Arguments) == 1 && ident.Value != "byte" {
			return s, nil
		}
		if target, op, _, isConv := typechecker.ConversionParts(ident.Value); isConv && len(e.Arguments) == 1 {
			if op != "trunc" && op != "bits" {
				return scalar{}, unsupported("a %s conversion", op)
			}
			if s, ok := scalars[target]; ok {
				return s, nil
			}
			return scalar{}, unsupported("a conversion to %s", target)
		}
		if callee, ok := g.functions[ident.Value]; ok {
			if callee.ReturnType == nil || callee.ReturnType.String() == "()" {
				return scalar{}, unsupported("a call to %s (no result) in value position", ident.Value)
			}
			if s, ok := scalarOf(callee.ReturnType); ok {
				return s, nil
			}
			return scalar{}, unsupported("a call to %s returning %s", ident.Value, callee.ReturnType.String())
		}
		return scalar{}, unsupported("a call to %s", ident.Value)
	case *ast.MatchExpression:
		whenTrue, _, ok := boolConditional(e)
		if !ok {
			return scalar{}, unsupported("a match that is not a Bool conditional")
		}
		return g.typeOf(whenTrue, hint)
	case *ast.BlockExpression:
		if r := e.Result(); r != nil {
			return g.typeOf(r, hint)
		}
		return scalar{}, unsupported("a block without a result")
	}
	return scalar{}, unsupported("%T", expr)
}

// ---- the body -------------------------------------------------------------

// lowerBody lowers the function body; the result (if any) ends in w0/x0
// and control reaches ret with the frame released.
func (g *generator) lowerBody(body ast.Expression) ([]asm.Item, error) {
	retLabel := g.newLabel("ret")
	trapLabel := g.newLabel("trap")
	g.trap = trapLabel
	switch b := body.(type) {
	case *ast.BlockExpression:
		if b.Block == nil {
			return nil, unsupported("an empty body")
		}
		if err := g.lowerStatements(b.Block.Statements, true, retLabel); err != nil {
			return nil, err
		}
	default:
		if g.result == nil {
			return nil, unsupported("an expression body in a function without a result")
		}
		r, err := g.expr(body, g.result)
		if err != nil {
			return nil, err
		}
		g.moveResult(r, *g.result)
		g.release(r)
	}
	g.label(retLabel)
	g.epilogue()
	if g.usedTrap {
		g.label(trapLabel)
		g.emit("brk", imm(1))
	}
	return g.items, nil
}

func (g *generator) epilogue() {
	frame := g.frameSize()
	if g.hasCalls {
		g.emit("ldp", xr(29), xr(30), mem(0))
	}
	if frame > 0 {
		g.emit("add", sp(), sp(), imm(frame))
	}
	g.emit("ret")
}

// moveResult places a value in the result register.
func (g *generator) moveResult(r int, s scalar) {
	g.emit("mov", reg(0, s), reg(r, s))
}

// lowerStatements lowers a block; in a function body the last expression
// statement is the result.
func (g *generator) lowerStatements(stmts []ast.Statement, functionBody bool, retLabel string) error {
	for i, stmt := range stmts {
		last := functionBody && i == len(stmts)-1
		g.line = statementLine(stmt)
		switch s := stmt.(type) {
		case *ast.VariableDeclaration:
			if s.Value == nil {
				return unsupported("a local without an initializer")
			}
			var typ scalar
			if s.Type != nil {
				t, ok := scalarOf(s.Type)
				if !ok {
					return unsupported("a local of type %s", s.Type.String())
				}
				typ = t
			} else {
				t, err := g.typeOf(s.Value, nil)
				if err != nil {
					return err
				}
				typ = t
			}
			r, err := g.expr(s.Value, &typ)
			if err != nil {
				return err
			}
			offset := g.declare(s.Name.Value, typ)
			g.emit("str", reg(r, typ), g.slotMem(offset))
			g.release(r)
		case *ast.AssignmentStatement:
			typ, ok := g.types[s.Name.Value]
			if !ok {
				return unsupported("an assignment to %s", s.Name.Value)
			}
			r, err := g.expr(s.Value, &typ)
			if err != nil {
				return err
			}
			g.emit("str", reg(r, typ), g.slotMem(g.slots[s.Name.Value]))
			g.release(r)
		case *ast.WhileStatement:
			if err := g.lowerWhile(s); err != nil {
				return err
			}
		case *ast.IfStatement:
			if err := g.lowerIf(s); err != nil {
				return err
			}
		case *ast.BreakStatement:
			if len(g.loops) == 0 {
				return unsupported("break outside a loop")
			}
			g.emit("b", asm.Symbol{Name: g.loops[len(g.loops)-1]})
		case *ast.BlockStatement:
			g.pushScope()
			err := g.lowerStatements(s.Statements, false, "")
			g.popScope()
			if err != nil {
				return err
			}
		case *ast.ExpressionStatement:
			if last && !s.Discard {
				if g.result == nil {
					// A unit function whose last statement is an expression.
					if err := g.effect(s.Expression); err != nil {
						return err
					}
					continue
				}
				r, err := g.expr(s.Expression, g.result)
				if err != nil {
					return err
				}
				g.moveResult(r, *g.result)
				g.release(r)
				continue
			}
			if match, isMatch := s.Expression.(*ast.MatchExpression); isMatch {
				if err := g.lowerConditionalStatement(match); err != nil {
					return err
				}
				continue
			}
			if err := g.effect(s.Expression); err != nil {
				return err
			}
		default:
			return unsupported("%T", stmt)
		}
	}
	if functionBody && g.result != nil {
		if len(stmts) == 0 {
			return unsupported("an empty body with a result")
		}
		if es, ok := stmts[len(stmts)-1].(*ast.ExpressionStatement); !ok || es.Discard {
			return unsupported("a body whose last statement is not its result")
		}
	}
	return nil
}

// effect evaluates an expression for its effects: a call, or assert.
func (g *generator) effect(expr ast.Expression) error {
	call, isCall := expr.(*ast.InvocationExpression)
	if !isCall {
		return unsupported("an expression statement that is not a call")
	}
	ident, isIdent := call.Function.(*ast.Identifier)
	if !isIdent {
		return unsupported("a call through a value")
	}
	if ident.Value == "assert" && len(call.Arguments) == 1 {
		b := scalars["Bool"]
		r, err := g.expr(call.Arguments[0], &b)
		if err != nil {
			return err
		}
		g.usedTrap = true
		g.emit("cbz", wr(r), asm.Symbol{Name: g.trap})
		g.release(r)
		return nil
	}
	r, err := g.call(call)
	if err != nil {
		return err
	}
	if r >= 0 {
		g.release(r)
	}
	return nil
}

func (g *generator) lowerWhile(loop *ast.WhileStatement) error {
	head, end := g.newLabel("loop"), g.newLabel("done")
	g.label(head)
	if err := g.condition(loop.Condition, end); err != nil {
		return err
	}
	g.loops = append(g.loops, end)
	g.pushScope()
	err := g.lowerStatements(loop.Body.Statements, false, "")
	g.popScope()
	g.loops = g.loops[:len(g.loops)-1]
	if err != nil {
		return err
	}
	g.emit("b", asm.Symbol{Name: head})
	g.label(end)
	return nil
}

func (g *generator) lowerIf(s *ast.IfStatement) error {
	elseLabel, end := g.newLabel("else"), g.newLabel("endif")
	if err := g.condition(s.Condition, elseLabel); err != nil {
		return err
	}
	if s.Consequence != nil {
		g.pushScope()
		err := g.lowerStatements(s.Consequence.Statements, false, "")
		g.popScope()
		if err != nil {
			return err
		}
	}
	g.emit("b", asm.Symbol{Name: end})
	g.label(elseLabel)
	switch alt := s.Alternative.(type) {
	case nil:
	case *ast.IfStatement:
		if err := g.lowerIf(alt); err != nil {
			return err
		}
	case *ast.BlockStatement:
		g.pushScope()
		err := g.lowerStatements(alt.Statements, false, "")
		g.popScope()
		if err != nil {
			return err
		}
	default:
		return unsupported("an else of %T", alt)
	}
	g.label(end)
	return nil
}

// lowerConditionalStatement: `c ? { ... } | { ... }` in statement position.
func (g *generator) lowerConditionalStatement(match *ast.MatchExpression) error {
	whenTrue, whenFalse, ok := boolConditional(match)
	if !ok {
		return unsupported("a statement-level match that is not a Bool conditional")
	}
	elseLabel, end := g.newLabel("else"), g.newLabel("endif")
	if err := g.condition(match.Scrutinee, elseLabel); err != nil {
		return err
	}
	if err := g.lowerArm(whenTrue); err != nil {
		return err
	}
	g.emit("b", asm.Symbol{Name: end})
	g.label(elseLabel)
	if err := g.lowerArm(whenFalse); err != nil {
		return err
	}
	g.label(end)
	return nil
}

func (g *generator) lowerArm(arm ast.Expression) error {
	block, isBlock := arm.(*ast.BlockExpression)
	if !isBlock {
		return unsupported("a conditional arm in statement position that is not a block")
	}
	if block.Block == nil {
		return nil
	}
	g.pushScope()
	defer g.popScope()
	return g.lowerStatements(block.Block.Statements, false, "")
}

// condition evaluates a Bool expression and branches to target when false.
func (g *generator) condition(expr ast.Expression, target string) error {
	b := scalars["Bool"]
	r, err := g.expr(expr, &b)
	if err != nil {
		return err
	}
	g.emit("cbz", wr(r), asm.Symbol{Name: target})
	g.release(r)
	return nil
}

// ---- expressions ------------------------------------------------------------

// expr evaluates an expression into a fresh scratch register, normalized at
// its own type; hint types literals.
func (g *generator) expr(expr ast.Expression, hint *scalar) (int, error) {
	typ, err := g.typeOf(expr, hint)
	if err != nil {
		return 0, err
	}
	switch e := expr.(type) {
	case *ast.IntegerLiteral:
		r, err := g.alloc()
		if err != nil {
			return 0, err
		}
		g.constant(r, uint64(e.Value), typ)
		return r, nil
	case *ast.Boolean:
		r, err := g.alloc()
		if err != nil {
			return 0, err
		}
		v := uint64(0)
		if e.Value {
			v = 1
		}
		g.constant(r, v, typ)
		return r, nil
	case *ast.Identifier:
		r, err := g.alloc()
		if err != nil {
			return 0, err
		}
		g.emit("ldr", reg(r, typ), g.slotMem(g.slots[e.Value]))
		return r, nil
	case *ast.InfixExpression:
		return g.infix(e, typ)
	case *ast.PrefixExpression:
		return g.prefix(e, typ)
	case *ast.InvocationExpression:
		ident := e.Function.(*ast.Identifier)
		if target, isConv := scalars[ident.Value]; isConv && len(e.Arguments) == 1 && ident.Value != "byte" {
			return g.convert(e.Arguments[0], target)
		}
		if targetName, _, _, isConv := typechecker.ConversionParts(ident.Value); isConv && len(e.Arguments) == 1 {
			// {target}_trunc_{source} / {target}_bits_{source}: the operand's
			// bits at the target width (typeOf admitted only these two).
			return g.convert(e.Arguments[0], scalars[targetName])
		}
		return g.call(e)
	case *ast.MatchExpression:
		whenTrue, whenFalse, _ := boolConditional(e)
		elseLabel, end := g.newLabel("else"), g.newLabel("endif")
		if err := g.condition(e.Scrutinee, elseLabel); err != nil {
			return 0, err
		}
		out, err := g.alloc()
		if err != nil {
			return 0, err
		}
		t, err := g.expr(whenTrue, &typ)
		if err != nil {
			return 0, err
		}
		g.emit("mov", reg(out, typ), reg(t, typ))
		g.release(t)
		g.emit("b", asm.Symbol{Name: end})
		g.label(elseLabel)
		f, err := g.expr(whenFalse, &typ)
		if err != nil {
			return 0, err
		}
		g.emit("mov", reg(out, typ), reg(f, typ))
		g.release(f)
		g.label(end)
		return out, nil
	case *ast.BlockExpression:
		if e.Block == nil || len(e.Block.Statements) == 0 {
			return 0, unsupported("an empty block in value position")
		}
		g.pushScope()
		defer g.popScope()
		stmts := e.Block.Statements
		if err := g.lowerStatements(stmts[:len(stmts)-1], false, ""); err != nil {
			return 0, err
		}
		es, ok := stmts[len(stmts)-1].(*ast.ExpressionStatement)
		if !ok {
			return 0, unsupported("a block whose last statement is not an expression")
		}
		return g.expr(es.Expression, &typ)
	}
	return 0, unsupported("%T", expr)
}

// constant materializes a value at a type (movz/movk pieces).
func (g *generator) constant(r int, v uint64, s scalar) {
	if !s.wide() {
		v &= 0xffffffff
		// Narrow signed values keep their sign extension within the word.
		if s.signed && s.bits < 32 {
			v = uint64(int64(int32(v)<<uint(32-s.bits)>>uint(32-s.bits))) & 0xffffffff
		}
	}
	dst := reg(r, s)
	if v == 0 {
		g.emit("mov", dst, reg(31, s))
		return
	}
	first := true
	for shift := 0; shift < 64; shift += 16 {
		if !s.wide() && shift >= 32 {
			break
		}
		piece := (v >> uint(shift)) & 0xffff
		if piece == 0 {
			continue
		}
		if first {
			g.emit("movz", dst, asm.Immediate{Value: int64(piece), Shift: int64(shift)})
			first = false
		} else {
			g.emit("movk", dst, asm.Immediate{Value: int64(piece), Shift: int64(shift)})
		}
	}
}

// normalize re-establishes a narrow type's representation after an
// operation on the whole register.
func (g *generator) normalize(r int, s scalar) {
	for _, it := range g.normalizeInto(r, s) {
		g.items = append(g.items, it)
	}
}

func (g *generator) normalizeInto(r int, s scalar) []asm.Item {
	switch {
	case s.bits >= 32:
		return nil
	case s.signed && s.bits == 8:
		return []asm.Item{g.ins("sxtb", wr(r), wr(r))}
	case s.signed:
		return []asm.Item{g.ins("sxth", wr(r), wr(r))}
	case s.bits == 8:
		return []asm.Item{g.ins("and", wr(r), wr(r), imm(0xff))}
	default:
		return []asm.Item{g.ins("and", wr(r), wr(r), imm(0xffff))}
	}
}

var conditionCodes = map[string][2]string{
	"==": {"eq", "eq"}, "!=": {"ne", "ne"},
	"<": {"lo", "lt"}, "<=": {"ls", "le"}, ">": {"hi", "gt"}, ">=": {"hs", "ge"},
}

func (g *generator) infix(e *ast.InfixExpression, typ scalar) (int, error) {
	switch e.Operator {
	case "&&", "||":
		out, err := g.alloc()
		if err != nil {
			return 0, err
		}
		end := g.newLabel("short")
		b := scalars["Bool"]
		l, err := g.expr(e.Left, &b)
		if err != nil {
			return 0, err
		}
		g.emit("mov", wr(out), wr(l))
		g.release(l)
		if e.Operator == "&&" {
			g.emit("cbz", wr(out), asm.Symbol{Name: end})
		} else {
			g.emit("cbnz", wr(out), asm.Symbol{Name: end})
		}
		rr, err := g.expr(e.Right, &b)
		if err != nil {
			return 0, err
		}
		g.emit("mov", wr(out), wr(rr))
		g.release(rr)
		g.label(end)
		return out, nil
	case "==", "!=", "<", "<=", ">", ">=":
		operand, err := g.operandType(e)
		if err != nil {
			return 0, err
		}
		l, err := g.expr(e.Left, &operand)
		if err != nil {
			return 0, err
		}
		r, err := g.expr(e.Right, &operand)
		if err != nil {
			return 0, err
		}
		g.emit("cmp", reg(l, operand), reg(r, operand))
		g.release(r)
		code := conditionCodes[e.Operator][0]
		if operand.signed {
			code = conditionCodes[e.Operator][1]
		}
		g.emit("cset", wr(l), asm.Condition{Code: code})
		return l, nil
	}
	l, err := g.expr(e.Left, &typ)
	if err != nil {
		return 0, err
	}
	switch e.Operator {
	case "<<", ">>":
		if typ.signed {
			return 0, unsupported("a shift of a signed operand")
		}
		count, isConst := constantValue(e.Right)
		if isConst {
			if count < 0 || count >= int64(typ.bits) {
				return 0, unsupported("a constant shift count of %d", count)
			}
			op := "lsl"
			if e.Operator == ">>" {
				op = "lsr"
			}
			g.emit(op, reg(l, typ), reg(l, typ), imm(count))
			g.normalize(l, typ)
			return l, nil
		}
		r, err := g.expr(e.Right, &typ)
		if err != nil {
			return 0, err
		}
		// A count at or beyond the width traps (10-syntax.md §3b).
		g.usedTrap = true
		g.emit("cmp", reg(r, typ), imm(int64(typ.bits)))
		g.branch("hs", g.trap)
		op := "lsl"
		if e.Operator == ">>" {
			op = "lsr"
		}
		g.emit(op, reg(l, typ), reg(l, typ), reg(r, typ))
		g.release(r)
		g.normalize(l, typ)
		return l, nil
	}
	r, err := g.expr(e.Right, &typ)
	if err != nil {
		return 0, err
	}
	switch e.Operator {
	case "+":
		g.emit("add", reg(l, typ), reg(l, typ), reg(r, typ))
	case "-":
		g.emit("sub", reg(l, typ), reg(l, typ), reg(r, typ))
	case "*":
		g.emit("mul", reg(l, typ), reg(l, typ), reg(r, typ))
	case "&":
		g.emit("and", reg(l, typ), reg(l, typ), reg(r, typ))
	case "|":
		g.emit("orr", reg(l, typ), reg(l, typ), reg(r, typ))
	case "^":
		g.emit("eor", reg(l, typ), reg(l, typ), reg(r, typ))
	case "/", "%":
		// Division by zero traps; MIN / -1 and MIN % -1 wrap as the C
		// helpers state (sdiv and msub give exactly that).
		g.usedTrap = true
		g.emit("cbz", reg(r, typ), asm.Symbol{Name: g.trap})
		div := "udiv"
		if typ.signed {
			div = "sdiv"
		}
		if e.Operator == "/" {
			g.emit(div, reg(l, typ), reg(l, typ), reg(r, typ))
		} else {
			q, err := g.alloc()
			if err != nil {
				return 0, err
			}
			g.emit(div, reg(q, typ), reg(l, typ), reg(r, typ))
			g.emit("msub", reg(l, typ), reg(q, typ), reg(r, typ), reg(l, typ))
			g.release(q)
		}
	default:
		return 0, unsupported("operator %s", e.Operator)
	}
	g.release(r)
	g.normalize(l, typ)
	return l, nil
}

// operandType is the common type of a comparison's operands.
func (g *generator) operandType(e *ast.InfixExpression) (scalar, error) {
	if s, err := g.typeOf(e.Left, nil); err == nil && !isLiteral(e.Left) {
		return s, nil
	}
	if s, err := g.typeOf(e.Right, nil); err == nil && !isLiteral(e.Right) {
		return s, nil
	}
	return g.typeOf(e.Left, nil)
}

func isLiteral(expr ast.Expression) bool {
	switch expr.(type) {
	case *ast.IntegerLiteral, *ast.Boolean:
		return true
	}
	return false
}

func constantValue(expr ast.Expression) (int64, bool) {
	switch e := expr.(type) {
	case *ast.IntegerLiteral:
		return e.Value, true
	case *ast.InvocationExpression:
		if ident, ok := e.Function.(*ast.Identifier); ok && len(e.Arguments) == 1 {
			if _, isConv := scalars[ident.Value]; isConv {
				return constantValue(e.Arguments[0])
			}
		}
	}
	return 0, false
}

// isConversion reports the conversion spellings the subset lowers inline
// (not calls): `u32(x)`, `u16_trunc_u64(x)`, `i32_bits_u32(x)`.
func isConversion(name string) bool {
	if _, isCtor := scalars[name]; isCtor && name != "byte" {
		return true
	}
	_, op, _, ok := typechecker.ConversionParts(name)
	return ok && (op == "trunc" || op == "bits")
}

func (g *generator) prefix(e *ast.PrefixExpression, typ scalar) (int, error) {
	switch e.Operator {
	case "!":
		b := scalars["Bool"]
		r, err := g.expr(e.Right, &b)
		if err != nil {
			return 0, err
		}
		g.emit("eor", wr(r), wr(r), imm(1))
		return r, nil
	case "-":
		r, err := g.expr(e.Right, &typ)
		if err != nil {
			return 0, err
		}
		g.emit("neg", reg(r, typ), reg(r, typ))
		g.normalize(r, typ)
		return r, nil
	case "^":
		r, err := g.expr(e.Right, &typ)
		if err != nil {
			return 0, err
		}
		g.emit("mvn", reg(r, typ), reg(r, typ))
		g.normalize(r, typ)
		return r, nil
	}
	return 0, unsupported("prefix operator %s", e.Operator)
}

// convert lowers `T(x)`: the operand's bits at the new width — a widening
// of a signed operand sign-extends, everything else truncates or zero-fills.
func (g *generator) convert(operand ast.Expression, target scalar) (int, error) {
	source, err := g.typeOf(operand, &target)
	if err != nil {
		return 0, err
	}
	r, err := g.expr(operand, &source)
	if err != nil {
		return 0, err
	}
	switch {
	case source.wide() && target.wide():
	case !source.wide() && target.wide():
		if source.signed {
			g.emit("sxtw", xr(r), wr(r))
		} else {
			g.emit("mov", wr(r), wr(r)) // the upper half is already zero: a w write clears it
		}
	case source.wide() && !target.wide():
		g.emit("mov", wr(r), wr(r))
		g.normalize(r, target)
	default:
		g.normalize(r, target)
	}
	return r, nil
}

// call evaluates a call: arguments into x0–x7, live scratch spilled around
// the bl, the result (if any) into a fresh scratch register (-1 for unit).
func (g *generator) call(e *ast.InvocationExpression) (int, error) {
	ident := e.Function.(*ast.Identifier)
	callee, ok := g.functions[ident.Value]
	if !ok {
		return 0, unsupported("a call to %s", ident.Value)
	}
	if len(e.Arguments) != len(callee.Parameters) || len(e.Arguments) > 8 {
		return 0, unsupported("a call to %s with %d arguments", ident.Value, len(e.Arguments))
	}
	var argTypes []scalar
	for _, p := range callee.Parameters {
		s, ok := scalarOf(p.Type)
		if !ok || p.Variadic {
			return 0, unsupported("a call to %s (parameter %s: %s)", ident.Value, p.Name.Value, p.Type.String())
		}
		argTypes = append(argTypes, s)
	}
	var resultType *scalar
	if callee.ReturnType != nil && callee.ReturnType.String() != "()" {
		s, ok := scalarOf(callee.ReturnType)
		if !ok {
			return 0, unsupported("a call to %s returning %s", ident.Value, callee.ReturnType.String())
		}
		resultType = &s
	}
	// Arguments evaluate into scratch registers first (an argument may
	// itself call), then move to the argument registers.
	var args []int
	for i, arg := range e.Arguments {
		r, err := g.expr(arg, &argTypes[i])
		if err != nil {
			return 0, err
		}
		args = append(args, r)
	}
	for i, r := range args {
		g.emit("mov", reg(i, argTypes[i]), reg(r, argTypes[i]))
		g.release(r)
	}
	// Spill the live scratch registers: the callee owns x9–x15.
	var spilled []int
	for _, r := range g.live {
		if _, ok := g.spill[r]; !ok {
			g.spill[r] = 8 * g.nslots
			g.nslots++
		}
		g.emit("str", xr(r), g.slotMem(g.spill[r]))
		spilled = append(spilled, r)
	}
	g.emit("bl", asm.Symbol{Name: ident.Value})
	for _, r := range spilled {
		g.emit("ldr", xr(r), g.slotMem(g.spill[r]))
	}
	if resultType == nil {
		return -1, nil
	}
	out, err := g.alloc()
	if err != nil {
		return 0, err
	}
	g.emit("mov", reg(out, *resultType), reg(0, *resultType))
	return out, nil
}

// ---- helpers ------------------------------------------------------------------

// boolConditional recognizes `cond ? a | b`: two arms on the Bool literals,
// or one literal and a trailing wildcard.
func boolConditional(match *ast.MatchExpression) (whenTrue, whenFalse ast.Expression, ok bool) {
	if match.Scrutinee == nil || len(match.Arms) != 2 {
		return nil, nil, false
	}
	for i, arm := range match.Arms {
		switch pattern := arm.Pattern.(type) {
		case *ast.LiteralPattern:
			lit, isBool := pattern.Value.(*ast.Boolean)
			if !isBool {
				return nil, nil, false
			}
			if lit.Value {
				whenTrue = arm.Body
			} else {
				whenFalse = arm.Body
			}
		case *ast.WildcardPattern:
			if i != 1 {
				return nil, nil, false
			}
			if whenTrue == nil {
				whenTrue = arm.Body
			} else {
				whenFalse = arm.Body
			}
		default:
			return nil, nil, false
		}
	}
	return whenTrue, whenFalse, whenTrue != nil && whenFalse != nil
}

// mentionsCall reports a body with a call to a program function or assert
// (a conversion `u32(x)` is not a call).
func mentionsCall(body ast.Node) bool {
	found := false
	walk(body, func(n ast.Node) {
		if call, ok := n.(*ast.InvocationExpression); ok {
			if ident, ok := call.Function.(*ast.Identifier); ok {
				if isConversion(ident.Value) || ident.Value == "assert" {
					return
				}
			}
			found = true
		}
	})
	return found
}

// walk visits the nodes of the subset's shapes.
func walk(n ast.Node, visit func(ast.Node)) {
	if n == nil {
		return
	}
	visit(n)
	switch e := n.(type) {
	case *ast.BlockStatement:
		for _, s := range e.Statements {
			walk(s, visit)
		}
	case *ast.BlockExpression:
		if e.Block != nil {
			walk(e.Block, visit)
		}
	case *ast.ExpressionStatement:
		walk(e.Expression, visit)
	case *ast.VariableDeclaration:
		if e.Value != nil {
			walk(e.Value, visit)
		}
	case *ast.AssignmentStatement:
		walk(e.Value, visit)
	case *ast.WhileStatement:
		walk(e.Condition, visit)
		walk(e.Body, visit)
	case *ast.IfStatement:
		walk(e.Condition, visit)
		if e.Consequence != nil {
			walk(e.Consequence, visit)
		}
		if e.Alternative != nil {
			walk(e.Alternative, visit)
		}
	case *ast.InfixExpression:
		walk(e.Left, visit)
		walk(e.Right, visit)
	case *ast.PrefixExpression:
		walk(e.Right, visit)
	case *ast.InvocationExpression:
		for _, a := range e.Arguments {
			walk(a, visit)
		}
	case *ast.MatchExpression:
		walk(e.Scrutinee, visit)
		for _, arm := range e.Arms {
			walk(arm.Body, visit)
		}
	}
}

func statementLine(stmt ast.Statement) int {
	switch s := stmt.(type) {
	case *ast.VariableDeclaration:
		return s.Token.Line
	case *ast.AssignmentStatement:
		return s.Token.Line
	case *ast.WhileStatement:
		return s.Token.Line
	case *ast.IfStatement:
		return s.Token.Line
	case *ast.ExpressionStatement:
		return s.Token.Line
	case *ast.BreakStatement:
		return s.Token.Line
	}
	return 0
}

// Describe spells a lowered function as `.oakasm` text (diagnostics, tests).
func Describe(fn *asm.Function) string {
	var b strings.Builder
	fmt.Fprintf(&b, "%s = {\n", fn.Name)
	for _, bind := range fn.Bindings {
		fmt.Fprintf(&b, "  bind %s = %s\n", bind.Register.Text, bind.Param)
	}
	if len(fn.Clobbers) > 0 {
		names := make([]string, len(fn.Clobbers))
		for i, c := range fn.Clobbers {
			names[i] = c.Text
		}
		fmt.Fprintf(&b, "  clobber %s\n", strings.Join(names, ", "))
	}
	if fn.Frame > 0 {
		fmt.Fprintf(&b, "  frame %d\n", fn.Frame)
	}
	for _, item := range fn.Items {
		switch it := item.(type) {
		case asm.Label:
			fmt.Fprintf(&b, "%s:\n", it.Name)
		case asm.Instruction:
			fmt.Fprintf(&b, "  %s\n", it.String())
		}
	}
	b.WriteString("}\n")
	return b.String()
}
