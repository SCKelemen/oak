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

// span is a span ([*]T, writable) or view ([]T) parameter of fixed-width
// elements: it arrives as a {base, u32 len} register pair and stays in
// those registers (the checker keys its facts on the bound base register).
type span struct {
	elem     scalar
	writable bool
	baseReg  int // x register holding the base
	lenReg   int // w register holding the length
}

// spanOf reads a span or view type of the subset.
func spanOf(expr ast.Expression) (span, bool) {
	index, ok := expr.(*ast.IndexExpression)
	if !ok || index.Dot {
		return span{}, false
	}
	marker, isIdent := index.Index.(*ast.Identifier)
	if !isIdent || (marker.Value != "*" && marker.Value != "") {
		return span{}, false
	}
	elem, ok := scalarOf(index.Left)
	if !ok || elem.isBool {
		return span{}, false
	}
	return span{elem: elem, writable: marker.Value == "*"}, true
}

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

	items []asm.Item
	slots map[string]int64  // variable → frame offset (relative to the frame base after the prologue)
	types map[string]scalar // variable → type
	spans map[string]span   // span and view parameters, register-resident
	head  string            // the loop header a tail self-call jumps to
	// Variables live in the callee-saved registers x19–x28 in declaration
	// order (saved in the prologue, restored before ret), and in frame
	// slots once those run out; regs maps a variable to its register.
	regs       map[string]int
	usedCallee int
	saveArea   int64 // bytes reserved for the callee-saved pairs (fixed once any variable exists)
	scopes     []map[string]slotBinding
	nslots     int64
	spill      map[int]int64 // scratch register → its spill slot offset
	free       []int         // free scratch registers
	live       []int         // allocated scratch registers, allocation order
	labels     int
	loops      []string // break targets
	hasCalls   bool
	line       int
	trap       string // the trap block's label (division by zero, shift overflow, assert)
	usedTrap   bool
	// terminated: an unconditional jump was emitted and no label has
	// followed — instructions there are unreachable and are not emitted (the
	// checker refuses them).
	terminated bool
}

type slotBinding struct {
	offset int64
	typ    scalar
	reg    int // callee-saved register, or -1 for a slot
}

const scratchLow, scratchHigh = 9, 15
const calleeLow, calleeHigh = 19, 28

// Compile lowers one Oak function. functions maps every program function by
// name (callees' signatures); tc is the checker that typed the program.
func Compile(fn *ast.FunctionStatement, functions map[string]*ast.FunctionStatement, tc *typechecker.TypeChecker) (*asm.Function, error) {
	if fn.Body == nil || fn.ExternSymbol != "" || fn.Receiver != nil || len(fn.TypeParams) > 0 || fn.AsmBacked {
		return nil, unsupported("not an ordinary function body")
	}
	if len(fn.Parameters) > 8 {
		return nil, unsupported("more than eight parameters")
	}
	g := &generator{fn: fn, tc: tc, functions: functions, slots: map[string]int64{}, types: map[string]scalar{}, spans: map[string]span{}, regs: map[string]int{}, spill: map[int]int64{}, line: fn.Token.Line}
	if hasVariables(fn) {
		g.saveArea = 8 * (calleeHigh - calleeLow + 1)
	}
	for r := scratchHigh; r >= scratchLow; r-- {
		g.free = append(g.free, r)
	}
	// Parameters take AAPCS64's integer registers in order: a scalar one, a
	// span or view two (base, then the 32-bit length).
	nextReg := 0
	for _, p := range fn.Parameters {
		if p.Variadic {
			return nil, unsupported("variadic parameter %s", p.Name.Value)
		}
		if _, ok := scalarOf(p.Type); ok {
			nextReg++
			continue
		}
		if sp, ok := spanOf(p.Type); ok {
			sp.baseReg, sp.lenReg = nextReg, nextReg+1
			nextReg += 2
			g.spans[p.Name.Value] = sp
			continue
		}
		return nil, unsupported("parameter %s of type %s", p.Name.Value, p.Type.String())
	}
	if nextReg > 8 {
		return nil, unsupported("the parameters exhaust the eight argument registers")
	}
	if len(g.spans) > 0 && mentionsCall(fn.Body) {
		// A call would clobber the span's registers, and reloading the base
		// would drop the checker's span fact: span kernels are leaves.
		return nil, unsupported("a span parameter in a function that calls")
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
	// Scalar parameters occupy the first slots, in order.
	g.pushScope()
	for _, p := range fn.Parameters {
		if s, ok := scalarOf(p.Type); ok {
			g.declare(p.Name.Value, s)
		}
	}
	g.head = g.newLabel("head")
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
	// Save the callee-saved registers the variables occupy, in pairs.
	for i := 0; i < g.usedCallee; i += 2 {
		offset := g.saveBase() + int64(8*i)
		if i+1 < g.usedCallee {
			prologue = append(prologue, g.ins("stp", xr(calleeLow+i), xr(calleeLow+i+1), mem(offset)))
		} else {
			prologue = append(prologue, g.ins("str", xr(calleeLow+i), mem(offset)))
		}
	}
	// Bind and store the parameters (narrow ones normalized: the caller's
	// upper bits are unspecified under AAPCS64); a span's pair stays bound.
	regIndex := 0
	for _, p := range fn.Parameters {
		if sp, isSpan := g.spans[p.Name.Value]; isSpan {
			length := wr(sp.lenReg)
			out.Bindings = append(out.Bindings, asm.Binding{Register: xr(sp.baseReg), Length: &length, Param: p.Name.Value, Line: fn.Token.Line})
			regIndex += 2
			continue
		}
		s, _ := scalarOf(p.Type)
		i := regIndex
		regIndex++
		bound := wr(i)
		if s.wide() {
			bound = xr(i)
		}
		out.Bindings = append(out.Bindings, asm.Binding{Register: bound, Param: p.Name.Value, Line: fn.Token.Line})
		prologue = append(prologue, g.normalizeInto(i, s)...)
		prologue = append(prologue, g.storeVar(p.Name.Value, i))
	}
	// The loop header a tail self-call re-enters: after the parameters are
	// in their slots.
	prologue = append(prologue, asm.Label{Name: g.head, Line: fn.Token.Line})
	out.Items = append(prologue, body...)
	// Clobbers: the scratch registers, the argument registers a call
	// writes beyond the bound parameters, and the link register.
	for r := scratchLow; r <= scratchHigh; r++ {
		out.Clobbers = append(out.Clobbers, xr(r))
	}
	for i := 0; i < g.usedCallee; i++ {
		out.Clobbers = append(out.Clobbers, xr(calleeLow+i))
	}
	if g.hasCalls {
		for r := regIndex; r <= 7; r++ {
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
	return (g.saveBase() + g.saveArea + 8*g.nslots + 15) / 16 * 16
}

// saveBase is the frame offset of the callee-saved save area: past the
// [x29, x30] pair when the body calls.
func (g *generator) saveBase() int64 {
	if g.hasCalls {
		return 16
	}
	return 0
}

// hasVariables reports scalar parameters or local declarations: what the
// callee-saved registers are reserved for.
func hasVariables(fn *ast.FunctionStatement) bool {
	for _, p := range fn.Parameters {
		if _, ok := scalarOf(p.Type); ok {
			return true
		}
	}
	found := false
	walk(fn.Body, func(n ast.Node) {
		if _, ok := n.(*ast.VariableDeclaration); ok {
			found = true
		}
	})
	return found
}

// storeVar moves a value held in register r into a variable's home.
func (g *generator) storeVar(name string, r int) asm.Instruction {
	typ := g.types[name]
	if v, inReg := g.regs[name]; inReg && v >= 0 {
		return g.ins("mov", reg(v, typ), reg(r, typ))
	}
	return g.ins("str", reg(r, typ), g.slotMem(g.slots[name]))
}

// loadVar brings a variable's value into register r.
func (g *generator) loadVar(name string, r int) asm.Instruction {
	typ := g.types[name]
	if v, inReg := g.regs[name]; inReg && v >= 0 {
		return g.ins("mov", reg(r, typ), reg(v, typ))
	}
	return g.ins("ldr", reg(r, typ), g.slotMem(g.slots[name]))
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
		delete(g.regs, name)
		// A shadowed outer binding comes back into view.
		for i := len(g.scopes) - 1; i >= 0; i-- {
			if b, ok := g.scopes[i][name]; ok {
				g.slots[name], g.types[name], g.regs[name] = b.offset, b.typ, b.reg
				break
			}
		}
	}
}

// declare gives a variable a fresh slot in the current scope.
func (g *generator) declare(name string, s scalar) int64 {
	offset := int64(-1)
	r := -1
	if g.usedCallee < calleeHigh-calleeLow+1 {
		r = calleeLow + g.usedCallee
		g.usedCallee++
	} else {
		offset = 8 * g.nslots
		g.nslots++
	}
	g.slots[name], g.types[name], g.regs[name] = offset, s, r
	g.scopes[len(g.scopes)-1][name] = slotBinding{offset, s, r}
	return offset
}

// slotMem is the frame address of a slot: past the [x29, x30] pair and the
// callee-saved save area.
func (g *generator) slotMem(offset int64) asm.Memory {
	return mem(g.saveBase() + g.saveArea + offset)
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
	case *ast.IndexExpression:
		if e.Dot {
			return scalar{}, unsupported("a field access")
		}
		sp, err := g.spanOperand(e.Left)
		if err != nil {
			return scalar{}, err
		}
		return sp.elem, nil
	case *ast.InvocationExpression:
		ident, isIdent := e.Function.(*ast.Identifier)
		if !isIdent {
			return scalar{}, unsupported("a call through a value")
		}
		if ident.Value == "len" && len(e.Arguments) == 1 {
			if _, err := g.spanOperand(e.Arguments[0]); err != nil {
				return scalar{}, err
			}
			return scalars["u32"], nil
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
		if err := g.resultExpr(body); err != nil {
			return nil, err
		}
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
	for i := 0; i < g.usedCallee; i += 2 {
		offset := g.saveBase() + int64(8*i)
		if i+1 < g.usedCallee {
			g.emit("ldp", xr(calleeLow+i), xr(calleeLow+i+1), mem(offset))
		} else {
			g.emit("ldr", xr(calleeLow+i), mem(offset))
		}
	}
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
			g.declare(s.Name.Value, typ)
			g.items = append(g.items, g.storeVar(s.Name.Value, r))
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
			g.items = append(g.items, g.storeVar(s.Name.Value, r))
			g.release(r)
		case *ast.IndexAssignmentStatement:
			if err := g.elementStore(s); err != nil {
				return err
			}
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
				if err := g.resultExpr(s.Expression); err != nil {
					return err
				}
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
	return g.conditionBranch(expr, target, true)
}

var inverseCondition = map[string]string{"eq": "ne", "ne": "eq", "lo": "hs", "hs": "lo", "ls": "hi", "hi": "ls", "lt": "ge", "ge": "lt", "le": "gt", "gt": "le"}

// conditionBranch evaluates a Bool expression and branches to target when
// it is false (jumpIfFalse) or true. A comparison of simple operands —
// variables in registers, a span length, a small constant — emits directly
// as `cmp` then `b.cond`, the shape the checker's guards and the
// verifier's loop recognizer read.
func (g *generator) conditionBranch(expr ast.Expression, target string, jumpIfFalse bool) error {
	if infix, ok := expr.(*ast.InfixExpression); ok {
		if codes, isComparison := conditionCodes[infix.Operator]; isComparison {
			if operand, err := g.operandType(infix); err == nil {
				left, leftOK := g.simpleOperand(infix.Left, operand, false)
				right, rightOK := g.simpleOperand(infix.Right, operand, true)
				if leftOK && rightOK {
					code := codes[0]
					if operand.signed {
						code = codes[1]
					}
					if jumpIfFalse {
						code = inverseCondition[code]
					}
					g.emit("cmp", left, right)
					g.branch(code, target)
					return nil
				}
			}
		}
	}
	b := scalars["Bool"]
	r, err := g.expr(expr, &b)
	if err != nil {
		return err
	}
	if jumpIfFalse {
		g.emit("cbz", wr(r), asm.Symbol{Name: target})
	} else {
		g.emit("cbnz", wr(r), asm.Symbol{Name: target})
	}
	g.release(r)
	return nil
}

// simpleOperand spells an operand `cmp` takes directly: a variable in its
// register, a span's length register, or (on the right) a constant below
// 4096, possibly under a widening constructor.
func (g *generator) simpleOperand(expr ast.Expression, typ scalar, allowImm bool) (asm.Operand, bool) {
	switch e := expr.(type) {
	case *ast.Identifier:
		if v, inReg := g.regs[e.Value]; inReg && v >= 0 {
			if t, ok := g.types[e.Value]; ok && t.wide() == typ.wide() {
				return reg(v, typ), true
			}
		}
	case *ast.InvocationExpression:
		if ident, ok := e.Function.(*ast.Identifier); ok && len(e.Arguments) == 1 {
			if ident.Value == "len" && !typ.wide() {
				if sp, err := g.spanOperand(e.Arguments[0]); err == nil {
					return wr(sp.lenReg), true
				}
			}
			if _, isConv := scalars[ident.Value]; isConv && allowImm {
				if v, ok := constantValue(e.Arguments[0]); ok && v >= 0 && v < 4096 {
					return imm(v), true
				}
			}
		}
	case *ast.IntegerLiteral:
		if allowImm && e.Value >= 0 && e.Value < 4096 {
			return imm(e.Value), true
		}
	}
	return nil, false
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
		g.items = append(g.items, g.loadVar(e.Value, r))
		return r, nil
	case *ast.InfixExpression:
		return g.infix(e, typ)
	case *ast.PrefixExpression:
		return g.prefix(e, typ)
	case *ast.IndexExpression:
		return g.element(e)
	case *ast.InvocationExpression:
		ident := e.Function.(*ast.Identifier)
		if ident.Value == "len" && len(e.Arguments) == 1 {
			sp, err := g.spanOperand(e.Arguments[0])
			if err != nil {
				return 0, err
			}
			r, err := g.alloc()
			if err != nil {
				return 0, err
			}
			g.emit("mov", wr(r), wr(sp.lenReg))
			return r, nil
		}
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
				if isConversion(ident.Value) || ident.Value == "assert" || ident.Value == "len" {
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
	case *ast.IndexAssignmentStatement:
		walk(e.Target, visit)
		walk(e.Value, visit)
	case *ast.IndexExpression:
		walk(e.Left, visit)
		walk(e.Index, visit)
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
	case *ast.IndexAssignmentStatement:
		return s.Token.Line
	}
	return 0
}

// ---- spans ------------------------------------------------------------------------

// spanOperand resolves the span or view a `len(v)` / `v[i]` names.
func (g *generator) spanOperand(expr ast.Expression) (span, error) {
	ident, isIdent := expr.(*ast.Identifier)
	if !isIdent {
		return span{}, unsupported("an index into %s (not a span parameter)", expr.String())
	}
	sp, ok := g.spans[ident.Value]
	if !ok {
		return span{}, unsupported("an index into %s (not a span parameter)", ident.Value)
	}
	return sp, nil
}

// guardedIndex evaluates an element index into a 32-bit scratch register
// and emits the checker's guard: `cmp wI, wL; b.hs <trap>` right before the
// access, so an index at or past the length traps and the fall-through
// path carries the fact that wI < len.
func (g *generator) guardedIndex(sp span, index ast.Expression) (int, error) {
	idxType, err := g.typeOf(index, nil)
	if err != nil {
		return 0, err
	}
	if idxType.wide() || idxType.signed || idxType.isBool {
		return 0, unsupported("an element index of type %s (the span idiom walks by a u32 index)", idxType.name)
	}
	r, err := g.expr(index, &idxType)
	if err != nil {
		return 0, err
	}
	g.usedTrap = true
	g.emit("cmp", wr(r), wr(sp.lenReg))
	g.branch("hs", g.trap)
	return r, nil
}

func log2Bytes(bytes int) int {
	n := 0
	for 1<<uint(n) < bytes {
		n++
	}
	return n
}

// element lowers `v[i]`: a guarded, whole-element load through the bound
// base, zero- or sign-extending as the element type reads in C.
func (g *generator) element(e *ast.IndexExpression) (int, error) {
	sp, err := g.spanOperand(e.Left)
	if err != nil {
		return 0, err
	}
	r, err := g.guardedIndex(sp, e.Index)
	if err != nil {
		return 0, err
	}
	index := wr(r)
	address := asm.Memory{Base: xr(sp.baseReg), Index: &index, Shift: log2Bytes(sp.elem.bits / 8), Extend: "uxtw"}
	var load string
	switch {
	case sp.elem.bits >= 32:
		load = "ldr"
	case sp.elem.bits == 16 && sp.elem.signed:
		load = "ldrsh"
	case sp.elem.bits == 16:
		load = "ldrh"
	case sp.elem.signed:
		load = "ldrsb"
	default:
		load = "ldrb"
	}
	// The element lands in the index register: the index is spent.
	g.emit(load, reg(r, sp.elem), address)
	return r, nil
}

// elementStore lowers `v[i] = e` through a writable span.
func (g *generator) elementStore(s *ast.IndexAssignmentStatement) error {
	if s.Target.Dot {
		return unsupported("a field store")
	}
	sp, err := g.spanOperand(s.Target.Left)
	if err != nil {
		return err
	}
	if !sp.writable {
		return unsupported("a store through the view %s", s.Target.Left.String())
	}
	value, err := g.expr(s.Value, &sp.elem)
	if err != nil {
		return err
	}
	r, err := g.guardedIndex(sp, s.Target.Index)
	if err != nil {
		return err
	}
	index := wr(r)
	address := asm.Memory{Base: xr(sp.baseReg), Index: &index, Shift: log2Bytes(sp.elem.bits / 8), Extend: "uxtw"}
	store := "str"
	switch sp.elem.bits {
	case 16:
		store = "strh"
	case 8:
		store = "strb"
	}
	g.emit(store, reg(value, sp.elem), address)
	g.release(r)
	g.release(value)
	return nil
}

// ---- results and tail calls ----------------------------------------------------

// resultExpr places an expression in result position: a tail self-call
// becomes the next iteration (the arguments into the parameter slots, then
// a jump to the header); a Bool conditional keeps its arms in result
// position; anything else evaluates into the result register.
func (g *generator) resultExpr(expr ast.Expression) error {
	switch e := expr.(type) {
	case *ast.InvocationExpression:
		if ident, ok := e.Function.(*ast.Identifier); ok && ident.Value == g.fn.Name.Value && len(g.spans) == 0 {
			return g.tailCall(e)
		}
	case *ast.MatchExpression:
		if whenTrue, whenFalse, ok := boolConditional(e); ok {
			// With one arm a tail self-call, the loop shape the verifier
			// recognizes: the exit branch leaves for the value arm, the tail
			// arm falls through to the back edge.
			if g.isTailCall(whenFalse) != g.isTailCall(whenTrue) {
				tail, value, jumpIfFalse := whenTrue, whenFalse, true
				if g.isTailCall(whenFalse) {
					tail, value, jumpIfFalse = whenFalse, whenTrue, false
				}
				exit := g.newLabel("exit")
				if err := g.conditionBranch(e.Scrutinee, exit, jumpIfFalse); err != nil {
					return err
				}
				if err := g.resultExpr(tail); err != nil {
					return err
				}
				g.label(exit)
				return g.resultExpr(value)
			}
			elseLabel, end := g.newLabel("else"), g.newLabel("endif")
			if err := g.condition(e.Scrutinee, elseLabel); err != nil {
				return err
			}
			if err := g.resultExpr(whenTrue); err != nil {
				return err
			}
			g.emit("b", asm.Symbol{Name: end})
			g.label(elseLabel)
			if err := g.resultExpr(whenFalse); err != nil {
				return err
			}
			g.label(end)
			return nil
		}
	case *ast.BlockExpression:
		if e.Block != nil && len(e.Block.Statements) > 0 {
			g.pushScope()
			defer g.popScope()
			stmts := e.Block.Statements
			if err := g.lowerStatements(stmts[:len(stmts)-1], false, ""); err != nil {
				return err
			}
			if es, ok := stmts[len(stmts)-1].(*ast.ExpressionStatement); ok && !es.Discard {
				return g.resultExpr(es.Expression)
			}
		}
	}
	r, err := g.expr(expr, g.result)
	if err != nil {
		return err
	}
	g.moveResult(r, *g.result)
	g.release(r)
	return nil
}

// tailCall lowers a self-call in result position as a loop: every argument
// is evaluated before any parameter slot changes.
func (g *generator) tailCall(e *ast.InvocationExpression) error {
	if len(e.Arguments) != len(g.fn.Parameters) {
		return unsupported("a self-call with %d arguments", len(e.Arguments))
	}
	var values []int
	for i, arg := range e.Arguments {
		typ, _ := scalarOf(g.fn.Parameters[i].Type)
		r, err := g.expr(arg, &typ)
		if err != nil {
			return err
		}
		values = append(values, r)
	}
	for i, r := range values {
		g.items = append(g.items, g.storeVar(g.fn.Parameters[i].Name.Value, r))
		g.release(r)
	}
	g.emit("b", asm.Symbol{Name: g.head})
	return nil
}

// isTailCall recognizes a self-call the loop lowering handles.
func (g *generator) isTailCall(expr ast.Expression) bool {
	call, ok := expr.(*ast.InvocationExpression)
	if !ok || len(g.spans) != 0 {
		return false
	}
	ident, ok := call.Function.(*ast.Identifier)
	return ok && ident.Value == g.fn.Name.Value
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
