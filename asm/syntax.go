package asm

import (
	"fmt"
	"sort"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// The syntax table: a theorem and the functions it calls, serialized for
// the lowering written in Oak (prove/solver/lower.oak), which turns it
// into the decider's terms the way asm/verify.go does. The scalar subset:
// fixed-width integer and Bool parameters, locals, and results; integer
// and Bool literals; the prefix operators ! ^ -; the infix arithmetic,
// bitwise, shift, comparison, and Boolean operators, with / and % by an
// unsigned constant power of two; the primitive constructors and the
// trunc/bits conversions; the scalar instruction functions; conditionals
// in value and statement position; typed locals and assignments; counted
// while loops; calls to program functions, inlined. Everything else —
// records, arrays, spans, floats, refinements, asserts, matches over sum
// types, recursion — keeps the theorem with the Go lowering.
//
// Words: a header (functions, nodes, list words, largest symbol count,
// theorem function, leaves), the function table (8 words each: parameter
// start, parameter count, result width, result signedness, body node,
// symbol count), the parameter table (4 words each: width, signedness,
// leaf index for the theorem's parameters), the nodes (8 words each:
// kind, a, b, c, d, value low, value high), and the lists (node ids).

const (
	synIntLit   = 0  // vlo, vhi
	synBoolLit  = 1  // a = 1 or 0
	synSym      = 2  // a = symbol
	synPrefix   = 3  // a = op (0 !, 1 ^, 2 -), b = operand
	synInfix    = 4  // a = op, b = left, c = right
	synCond     = 5  // a = condition, b = then, c = else (value position)
	synCall     = 6  // a = function, b = list start, c = argument count
	synConv     = 7  // a = target width, b = target signedness, c = operand
	synBlock    = 8  // a = list start, b = statement count
	synVarDecl  = 9  // a = symbol, b = width, c = signedness, d = initializer
	synAssign   = 10 // a = symbol, b = value
	synWhile    = 11 // a = condition, b = body block
	synInstr    = 12 // a = operator code, b = member width, c = operand
	synCondStmt = 13 // a = condition, b = then block, c = else block
)

var synInfixOps = map[string]uint32{
	"+": 0, "-": 1, "*": 2, "&": 3, "|": 4, "^": 5, "<<": 6, ">>": 7, "/": 8, "%": 9,
	"==": 10, "!=": 11, "<": 12, "<=": 13, ">": 14, ">=": 15, "&&": 16, "||": 17,
}

var synInstrOps = map[string]uint32{"rev": 10, "rev16": 11, "rev32": 12, "rbit": 13, "clz": 14, "cnt": 15, "cls": 16}

type synFunction struct {
	sig     *ast.FunctionStatement
	index   int
	symbols map[string]int
	params  []synParam
	body    uint32
}

type synParam struct {
	width  int
	signed bool
	leaf   int // -1 for a callee's parameter
}

type syntaxWriter struct {
	functions map[string]*ast.FunctionStatement
	order     []*synFunction
	byName    map[string]*synFunction
	nodes     []uint32
	lists     []uint32
	maxSyms   int
}

// ExportSyntax serializes the theorem and its callees for the Oak
// lowering, or says which construct keeps it with the Go lowering.
func ExportSyntax(sig *ast.FunctionStatement, functions map[string]*ast.FunctionStatement) ([]uint32, string, bool) {
	if sig == nil || sig.Name == nil || sig.Body == nil {
		return nil, "no body", false
	}
	w := &syntaxWriter{functions: functions, byName: map[string]*synFunction{}}
	theorem, reason, ok := w.function(sig, true)
	if !ok {
		return nil, reason, false
	}
	// Functions in call order, the theorem first.
	words := make([]uint32, 0, 8+len(w.order)*8+64+len(w.nodes)+len(w.lists))
	var params []uint32
	funcs := make([]uint32, 0, len(w.order)*8)
	for _, f := range w.order {
		funcs = append(funcs, uint32(len(params)/4), uint32(len(f.params)), 0, 0, f.body, uint32(len(f.symbols)), 0, 0)
		width, signed, _ := scalarBits(f.sig.ReturnType)
		funcs[len(funcs)-6] = uint32(width)
		if signed {
			funcs[len(funcs)-5] = 1
		}
		for _, p := range f.params {
			leaf := problemNone
			if p.leaf >= 0 {
				leaf = uint32(p.leaf)
			}
			signedWord := uint32(0)
			if p.signed {
				signedWord = 1
			}
			params = append(params, uint32(p.width), signedWord, leaf, 0)
		}
	}
	words = append(words, uint32(len(w.order)), uint32(len(w.nodes)/8), uint32(len(w.lists)), uint32(w.maxSyms), uint32(theorem.index), uint32(len(theorem.params)), 0, 0)
	words = append(words, funcs...)
	words = append(words, params...)
	words = append(words, w.nodes...)
	words = append(words, w.lists...)
	return words, "", true
}

// scalarBits is contractBits without the floats (their arithmetic is not
// in the Oak lowering's subset).
func scalarBits(typ ast.Expression) (int, bool, bool) {
	switch typeText(typ) {
	case "f32", "f64", "f16", "bf16":
		return 0, false, false
	}
	return contractBits(typ)
}

func (w *syntaxWriter) function(sig *ast.FunctionStatement, theorem bool) (*synFunction, string, bool) {
	name := sig.Name.Value
	if f, seen := w.byName[name]; seen {
		if f.body == problemNone {
			return nil, fmt.Sprintf("a recursive call to %s", name), false
		}
		return f, "", true
	}
	if sig.Receiver != nil || len(sig.TypeParams) != 0 || sig.Body == nil || sig.ExternSymbol != "" {
		return nil, fmt.Sprintf("a call to %s (a method, generic, foreign, or definition-less function)", name), false
	}
	if _, _, ok := scalarBits(sig.ReturnType); !ok && !theorem {
		return nil, fmt.Sprintf("a call to %s returning %s", name, typeText(sig.ReturnType)), false
	}
	f := &synFunction{sig: sig, index: len(w.order), symbols: map[string]int{}, body: problemNone}
	w.order = append(w.order, f)
	w.byName[name] = f
	names := make([]string, 0, len(sig.Parameters))
	for _, param := range sig.Parameters {
		if param.Variadic {
			return nil, fmt.Sprintf("parameter %s is variadic", param.Name.Value), false
		}
		width, signed, ok := scalarBits(param.Type)
		if !ok {
			return nil, fmt.Sprintf("parameter %s: %s is not a fixed-width integer or Bool", param.Name.Value, typeText(param.Type)), false
		}
		f.symbols[param.Name.Value] = len(f.params)
		f.params = append(f.params, synParam{width: width, signed: signed, leaf: -1})
		names = append(names, param.Name.Value)
	}
	if theorem {
		// The leaves are the parameters in name order (the decider's
		// interleaved variable order sorts the parameter names).
		sorted := append([]string{}, names...)
		sort.Strings(sorted)
		for leaf, pname := range sorted {
			f.params[f.symbols[pname]].leaf = leaf
		}
	}
	body, reason, ok := w.expr(f, sig.Body)
	if !ok {
		if theorem {
			return nil, reason, false
		}
		return nil, fmt.Sprintf("a call to %s whose body contains %s", name, reason), false
	}
	f.body = body
	if len(f.symbols) > w.maxSyms {
		w.maxSyms = len(f.symbols)
	}
	return f, "", true
}

func (w *syntaxWriter) node(kind, a, b, c, d, vlo, vhi uint32) uint32 {
	id := uint32(len(w.nodes) / 8)
	w.nodes = append(w.nodes, kind, a, b, c, d, vlo, vhi, 0)
	return id
}

func (w *syntaxWriter) list(ids []uint32) uint32 {
	start := uint32(len(w.lists))
	w.lists = append(w.lists, ids...)
	return start
}

// expr serializes an expression, failing closed outside the subset.
func (w *syntaxWriter) expr(f *synFunction, e ast.Expression) (uint32, string, bool) {
	switch e := e.(type) {
	case *ast.IntegerLiteral:
		v := uint64(e.Value)
		return w.node(synIntLit, 0, 0, 0, 0, uint32(v), uint32(v>>32)), "", true
	case *ast.Boolean:
		bit := uint32(0)
		if e.Value {
			bit = 1
		}
		return w.node(synBoolLit, bit, 0, 0, 0, 0, 0), "", true
	case *ast.Identifier:
		sym, known := f.symbols[e.Value]
		if !known {
			return 0, fmt.Sprintf("identifier %s (not a parameter or local)", e.Value), false
		}
		return w.node(synSym, uint32(sym), 0, 0, 0, 0, 0), "", true
	case *ast.PrefixExpression:
		op := map[string]uint32{"!": 0, "^": 1, "-": 2}
		code, known := op[e.Operator]
		if !known {
			return 0, fmt.Sprintf("prefix operator %s", e.Operator), false
		}
		operand, reason, ok := w.expr(f, e.Right)
		if !ok {
			return 0, reason, false
		}
		return w.node(synPrefix, code, operand, 0, 0, 0, 0), "", true
	case *ast.InfixExpression:
		code, known := synInfixOps[e.Operator]
		if !known {
			return 0, fmt.Sprintf("operator %s", e.Operator), false
		}
		left, reason, ok := w.expr(f, e.Left)
		if !ok {
			return 0, reason, false
		}
		right, reason, ok := w.expr(f, e.Right)
		if !ok {
			return 0, reason, false
		}
		return w.node(synInfix, code, left, right, 0, 0, 0), "", true
	case *ast.BlockExpression:
		return w.block(f, e.Block, true)
	case *ast.MatchExpression:
		whenTrue, whenFalse, isBool := boolConditional(e)
		if !isBool {
			return 0, "a match that is not a Bool conditional", false
		}
		cond, reason, ok := w.expr(f, e.Scrutinee)
		if !ok {
			return 0, reason, false
		}
		then, reason, ok := w.expr(f, whenTrue)
		if !ok {
			return 0, reason, false
		}
		otherwise, reason, ok := w.expr(f, whenFalse)
		if !ok {
			return 0, reason, false
		}
		return w.node(synCond, cond, then, otherwise, 0, 0, 0), "", true
	case *ast.InvocationExpression:
		if member, width, isInstruction := instructionFunction(e); isInstruction {
			code, known := synInstrOps[member]
			if !known || len(e.Arguments) != 1 {
				return 0, fmt.Sprintf("the instruction function %s", member), false
			}
			operand, reason, ok := w.expr(f, e.Arguments[0])
			if !ok {
				return 0, reason, false
			}
			return w.node(synInstr, code, uint32(width), operand, 0, 0, 0), "", true
		}
		ident, isIdent := e.Function.(*ast.Identifier)
		if !isIdent {
			return 0, "a call through a value", false
		}
		if callee, known := w.functions[ident.Value]; known {
			cf, reason, ok := w.function(callee, false)
			if !ok {
				return 0, reason, false
			}
			if len(e.Arguments) != len(cf.params) {
				return 0, fmt.Sprintf("a call to %s with %d arguments", ident.Value, len(e.Arguments)), false
			}
			var args []uint32
			for _, arg := range e.Arguments {
				id, reason, ok := w.expr(f, arg)
				if !ok {
					return 0, reason, false
				}
				args = append(args, id)
			}
			return w.node(synCall, uint32(cf.index), w.list(args), uint32(len(args)), 0, 0, 0), "", true
		}
		if len(e.Arguments) != 1 {
			return 0, fmt.Sprintf("call to %s", ident.Value), false
		}
		target := ""
		switch ident.Value {
		case "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64":
			target = ident.Value
		default:
			if t, op, _, isConv := typechecker.ConversionParts(ident.Value); isConv && (op == "trunc" || op == "bits") {
				target = t
			}
		}
		if target == "" {
			return 0, fmt.Sprintf("call to %s", ident.Value), false
		}
		width, signed, _ := contractBits(&ast.Identifier{Value: target})
		operand, reason, ok := w.expr(f, e.Arguments[0])
		if !ok {
			return 0, reason, false
		}
		signedWord := uint32(0)
		if signed {
			signedWord = 1
		}
		return w.node(synConv, uint32(width), signedWord, operand, 0, 0, 0), "", true
	}
	return 0, fmt.Sprintf("%T", e), false
}

// block serializes a block: statements, the last an expression (the
// result) in value position; in statement position (a loop body, a
// conditional's arm) every statement is a statement, a conditional among
// them a statement conditional.
func (w *syntaxWriter) block(f *synFunction, block *ast.BlockStatement, value bool) (uint32, string, bool) {
	if block == nil {
		return w.node(synBlock, 0, 0, 0, 0, 0, 0), "", true
	}
	var ids []uint32
	for i, stmt := range block.Statements {
		last := i == len(block.Statements)-1
		switch s := stmt.(type) {
		case *ast.ExpressionStatement:
			if match, isMatch := s.Expression.(*ast.MatchExpression); isMatch && (!last || !value) {
				id, reason, ok := w.condStmt(f, match)
				if !ok {
					return 0, reason, false
				}
				ids = append(ids, id)
				continue
			}
			if !last || !value {
				return 0, "an expression statement before the end of a block", false
			}
			id, reason, ok := w.expr(f, s.Expression)
			if !ok {
				return 0, reason, false
			}
			ids = append(ids, id)
		case *ast.VariableDeclaration:
			if s.Type == nil || s.Value == nil {
				return 0, "a local without both a type and an initializer", false
			}
			width, signed, ok := scalarBits(s.Type)
			if !ok {
				return 0, fmt.Sprintf("a local of type %s", typeText(s.Type)), false
			}
			init, reason, ok := w.expr(f, s.Value)
			if !ok {
				return 0, reason, false
			}
			sym, seen := f.symbols[s.Name.Value]
			if !seen {
				sym = len(f.symbols)
				f.symbols[s.Name.Value] = sym
			}
			signedWord := uint32(0)
			if signed {
				signedWord = 1
			}
			ids = append(ids, w.node(synVarDecl, uint32(sym), uint32(width), signedWord, init, 0, 0))
		case *ast.AssignmentStatement:
			sym, known := f.symbols[s.Name.Value]
			if !known {
				return 0, fmt.Sprintf("an assignment to %s (not a local)", s.Name.Value), false
			}
			value, reason, ok := w.expr(f, s.Value)
			if !ok {
				return 0, reason, false
			}
			ids = append(ids, w.node(synAssign, uint32(sym), value, 0, 0, 0, 0))
		case *ast.WhileStatement:
			cond, reason, ok := w.expr(f, s.Condition)
			if !ok {
				return 0, reason, false
			}
			body, reason, ok := w.block(f, s.Body, false)
			if !ok {
				return 0, reason, false
			}
			ids = append(ids, w.node(synWhile, cond, body, 0, 0, 0, 0))
		default:
			return 0, fmt.Sprintf("%T", stmt), false
		}
	}
	return w.node(synBlock, w.list(ids), uint32(len(ids)), 0, 0, 0, 0), "", true
}

// condStmt serializes `c ? { ... } | { ... }` in statement position: the
// arms are blocks of statements.
func (w *syntaxWriter) condStmt(f *synFunction, match *ast.MatchExpression) (uint32, string, bool) {
	whenTrue, whenFalse, isBool := boolConditional(match)
	if !isBool {
		return 0, "a match statement that is not a Bool conditional", false
	}
	cond, reason, ok := w.expr(f, match.Scrutinee)
	if !ok {
		return 0, reason, false
	}
	arm := func(e ast.Expression) (uint32, string, bool) {
		block, isBlock := e.(*ast.BlockExpression)
		if !isBlock {
			return 0, "a conditional arm in statement position that is not a block", false
		}
		return w.block(f, block.Block, false)
	}
	then, reason, ok := arm(whenTrue)
	if !ok {
		return 0, reason, false
	}
	otherwise, reason, ok := arm(whenFalse)
	if !ok {
		return 0, reason, false
	}
	return w.node(synCondStmt, cond, then, otherwise, 0, 0, 0), "", true
}
