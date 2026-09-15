package nativegen

import (
	"sync"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
)

// Verified reduction unrolling (docs/spec/94-assembler.md §9 "Reductions";
// spec/lean/Oak/Reduction.lean). An integer reduction over a span,
//
//	while i < len(v) {
//	  acc = acc + v[i]
//	  i = i + u32(1)
//	}
//
// is rewritten, before lowering, into a four-accumulator main loop under
// the slack guard the vector kernels spell, the remainder loop as written,
// and the combine:
//
//	acc_u1: T = 0    acc_u2: T = 0    acc_u3: T = 0
//	while len(v) >= u32(4) && i <= len(v) - u32(4) {
//	  acc = acc + v[i]              acc_u1 = acc_u1 + v[i + u32(1)]
//	  acc_u2 = acc_u2 + v[i + u32(2)]   acc_u3 = acc_u3 + v[i + u32(3)]
//	  i = i + u32(4)
//	}
//	while i < len(v) { acc = acc + v[i]; i = i + u32(1) }
//	acc = (acc + acc_u1) + (acc_u2 + acc_u3)
//
// The lowering sees the rewritten body — four independent adds per four
// loads, the loop-carried chain a quarter as long — and the verifier
// proves the assembly against the rewritten body (asm.Function.Body), two
// loops coupled inductively as it proves the tiled kernels. The rewrite
// itself is the theorem: integer addition wraps, so it is associative and
// commutative at every width, and the strided four-way fold of the
// elements equals the sequential fold (Oak.Reduction.unrolled4_eq); a
// float accumulator is never rewritten (its addition does not
// reassociate), nor a loop with any other statement, an index of another
// stride, or an accumulator read elsewhere in the body of the loop. The
// index ends at len(v) on both sides, so a use after the loop reads the
// same value.

// reductionLoop is a recognized `while i < len(v) { acc = acc + v[i]; i = i + 1 }`.
type reductionLoop struct {
	loop     *ast.WhileStatement
	acc, idx string
	span     string
	accType  ast.Expression // the accumulator's declared type
}

// unrollReductions returns the body with its plain integer reductions
// unrolled four ways, and whether any was.
func unrollReductions(fn *ast.FunctionStatement, body ast.Expression) (ast.Expression, bool) {
	block, isBlock := body.(*ast.BlockExpression)
	if !isBlock || block.Block == nil {
		return body, false
	}
	types := declaredScalarTypes(block.Block.Statements)
	changed := false
	var rewrite func(stmts []ast.Statement) []ast.Statement
	rewrite = func(stmts []ast.Statement) []ast.Statement {
		var out []ast.Statement
		for _, stmt := range stmts {
			switch s := stmt.(type) {
			case *ast.WhileStatement:
				if red, ok := recognizeReduction(s, types, body); ok {
					out = append(out, unrolledReduction(red)...)
					changed = true
					continue
				}
				if s.Body != nil {
					s.Body.Statements = rewrite(s.Body.Statements)
				}
			case *ast.ExpressionStatement:
				if inner, isBlock := s.Expression.(*ast.BlockExpression); isBlock && inner.Block != nil {
					inner.Block.Statements = rewrite(inner.Block.Statements)
				}
				if match, isMatch := s.Expression.(*ast.MatchExpression); isMatch {
					for _, arm := range match.Arms {
						if armBlock, isBlock := arm.Body.(*ast.BlockExpression); isBlock && armBlock.Block != nil {
							armBlock.Block.Statements = rewrite(armBlock.Block.Statements)
						}
					}
				}
			case *ast.BlockStatement:
				s.Statements = rewrite(s.Statements)
			}
			out = append(out, stmt)
		}
		return out
	}
	// Rewrite a copy: the source body stays the typechecker's.
	clone := cloneNode(body).(*ast.BlockExpression)
	clone.Block.Statements = rewrite(clone.Block.Statements)
	if !changed {
		return body, false
	}
	return clone, true
}

// declaredScalarTypes maps every local declared with an explicit scalar
// type anywhere in the statements to its type expression.
func declaredScalarTypes(stmts []ast.Statement) map[string]ast.Expression {
	types := map[string]ast.Expression{}
	var visit func(stmts []ast.Statement)
	visit = func(stmts []ast.Statement) {
		for _, stmt := range stmts {
			switch s := stmt.(type) {
			case *ast.VariableDeclaration:
				if s.Type != nil && s.Name != nil {
					if _, isScalar := scalarOf(s.Type); isScalar {
						types[s.Name.Value] = s.Type
					}
				}
			case *ast.WhileStatement:
				if s.Body != nil {
					visit(s.Body.Statements)
				}
			case *ast.BlockStatement:
				visit(s.Statements)
			case *ast.ExpressionStatement:
				if inner, isBlock := s.Expression.(*ast.BlockExpression); isBlock && inner.Block != nil {
					visit(inner.Block.Statements)
				}
				if match, isMatch := s.Expression.(*ast.MatchExpression); isMatch {
					for _, arm := range match.Arms {
						if armBlock, isBlock := arm.Body.(*ast.BlockExpression); isBlock && armBlock.Block != nil {
							visit(armBlock.Block.Statements)
						}
					}
				}
			}
		}
	}
	visit(stmts)
	return types
}

// recognizeReduction reads a while statement as a plain integer reduction.
func recognizeReduction(loop *ast.WhileStatement, types map[string]ast.Expression, body ast.Expression) (reductionLoop, bool) {
	cond, isInfix := loop.Condition.(*ast.InfixExpression)
	if !isInfix || cond.Operator != "<" || loop.Body == nil || len(loop.Body.Statements) != 2 {
		return reductionLoop{}, false
	}
	idx, isIdent := cond.Left.(*ast.Identifier)
	if !isIdent {
		return reductionLoop{}, false
	}
	span, isLen := lenOf(cond.Right)
	if !isLen {
		return reductionLoop{}, false
	}
	accum, isAssign := loop.Body.Statements[0].(*ast.AssignmentStatement)
	step, isStep := loop.Body.Statements[1].(*ast.AssignmentStatement)
	if !isAssign || !isStep || accum.Name == nil || step.Name == nil {
		return reductionLoop{}, false
	}
	acc := accum.Name.Value
	if acc == idx.Value || acc == span || idx.Value == span || step.Name.Value != idx.Value {
		return reductionLoop{}, false
	}
	// acc = acc + v[i] (either order).
	sum, isSum := accum.Value.(*ast.InfixExpression)
	if !isSum || sum.Operator != "+" {
		return reductionLoop{}, false
	}
	if !(isName(sum.Left, acc) && isElement(sum.Right, span, idx.Value)) && !(isName(sum.Right, acc) && isElement(sum.Left, span, idx.Value)) {
		return reductionLoop{}, false
	}
	// i = i + 1.
	inc, isInc := step.Value.(*ast.InfixExpression)
	if !isInc || inc.Operator != "+" || !isName(inc.Left, idx.Value) {
		return reductionLoop{}, false
	}
	if one, isConst := constantValue(inc.Right); !isConst || one != 1 {
		return reductionLoop{}, false
	}
	// The accumulator: an integer local with a declared type; the index a u32.
	accType, declared := types[acc]
	if !declared {
		return reductionLoop{}, false
	}
	typ, isScalar := scalarOf(accType)
	if !isScalar || typ.isFloat || typ.isBool || typ.isVec {
		return reductionLoop{}, false
	}
	if idxType, declared := types[idx.Value]; !declared || idxType.String() != "u32" {
		return reductionLoop{}, false
	}
	// Fresh names, and not a loop this rewrite made (its remainder loop has
	// this shape).
	for k := 1; k <= 3; k++ {
		if mentionsName(body, unrolledName(acc, k)) {
			return reductionLoop{}, false
		}
	}
	return reductionLoop{loop: loop, acc: acc, idx: idx.Value, span: span, accType: accType}, true
}

func unrolledName(acc string, k int) string { return acc + "_u" + string(rune('0'+k)) }

func lenOf(e ast.Expression) (string, bool) {
	call, isCall := e.(*ast.InvocationExpression)
	if !isCall || len(call.Arguments) != 1 {
		return "", false
	}
	fn, isIdent := call.Function.(*ast.Identifier)
	arg, argIdent := call.Arguments[0].(*ast.Identifier)
	if !isIdent || fn.Value != "len" || !argIdent {
		return "", false
	}
	return arg.Value, true
}

func isName(e ast.Expression, name string) bool {
	ident, isIdent := e.(*ast.Identifier)
	return isIdent && ident.Value == name
}

func isElement(e ast.Expression, span, idx string) bool {
	index, isIndex := e.(*ast.IndexExpression)
	return isIndex && !index.Dot && isName(index.Left, span) && isName(index.Index, idx)
}

// unrolledReduction builds the rewritten statements.
func unrolledReduction(red reductionLoop) []ast.Statement {
	tok := red.loop.Token
	ident := func(name string) *ast.Identifier { return &ast.Identifier{Token: tok, Value: name} }
	literal := func(v int64) ast.Expression { return &ast.IntegerLiteral{Token: tok, Value: v} }
	u32 := func(v int64) ast.Expression {
		return &ast.InvocationExpression{Token: tok, Function: ident("u32"), Arguments: []ast.Expression{literal(v)}}
	}
	infix := func(l ast.Expression, op string, r ast.Expression) ast.Expression {
		return &ast.InfixExpression{Token: token.Token{Line: tok.Line, Literal: op}, Left: l, Operator: op, Right: r}
	}
	length := func() ast.Expression {
		return &ast.InvocationExpression{Token: tok, Function: ident("len"), Arguments: []ast.Expression{ident(red.span)}}
	}
	element := func(offset int64) ast.Expression {
		var index ast.Expression = ident(red.idx)
		if offset > 0 {
			index = infix(ident(red.idx), "+", u32(offset))
		}
		// The access is inside the span under the main loop's guard
		// (i + 4 <= len(v), offset < 4); its guard is elided as a
		// typechecker-proven one is, the seam checker confirming the
		// elided form or keeping the guard (compiler/native_bodies.go).
		at := token.Token{SemanticContext: rewriteContext, Line: tok.Line, Column: int(offset) + 1, Literal: "["}
		markRewriteProven(at)
		return &ast.IndexExpression{Token: at, Left: ident(red.span), Index: index}
	}
	assign := func(name string, value ast.Expression) ast.Statement {
		return &ast.AssignmentStatement{Token: tok, Name: ident(name), Value: value}
	}
	accumulate := func(name string, offset int64) ast.Statement {
		return assign(name, infix(ident(name), "+", element(offset)))
	}
	var out []ast.Statement
	names := []string{red.acc, unrolledName(red.acc, 1), unrolledName(red.acc, 2), unrolledName(red.acc, 3)}
	for k := 1; k <= 3; k++ {
		out = append(out, &ast.VariableDeclaration{Token: tok, Name: ident(names[k]), Type: cloneNode(red.accType).(ast.Expression), Value: literal(0)})
	}
	guard := infix(infix(length(), ">=", u32(4)), "&&", infix(ident(red.idx), "<=", infix(length(), "-", u32(4))))
	main := &ast.WhileStatement{Token: tok, Condition: guard, Body: &ast.BlockStatement{Token: tok}}
	for k := int64(0); k < 4; k++ {
		main.Body.Statements = append(main.Body.Statements, accumulate(names[k], k))
	}
	main.Body.Statements = append(main.Body.Statements, assign(red.idx, infix(ident(red.idx), "+", u32(4))))
	out = append(out, main, red.loop)
	out = append(out, assign(red.acc, infix(infix(ident(names[0]), "+", ident(names[1])), "+", infix(ident(names[2]), "+", ident(names[3])))))
	return out
}

// mentionsName reports whether the node names the identifier.
func mentionsName(node ast.Node, name string) bool {
	found := false
	mentionIdents(node, func(ident string) {
		if ident == name {
			found = true
		}
	})
	return found
}

// rewriteContext marks the tokens the rewrite makes: no source token
// carries it, so a proven position never collides with a program's.
const rewriteContext = "oak.native.reduction"

var (
	rewriteProvenMu sync.Mutex
	rewriteProven   = map[token.Token]bool{}
)

func markRewriteProven(tok token.Token) {
	rewriteProvenMu.Lock()
	rewriteProven[tok] = true
	rewriteProvenMu.Unlock()
}

// rewriteProvenIndex reports whether the access at tok is one the
// reduction rewrite placed under its guard.
func rewriteProvenIndex(tok token.Token) bool {
	if tok.SemanticContext != rewriteContext {
		return false
	}
	rewriteProvenMu.Lock()
	defer rewriteProvenMu.Unlock()
	return rewriteProven[tok]
}
