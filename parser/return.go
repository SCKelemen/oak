package parser

// Early return (docs/spec/10-syntax.md section 2e). Functions are
// tail-expression valued; `return e` leaves the function with e from
// anywhere in its body, and `return` leaves a unit function. Like `defer`
// (parser/defer.go) it is a syntax-tree rewrite the parser performs when a
// function body is complete, so every later phase — the checker, the
// borrow checker, the interpreter, the backends, the native verifier —
// sees shapes it already handles:
//
//   - A return in a conditional's arm, outside any loop, nests the rest of
//     the block into the arm that did not return, and the conditional
//     becomes the block's value: `c ? { return e } | {}; rest; tail` is
//     `c ? { e } | { rest; tail }`. Statements after a return in its own
//     block are unreachable and dropped.
//   - A return inside a loop sets the function's value cell
//     (`return__value: T`) and flag (`return__done: Bool`), runs the
//     enclosing blocks' deferred statements, and breaks the innermost
//     loop; after the loop the lowering places `return__done ? { return
//     return__value }`, which the enclosing context lowers in turn — a
//     break again inside an outer loop, a nesting at the function level.
//     The body's declarations of the cell and the flag come first.
//
// The block's deferred statements stay at its end, so a return runs them
// after its value as the spec says (§4b); a break placed by the lowering
// is preceded by clones of the deferred statements of every block it
// leaves, as the parser places them before a written `break`.

import (
	"reflect"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
)

const (
	returnCell = "return__value"
	returnFlag = "return__done"
)

// parseReturnStatement parses `return` or `return e`; the value must begin
// on the keyword's line (docs/spec/10-syntax.md section 4a).
func (p *Parser) parseReturnStatement() ast.Statement {
	tok := p.currentToken
	if p.blockDepth == 0 {
		p.addErrorAtCurrentToken("return is only allowed inside a function body")
	}
	if p.peekTokenIs(token.RBRACE) || p.peekTokenIs(token.PIPE) || p.peekTokenIs(token.SEMI) || p.peekTokenIs(token.EOF) || p.peekToken.Line != tok.Line {
		return &ast.ReturnStatement{Token: tok}
	}
	p.nextToken()
	value := p.parseExpression(LOWEST)
	if value == nil {
		return nil
	}
	return &ast.ReturnStatement{Token: tok, Value: value}
}

type returnLowering struct {
	p          *Parser
	returnType ast.Expression // nil: unannotated (a literal), the type inferred
	unit       bool
	usesCell   bool
	usesFlag   bool
	returnTok  token.Token
}

// lowerReturns rewrites every `return` in a function body. annotated is
// false for a function literal without a return annotation, whose type
// is inferred: a value may be returned from a conditional (the nesting
// needs no type) but not from inside a loop (the cell needs one).
func (p *Parser) lowerReturns(body *ast.BlockStatement, returnType ast.Expression, annotated bool) {
	if body == nil || !blockReturns(body, true) {
		return
	}
	lr := &returnLowering{p: p, returnType: returnType, unit: isUnitTypeExpression(returnType) || (returnType == nil && annotated)}
	if !annotated {
		lr.returnType = nil
	}
	body.Statements = lr.loops(body.Statements, nil)
	lr.nest(body, nil)
	lr.declare(body)
}

func isUnitTypeExpression(t ast.Expression) bool {
	ident, isIdent := t.(*ast.Identifier)
	return isIdent && ident.Value == "()"
}

// blockReturns reports a block holding a return: in its statements, its
// conditionals' arms, its bare and unsafe blocks, and — when intoLoops —
// its loops' bodies. A function literal is another body.
func blockReturns(block *ast.BlockStatement, intoLoops bool) bool {
	if block == nil {
		return false
	}
	for _, stmt := range block.Statements {
		if statementReturns(stmt, intoLoops) {
			return true
		}
	}
	return false
}

func statementReturns(stmt ast.Statement, intoLoops bool) bool {
	switch s := stmt.(type) {
	case *ast.ReturnStatement:
		return true
	case *ast.BlockStatement:
		return blockReturns(s, intoLoops)
	case *ast.UnsafeBlock:
		return blockReturns(s.Body, intoLoops)
	case *ast.IfStatement:
		if blockReturns(s.Consequence, intoLoops) {
			return true
		}
		if s.Alternative != nil {
			return statementReturns(s.Alternative, intoLoops)
		}
	case *ast.WhileStatement:
		return intoLoops && blockReturns(s.Body, true)
	case *ast.ExpressionStatement:
		return expressionReturns(s.Expression, intoLoops)
	}
	return false
}

func expressionReturns(expr ast.Expression, intoLoops bool) bool {
	switch e := expr.(type) {
	case *ast.BlockExpression:
		return blockReturns(e.Block, intoLoops)
	case *ast.MatchExpression:
		for _, arm := range e.Arms {
			if arm != nil && expressionReturns(arm.Body, intoLoops) {
				return true
			}
		}
	}
	return false
}

// ---- pass 1: returns inside loops --------------------------------------

// loops rewrites, in a statement list, every loop whose body returns
// (inner loops first) and places the propagating return after it.
// deferredOuter are the deferred statements of the enclosing blocks that a
// break from a loop here would leave — none at the function level.
func (lr *returnLowering) loops(statements []ast.Statement, deferredOuter [][]ast.Statement) []ast.Statement {
	out := make([]ast.Statement, 0, len(statements))
	for _, stmt := range statements {
		lr.loopsInStatement(stmt, deferredOuter)
		out = append(out, stmt)
		if loop, isLoop := stmt.(*ast.WhileStatement); isLoop && blockReturns(loop.Body, true) {
			lr.rewriteLoop(loop)
			out = append(out, lr.propagatedReturn(loop.Token))
		}
	}
	return out
}

// loopsInStatement descends into the blocks a statement holds, rewriting
// the loops inside them.
func (lr *returnLowering) loopsInStatement(stmt ast.Statement, deferredOuter [][]ast.Statement) {
	switch s := stmt.(type) {
	case *ast.WhileStatement:
		// The loop's own body: a break placed inside leaves the body block
		// and the blocks nested in it, not the blocks outside the loop.
		s.Body.Statements = lr.loops(s.Body.Statements, [][]ast.Statement{deferredOf(s.Body)})
	case *ast.BlockStatement:
		s.Statements = lr.loops(s.Statements, append(deferredOuter, deferredOf(s)))
	case *ast.UnsafeBlock:
		if s.Body != nil {
			s.Body.Statements = lr.loops(s.Body.Statements, append(deferredOuter, deferredOf(s.Body)))
		}
	case *ast.IfStatement:
		if s.Consequence != nil {
			s.Consequence.Statements = lr.loops(s.Consequence.Statements, append(deferredOuter, deferredOf(s.Consequence)))
		}
		if s.Alternative != nil {
			lr.loopsInStatement(s.Alternative, deferredOuter)
		}
	case *ast.ExpressionStatement:
		lr.loopsInExpression(s.Expression, deferredOuter)
	}
}

func (lr *returnLowering) loopsInExpression(expr ast.Expression, deferredOuter [][]ast.Statement) {
	switch e := expr.(type) {
	case *ast.BlockExpression:
		if e.Block != nil {
			e.Block.Statements = lr.loops(e.Block.Statements, append(deferredOuter, deferredOf(e.Block)))
		}
	case *ast.MatchExpression:
		for _, arm := range e.Arms {
			if arm != nil {
				lr.loopsInExpression(arm.Body, deferredOuter)
			}
		}
	}
}

// deferredOf is a block's deferred statements (parser/defer.go places
// them at its end, from DeferredFrom).
func deferredOf(block *ast.BlockStatement) []ast.Statement {
	if block == nil || block.DeferredFrom <= 0 || block.DeferredFrom > len(block.Statements) {
		return nil
	}
	return block.Statements[block.DeferredFrom:]
}

// rewriteLoop turns every return in a loop body (not in a nested loop:
// those were rewritten already and left their propagating return in this
// body) into the cell and flag assignments, the deferred statements of
// the blocks left, and a break.
func (lr *returnLowering) rewriteLoop(loop *ast.WhileStatement) {
	lr.breakReturns(loop.Body, nil)
}

// breakReturns rewrites the returns of block, whose enclosing blocks
// inside the loop have the deferred statements deferredOuter (innermost
// last). A return's block ends at the break: the statements after it are
// unreachable.
func (lr *returnLowering) breakReturns(block *ast.BlockStatement, deferredOuter [][]ast.Statement) {
	if block == nil {
		return
	}
	own := deferredOf(block)
	inner := append(append([][]ast.Statement{}, deferredOuter...), own)
	for i, stmt := range block.Statements {
		if ret, isReturn := stmt.(*ast.ReturnStatement); isReturn {
			block.Statements = append(block.Statements[:i:i], lr.breakFrom(ret, inner)...)
			block.DeferredFrom = 0
			return
		}
		lr.breakReturnsIn(stmt, inner)
	}
}

func (lr *returnLowering) breakReturnsIn(stmt ast.Statement, deferredOuter [][]ast.Statement) {
	switch s := stmt.(type) {
	case *ast.BlockStatement:
		lr.breakReturns(s, deferredOuter)
	case *ast.UnsafeBlock:
		lr.breakReturns(s.Body, deferredOuter)
	case *ast.IfStatement:
		lr.breakReturns(s.Consequence, deferredOuter)
		if s.Alternative != nil {
			lr.breakReturnsIn(s.Alternative, deferredOuter)
		}
	case *ast.ExpressionStatement:
		lr.breakReturnsInExpression(s.Expression, deferredOuter)
	}
}

func (lr *returnLowering) breakReturnsInExpression(expr ast.Expression, deferredOuter [][]ast.Statement) {
	switch e := expr.(type) {
	case *ast.BlockExpression:
		lr.breakReturns(e.Block, deferredOuter)
	case *ast.MatchExpression:
		for _, arm := range e.Arms {
			if arm != nil {
				lr.breakReturnsInExpression(arm.Body, deferredOuter)
			}
		}
	}
}

// breakFrom is what a return inside a loop becomes: `return__value = e`,
// `return__done = true`, the deferred statements of the blocks the break
// leaves (innermost first), `break`. A propagated return (an inner loop's)
// has set both already.
func (lr *returnLowering) breakFrom(ret *ast.ReturnStatement, deferred [][]ast.Statement) []ast.Statement {
	var out []ast.Statement
	if !ret.Propagated {
		if !lr.checkValue(ret) {
			return []ast.Statement{&ast.BreakStatement{Token: ret.Token}}
		}
		if ret.Value != nil {
			if lr.returnType == nil {
				lr.p.addErrorAtToken(&ret.Token, "a return with a value inside a loop needs the function's return type annotated")
			}
			lr.usesCell = true
			out = append(out, &ast.AssignmentStatement{Token: ret.Token, Name: lr.ident(returnCell, ret.Token), Value: ret.Value})
		}
		lr.usesFlag = true
		out = append(out, &ast.AssignmentStatement{Token: ret.Token, Name: lr.ident(returnFlag, ret.Token), Value: &ast.Boolean{Token: token.Token{TokenKind: token.TRUE, Literal: "true", Line: ret.Token.Line, Column: ret.Token.Column}, Value: true}})
	}
	for k := len(deferred) - 1; k >= 0; k-- {
		for _, d := range reverseStatements(deferred[k]) {
			out = append(out, cloneStatement(d))
		}
	}
	return append(out, &ast.BreakStatement{Token: ret.Token})
}

// propagatedReturn is the statement after a loop that returned:
// `return__done ? { return return__value } | {}` (a bare return in a unit
// function).
func (lr *returnLowering) propagatedReturn(tok token.Token) ast.Statement {
	lr.usesFlag = true
	ret := &ast.ReturnStatement{Token: tok, Propagated: true}
	if !lr.unit {
		lr.usesCell = true
		ret.Value = lr.ident(returnCell, tok)
	}
	return &ast.ExpressionStatement{Token: tok, Expression: lr.conditional(lr.ident(returnFlag, tok), []ast.Statement{ret}, nil, tok)}
}

// ---- pass 2: returns in conditionals, outside loops --------------------

// nest rewrites the returns of a block outside any loop, with k the
// statements a path that does not return runs after the block (a copy per
// path). The block's deferred statements stay at its end.
func (lr *returnLowering) nest(block *ast.BlockStatement, k []ast.Statement) {
	if block == nil {
		return
	}
	end := len(block.Statements)
	if block.DeferredFrom > 0 && block.DeferredFrom <= end {
		end = block.DeferredFrom
	}
	deferred := block.Statements[end:]
	relayout := func(kept []ast.Statement) {
		block.Statements = append(kept, deferred...)
		if len(deferred) > 0 {
			block.DeferredFrom = len(kept)
		} else {
			block.DeferredFrom = 0
		}
	}
	for i := 0; i < end; i++ {
		stmt := block.Statements[i]
		switch s := stmt.(type) {
		case *ast.ReturnStatement:
			kept := append([]ast.Statement{}, block.Statements[:i]...)
			if lr.checkValue(s) && s.Value != nil {
				kept = append(kept, &ast.ExpressionStatement{Token: s.Token, Expression: s.Value})
			}
			relayout(kept)
			return
		default:
			if !statementReturns(stmt, false) {
				continue
			}
			rest := cloneStatements(append(append([]ast.Statement{}, block.Statements[i+1:end]...), k...))
			lr.nestInStatement(stmt, rest)
			relayout(append([]ast.Statement{}, block.Statements[:i+1]...))
			return
		}
	}
	if len(k) > 0 {
		// The continuation runs here; its own returns (a later guard, a
		// loop's propagated return) are lowered in their new place.
		relayout(append(append([]ast.Statement{}, block.Statements[:end]...), cloneStatements(k)...))
		lr.nest(block, nil)
	}
}

func (lr *returnLowering) nestInStatement(stmt ast.Statement, k []ast.Statement) {
	switch s := stmt.(type) {
	case *ast.BlockStatement:
		lr.nest(s, k)
	case *ast.UnsafeBlock:
		lr.nest(s.Body, k)
	case *ast.IfStatement:
		lr.nest(s.Consequence, k)
		if s.Alternative != nil {
			lr.nestInStatement(s.Alternative, k)
		}
	case *ast.ExpressionStatement:
		lr.nestInExpression(s.Expression, k, &s.Expression)
	}
}

// nestInExpression threads k into every arm of a conditional: an arm block
// gets nest (its own returns, or k appended), a chained conditional its
// arms, a bare expression arm becomes a block running it and then k.
func (lr *returnLowering) nestInExpression(expr ast.Expression, k []ast.Statement, slot *ast.Expression) {
	switch e := expr.(type) {
	case *ast.BlockExpression:
		if e.Block == nil {
			e.Block = &ast.BlockStatement{Token: e.Token}
		}
		lr.nest(e.Block, k)
	case *ast.MatchExpression:
		for _, arm := range e.Arms {
			if arm == nil {
				continue
			}
			lr.nestInExpression(arm.Body, k, &arm.Body)
		}
	default:
		if len(k) > 0 && slot != nil {
			block := &ast.BlockStatement{Statements: append([]ast.Statement{&ast.ExpressionStatement{Expression: expr}}, cloneStatements(k)...)}
			lr.nest(block, nil)
			*slot = &ast.BlockExpression{Block: block}
		}
	}
}

// ---- shared -------------------------------------------------------------

// checkValue diagnoses a value in a unit function and a bare return in a
// valued one; it reports whether the return is well formed.
func (lr *returnLowering) checkValue(ret *ast.ReturnStatement) bool {
	if ret.Propagated {
		return true
	}
	if lr.unit && ret.Value != nil {
		lr.p.addErrorAtToken(&ret.Token, "a unit function returns no value; write `return`")
		return false
	}
	if !lr.unit && ret.Value == nil {
		lr.p.addErrorAtToken(&ret.Token, "return needs the function's value; write `return e`")
		return false
	}
	return true
}

func (lr *returnLowering) ident(name string, tok token.Token) *ast.Identifier {
	return &ast.Identifier{Token: token.Token{TokenKind: token.IDENT, Literal: name, Line: tok.Line, Column: tok.Column}, Value: name}
}

// conditional is `cond ? { whenTrue } | { whenFalse }` in the parser's own
// spelling (parseConditionSugarArms).
func (lr *returnLowering) conditional(cond ast.Expression, whenTrue, whenFalse []ast.Statement, tok token.Token) *ast.MatchExpression {
	qmark := token.Token{TokenKind: token.QMARK, Literal: "?", Line: tok.Line, Column: tok.Column}
	return &ast.MatchExpression{
		Token:     qmark,
		Scrutinee: cond,
		Arms: []*ast.MatchArm{
			{Token: qmark, Pattern: &ast.LiteralPattern{Token: qmark, Value: &ast.Boolean{Token: qmark, Value: true}}, Body: &ast.BlockExpression{Token: qmark, Block: &ast.BlockStatement{Token: qmark, Statements: whenTrue}}},
			{Token: qmark, Pattern: &ast.LiteralPattern{Token: qmark, Value: &ast.Boolean{Token: qmark, Value: false}}, Body: &ast.BlockExpression{Token: qmark, Block: &ast.BlockStatement{Token: qmark, Statements: whenFalse}}},
		},
	}
}

// declare places the cell and the flag at the body's start when a loop
// returned. A scalar cell starts at zero through its constructor, so the
// native lane lowers it; any other type is zero-initialized by declaration.
func (lr *returnLowering) declare(body *ast.BlockStatement) {
	var decls []ast.Statement
	tok := body.Token
	if lr.usesCell && lr.returnType != nil {
		decl := &ast.VariableDeclaration{Token: tok, Name: lr.ident(returnCell, tok), Type: cloneExpression(lr.returnType)}
		if ident, isIdent := lr.returnType.(*ast.Identifier); isIdent {
			switch ident.Value {
			case "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64":
				decl.Value = &ast.InvocationExpression{Token: tok, Function: lr.ident(ident.Value, tok), Arguments: []ast.Expression{&ast.IntegerLiteral{Token: token.Token{TokenKind: token.INT, Literal: "0", Line: tok.Line, Column: tok.Column}, Value: 0}}}
			case "f32", "f64":
				decl.Value = &ast.InvocationExpression{Token: tok, Function: lr.ident(ident.Value, tok), Arguments: []ast.Expression{&ast.FloatLiteral{Token: token.Token{TokenKind: token.FLOAT, Literal: "0.0", Line: tok.Line, Column: tok.Column}, Text: "0.0"}}}
			case "Bool":
				decl.Value = &ast.Boolean{Token: token.Token{TokenKind: token.FALSE, Literal: "false", Line: tok.Line, Column: tok.Column}, Value: false}
			}
		}
		decls = append(decls, decl)
	}
	if lr.usesFlag {
		decls = append(decls, &ast.VariableDeclaration{Token: tok, Name: lr.ident(returnFlag, tok), Type: lr.ident("Bool", tok), Value: &ast.Boolean{Token: token.Token{TokenKind: token.FALSE, Literal: "false", Line: tok.Line, Column: tok.Column}, Value: false}})
	}
	if len(decls) == 0 {
		return
	}
	body.Statements = append(decls, body.Statements...)
	if body.DeferredFrom > 0 {
		body.DeferredFrom += len(decls)
	}
}

func cloneStatements(statements []ast.Statement) []ast.Statement {
	out := make([]ast.Statement, 0, len(statements))
	for _, stmt := range statements {
		out = append(out, cloneStatement(stmt))
	}
	return out
}

func cloneExpression(expr ast.Expression) ast.Expression {
	if expr == nil {
		return nil
	}
	cloned, ok := cloneValue(reflect.ValueOf(expr)).Interface().(ast.Expression)
	if !ok {
		return expr
	}
	return cloned
}
