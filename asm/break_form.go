package asm

// The Oak side of `break` (docs/spec/94-assembler.md §9 "Loops that
// break"). A `while c { … break … }` is lowered as the loop that carries a
// one-bit flag:
//
//	#brk@L: Bool = false
//	while !#brk@L && c {
//	  … #brk@L = true            (the break)
//	  !#brk@L ? { rest } | {}    (what followed the statement that broke)
//	}
//
// which is the summary the machine side builds for a body branching to
// the loop's exit label (loopShape.breaks, breakVar): the flag is 0 at
// the header, an iteration that breaks sets it, the continue condition
// reads it first so the exit tests — and their traps — are not evaluated
// after a break, and the statements after the break do not run. The
// rewrite is a syntax-tree transformation done once per loop, like the
// parser's `defer` reordering; every later step of the lowering sees
// shapes it already handles.

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
)

type breakForm struct {
	decl *ast.VariableDeclaration
	loop *ast.WhileStatement
	// original is the loop's own condition, decided at entry (lowerWhile).
	original ast.Expression
}

// breakForm is the flag form of a loop whose body breaks, or has=false
// for a loop without a break. Two loops that break on one source line
// would share a flag name; that is refused.
func (lo *oakLowering) breakForm(loop *ast.WhileStatement) (form *breakForm, has bool, reason string) {
	if !blockBreaks(loop.Body) {
		return nil, false, ""
	}
	if lo.breakForms == nil {
		lo.breakForms = map[*ast.WhileStatement]*breakForm{}
		lo.breakNames = map[string]*ast.WhileStatement{}
	}
	if cached, seen := lo.breakForms[loop]; seen {
		return cached, true, ""
	}
	name := fmt.Sprintf("%s@%d", breakVar, loop.Token.Line)
	if other, taken := lo.breakNames[name]; taken && other != loop {
		return nil, false, "two loops that break on one line"
	}
	lo.breakNames[name] = loop
	ident := func() *ast.Identifier { return &ast.Identifier{Token: token.Token{Literal: name}, Value: name} }
	boolean := func(v bool) *ast.Boolean {
		text := "false"
		if v {
			text = "true"
		}
		return &ast.Boolean{Token: token.Token{Literal: text}, Value: v}
	}
	notBroken := func() ast.Expression {
		return &ast.PrefixExpression{Token: token.Token{Literal: "!"}, Operator: "!", Right: ident()}
	}
	setBroken := func() ast.Statement {
		return &ast.AssignmentStatement{Token: loop.Token, Name: ident(), Value: boolean(true)}
	}
	// guard wraps statements as `!#brk ? { rest } | {}`.
	guard := func(rest *ast.BlockStatement) ast.Statement {
		return &ast.ExpressionStatement{Token: loop.Token, Expression: &ast.MatchExpression{
			Token:     token.Token{Literal: "?"},
			Scrutinee: notBroken(),
			Arms: []*ast.MatchArm{
				{Pattern: &ast.LiteralPattern{Value: boolean(true)}, Body: &ast.BlockExpression{Block: rest}},
				{Pattern: &ast.WildcardPattern{}, Body: &ast.BlockExpression{Block: &ast.BlockStatement{}}},
			},
		}}
	}
	var rewriteBlock func(block *ast.BlockStatement) *ast.BlockStatement
	var rewriteMatch func(match *ast.MatchExpression) *ast.MatchExpression
	rewriteMatch = func(match *ast.MatchExpression) *ast.MatchExpression {
		out := *match
		out.Arms = make([]*ast.MatchArm, len(match.Arms))
		for k, arm := range match.Arms {
			copied := *arm
			switch body := arm.Body.(type) {
			case *ast.BlockExpression:
				if body.Block != nil && blockBreaks(body.Block) {
					copied.Body = &ast.BlockExpression{Token: body.Token, Block: rewriteBlock(body.Block)}
				}
			case *ast.MatchExpression:
				if matchBreaks(body) {
					copied.Body = rewriteMatch(body)
				}
			}
			out.Arms[k] = &copied
		}
		return &out
	}
	rewriteBlock = func(block *ast.BlockStatement) *ast.BlockStatement {
		out := &ast.BlockStatement{Token: block.Token, Order: block.Order}
		for i, stmt := range block.Statements {
			switch s := stmt.(type) {
			case *ast.BreakStatement:
				// The break: set the flag; what follows in this block is
				// unreachable.
				out.Statements = append(out.Statements, setBroken())
				return out
			case *ast.ExpressionStatement:
				match, isMatch := s.Expression.(*ast.MatchExpression)
				if isMatch && matchBreaks(match) {
					out.Statements = append(out.Statements, &ast.ExpressionStatement{Token: s.Token, Expression: rewriteMatch(match), Discard: s.Discard})
					if rest := block.Statements[i+1:]; len(rest) > 0 {
						out.Statements = append(out.Statements, guard(rewriteBlock(&ast.BlockStatement{Token: block.Token, Statements: rest})))
					}
					return out
				}
			}
			out.Statements = append(out.Statements, stmt)
		}
		return out
	}
	body := rewriteBlock(loop.Body)
	form = &breakForm{
		decl: &ast.VariableDeclaration{Token: loop.Token, Name: ident(), Type: &ast.Identifier{Token: token.Token{Literal: "Bool"}, Value: "Bool"}, Value: boolean(false)},
		loop: &ast.WhileStatement{
			Token:     loop.Token,
			Condition: &ast.InfixExpression{Token: token.Token{Literal: "&&"}, Left: notBroken(), Operator: "&&", Right: loop.Condition},
			Body:      body,
		},
		original: loop.Condition,
	}
	lo.breakForms[loop] = form
	return form, true, ""
}

// blockBreaks reports a block with a `break` of its own loop: in its
// statements or the arms of its statement conditionals, not inside a
// nested loop (whose break is that loop's) or a function literal.
func blockBreaks(block *ast.BlockStatement) bool {
	if block == nil {
		return false
	}
	for _, stmt := range block.Statements {
		switch s := stmt.(type) {
		case *ast.BreakStatement:
			return true
		case *ast.ExpressionStatement:
			if match, isMatch := s.Expression.(*ast.MatchExpression); isMatch && matchBreaks(match) {
				return true
			}
		}
	}
	return false
}

func matchBreaks(match *ast.MatchExpression) bool {
	for _, arm := range match.Arms {
		switch body := arm.Body.(type) {
		case *ast.BlockExpression:
			if blockBreaks(body.Block) {
				return true
			}
		case *ast.MatchExpression:
			if matchBreaks(body) {
				return true
			}
		}
	}
	return false
}
