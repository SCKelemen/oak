package compiler

// The propagation form (docs/spec/10-syntax.md section 2d;
// docs/notes/algebraic-semantics-2026-09.md section 5). `x: T = try e` in a
// block whose value is the enclosing function's result binds the Ok (Some)
// payload and re-raises the Err (None): it is sugar for the match the
// standard library writes by hand,
//
//	e ? | .Err(err) => .Err(err) | .Ok(x) => { rest of the block }
//
// and lowers to exactly that before checking, so it costs what a match
// costs and no later phase knows the form exists. Which pair of variants is
// meant is read from the function's declared return type — Result or
// Option — which is also what makes the re-raise well typed. The Lean
// statement of the lowering is Oak.Propagation: try is bind on Except and
// on Option, and try-then-rewrap is the identity.
//
// The form is legal only where the block's value is the function's result:
// the function body, and a block that is the tail expression of such a
// block (a `?` arm). Anywhere else — a loop body, a non-tail block, an
// expression operand, a bare statement — the re-raise would not leave the
// function, so it is a diagnostic at the `try`.

import (
	"fmt"
	"reflect"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/token"
)

// CodeTryShape reports a `try` the lowering cannot give a meaning: outside
// a tail block, unbound, in a function that returns neither Result nor
// Option, or as a block's last statement.
const CodeTryShape = "OAK-M0401"

// tryKind is the variant pair a function's return type selects.
type tryKind struct {
	ok, err    string
	errPayload bool // Err carries the error; None carries nothing
}

// tryKindOf reads the propagation pair from a declared return type.
func tryKindOf(returnType ast.Expression) (tryKind, bool) {
	// `Result[T, E]` parses as nested applications, (Result[T])[E]: walk
	// the applications down to the head.
	head := returnType
	applied := false
	for {
		application, isApplication := head.(*ast.IndexExpression)
		if !isApplication || application.Dot {
			break
		}
		head = application.Left
		applied = true
	}
	name, isIdent := head.(*ast.Identifier)
	if !applied || !isIdent {
		return tryKind{}, false
	}
	switch name.Value {
	case "Result":
		return tryKind{ok: "Ok", err: "Err", errPayload: true}, true
	case "Option":
		return tryKind{ok: "Some", err: "None"}, true
	}
	return tryKind{}, false
}

type tryLowering struct {
	diags []*diagnostic.Diagnostic
}

func (l *tryLowering) report(node ast.Node, format string, args ...interface{}) {
	l.diags = append(l.diags, diagnostic.NewDiagnosticFromNodeWithCode(node, "compiler", CodeTryShape, fmt.Sprintf(format, args...)))
}

// lowerTry rewrites every `try` in the program or reports why it cannot.
func lowerTry(program *ast.Program) error {
	l := &tryLowering{}
	for _, stmt := range program.Statements {
		fn, isFunction := stmt.(*ast.FunctionStatement)
		if !isFunction || fn.Body == nil {
			continue
		}
		kind, propagates := tryKindOf(fn.ReturnType)
		if !propagates {
			continue
		}
		fn.Body = l.lowerTail(fn.Body, kind)
	}
	// Whatever is left is a try the rule does not cover.
	_ = transformSyntax(reflect.ValueOf(program), func(e ast.Expression) (ast.Expression, error) {
		if t, isTry := e.(*ast.TryExpression); isTry {
			l.report(t, "try here does not return from the function: propagate only in a block whose value is the function's Result or Option — the body, or a tail `?` arm — as `x: T = try e` or `_ = try e`")
		}
		return e, nil
	})
	if len(l.diags) != 0 {
		return &DiagnosticError{Phase: "try", Diagnostics: l.diags}
	}
	return nil
}

// lowerTail lowers an expression whose value is the function's result.
func (l *tryLowering) lowerTail(expr ast.Expression, kind tryKind) ast.Expression {
	switch e := expr.(type) {
	case *ast.BlockExpression:
		if e.Block != nil {
			e.Block.Statements = l.lowerBlock(e.Block.Statements, kind)
		}
		return e
	case *ast.MatchExpression:
		for _, arm := range e.Arms {
			if arm != nil {
				arm.Body = l.lowerTail(arm.Body, kind)
			}
		}
		return e
	case *ast.TryExpression:
		// `try e` as a block's value: propagate and re-wrap. Lean:
		// Oak.Propagation.tryResult_id — this is `e` itself, spelled as
		// the match so one form reaches the backends.
		name := tryName(e.Token, "ok")
		rewrap := &ast.VariantExpression{Token: e.Token, Variant: ident(e.Token, kind.ok), Payload: ident(e.Token, name)}
		return l.match(e, kind, &ast.BindingPattern{Token: e.Token, Name: ident(e.Token, name)}, rewrap)
	}
	return expr
}

// lowerBlock lowers the statements of a tail block: the first statement
// that propagates nests the rest of the block into the Ok arm.
func (l *tryLowering) lowerBlock(stmts []ast.Statement, kind tryKind) []ast.Statement {
	for i, stmt := range stmts {
		var t *ast.TryExpression
		var okPattern ast.Pattern
		switch s := stmt.(type) {
		case *ast.VariableDeclaration:
			if candidate, isTry := s.Value.(*ast.TryExpression); isTry {
				t = candidate
				okPattern = &ast.BindingPattern{Token: s.Name.Token, Name: s.Name}
			}
		case *ast.ExpressionStatement:
			if candidate, isTry := s.Expression.(*ast.TryExpression); isTry {
				if !s.Discard && i == len(stmts)-1 {
					// `try e` as the block's value: propagate and re-wrap.
					s.Expression = l.lowerTail(candidate, kind)
					return stmts
				}
				if !s.Discard {
					l.report(candidate, "try as a bare statement drops the Ok value silently: bind it (`x: T = try e`) or discard it on purpose (`_ = try e`)")
					return stmts
				}
				t = candidate
				okPattern = &ast.WildcardPattern{Token: candidate.Token}
			}
		}
		if t == nil {
			if i == len(stmts)-1 {
				if es, isExpression := stmt.(*ast.ExpressionStatement); isExpression && !es.Discard {
					es.Expression = l.lowerTail(es.Expression, kind)
				}
			}
			continue
		}
		rest := stmts[i+1:]
		if len(rest) == 0 {
			l.report(t, "try in the last statement of a block: nothing follows to use the value; end the block with the result it produces (`try e` alone as the block's value re-wraps it)")
			return stmts
		}
		rest = l.lowerBlock(append([]ast.Statement(nil), rest...), kind)
		body := &ast.BlockExpression{Token: t.Token, Block: &ast.BlockStatement{Token: t.Token, Statements: rest}}
		lowered := append([]ast.Statement(nil), stmts[:i]...)
		return append(lowered, &ast.ExpressionStatement{Token: t.Token, Expression: l.match(t, kind, okPattern, body)})
	}
	return stmts
}

// match builds `e ? | .Err(err) => .Err(err) | .Ok(pattern) => body` (or
// the None/Some pair) at the try's position.
func (l *tryLowering) match(t *ast.TryExpression, kind tryKind, okPattern ast.Pattern, body ast.Expression) *ast.MatchExpression {
	errArm := &ast.MatchArm{Token: t.Token}
	if kind.errPayload {
		name := tryName(t.Token, "err")
		errArm.Pattern = &ast.VariantPattern{Token: t.Token, Variant: ident(t.Token, kind.err), Payload: &ast.BindingPattern{Token: t.Token, Name: ident(t.Token, name)}}
		errArm.Body = &ast.VariantExpression{Token: t.Token, Variant: ident(t.Token, kind.err), Payload: ident(t.Token, name)}
	} else {
		errArm.Pattern = &ast.VariantPattern{Token: t.Token, Variant: ident(t.Token, kind.err)}
		errArm.Body = &ast.VariantExpression{Token: t.Token, Variant: ident(t.Token, kind.err)}
	}
	okArm := &ast.MatchArm{Token: t.Token, Pattern: &ast.VariantPattern{Token: t.Token, Variant: ident(t.Token, kind.ok), Payload: okPattern}, Body: body}
	return &ast.MatchExpression{Token: t.Token, Scrutinee: t.Operand, Arms: []*ast.MatchArm{errArm, okArm}}
}

// tryName is a binder no program spells, unique per try so nested forms
// never shadow (Oak forbids shadowing).
func tryName(tok token.Token, role string) string {
	return fmt.Sprintf("_try_%s_%d_%d", role, tok.Line, tok.Column)
}

func ident(at token.Token, name string) *ast.Identifier {
	tok := at
	tok.TokenKind = token.IDENT
	tok.Literal = name
	return &ast.Identifier{Token: tok, Value: name}
}
