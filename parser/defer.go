package parser

import (
	"fmt"
	"reflect"

	"github.com/SCKelemen/oak/ast"
)

// Deferred statements (docs/spec/10-syntax.md section 4b). `defer s` runs s
// when the enclosing block ends — after the block's value is computed, in
// reverse order of appearance, at the end of every loop iteration, and
// before a `break` leaves the block. The statement is evaluated when it
// runs; nothing is captured or allocated. The parser performs the
// reordering, so every later phase sees ordinary statements exactly where
// they execute.

// parseDeferStatement parses `defer <statement>`.
func (p *Parser) parseDeferStatement() ast.Statement {
	deferToken := p.currentToken
	if p.blockDepth == 0 {
		p.addErrorAtCurrentToken("defer is only allowed inside a block")
		p.nextToken()
		p.parseStatement()
		return nil
	}
	p.nextToken()
	body := p.parseStatement()
	if body == nil {
		p.addErrorAtToken(&deferToken, "defer requires a statement to run at the end of the block")
		return nil
	}
	switch body.(type) {
	case *ast.DeferStatement:
		p.addErrorAtToken(&deferToken, "defer cannot be nested; write one defer per statement")
		return nil
	case *ast.BreakStatement, *ast.WhileStatement, *ast.VariableDeclaration:
		p.addErrorAtToken(&deferToken, fmt.Sprintf("defer takes a call, an assignment, or a discard, not %s", body.TokenLiteral()))
		return nil
	}
	return &ast.DeferStatement{Token: deferToken, Body: body}
}

// desugarDefers rewrites a block containing `defer` statements into the
// block that runs them: `{ a; defer d1; b; defer d2; tail }` becomes
// `{ a; b; tail; d2; d1 }` with DeferredFrom marking where d2 starts (the
// typechecker binds a valued tail to a temporary before d2 and yields it
// after d1), and the pending deferred statements are cloned in before
// every `break` a later statement reaches without crossing a nested loop
// or function literal.
func (p *Parser) desugarDefers(block *ast.BlockStatement) {
	if block == nil {
		return
	}
	hasDefer := false
	for _, stmt := range block.Statements {
		if _, isDefer := stmt.(*ast.DeferStatement); isDefer {
			hasDefer = true
			break
		}
	}
	if !hasDefer {
		return
	}
	out := make([]ast.Statement, 0, len(block.Statements))
	var pending []ast.Statement
	for _, stmt := range block.Statements {
		if deferred, isDefer := stmt.(*ast.DeferStatement); isDefer {
			pending = append(pending, deferred.Body)
			continue
		}
		if len(pending) > 0 {
			insertBeforeBreaks(stmt, pending)
		}
		out = append(out, stmt)
	}
	// The deferred statements follow the original tail; the typechecker,
	// which knows whether the tail is a value, binds it before them.
	block.DeferredFrom = len(out)
	out = append(out, reverseStatements(pending)...)
	block.Statements = out
}

func reverseStatements(statements []ast.Statement) []ast.Statement {
	out := make([]ast.Statement, 0, len(statements))
	for i := len(statements) - 1; i >= 0; i-- {
		out = append(out, statements[i])
	}
	return out
}

// insertBeforeBreaks places clones of the pending deferred statements, in
// reverse order, immediately before every `break` inside stmt that leaves
// the block being rewritten: nested loops own their own breaks and
// function literals are other bodies, so neither is entered.
func insertBeforeBreaks(stmt ast.Statement, pending []ast.Statement) {
	switch s := stmt.(type) {
	case *ast.BlockStatement:
		insertInBlock(s, pending)
	case *ast.IfStatement:
		insertInBlock(s.Consequence, pending)
		switch alt := s.Alternative.(type) {
		case *ast.IfStatement:
			insertBeforeBreaks(alt, pending)
		case *ast.BlockStatement:
			insertInBlock(alt, pending)
		}
	case *ast.UnsafeBlock:
		insertInBlock(s.Body, pending)
	case *ast.ExpressionStatement:
		insertInExpression(s.Expression, pending)
	case *ast.VariableDeclaration:
		insertInExpression(s.Value, pending)
	case *ast.AssignmentStatement:
		insertInExpression(s.Value, pending)
	}
}

func insertInBlock(block *ast.BlockStatement, pending []ast.Statement) {
	if block == nil {
		return
	}
	out := make([]ast.Statement, 0, len(block.Statements)+len(pending))
	for _, stmt := range block.Statements {
		if _, isBreak := stmt.(*ast.BreakStatement); isBreak {
			for _, deferred := range reverseStatements(pending) {
				out = append(out, cloneStatement(deferred))
			}
			out = append(out, stmt)
			continue
		}
		insertBeforeBreaks(stmt, pending)
		out = append(out, stmt)
	}
	block.Statements = out
}

func insertInExpression(expr ast.Expression, pending []ast.Statement) {
	switch e := expr.(type) {
	case *ast.BlockExpression:
		insertInBlock(e.Block, pending)
	case *ast.MatchExpression:
		for _, arm := range e.Arms {
			if arm != nil {
				insertInExpression(arm.Body, pending)
			}
		}
	}
}

// cloneStatement deep-copies a statement so that a deferred statement
// placed before several exits is a distinct node at each: analyses that
// record facts per node never see one node in two places.
func cloneStatement(stmt ast.Statement) ast.Statement {
	cloned, ok := cloneValue(reflect.ValueOf(stmt)).Interface().(ast.Statement)
	if !ok {
		return stmt
	}
	return cloned
}

func cloneValue(v reflect.Value) reflect.Value {
	switch v.Kind() {
	case reflect.Ptr:
		if v.IsNil() {
			return v
		}
		out := reflect.New(v.Elem().Type())
		out.Elem().Set(cloneValue(v.Elem()))
		return out
	case reflect.Interface:
		if v.IsNil() {
			return v
		}
		out := reflect.New(v.Type()).Elem()
		out.Set(cloneValue(v.Elem()))
		return out
	case reflect.Struct:
		out := reflect.New(v.Type()).Elem()
		for i := 0; i < v.NumField(); i++ {
			if !out.Field(i).CanSet() {
				continue
			}
			out.Field(i).Set(cloneValue(v.Field(i)))
		}
		return out
	case reflect.Slice:
		if v.IsNil() {
			return v
		}
		out := reflect.MakeSlice(v.Type(), v.Len(), v.Len())
		for i := 0; i < v.Len(); i++ {
			out.Index(i).Set(cloneValue(v.Index(i)))
		}
		return out
	case reflect.Map:
		if v.IsNil() {
			return v
		}
		out := reflect.MakeMapWithSize(v.Type(), v.Len())
		iter := v.MapRange()
		for iter.Next() {
			out.SetMapIndex(iter.Key(), cloneValue(iter.Value()))
		}
		return out
	default:
		return v
	}
}
