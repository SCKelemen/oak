package nativegen

import "github.com/SCKelemen/oak/ast"

// Single-use span locals forwarded into their call (docs/spec/94-assembler.md
// §9 "The register budget"). A span or view local — `hs: [*]u32 =
// span(&state)`, `w: []u8 = subslice(a, i, u32(4))` — takes a callee-saved
// pair for its whole scope, and the pair is never returned; a body whose
// parameters and locals fill the file then refuses at the declaration. When
// the local is used exactly once, in the statement that follows, as an
// argument of a call to a program function, the declaration goes and the
// argument is the span expression itself: the lowering evaluates it into a
// fresh pair for the call alone (callWith's span arguments). The expression
// is pure (an address, a length, a subslice's guard), so the meaning is
// the declaration's (Oak.SpanForward.let_forward); the verifier reads the
// body as written.

// forwardSingleUseSpans rewrites a body (a clone: the declaration is
// removed and the argument replaced) and reports whether anything changed.
func forwardSingleUseSpans(body ast.Expression) (ast.Expression, bool) {
	if body == nil {
		return body, false
	}
	changed := false
	rewrite := func(stmts []ast.Statement) []ast.Statement {
		out := make([]ast.Statement, 0, len(stmts))
		for i := 0; i < len(stmts); i++ {
			decl, isDecl := stmts[i].(*ast.VariableDeclaration)
			if isDecl && i+1 < len(stmts) && decl.Name != nil && decl.Type != nil && isSpanSyntax(decl.Type) && spanExpression(decl.Value) {
				name := decl.Name.Value
				uses := 0
				for _, later := range stmts[i+1:] {
					uses += mentions(later, name)
				}
				if uses == 1 && mentions(stmts[i+1], name) == 1 && substituteArgument(stmts[i+1], name, decl.Value) {
					changed = true
					continue
				}
			}
			out = append(out, stmts[i])
		}
		return out
	}
	walk(body, func(n ast.Node) {
		if block, isBlock := n.(*ast.BlockStatement); isBlock {
			block.Statements = rewrite(block.Statements)
		}
	})
	return body, changed
}

// isSpanSyntax reports `[]T` or `[*]T`.
func isSpanSyntax(typ ast.Expression) bool {
	index, isIndex := typ.(*ast.IndexExpression)
	if !isIndex || index.Dot {
		return false
	}
	marker, isMarker := index.Index.(*ast.Identifier)
	return isMarker && (marker.Value == "" || marker.Value == "*")
}

// spanExpression reports the span-making calls: span(&…), view(&…),
// subslice(…), subview(…).
func spanExpression(expr ast.Expression) bool {
	call, isCall := expr.(*ast.InvocationExpression)
	if !isCall {
		return false
	}
	ident, isIdent := call.Function.(*ast.Identifier)
	if !isIdent {
		return false
	}
	switch ident.Value {
	case "span", "view", "subslice", "subview":
		return true
	}
	return false
}

// mentions counts a name's identifier occurrences in a node, field names
// after a dot excluded.
func mentions(n ast.Node, name string) int {
	fields := map[*ast.Identifier]bool{}
	walk(n, func(m ast.Node) {
		if access, isAccess := m.(*ast.IndexExpression); isAccess && access.Dot {
			if field, isField := access.Index.(*ast.Identifier); isField {
				fields[field] = true
			}
		}
	})
	count := 0
	walk(n, func(m ast.Node) {
		if id, isIdent := m.(*ast.Identifier); isIdent && id.Value == name && !fields[id] {
			count++
		}
	})
	return count
}

// substituteArgument replaces the one argument naming `name` in a call to
// a program function (not a builtin such as len) inside stmt with a copy
// of value; reports whether it did.
func substituteArgument(stmt ast.Node, name string, value ast.Expression) bool {
	done := false
	walk(stmt, func(m ast.Node) {
		call, isCall := m.(*ast.InvocationExpression)
		if !isCall || done {
			return
		}
		if fn, isIdent := call.Function.(*ast.Identifier); !isIdent || fn.Value == "len" || isConversion(fn.Value) {
			return
		}
		for i, arg := range call.Arguments {
			if id, isIdent := arg.(*ast.Identifier); isIdent && id.Value == name {
				call.Arguments[i] = cloneNode(value).(ast.Expression)
				done = true
				return
			}
		}
	})
	return done
}
