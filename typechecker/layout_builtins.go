package typechecker

// Layout introspection, compile-time assertion, and code addresses
// (docs/spec/40-records.md §6b, docs/spec/94-assembler.md §7):
//
//	size_of[T]()          u32 — sizeof the emitted struct or primitive
//	align_of[T]()         u32 — its alignment
//	offset_of[T](field)   u32 — a declared field's offset
//	static_assert(cond)   compile-time: cond is a constant over the above
//	address_of(f)         u64 — the code address of an asm-backed function
//
// The checker rewrites the indexed spellings to plain identifiers and
// records the queried type position-keyed (the resolution pattern of
// typechecker/mono.go), so lowering never sees an index to rewrite and the
// backend emits sizeof/_Alignof/offsetof over the real emitted type — the C
// compiler is the authority on the numbers, and static_assert makes it
// ratify the author's claim.

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
)

// LayoutQuery is one recorded size_of/align_of/offset_of resolution.
type LayoutQuery struct {
	Kind     string // "size_of" | "align_of" | "offset_of"
	TypeName string // declared record name (or instantiation) or primitive
	Record   bool   // TypeName is a declared record (emitted struct)
	Field    string // offset_of only
}

// LayoutQueryAt reports the recorded query for a rewritten builtin call.
func (tc *TypeChecker) LayoutQueryAt(tok token.Token) (LayoutQuery, bool) {
	query, ok := tc.layoutQueries[positionKey(tok)]
	return query, ok
}

// IsAsmBacked reports whether name is an asm-backed declaration.
func (tc *TypeChecker) IsAsmBacked(name string) bool {
	return tc.asmBackedFunctions[name]
}

var layoutBuiltinNames = map[string]bool{"size_of": true, "align_of": true, "offset_of": true}

// resolveLayoutBuiltin recognizes the layout and address builtins,
// reporting (type, true) when the call was one (even on error).
func (tc *TypeChecker) resolveLayoutBuiltin(expr *ast.InvocationExpression) (Type, bool) {
	if ident, ok := expr.Function.(*ast.Identifier); ok {
		switch ident.Value {
		case "address_of":
			return tc.checkAddressOf(expr), true
		case "static_assert":
			return tc.checkStaticAssert(expr), true
		}
		return nil, false
	}
	indexExpr, isIndex := expr.Function.(*ast.IndexExpression)
	if !isIndex || indexExpr.Dot {
		return nil, false
	}
	callee, isIdent := indexExpr.Left.(*ast.Identifier)
	if !isIdent || !layoutBuiltinNames[callee.Value] {
		return nil, false
	}
	u32 := &PrimitiveType{Name: "u32"}
	queried := tc.parseTypeExpression(indexExpr.Index)
	if queried == nil {
		return nil, true
	}
	query := LayoutQuery{Kind: callee.Value}
	switch t := queried.(type) {
	case *RecordType:
		if t.Name == "" {
			tc.addError(expr, "%s requires a declared record or primitive type, not an anonymous shape", callee.Value)
			return nil, true
		}
		query.TypeName = t.Name
		query.Record = true
	case *PrimitiveType:
		query.TypeName = normalizePrimitiveName(t.Name)
	case *ADTType:
		// A tagged union is an emitted struct too: a u32 tag, then the
		// payload union (docs/spec/92-ffi.md section 2.6).
		query.TypeName = t.Name
		query.Record = true
	default:
		tc.addError(expr, "%s requires a declared record, tagged union, or primitive type, got %s", callee.Value, queried)
		return nil, true
	}
	switch callee.Value {
	case "size_of", "align_of":
		if len(expr.Arguments) != 0 {
			tc.addError(expr, "%s[T] takes no arguments", callee.Value)
			return nil, true
		}
	case "offset_of":
		record, isRecord := queried.(*RecordType)
		adt, isADT := queried.(*ADTType)
		if !isRecord && !isADT {
			tc.addError(expr, "offset_of requires a declared record or tagged union type")
			return nil, true
		}
		if len(expr.Arguments) != 1 {
			tc.addError(expr, "offset_of[T] takes exactly one field name")
			return nil, true
		}
		fieldIdent, isField := expr.Arguments[0].(*ast.Identifier)
		if !isField {
			tc.addError(expr.Arguments[0], "offset_of[T] takes a bare field name")
			return nil, true
		}
		if isADT {
			if fieldIdent.Value != "tag" && fieldIdent.Value != "payload" {
				tc.addError(expr.Arguments[0], "offset_of: tagged union %s has the fields tag and payload (docs/spec/92-ffi.md section 2.6), not %s", adt.Name, fieldIdent.Value)
				return nil, true
			}
		} else if _, exists := record.Fields[fieldIdent.Value]; !exists {
			tc.addError(expr.Arguments[0], "offset_of: %s has no field %s", record.Name, fieldIdent.Value)
			return nil, true
		}
		query.Field = fieldIdent.Value
	}
	// Rewrite to the plain identifier so lowering never treats size_of[T]
	// as an element index; the query travels position-keyed.
	rewritten := &ast.Identifier{Token: callee.Token, Value: callee.Value}
	expr.Function = rewritten
	if tc.layoutQueries == nil {
		tc.layoutQueries = make(map[tokenKey]LayoutQuery)
	}
	tc.layoutQueries[positionKey(callee.Token)] = query
	return u32, true
}

// checkAddressOf admits only asm-backed functions: stable code symbols
// with no Oak body to inline, the vector-table case. No other address is
// exposed, and no arithmetic on it is a pointer.
func (tc *TypeChecker) checkAddressOf(expr *ast.InvocationExpression) Type {
	u64 := &PrimitiveType{Name: "u64"}
	if len(expr.Arguments) != 1 {
		tc.addError(expr, "address_of takes exactly one asm-backed function name")
		return u64
	}
	target, isIdent := expr.Arguments[0].(*ast.Identifier)
	if !isIdent || !tc.asmBackedFunctions[target.Value] {
		tc.addError(expr.Arguments[0], "address_of admits only asm-backed functions (docs/spec/94-assembler.md §7): stable code symbols such as an exception vector table")
		return u64
	}
	return u64
}

// checkStaticAssert requires a Bool condition built only from layout
// builtins, literals, and operators — a constant the C compiler can fold
// and ratify at compile time.
func (tc *TypeChecker) checkStaticAssert(expr *ast.InvocationExpression) Type {
	if len(expr.Arguments) != 1 {
		tc.addError(expr, "static_assert takes exactly one condition")
		return &UnitType{}
	}
	condType := tc.checkExpression(expr.Arguments[0])
	if condType != nil && !condType.Equals(&BoolType{}) {
		tc.addError(expr.Arguments[0], "static_assert condition must be Bool, got %s", condType)
	}
	if !tc.layoutConstant(expr.Arguments[0]) {
		tc.addError(expr.Arguments[0], "static_assert condition must be a compile-time constant over size_of/align_of/offset_of, literals, and operators; runtime conditions use assert")
	}
	return &UnitType{}
}

func (tc *TypeChecker) layoutConstant(expr ast.Expression) bool {
	switch e := expr.(type) {
	case *ast.IntegerLiteral, *ast.Boolean:
		return true
	case *ast.PrefixExpression:
		return tc.layoutConstant(e.Right)
	case *ast.InfixExpression:
		return tc.layoutConstant(e.Left) && tc.layoutConstant(e.Right)
	case *ast.InvocationExpression:
		ident, isIdent := e.Function.(*ast.Identifier)
		if !isIdent {
			return false
		}
		if layoutBuiltinNames[ident.Value] {
			return true
		}
		// Primitive constructors over constants: u32(16).
		if _, isPrim := conversionPrimitives[ident.Value]; isPrim && len(e.Arguments) == 1 {
			return tc.layoutConstant(e.Arguments[0])
		}
	}
	return false
}
