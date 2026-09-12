package compiler

import (
	"fmt"
	"reflect"
	"sort"

	"github.com/SCKelemen/oak/ast"
)

// Capturing closures, first increment (docs/spec/60-effects-allocation.md
// §11, 10-syntax.md §3c): static higher-order specialization.
//
// A function literal that captures enclosing locals has no representation
// in Oak — a literal is a code pointer, never an environment — and the
// checker rejects it (OAK-T0401) unless the environment's storage is
// justified. This pass justifies the one shape whose storage is already
// there: the literal is passed directly to a top-level Oak function whose
// parameter is only ever called, and every capture is a scalar, a string, a
// view or a span the caller holds. Then the callee is specialized for the call site — cloned with the
// function parameter removed and the captures appended as by-value
// parameters, each call through the parameter replaced by a direct call to
// the lifted literal — and the call site passes the captured values as
// ordinary arguments. The environment is the argument list: caller-owned
// storage that lives exactly as long as the call (Oak.ClosureCapture,
// non-escaping stack capture), no closure object, no allocation, no
// pointer into the frame, and the effect analysis sees a direct call.
//
// Everything outside the shape is left untouched, so the checker's
// rejection still names the captures: a literal bound to a local first,
// a callee that stores, returns or forwards its function parameter, a
// generic or extern callee, a capture that is a record, a Buffer, an ADT or
// an unannotated local, or a capture the literal assigns to.

// closureScalarTypes are the scalar capture types, copied by value:
// fixed-width and platform integers, Bool, and the two arithmetic floats.
// Strings, views and spans of these are capturable too (captureTypeSpelling).
var closureScalarTypes = map[string]bool{
	"u8": true, "u16": true, "u32": true, "u64": true, "u128": true,
	"i8": true, "i16": true, "i32": true, "i64": true,
	"int": true, "uint": true, "ptr": true, "uptr": true,
	"byte": true, "rune": true, "Bool": true, "f32": true, "f64": true,
}

// specializeCapturingLiterals rewrites every call in the program that fits
// the shape above. It appends the lifted literals and specialized callees
// to the program; the counter keeps their names distinct and deterministic.
func specializeCapturingLiterals(program *ast.Program) {
	if program == nil {
		return
	}
	functions := map[string]*ast.FunctionStatement{}
	for _, stmt := range program.Statements {
		if fn, ok := stmt.(*ast.FunctionStatement); ok && fn.Name != nil {
			functions[fn.Name.Value] = fn
		}
	}
	var added []ast.Statement
	counter := 0
	for _, stmt := range program.Statements {
		enclosing, ok := stmt.(*ast.FunctionStatement)
		if !ok || enclosing.Body == nil || enclosing.ExternSymbol != "" {
			continue
		}
		candidates := enclosingScalars(enclosing)
		if len(candidates) == 0 {
			continue
		}
		_ = transformSyntax(reflect.ValueOf(&enclosing.Body).Elem(), func(e ast.Expression) (ast.Expression, error) {
			call, ok := e.(*ast.InvocationExpression)
			if !ok {
				return e, nil
			}
			if lifted, clone, ok := specializeCall(call, functions, candidates, counter); ok {
				added = append(added, lifted, clone)
				counter++
			}
			return call, nil
		})
	}
	program.Statements = append(program.Statements, added...)
}

// enclosingScalars maps every parameter and annotated local of the function
// to its declared type when that type is capturable (captureTypeSpelling). A
// name declared twice with different types, or with an uncapturable type,
// is not a candidate: capturing it stays rejected.
func enclosingScalars(fn *ast.FunctionStatement) map[string]ast.Expression {
	types := map[string]ast.Expression{}
	spellings := map[string]string{}
	blocked := map[string]bool{}
	note := func(name string, typeExpr ast.Expression) {
		spelled, ok := captureTypeSpelling(typeExpr)
		if name == "" || !ok {
			blocked[name] = true
			return
		}
		if prior, seen := spellings[name]; seen && prior != spelled {
			blocked[name] = true
			return
		}
		spellings[name] = spelled
		types[name] = typeExpr
	}
	for _, param := range fn.Parameters {
		if param != nil && param.Name != nil {
			if param.Variadic {
				blocked[param.Name.Value] = true
				continue
			}
			note(param.Name.Value, param.Type)
		}
	}
	if fn.Receiver != nil && fn.Receiver.Name != nil {
		blocked[fn.Receiver.Name.Value] = true
	}
	walkStatements(fn.Body, func(s ast.Statement) {
		if decl, ok := s.(*ast.VariableDeclaration); ok && decl.Name != nil {
			note(decl.Name.Value, decl.Type)
		}
	})
	for name := range blocked {
		delete(types, name)
	}
	return types
}

// walkStatements visits every statement nested anywhere under node,
// function literals included (their locals shadow, which is why a name
// declared with two types is blocked rather than resolved).
func walkStatements(node ast.Node, visit func(ast.Statement)) {
	if node == nil {
		return
	}
	var walk func(v reflect.Value)
	walk = func(v reflect.Value) {
		switch v.Kind() {
		case reflect.Interface, reflect.Pointer:
			if v.IsNil() {
				return
			}
			if s, ok := v.Interface().(ast.Statement); ok {
				visit(s)
			}
			walk(v.Elem())
		case reflect.Struct:
			for i := 0; i < v.NumField(); i++ {
				if v.Type().Field(i).IsExported() {
					walk(v.Field(i))
				}
			}
		case reflect.Slice:
			for i := 0; i < v.Len(); i++ {
				walk(v.Index(i))
			}
		}
	}
	walk(reflect.ValueOf(node))
}

// specializeCall rewrites one call in place when exactly one argument is a
// capturing typed literal in the supported shape, returning the lifted
// literal and the specialized callee to append to the program.
func specializeCall(call *ast.InvocationExpression, functions map[string]*ast.FunctionStatement, candidates map[string]ast.Expression, counter int) (lifted, clone *ast.FunctionStatement, ok bool) {
	calleeIdent, isIdent := call.Function.(*ast.Identifier)
	if !isIdent {
		return nil, nil, false
	}
	callee := functions[calleeIdent.Value]
	if callee == nil || callee.Body == nil || callee.ExternSymbol != "" || callee.AsmBacked || callee.Kernel || callee.Theorem ||
		len(callee.TypeParams) != 0 || callee.Receiver != nil || len(callee.Parameters) != len(call.Arguments) {
		return nil, nil, false
	}
	position := -1
	var literal *ast.FunctionLiteral
	var captures []string
	for i, arg := range call.Arguments {
		lit, isLiteral := arg.(*ast.FunctionLiteral)
		if !isLiteral {
			continue
		}
		names := literalCaptures(lit, candidates)
		if len(names) == 0 {
			continue // captureless: a code pointer already, nothing to do
		}
		if position != -1 {
			return nil, nil, false // two capturing literals in one call: not this increment
		}
		position, literal, captures = i, lit, names
	}
	if literal == nil || len(literal.Parameters) == 0 && literal.ReturnType == nil || literal.Body == nil {
		return nil, nil, false
	}
	param := callee.Parameters[position]
	if param == nil || param.Name == nil || param.Variadic {
		return nil, nil, false
	}
	if _, isFunctionType := param.Type.(*ast.FunctionTypeExpression); !isFunctionType {
		return nil, nil, false
	}
	if !callOnly(callee.Body, param.Name.Value) || assignsAny(literal.Body, captures) {
		return nil, nil, false
	}

	tok := literal.Token
	ident := func(name string) *ast.Identifier {
		t := tok
		t.Literal = name
		return &ast.Identifier{Token: t, Value: name}
	}
	captureParams := func() []*ast.FunctionParameter {
		params := make([]*ast.FunctionParameter, 0, len(captures))
		for _, name := range captures {
			params = append(params, &ast.FunctionParameter{Token: tok, Name: ident(name), Type: cloneExpression(candidates[name])})
		}
		return params
	}

	// The literal, lifted, with the captures as trailing parameters: its
	// body already names them.
	litName := fmt.Sprintf("0clos_lit_%d", counter)
	lifted = &ast.FunctionStatement{
		Token:      tok,
		EndToken:   tok,
		Name:       ident(litName),
		Parameters: append(append([]*ast.FunctionParameter{}, literal.Parameters...), captureParams()...),
		ReturnType: literal.ReturnType,
		Body:       &ast.BlockExpression{Token: tok, Block: literal.Body},
	}

	// The callee, specialized: the function parameter gone, the captures
	// appended, every call through the parameter now a direct call to the
	// lifted literal carrying the captures.
	clone = cloneSyntax(reflect.ValueOf(callee)).Interface().(*ast.FunctionStatement)
	cloneName := fmt.Sprintf("0clos_%d_%s", counter, callee.Name.Value)
	clone.Name = ident(cloneName)
	clone.Exported, clone.Opaque = false, false
	params := make([]*ast.FunctionParameter, 0, len(clone.Parameters)+len(captures)-1)
	for i, p := range clone.Parameters {
		if i != position {
			params = append(params, p)
		}
	}
	clone.Parameters = append(params, captureParams()...)
	fname := param.Name.Value
	_ = transformSyntax(reflect.ValueOf(&clone.Body).Elem(), func(e ast.Expression) (ast.Expression, error) {
		inner, isCall := e.(*ast.InvocationExpression)
		if !isCall {
			return e, nil
		}
		if head, isHead := inner.Function.(*ast.Identifier); isHead && head.Value == fname {
			inner.Function = ident(litName)
			for _, name := range captures {
				inner.Arguments = append(inner.Arguments, ident(name))
			}
		}
		return inner, nil
	})

	// The call site: the literal's slot removed, the captured values passed.
	call.Function = ident(cloneName)
	args := make([]ast.Expression, 0, len(call.Arguments)+len(captures)-1)
	for i, arg := range call.Arguments {
		if i != position {
			args = append(args, arg)
		}
	}
	for _, name := range captures {
		args = append(args, ident(name))
	}
	call.Arguments = args
	return lifted, clone, true
}

// literalCaptures returns the candidate names the literal reads without
// declaring them itself, sorted. A name the literal binds — a parameter, a
// local, a pattern binding — shadows the enclosing one and is not a
// capture; the checker's own analysis (typechecker.closureCaptures) is the
// authority for the rejection, this is the pass's conservative view.
func literalCaptures(lit *ast.FunctionLiteral, candidates map[string]ast.Expression) []string {
	bound := map[string]bool{}
	for _, p := range lit.Parameters {
		if p != nil && p.Name != nil {
			bound[p.Name.Value] = true
		}
	}
	for _, a := range lit.Arguments {
		if a != nil {
			bound[a.Value] = true
		}
	}
	walkStatements(lit.Body, func(s ast.Statement) {
		if decl, ok := s.(*ast.VariableDeclaration); ok && decl.Name != nil {
			bound[decl.Name.Value] = true
		}
	})
	walkPatterns(lit.Body, func(name string) { bound[name] = true })
	used := map[string]bool{}
	_ = transformSyntax(reflect.ValueOf(&lit.Body).Elem(), func(e ast.Expression) (ast.Expression, error) {
		if id, ok := e.(*ast.Identifier); ok {
			if _, candidate := candidates[id.Value]; candidate && !bound[id.Value] {
				used[id.Value] = true
			}
		}
		return e, nil
	})
	names := make([]string, 0, len(used))
	for name := range used {
		names = append(names, name)
	}
	sort.Strings(names)
	return names
}

// walkPatterns reports every name a match pattern binds anywhere under node.
func walkPatterns(node ast.Node, visit func(string)) {
	if node == nil {
		return
	}
	var walk func(v reflect.Value)
	walk = func(v reflect.Value) {
		switch v.Kind() {
		case reflect.Interface, reflect.Pointer:
			if v.IsNil() {
				return
			}
			if p, ok := v.Interface().(*ast.BindingPattern); ok && p.Name != nil {
				visit(p.Name.Value)
			}
			walk(v.Elem())
		case reflect.Struct:
			for i := 0; i < v.NumField(); i++ {
				if v.Type().Field(i).IsExported() {
					walk(v.Field(i))
				}
			}
		case reflect.Slice:
			for i := 0; i < v.Len(); i++ {
				walk(v.Index(i))
			}
		}
	}
	walk(reflect.ValueOf(node))
}

// callOnly reports whether every mention of name in body is the head of a
// call: the parameter is never stored, returned, compared, or passed on.
func callOnly(body ast.Expression, name string) bool {
	mentions, heads := 0, 0
	_ = transformSyntax(reflect.ValueOf(&body).Elem(), func(e ast.Expression) (ast.Expression, error) {
		switch x := e.(type) {
		case *ast.Identifier:
			if x.Value == name {
				mentions++
			}
		case *ast.InvocationExpression:
			if head, ok := x.Function.(*ast.Identifier); ok && head.Value == name {
				heads++
			}
		}
		return e, nil
	})
	return mentions > 0 && mentions == heads
}

// assignsAny reports whether the body rebinds any of the names: a by-value
// capture would then diverge from the caller's variable. An element store
// through a captured span (`s[i] = v`) is a write through the borrow, not a
// rebinding, and stays allowed; on a scalar or view it is the checker's
// ordinary type error.
func assignsAny(body ast.Node, names []string) bool {
	set := map[string]bool{}
	for _, n := range names {
		set[n] = true
	}
	found := false
	walkStatements(body, func(s ast.Statement) {
		switch a := s.(type) {
		case *ast.AssignmentStatement:
			if a.Name != nil && set[a.Name.Value] {
				found = true
			}
		}
	})
	return found
}

// captureTypeSpelling reports whether a declared type may be captured by
// value and returns its canonical spelling for comparing declarations: the
// scalars (closureScalarTypes), `string`, and views `[]T` and spans `[*]T`
// of a scalar — the parser spells `[]T` as an IndexExpression with the
// element on the left and an empty identifier index, `[*]T` with `*`. A
// view or span travels as the ordinary borrowed parameter it already is,
// so the borrow checker's call-local exclusivity rules judge the
// specialized call exactly as they judge a hand-written one.
func captureTypeSpelling(typeExpr ast.Expression) (string, bool) {
	switch t := typeExpr.(type) {
	case *ast.Identifier:
		if closureScalarTypes[t.Value] || t.Value == "string" {
			return t.Value, true
		}
	case *ast.IndexExpression:
		element, isIdent := t.Left.(*ast.Identifier)
		marker, isMarker := t.Index.(*ast.Identifier)
		if !t.Dot && isIdent && isMarker && closureScalarTypes[element.Value] {
			switch marker.Value {
			case "":
				return "[]" + element.Value, true
			case "*":
				return "[*]" + element.Value, true
			}
		}
	}
	return "", false
}
