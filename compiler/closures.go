package compiler

import (
	"fmt"
	"reflect"
	"sort"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
)

// Capturing closures (docs/spec/60-effects-allocation.md §11, 10-syntax.md
// §3c): static higher-order specialization.
//
// A function literal that captures enclosing locals has no representation
// in Oak — a literal is a code pointer, never an environment — and the
// checker rejects it (OAK-T0401) unless the environment's storage is
// justified. This pass justifies the one shape whose storage is already
// there: the literal is passed to a top-level Oak function whose parameter
// only ever flows into calls, and every capture is a value the caller
// holds — a scalar, a string, a view or span of a scalar, or a plain-data
// record or sum type. Then the callee is specialized for the call site —
// cloned with the function parameter removed and the captures appended as
// by-value parameters, each call through the parameter replaced by a
// direct call to the lifted literal — and the call site passes the
// captured values as ordinary arguments. A callee that forwards the
// parameter to another top-level function is specialized along with that
// function (the whole chain, once per call site; self-recursion resolves
// to the clone). A literal bound to a local first and used exactly once as
// a call argument is inlined into that call before the rewrite.
//
// The environment is the argument list: caller-owned storage that lives
// exactly as long as the call (Oak.ClosureCapture, non-escaping stack
// capture), no closure object, no allocation, no pointer into the frame,
// and the effect analysis sees a direct call. A captured view or span
// travels as the borrowed parameter it already is, so the borrow checker's
// call-local exclusivity judges the specialized call exactly as it judges
// a hand-written one; a captured record is the by-value copy a record
// parameter always is.
//
// Everything outside the shape is left untouched, so the checker's
// rejection still names the captures: a callee that stores, returns or
// compares its function parameter, a generic or extern callee, a capture
// of a Buffer-carrying or generic type or of an unannotated local, a
// capture the literal rebinds, or a bound literal mentioned more than once.

// closureScalarTypes are the scalar capture types, copied by value:
// fixed-width and platform integers, Bool, and the two arithmetic floats.
// Strings, views and spans of these, and plain-data records and sum types
// over them, are capturable too (captureTypes.spelling).
var closureScalarTypes = map[string]bool{
	"u8": true, "u16": true, "u32": true, "u64": true,
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
	types := captureTypes{adts: map[string]*ast.ADTType{}}
	for _, stmt := range program.Statements {
		switch d := stmt.(type) {
		case *ast.FunctionStatement:
			if d.Name != nil {
				functions[d.Name.Value] = d
			}
		case *ast.ADTType:
			if d.Name != nil {
				types.adts[d.Name.Value] = d
			}
		}
	}
	var added []ast.Statement
	counter := 0
	for _, stmt := range program.Statements {
		enclosing, ok := stmt.(*ast.FunctionStatement)
		if !ok || enclosing.Body == nil || enclosing.ExternSymbol != "" {
			continue
		}
		candidates := types.enclosingCaptures(enclosing)
		if len(candidates) == 0 {
			continue
		}
		inlineBoundLiterals(enclosing, candidates)
		_ = transformSyntax(reflect.ValueOf(&enclosing.Body).Elem(), func(e ast.Expression) (ast.Expression, error) {
			call, ok := e.(*ast.InvocationExpression)
			if !ok {
				return e, nil
			}
			if clones, ok := specializeCall(call, functions, candidates, counter); ok {
				added = append(added, clones...)
				counter++
			}
			return call, nil
		})
	}
	program.Statements = append(program.Statements, added...)
}

// captureTypes decides which declared types a capture may have.
type captureTypes struct {
	adts map[string]*ast.ADTType
}

// spelling reports whether a declared type may be captured by value and
// returns its canonical spelling for comparing declarations: the scalars,
// `string`, views `[]T` and spans `[*]T` of a scalar — the parser spells
// `[]T` as an IndexExpression with the element on the left and an empty
// identifier index, `[*]T` with `*` — and plain-data record and sum types
// (plain).
func (ct captureTypes) spelling(typeExpr ast.Expression) (string, bool) {
	switch t := typeExpr.(type) {
	case *ast.Identifier:
		if closureScalarTypes[t.Value] || t.Value == "string" {
			return t.Value, true
		}
		if ct.plain(t.Value, map[string]bool{}) {
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

// plain reports whether the named top-level type is plain data: a
// non-generic struct, sum type or alias whose fields and payloads are
// recursively scalars, strings, views or spans of scalars, or plain types.
// A Buffer field, a generic instantiation, a packed layout, an indexed
// result, or anything the parser spelled otherwise makes the type opaque
// to capture. A cycle through the type itself is plain (a sum type may
// refer to itself); the visiting set guards it.
func (ct captureTypes) plain(name string, visiting map[string]bool) bool {
	if visiting[name] {
		return true
	}
	decl := ct.adts[name]
	if decl == nil || len(decl.TypeParams) != 0 {
		return false
	}
	visiting[name] = true
	defer delete(visiting, name)
	component := func(typeExpr ast.Expression) bool {
		if typeExpr == nil {
			return true
		}
		if ident, ok := typeExpr.(*ast.Identifier); ok && !closureScalarTypes[ident.Value] && ident.Value != "string" {
			return ct.plain(ident.Value, visiting)
		}
		_, ok := ct.spelling(typeExpr)
		return ok
	}
	for _, variant := range decl.Variants {
		if variant == nil || variant.Result != nil {
			return false
		}
		switch shape := variant.Literal.(type) {
		case nil:
			if !component(variant.Payload) {
				return false
			}
		case *ast.RecordLiteral:
			if shape.Layout != nil && shape.Layout.Packed {
				return false
			}
			for _, field := range shape.FieldOrder {
				if field.Manifest != nil || !component(field.Value) {
					return false
				}
			}
		case *ast.Identifier:
			if !component(shape) {
				return false
			}
		default:
			return false
		}
	}
	return true
}

// enclosingCaptures maps every parameter and annotated local of the
// function to its declared type when that type is capturable. A name
// declared twice with different types, or with an uncapturable type, is
// not a candidate: capturing it stays rejected.
func (ct captureTypes) enclosingCaptures(fn *ast.FunctionStatement) map[string]ast.Expression {
	types := map[string]ast.Expression{}
	spellings := map[string]string{}
	blocked := map[string]bool{}
	note := func(name string, typeExpr ast.Expression) {
		spelled, ok := ct.spelling(typeExpr)
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

// inlineBoundLiterals moves a capturing literal bound to a local — `g :=
// fn(...)`, or with a function-type annotation — into the one call that
// passes the local as an argument, and drops the declaration, so the
// ordinary rewrite sees the literal at the call. The local must be
// mentioned exactly once outside its declaration, as a direct argument of
// a call; and neither it nor any captured name may be assigned anywhere in
// the function, so the value captured at the call is the value that was in
// scope at the binding. A local that fails a condition is left alone and
// the checker's OAK-T0401 names its captures at the binding.
func inlineBoundLiterals(fn *ast.FunctionStatement, candidates map[string]ast.Expression) {
	var bound []*ast.VariableDeclaration
	walkStatements(fn.Body, func(s ast.Statement) {
		decl, ok := s.(*ast.VariableDeclaration)
		if !ok || decl.Name == nil || decl.Value == nil {
			return
		}
		lit, isLiteral := decl.Value.(*ast.FunctionLiteral)
		if !isLiteral || (len(lit.Parameters) == 0 && lit.ReturnType == nil) || lit.Body == nil {
			return
		}
		if decl.Type != nil {
			if _, isFunctionType := decl.Type.(*ast.FunctionTypeExpression); !isFunctionType {
				return
			}
		}
		if len(literalCaptures(lit, candidates)) != 0 {
			bound = append(bound, decl)
		}
	})
	for _, decl := range bound {
		name := decl.Name.Value
		lit := decl.Value.(*ast.FunctionLiteral)
		if assignsAny(fn.Body, append([]string{name}, literalCaptures(lit, candidates)...)) {
			continue
		}
		mentions, asArgument := 0, 0
		var site *ast.InvocationExpression
		position := -1
		_ = transformSyntax(reflect.ValueOf(&fn.Body).Elem(), func(e ast.Expression) (ast.Expression, error) {
			switch x := e.(type) {
			case *ast.Identifier:
				if x.Value == name {
					mentions++
				}
			case *ast.InvocationExpression:
				for i, arg := range x.Arguments {
					if id, ok := arg.(*ast.Identifier); ok && id.Value == name {
						asArgument++
						site, position = x, i
					}
				}
			}
			return e, nil
		})
		// The declaration's own name is not visited (VariableDeclaration.Name
		// is an *Identifier field, not an Expression), so the count is the
		// uses alone.
		if mentions != 1 || asArgument != 1 || site == nil {
			continue
		}
		site.Arguments[position] = lit
		removeStatement(fn.Body, decl)
	}
}

// removeStatement drops the statement (by identity) from whichever block
// under node holds it.
func removeStatement(node ast.Node, target ast.Statement) {
	var walk func(v reflect.Value)
	walk = func(v reflect.Value) {
		switch v.Kind() {
		case reflect.Interface, reflect.Pointer:
			if v.IsNil() {
				return
			}
			if block, ok := v.Interface().(*ast.BlockStatement); ok {
				kept := block.Statements[:0]
				for _, s := range block.Statements {
					if s != target {
						kept = append(kept, s)
					}
				}
				block.Statements = kept
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
// literal and the specialized callees (the whole forwarding chain) to
// append to the program.
func specializeCall(call *ast.InvocationExpression, functions map[string]*ast.FunctionStatement, candidates map[string]ast.Expression, counter int) ([]ast.Statement, bool) {
	calleeIdent, isIdent := call.Function.(*ast.Identifier)
	if !isIdent {
		return nil, false
	}
	callee := functions[calleeIdent.Value]
	if !specializable(callee) || len(callee.Parameters) != len(call.Arguments) {
		return nil, false
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
			return nil, false // two capturing literals in one call: not this increment
		}
		position, literal, captures = i, lit, names
	}
	if literal == nil || len(literal.Parameters) == 0 && literal.ReturnType == nil || literal.Body == nil {
		return nil, false
	}
	if !parameterFlowsIntoCalls(callee, position, functions, map[string]bool{}) || assignsAny(literal.Body, captures) {
		return nil, false
	}

	spec := &specialization{
		functions:  functions,
		candidates: candidates,
		captures:   captures,
		counter:    counter,
		tok:        literal.Token,
		clones:     map[string]string{},
	}

	// The literal, lifted, with the captures as trailing parameters: its
	// body already names them.
	spec.litName = fmt.Sprintf("0clos_lit_%d", counter)
	lifted := &ast.FunctionStatement{
		Token:      literal.Token,
		EndToken:   literal.Token,
		Name:       spec.ident(spec.litName),
		Parameters: append(append([]*ast.FunctionParameter{}, literal.Parameters...), spec.captureParams()...),
		ReturnType: literal.ReturnType,
		Body:       &ast.BlockExpression{Token: literal.Token, Block: literal.Body},
	}
	spec.added = append(spec.added, lifted)

	cloneName := spec.cloneOf(callee, position)

	// The call site: the literal's slot removed, the captured values passed.
	call.Function = spec.ident(cloneName)
	args := make([]ast.Expression, 0, len(call.Arguments)+len(captures)-1)
	for i, arg := range call.Arguments {
		if i != position {
			args = append(args, arg)
		}
	}
	for _, name := range captures {
		args = append(args, spec.ident(name))
	}
	call.Arguments = args
	return spec.added, true
}

// specializable reports whether a callee may be cloned: a top-level Oak
// function with a body, no type parameters, no receiver, no foreign, asm,
// kernel or theorem body.
func specializable(callee *ast.FunctionStatement) bool {
	return callee != nil && callee.Body != nil && callee.ExternSymbol == "" && !callee.AsmBacked && !callee.Kernel &&
		!callee.Theorem && len(callee.TypeParams) == 0 && callee.Receiver == nil && callee.Name != nil
}

// specialization carries one call site's rewrite: the lifted literal's name,
// the captures, and the clones made so far (callee name and parameter
// position → clone name), so a forwarding chain is cloned once and a
// recursive forward resolves to the clone under construction.
type specialization struct {
	functions  map[string]*ast.FunctionStatement
	candidates map[string]ast.Expression
	captures   []string
	counter    int
	tok        token.Token
	litName    string
	clones     map[string]string
	added      []ast.Statement
}

func (s *specialization) ident(name string) *ast.Identifier {
	t := s.tok
	t.Literal = name
	return &ast.Identifier{Token: t, Value: name}
}

func (s *specialization) captureParams() []*ast.FunctionParameter {
	params := make([]*ast.FunctionParameter, 0, len(s.captures))
	for _, name := range s.captures {
		params = append(params, &ast.FunctionParameter{Token: s.tok, Name: s.ident(name), Type: cloneExpression(s.candidates[name])})
	}
	return params
}

// cloneOf returns the name of the callee's clone for the function parameter
// at position, making it if needed: the parameter removed, the captures
// appended, every call through the parameter a direct call to the lifted
// literal, every forward of the parameter a call to that callee's clone.
func (s *specialization) cloneOf(callee *ast.FunctionStatement, position int) string {
	key := fmt.Sprintf("%s#%d", callee.Name.Value, position)
	if name, done := s.clones[key]; done {
		return name
	}
	cloneName := fmt.Sprintf("0clos_%d_%s", s.counter, callee.Name.Value)
	if len(s.clones) != 0 {
		cloneName = fmt.Sprintf("0clos_%d_%d_%s", s.counter, len(s.clones), callee.Name.Value)
	}
	s.clones[key] = cloneName
	fname := callee.Parameters[position].Name.Value

	clone := cloneSyntax(reflect.ValueOf(callee)).Interface().(*ast.FunctionStatement)
	clone.Name = s.ident(cloneName)
	clone.Exported, clone.Opaque = false, false
	params := make([]*ast.FunctionParameter, 0, len(clone.Parameters)+len(s.captures)-1)
	for i, p := range clone.Parameters {
		if i != position {
			params = append(params, p)
		}
	}
	clone.Parameters = append(params, s.captureParams()...)
	_ = transformSyntax(reflect.ValueOf(&clone.Body).Elem(), func(e ast.Expression) (ast.Expression, error) {
		inner, isCall := e.(*ast.InvocationExpression)
		if !isCall {
			return e, nil
		}
		head, isHead := inner.Function.(*ast.Identifier)
		if !isHead {
			return e, nil
		}
		if head.Value == fname {
			inner.Function = s.ident(s.litName)
			for _, name := range s.captures {
				inner.Arguments = append(inner.Arguments, s.ident(name))
			}
			return inner, nil
		}
		// A forward: the parameter passed on to another function at some
		// position — that function's clone takes the captures instead.
		forwardAt := -1
		for i, arg := range inner.Arguments {
			if id, ok := arg.(*ast.Identifier); ok && id.Value == fname {
				forwardAt = i
			}
		}
		if forwardAt == -1 {
			return e, nil
		}
		target := s.functions[head.Value]
		if target == nil {
			return e, nil
		}
		inner.Function = s.ident(s.cloneOf(target, forwardAt))
		args := make([]ast.Expression, 0, len(inner.Arguments)+len(s.captures)-1)
		for i, arg := range inner.Arguments {
			if i != forwardAt {
				args = append(args, arg)
			}
		}
		for _, name := range s.captures {
			args = append(args, s.ident(name))
		}
		inner.Arguments = args
		return inner, nil
	})
	s.added = append(s.added, clone)
	return cloneName
}

// parameterFlowsIntoCalls reports whether every mention of the callee's
// function parameter at position is either the head of a call or a direct
// argument to a call of another specializable top-level function at a
// position whose own parameter flows into calls the same way. The
// parameter is never stored, returned, compared, or captured. A cycle —
// self-recursion passing the parameter along — is accepted: its clone
// resolves to itself. A call passing the parameter twice is refused.
func parameterFlowsIntoCalls(callee *ast.FunctionStatement, position int, functions map[string]*ast.FunctionStatement, visiting map[string]bool) bool {
	if !specializable(callee) || position < 0 || position >= len(callee.Parameters) {
		return false
	}
	param := callee.Parameters[position]
	if param == nil || param.Name == nil || param.Variadic {
		return false
	}
	if _, isFunctionType := param.Type.(*ast.FunctionTypeExpression); !isFunctionType {
		return false
	}
	key := fmt.Sprintf("%s#%d", callee.Name.Value, position)
	if visiting[key] {
		return true
	}
	visiting[key] = true
	name := param.Name.Value
	mentions, accounted := 0, 0
	ok := true
	body := callee.Body
	_ = transformSyntax(reflect.ValueOf(&body).Elem(), func(e ast.Expression) (ast.Expression, error) {
		switch x := e.(type) {
		case *ast.Identifier:
			if x.Value == name {
				mentions++
			}
		case *ast.InvocationExpression:
			if head, isHead := x.Function.(*ast.Identifier); isHead && head.Value == name {
				accounted++
				return e, nil
			}
			forwards := 0
			forwardAt := -1
			for i, arg := range x.Arguments {
				if id, isIdent := arg.(*ast.Identifier); isIdent && id.Value == name {
					forwards++
					forwardAt = i
				}
			}
			if forwards == 0 {
				return e, nil
			}
			var target *ast.FunctionStatement
			if head, isHead := x.Function.(*ast.Identifier); isHead {
				target = functions[head.Value]
			}
			if forwards != 1 || target == nil || len(target.Parameters) != len(x.Arguments) ||
				!parameterFlowsIntoCalls(target, forwardAt, functions, visiting) {
				ok = false
				return e, nil
			}
			accounted++
		}
		return e, nil
	})
	return ok && mentions > 0 && mentions == accounted
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
		if a, ok := s.(*ast.AssignmentStatement); ok && a.Name != nil && set[a.Name.Value] {
			found = true
		}
	})
	return found
}
