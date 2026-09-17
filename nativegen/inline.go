package nativegen

import (
	"fmt"
	"reflect"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
)

// Vector-helper inlining for the native lane (docs/spec/94-assembler.md
// section 9). The source-level inliner (compiler/inline.go) expands scalar
// leaf helpers for both backends; the vector helpers of a SIMD kernel —
// functions whose signature carries a fixed vector, calling each other in
// a tree the C compiler flattens into one loop — are expanded here, on the
// native lane only, before lowering. A call `f(a, b)` becomes a block that
// binds each parameter to its argument (a plain identifier argument the
// callee never assigns substitutes directly, so no copy is made) and runs
// the callee's body with every bound name renamed apart; a call in
// statement position splices the block. The verifier compares the lowering
// with the original body, so the expansion must preserve meaning, and it
// does: a call is exactly that binding. With registers released at a
// local's last use (nativegen/liveness.go) the flattened kernel's vectors
// stay in registers. Refused: recursion, receivers, type parameters,
// variadic parameters, extern or asm bodies, matches that bind payloads.

const (
	inlineDepth  = 6
	inlineBudget = 800 // statements added per function
)

type inliner struct {
	functions map[string]*ast.FunctionStatement
	root      string
	stack     []string
	counter   int
	added     int
}

// inlineBody returns fn's body with the vector helpers it calls expanded,
// or the body itself when nothing applies.
func inlineBody(fn *ast.FunctionStatement, functions map[string]*ast.FunctionStatement) ast.Expression {
	if fn.Body == nil || !mentionsInlinableCall(fn.Body, functions) {
		return fn.Body
	}
	in := &inliner{functions: functions, root: fn.Name.Value}
	return in.expr(cloneNode(fn.Body).(ast.Expression))
}

// mentionsInlinableCall reports a call to a vector helper or to a small
// aggregate helper (aggregateHelper) anywhere in the body.
func mentionsInlinableCall(body ast.Node, functions map[string]*ast.FunctionStatement) bool {
	found := false
	walk(body, func(n ast.Node) {
		if call, ok := n.(*ast.InvocationExpression); ok {
			if ident, isIdent := call.Function.(*ast.Identifier); isIdent {
				if callee, declared := functions[ident.Value]; declared && (VectorContract(callee) || aggregateHelper(callee)) {
					found = true
				}
			}
		}
	})
	return found
}

// aggregateHelper reports a small helper that takes or returns a record or
// an owned array — the shape the source-level inliner leaves alone, since
// an aggregate temporary is a binding of its own there — expanded on the
// native lane only (docs/spec/94-assembler.md §9 "Aggregate helpers"): a
// body of at most aggregateInlineStatements statements and no loop, every
// parameter a scalar, record, owned array, span, or view, the result a
// scalar, record, or owned array (or unit), no dispatch, no effects row.
// The call's copies and the callee's prologue and epilogue go; the
// verifier still compares against the body as written, the callee taken
// at its Oak body.
func aggregateHelper(fn *ast.FunctionStatement) bool {
	if fn == nil || fn.Body == nil || fn.Name == nil || fn.Name.Value == "main" || fn.Receiver != nil || len(fn.TypeParams) > 0 || fn.ExternSymbol != "" || fn.AsmBacked || len(fn.Dispatch) > 0 || len(fn.Effects) > 0 || fn.EffectsDeclared || len(fn.Forbids) > 0 || fn.Kernel || fn.Theorem {
		return false
	}
	aggregate := false
	for _, p := range fn.Parameters {
		if p == nil || p.Variadic || p.Type == nil || p.Name == nil {
			return false
		}
		switch {
		case isScalarSyntax(p.Type):
		case isAggregateSyntax(p.Type):
			aggregate = true
		case isSpanSyntax(p.Type):
		default:
			return false
		}
	}
	if fn.ReturnType != nil && fn.ReturnType.String() != "()" {
		switch {
		case isScalarSyntax(fn.ReturnType):
		case isAggregateSyntax(fn.ReturnType):
			aggregate = true
		default:
			return false
		}
	}
	if !aggregate {
		return false
	}
	statements := 1
	if block, isBlock := fn.Body.(*ast.BlockExpression); isBlock {
		if block.Block == nil {
			return false
		}
		statements = len(block.Block.Statements)
	}
	if statements > aggregateInlineStatements {
		return false
	}
	loops := false
	walk(fn.Body, func(n ast.Node) {
		switch n.(type) {
		case *ast.WhileStatement, *ast.FunctionLiteral:
			loops = true
		}
	})
	return !loops
}

// aggregateInlineStatements bounds the body of an aggregate helper the
// native lane expands.
const aggregateInlineStatements = 8

// isScalarSyntax reports a type spelling a builtin scalar.
func isScalarSyntax(typ ast.Expression) bool {
	_, ok := scalarOf(typ)
	return ok
}

// isAggregateSyntax reports a type spelling a record or union by name (any
// identifier that is not a scalar; the lowering refuses a name it cannot
// place) or an owned array `[N]T`.
func isAggregateSyntax(typ ast.Expression) bool {
	if isScalarSyntax(typ) {
		return false
	}
	if _, isName := typ.(*ast.Identifier); isName {
		return true
	}
	if _, ok := asm.TypeApplicationName(typ); ok {
		if index, isIndex := typ.(*ast.IndexExpression); !isIndex || index.Dot {
			return true
		}
	}
	index, isIndex := typ.(*ast.IndexExpression)
	if !isIndex || index.Dot {
		return false
	}
	n, isLit := index.Index.(*ast.IntegerLiteral)
	return isLit && n.Value > 0
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

// writableSpanParam reports a parameter of span type `[*]T`, through which
// a callee reaches the caller's memory.
func writableSpanParam(fn *ast.FunctionStatement) bool {
	for _, p := range fn.Parameters {
		if index, isIndex := p.Type.(*ast.IndexExpression); isIndex && !index.Dot {
			if marker, isMarker := index.Index.(*ast.Identifier); isMarker && marker.Value == "*" {
				return true
			}
		}
	}
	return false
}

// fieldPath reports an argument that is a field path rooted at a local:
// `next.h`, `a.b.c` (no element index along the way), and the root's name.
func fieldPath(expr ast.Expression) (string, bool) {
	for {
		switch e := expr.(type) {
		case *ast.Identifier:
			return e.Value, true
		case *ast.IndexExpression:
			if !e.Dot {
				return "", false
			}
			expr = e.Left
		default:
			return "", false
		}
	}
}

// mentionsName reports a free mention of a name anywhere in a node.
func mentionsIdentifier(node ast.Node, name string) bool {
	found := false
	walk(node, func(n ast.Node) {
		if id, isIdent := n.(*ast.Identifier); isIdent && id.Value == name {
			found = true
		}
	})
	return found
}

// inlinable decides whether a callee is expanded at a call site.
func (in *inliner) inlinable(name string) (*ast.FunctionStatement, bool) {
	callee, declared := in.functions[name]
	if !declared || callee.Body == nil || callee.Receiver != nil || len(callee.TypeParams) > 0 || callee.ExternSymbol != "" || callee.AsmBacked {
		return nil, false
	}
	if (!VectorContract(callee) && !aggregateHelper(callee)) || name == in.root || len(in.stack) >= inlineDepth {
		return nil, false
	}
	for _, active := range in.stack {
		if active == name {
			return nil, false
		}
	}
	for _, p := range callee.Parameters {
		if p.Variadic || p.Type == nil || p.Name == nil {
			return nil, false
		}
	}
	if callee.ReturnType == nil || !bodyInlinable(callee.Body) {
		return nil, false
	}
	statements := 1
	if block, isBlock := callee.Body.(*ast.BlockExpression); isBlock {
		if block.Block == nil {
			return nil, false
		}
		statements = len(block.Block.Statements)
	}
	return callee, in.added+statements <= inlineBudget
}

// bodyInlinable refuses bodies whose matches bind payloads (their bound
// names are not collected for renaming).
func bodyInlinable(body ast.Node) bool {
	ok := true
	walk(body, func(n ast.Node) {
		if m, isMatch := n.(*ast.MatchExpression); isMatch {
			if _, _, isBool := boolConditional(m); !isBool {
				ok = false
			}
		}
	})
	return ok
}

func (in *inliner) expr(e ast.Expression) ast.Expression {
	switch x := e.(type) {
	case nil:
		return nil
	case *ast.InvocationExpression:
		for i := range x.Arguments {
			x.Arguments[i] = in.expr(x.Arguments[i])
		}
		ident, isIdent := x.Function.(*ast.Identifier)
		if !isIdent {
			return x
		}
		callee, ok := in.inlinable(ident.Value)
		if !ok || len(callee.Parameters) != len(x.Arguments) || callee.ReturnType.String() == "()" {
			return x
		}
		return in.expand(callee, x)
	case *ast.InfixExpression:
		x.Left, x.Right = in.expr(x.Left), in.expr(x.Right)
	case *ast.PrefixExpression:
		x.Right = in.expr(x.Right)
	case *ast.IndexExpression:
		x.Left = in.expr(x.Left)
		if !x.Dot {
			x.Index = in.expr(x.Index)
		}
	case *ast.MatchExpression:
		x.Scrutinee = in.expr(x.Scrutinee)
		for i := range x.Arms {
			x.Arms[i].Body = in.expr(x.Arms[i].Body)
		}
	case *ast.BlockExpression:
		if x.Block != nil {
			x.Block.Statements = in.statements(x.Block.Statements)
		}
	}
	return e
}

func (in *inliner) statements(stmts []ast.Statement) []ast.Statement {
	var out []ast.Statement
	for _, stmt := range stmts {
		switch s := stmt.(type) {
		case *ast.ExpressionStatement:
			if call, isCall := s.Expression.(*ast.InvocationExpression); isCall && !s.Discard {
				for i := range call.Arguments {
					call.Arguments[i] = in.expr(call.Arguments[i])
				}
				if ident, isIdent := call.Function.(*ast.Identifier); isIdent {
					if callee, ok := in.inlinable(ident.Value); ok && len(callee.Parameters) == len(call.Arguments) && callee.ReturnType.String() == "()" {
						out = append(out, in.expand(callee, call).Block.Statements...)
						continue
					}
				}
			}
			s.Expression = in.expr(s.Expression)
			out = append(out, s)
		case *ast.VariableDeclaration:
			s.Value = in.expr(s.Value)
			out = append(out, s)
		case *ast.AssignmentStatement:
			if call, isCall := s.Value.(*ast.InvocationExpression); isCall && s.Name != nil {
				if ident, isIdent := call.Function.(*ast.Identifier); isIdent {
					if callee, ok := in.inlinable(ident.Value); ok && len(callee.Parameters) == len(call.Arguments) {
						if at, inPlace := inPlaceParameter(callee, call, s.Name.Value); inPlace {
							for i := range call.Arguments {
								call.Arguments[i] = in.expr(call.Arguments[i])
							}
							out = append(out, in.expandInPlace(callee, call, at, s.Name.Value)...)
							continue
						}
					}
				}
			}
			s.Value = in.expr(s.Value)
			out = append(out, s)
		case *ast.IndexAssignmentStatement:
			s.Value = in.expr(s.Value)
			out = append(out, s)
		case *ast.WhileStatement:
			s.Condition = in.expr(s.Condition)
			if s.Body != nil {
				s.Body.Statements = in.statements(s.Body.Statements)
			}
			out = append(out, s)
		case *ast.IfStatement:
			s.Condition = in.expr(s.Condition)
			if s.Consequence != nil {
				s.Consequence.Statements = in.statements(s.Consequence.Statements)
			}
			in.alternative(s.Alternative)
			out = append(out, s)
		default:
			out = append(out, stmt)
		}
	}
	return out
}

func (in *inliner) alternative(alt ast.Statement) {
	switch a := alt.(type) {
	case *ast.BlockStatement:
		a.Statements = in.statements(a.Statements)
	case *ast.IfStatement:
		a.Condition = in.expr(a.Condition)
		if a.Consequence != nil {
			a.Consequence.Statements = in.statements(a.Consequence.Statements)
		}
		in.alternative(a.Alternative)
	}
}

// expand builds the block for one call: parameters bound to their
// arguments in order — an identifier argument the callee never assigns
// substitutes for the parameter, the others are declared — then the
// renamed body's statements, its result last.
func (in *inliner) expand(callee *ast.FunctionStatement, call *ast.InvocationExpression) *ast.BlockExpression {
	in.counter++
	prefix := fmt.Sprintf("inl%d_", in.counter)
	body := cloneNode(callee.Body).(ast.Expression)
	assigned := map[string]bool{}
	walk(body, func(n ast.Node) {
		if a, isAssign := n.(*ast.AssignmentStatement); isAssign && a.Name != nil {
			assigned[a.Name.Value] = true
		}
	})
	rename := map[string]string{}
	substitute := map[string]ast.Expression{}
	var declared []*ast.VariableDeclaration
	for i, p := range callee.Parameters {
		// An aggregate parameter substitutes only when the callee never
		// assigns, borrows, or addresses it — a field store `p.f = x` into
		// a substituted record would write the caller's variable — and no
		// parameter is a writable span the callee could reach it through.
		readOnly := !isAggregateSyntax(p.Type) || (!recordParamTouched(callee, p.Name.Value) && !writableSpanParam(callee))
		if arg, isIdent := call.Arguments[i].(*ast.Identifier); isIdent && !assigned[p.Name.Value] && readOnly {
			rename[p.Name.Value] = arg.Value
			continue
		}
		if element, isElement := in.ownedElementRead(call.Arguments[i]); isElement && isScalarSyntax(p.Type) && !assigned[p.Name.Value] && !writableSpanParam(callee) {
			// A constant-index read of the caller's owned array (`v[0]`)
			// to a scalar parameter the callee never assigns, with no
			// writable span through which the callee could reach the
			// array: the read stands for the parameter at every use
			// (Oak.Inlining.eval_subst), no copy — the array is the
			// caller's, which nothing in the callee names or addresses.
			rename[p.Name.Value] = prefix + p.Name.Value
			substitute[prefix+p.Name.Value] = element
			continue
		}
		if root, isPath := fieldPath(call.Arguments[i]); isPath && isAggregateSyntax(p.Type) && readOnly && !mentionsIdentifier(callee.Body, root) {
			// A field path (`next.h`) to a parameter the callee never
			// assigns, borrows, or addresses, with no writable span
			// through which the callee could reach the path's storage:
			// the path stands for the parameter at every use (§9
			// "Aggregate helpers"; Oak.Inlining.eval_subst), no copy.
			rename[p.Name.Value] = prefix + p.Name.Value
			substitute[prefix+p.Name.Value] = call.Arguments[i]
			continue
		}
		rename[p.Name.Value] = prefix + p.Name.Value
		declared = append(declared, &ast.VariableDeclaration{Token: call.Token, Name: &ast.Identifier{Token: p.Name.Token, Value: prefix + p.Name.Value}, Type: cloneNode(p.Type).(ast.Expression), Value: call.Arguments[i]})
	}
	walk(body, func(n ast.Node) {
		if d, isDecl := n.(*ast.VariableDeclaration); isDecl && d.Name != nil {
			rename[d.Name.Value] = prefix + d.Name.Value
		}
	})
	renameBound(body, rename)
	if len(substitute) > 0 {
		substituteBound(body, substitute)
	}
	block := &ast.BlockExpression{Token: call.Token, Block: &ast.BlockStatement{Token: call.Token}}
	for _, d := range declared {
		block.Block.Statements = append(block.Block.Statements, d)
	}
	in.added += len(declared)
	in.stack = append(in.stack, callee.Name.Value)
	if inner, isBlock := body.(*ast.BlockExpression); isBlock && inner.Block != nil {
		inner.Block.Statements = in.statements(inner.Block.Statements)
		block.Block.Statements = append(block.Block.Statements, inner.Block.Statements...)
		in.added += len(inner.Block.Statements)
	} else {
		block.Block.Statements = append(block.Block.Statements, &ast.ExpressionStatement{Token: call.Token, Expression: in.expr(body)})
		in.added++
	}
	in.stack = in.stack[:len(in.stack)-1]
	return block
}

// renameBound applies the renaming to every identifier except field names
// (`p.x`), which are not bindings.
func renameBound(node ast.Node, rename map[string]string) {
	var visit func(v reflect.Value, fieldOfDot bool)
	visit = func(v reflect.Value, fieldOfDot bool) {
		switch v.Kind() {
		case reflect.Interface, reflect.Pointer:
			if v.IsNil() {
				return
			}
			if id, ok := v.Interface().(*ast.Identifier); ok {
				if to, bound := rename[id.Value]; bound && !fieldOfDot {
					id.Value = to
				}
				return
			}
			if access, ok := v.Interface().(*ast.IndexExpression); ok {
				visit(reflect.ValueOf(access.Left), false)
				visit(reflect.ValueOf(access.Index), access.Dot)
				return
			}
			visit(v.Elem(), false)
		case reflect.Struct:
			for i := 0; i < v.NumField(); i++ {
				if v.Type().Field(i).IsExported() {
					visit(v.Field(i), false)
				}
			}
		case reflect.Slice:
			for i := 0; i < v.Len(); i++ {
				visit(v.Index(i), false)
			}
		case reflect.Map:
			iter := v.MapRange()
			for iter.Next() {
				visit(iter.Value(), false)
			}
		}
	}
	visit(reflect.ValueOf(node), false)
}

// substituteBound replaces every expression-position identifier naming a
// key of subst with a fresh copy of its expression; field names (`p.x`) and
// binding positions (typed *ast.Identifier fields) are left alone.
func substituteBound(node ast.Node, subst map[string]ast.Expression) {
	var visit func(v reflect.Value, fieldOfDot bool)
	visit = func(v reflect.Value, fieldOfDot bool) {
		switch v.Kind() {
		case reflect.Interface:
			if v.IsNil() {
				return
			}
			if id, ok := v.Interface().(*ast.Identifier); ok {
				if to, bound := subst[id.Value]; bound && !fieldOfDot && v.CanSet() {
					v.Set(reflect.ValueOf(cloneNode(to)))
				}
				return
			}
			if access, ok := v.Interface().(*ast.IndexExpression); ok {
				visit(reflect.ValueOf(access).Elem().FieldByName("Left"), false)
				visit(reflect.ValueOf(access).Elem().FieldByName("Index"), access.Dot)
				return
			}
			visit(v.Elem(), false)
		case reflect.Pointer:
			if v.IsNil() {
				return
			}
			if _, ok := v.Interface().(*ast.Identifier); ok {
				return // a typed identifier field: a binding or a field name
			}
			visit(v.Elem(), false)
		case reflect.Struct:
			for i := 0; i < v.NumField(); i++ {
				if v.Type().Field(i).IsExported() {
					visit(v.Field(i), false)
				}
			}
		case reflect.Slice:
			for i := 0; i < v.Len(); i++ {
				visit(v.Index(i), false)
			}
		case reflect.Map:
			iter := v.MapRange()
			for iter.Next() {
				visit(iter.Value(), false)
			}
		}
	}
	visit(reflect.ValueOf(node), false)
}

// cloneNode deep-copies syntax so an expansion never shares nodes with the
// callee's declaration.
func cloneNode(node ast.Node) ast.Node {
	return cloneValue(reflect.ValueOf(node)).Interface().(ast.Node)
}

func cloneValue(v reflect.Value) reflect.Value {
	switch v.Kind() {
	case reflect.Interface:
		if v.IsNil() {
			return reflect.Zero(v.Type())
		}
		out := reflect.New(v.Type()).Elem()
		out.Set(cloneValue(v.Elem()))
		return out
	case reflect.Pointer:
		if v.IsNil() {
			return reflect.Zero(v.Type())
		}
		out := reflect.New(v.Type().Elem())
		out.Elem().Set(cloneValue(v.Elem()))
		return out
	case reflect.Struct:
		out := reflect.New(v.Type()).Elem()
		out.Set(v)
		for i := 0; i < v.NumField(); i++ {
			if out.Field(i).CanSet() && v.Type().Field(i).IsExported() {
				out.Field(i).Set(cloneValue(v.Field(i)))
			}
		}
		return out
	case reflect.Slice:
		if v.IsNil() {
			return reflect.Zero(v.Type())
		}
		out := reflect.MakeSlice(v.Type(), v.Len(), v.Len())
		for i := 0; i < v.Len(); i++ {
			out.Index(i).Set(cloneValue(v.Index(i)))
		}
		return out
	case reflect.Map:
		if v.IsNil() {
			return reflect.Zero(v.Type())
		}
		out := reflect.MakeMapWithSize(v.Type(), v.Len())
		iter := v.MapRange()
		for iter.Next() {
			out.SetMapIndex(iter.Key(), cloneValue(iter.Value()))
		}
		return out
	}
	return v
}

// ownedElementRead recognizes an argument that reads an element of the
// root function's owned array — a local or parameter of type `[N]T` — at
// a constant index: the expression to substitute for the parameter.
func (in *inliner) ownedElementRead(arg ast.Expression) (ast.Expression, bool) {
	index, isIndex := arg.(*ast.IndexExpression)
	if !isIndex || index.Dot {
		return nil, false
	}
	base, isIdent := index.Left.(*ast.Identifier)
	if !isIdent {
		return nil, false
	}
	if _, isConst := constantValue(index.Index); !isConst {
		return nil, false
	}
	root := in.functions[in.root]
	if root == nil {
		return nil, false
	}
	owned := func(typ ast.Expression) bool {
		return isAggregateSyntax(typ) && !isSpanSyntax(typ) && isArraySyntax(typ)
	}
	for _, p := range root.Parameters {
		if p != nil && p.Name != nil && p.Name.Value == base.Value {
			if owned(p.Type) {
				return arg, true
			}
			return nil, false
		}
	}
	found := false
	walk(root.Body, func(n ast.Node) {
		if d, isDecl := n.(*ast.VariableDeclaration); isDecl && d.Name != nil && d.Name.Value == base.Value && d.Type != nil && owned(d.Type) {
			found = true
		}
	})
	return arg, found
}

// isArraySyntax reports an owned array type `[N]T`, N a literal.
func isArraySyntax(typ ast.Expression) bool {
	index, isIndex := typ.(*ast.IndexExpression)
	if !isIndex || index.Dot {
		return false
	}
	n, isLit := index.Index.(*ast.IntegerLiteral)
	return isLit && n.Value > 0
}

// inPlaceParameter recognizes `v = f(…, v, …)` where f copies that
// parameter into the local it returns and never reads it again:
//
//	f: (state: T, …): T { next: T = state; …; next }
//
// The parameter is mentioned exactly once, as the whole initializer of
// f's return-slot local (returnSlotLocal); no other argument mentions v.
// Expanded in place (expandInPlace), the call's copy in and copy out are
// identities on v and go: the body runs on the caller's variable itself.
// The index of that parameter is returned.
func inPlaceParameter(callee *ast.FunctionStatement, call *ast.InvocationExpression, target string) (int, bool) {
	slot := returnSlotLocal(callee)
	if slot == "" {
		return 0, false
	}
	at := -1
	for i, arg := range call.Arguments {
		if isName(arg, target) {
			if at >= 0 {
				return 0, false
			}
			at = i
		} else if mentionsName(arg, target) {
			return 0, false
		}
	}
	if at < 0 {
		return 0, false
	}
	param := callee.Parameters[at].Name.Value
	if !isAggregateSyntax(callee.Parameters[at].Type) || callee.Parameters[at].Type.String() != callee.ReturnType.String() {
		return 0, false
	}
	mentions := 0
	walk(callee.Body, func(n ast.Node) {
		if id, isId := n.(*ast.Identifier); isId && id.Value == param {
			mentions++
		}
	})
	block, isBlock := callee.Body.(*ast.BlockExpression)
	if mentions != 1 || !isBlock || block.Block == nil {
		return 0, false
	}
	for _, stmt := range block.Block.Statements {
		if decl, isDecl := stmt.(*ast.VariableDeclaration); isDecl && decl.Name != nil && decl.Name.Value == slot {
			return at, isName(decl.Value, param)
		}
	}
	return 0, false
}

// expandInPlace splices `target = f(args)` as f's body run on target: the
// other parameters bind as expand binds them, the return-slot local is
// renamed to target and its declaration from the parameter dropped (an
// identity copy), and the trailing result expression dropped (an
// identity assignment). What remains reads and writes target where f read
// and wrote its copy — the same values, since f never read the parameter
// again (inPlaceParameter).
func (in *inliner) expandInPlace(callee *ast.FunctionStatement, call *ast.InvocationExpression, at int, target string) []ast.Statement {
	in.counter++
	prefix := fmt.Sprintf("inl%d_", in.counter)
	body := cloneNode(callee.Body).(*ast.BlockExpression)
	slot := returnSlotLocal(callee)
	assigned := map[string]bool{}
	walk(body, func(n ast.Node) {
		if a, isAssign := n.(*ast.AssignmentStatement); isAssign && a.Name != nil {
			assigned[a.Name.Value] = true
		}
	})
	rename := map[string]string{slot: target}
	substitute := map[string]ast.Expression{}
	var declared []*ast.VariableDeclaration
	for i, p := range callee.Parameters {
		if i == at {
			continue // read once, by the dropped declaration
		}
		readOnly := !isAggregateSyntax(p.Type) || (!recordParamTouched(callee, p.Name.Value) && !writableSpanParam(callee))
		if arg, isIdent := call.Arguments[i].(*ast.Identifier); isIdent && !assigned[p.Name.Value] && readOnly {
			rename[p.Name.Value] = arg.Value
			continue
		}
		if element, isElement := in.ownedElementRead(call.Arguments[i]); isElement && isScalarSyntax(p.Type) && !assigned[p.Name.Value] && !writableSpanParam(callee) {
			rename[p.Name.Value] = prefix + p.Name.Value
			substitute[prefix+p.Name.Value] = element
			continue
		}
		rename[p.Name.Value] = prefix + p.Name.Value
		declared = append(declared, &ast.VariableDeclaration{Token: call.Token, Name: &ast.Identifier{Token: p.Name.Token, Value: prefix + p.Name.Value}, Type: cloneNode(p.Type).(ast.Expression), Value: call.Arguments[i]})
	}
	walk(body, func(n ast.Node) {
		if d, isDecl := n.(*ast.VariableDeclaration); isDecl && d.Name != nil && d.Name.Value != slot {
			rename[d.Name.Value] = prefix + d.Name.Value
		}
	})
	renameBound(body, rename)
	if len(substitute) > 0 {
		substituteBound(body, substitute)
	}
	var out []ast.Statement
	for _, d := range declared {
		out = append(out, d)
	}
	in.added += len(declared)
	in.stack = append(in.stack, callee.Name.Value)
	stmts := body.Block.Statements
	stmts = stmts[:len(stmts)-1] // the trailing `next`, now `target = target`
	var kept []ast.Statement
	for _, stmt := range stmts {
		if decl, isDecl := stmt.(*ast.VariableDeclaration); isDecl && decl.Name != nil && decl.Name.Value == target {
			continue // `next: T = state`, now an identity copy
		}
		kept = append(kept, stmt)
	}
	kept = in.statements(kept)
	out = append(out, kept...)
	in.added += len(kept)
	in.stack = in.stack[:len(in.stack)-1]
	return out
}
