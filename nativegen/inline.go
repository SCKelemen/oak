package nativegen

import (
	"fmt"
	"reflect"

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
	if fn.Body == nil || !mentionsVectorCall(fn.Body, functions) {
		return fn.Body
	}
	in := &inliner{functions: functions, root: fn.Name.Value}
	return in.expr(cloneNode(fn.Body).(ast.Expression))
}

func mentionsVectorCall(body ast.Node, functions map[string]*ast.FunctionStatement) bool {
	found := false
	walk(body, func(n ast.Node) {
		if call, ok := n.(*ast.InvocationExpression); ok {
			if ident, isIdent := call.Function.(*ast.Identifier); isIdent {
				if callee, declared := functions[ident.Value]; declared && VectorContract(callee) {
					found = true
				}
			}
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
	if !VectorContract(callee) || name == in.root || len(in.stack) >= inlineDepth {
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
	var declared []*ast.VariableDeclaration
	for i, p := range callee.Parameters {
		if arg, isIdent := call.Arguments[i].(*ast.Identifier); isIdent && !assigned[p.Name.Value] {
			rename[p.Name.Value] = arg.Value
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
