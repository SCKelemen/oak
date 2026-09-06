package typechecker

import (
	"fmt"
	"sort"

	"github.com/SCKelemen/oak/ast"
)

// CodeClosureCaptureStorage rejects capturing closures until environment
// storage can be justified explicitly (docs/spec/05-ergonomics-and-cost.md,
// docs/spec/60-effects-allocation.md section 10): capturing a local must
// never silently heap-promote it, and the backend must never silently drop
// the environment. Captureless function literals are bare code pointers and
// remain legal.
const CodeClosureCaptureStorage = "OAK-T0401"

// closureBuiltins are callable names that are language builtins, not
// environment captures.
var closureBuiltins = map[string]bool{
	"view": true, "span": true, "subslice": true,
	"view_as": true, "span_as": true, "assert": true,
	"len": true, "get": true, "try_slice": true,
}

// checkClosureCaptures reports OAK-T0401 when the function literal captures
// enclosing non-function bindings. Top-level function references are direct
// code pointers, not environment.
func (tc *TypeChecker) checkClosureCaptures(fn *ast.FunctionLiteral) {
	captures := tc.closureCaptures(fn)
	if len(captures) == 0 {
		return
	}
	d := tc.addTypeDiagnostic(fn, CodeClosureCaptureStorage,
		fmt.Sprintf("closure captures %v without established environment storage", captures))
	d.AddNote("a capturing closure's environment must live in explicitly justified storage: a non-escaping stack frame, caller-owned storage, an arena/region, or static storage (Oak.ClosureCapture)")
	d.AddNote("capturing a local never silently heap-promotes it; storage justification surfaces are planned")
	d.AddHelp("pass the value as a parameter, or use a captureless function value")
}

// closureCaptures computes the literal's free variables that resolve to
// enclosing non-function bindings, sorted for deterministic diagnostics.
func (tc *TypeChecker) closureCaptures(fn *ast.FunctionLiteral) []string {
	if fn == nil || fn.Body == nil {
		return nil
	}
	locals := make(map[string]bool)
	for _, param := range fn.Arguments {
		if param != nil {
			locals[param.Value] = true
		}
	}
	captured := make(map[string]bool)

	var walkExpr func(expr ast.Expression, locals map[string]bool)
	var walkStmt func(stmt ast.Statement, locals map[string]bool)

	noteUse := func(name string, locals map[string]bool) {
		if locals[name] || closureBuiltins[name] || name == "()" {
			return
		}
		scheme, ok := tc.env.Get(name)
		if !ok || scheme == nil {
			return // undefined names are ordinary type errors, not captures
		}
		if _, isFunction := scheme.Type.(*FunctionType); isFunction {
			return // direct code pointer, no environment needed
		}
		captured[name] = true
	}

	walkExpr = func(expr ast.Expression, locals map[string]bool) {
		switch e := expr.(type) {
		case *ast.Identifier:
			noteUse(e.Value, locals)
		case *ast.InfixExpression:
			walkExpr(e.Left, locals)
			walkExpr(e.Right, locals)
		case *ast.PrefixExpression:
			walkExpr(e.Right, locals)
		case *ast.IndexExpression:
			walkExpr(e.Left, locals)
			walkExpr(e.Index, locals)
		case *ast.SliceExpression:
			walkExpr(e.Seq, locals)
			if e.Low != nil {
				walkExpr(e.Low, locals)
			}
			if e.High != nil {
				walkExpr(e.High, locals)
			}
		case *ast.InvocationExpression:
			walkExpr(e.Function, locals)
			for _, arg := range e.Arguments {
				walkExpr(arg, locals)
			}
		case *ast.MatchExpression:
			walkExpr(e.Scrutinee, locals)
			for _, arm := range e.Arms {
				armLocals := copyLocals(locals)
				bindPatternNames(arm.Pattern, armLocals)
				walkExpr(arm.Body, armLocals)
			}
		case *ast.BlockExpression:
			if e.Block != nil {
				blockLocals := copyLocals(locals)
				for _, stmt := range e.Block.Statements {
					walkStmt(stmt, blockLocals)
				}
			}
		case *ast.ArrayLiteral:
			for _, elem := range e.Elements {
				walkExpr(elem, locals)
			}
		case *ast.RecordLiteral:
			for _, field := range e.OrderedFields() {
				walkExpr(field.Value, locals)
			}
		case *ast.VariantExpression:
			if e.Payload != nil {
				walkExpr(e.Payload, locals)
			}
		case *ast.FunctionLiteral:
			nested := copyLocals(locals)
			for _, param := range e.Arguments {
				if param != nil {
					nested[param.Value] = true
				}
			}
			if e.Body != nil {
				for _, stmt := range e.Body.Statements {
					walkStmt(stmt, nested)
				}
			}
		}
	}

	walkStmt = func(stmt ast.Statement, locals map[string]bool) {
		switch s := stmt.(type) {
		case *ast.ExpressionStatement:
			walkExpr(s.Expression, locals)
		case *ast.VariableDeclaration:
			if s.Value != nil {
				walkExpr(s.Value, locals)
			}
			if s.Name != nil {
				locals[s.Name.Value] = true
			}
		case *ast.AssignmentStatement:
			walkExpr(s.Value, locals)
			if s.Name != nil {
				noteUse(s.Name.Value, locals)
			}
		case *ast.WhileStatement:
			walkExpr(s.Condition, locals)
			if s.Body != nil {
				bodyLocals := copyLocals(locals)
				for _, inner := range s.Body.Statements {
					walkStmt(inner, bodyLocals)
				}
			}
		case *ast.BlockStatement:
			blockLocals := copyLocals(locals)
			for _, inner := range s.Statements {
				walkStmt(inner, blockLocals)
			}
		case *ast.UnsafeBlock:
			if s.Body != nil {
				blockLocals := copyLocals(locals)
				for _, inner := range s.Body.Statements {
					walkStmt(inner, blockLocals)
				}
			}
		}
	}

	for _, stmt := range fn.Body.Statements {
		walkStmt(stmt, locals)
	}

	names := make([]string, 0, len(captured))
	for name := range captured {
		names = append(names, name)
	}
	sort.Strings(names)
	return names
}

func copyLocals(locals map[string]bool) map[string]bool {
	copied := make(map[string]bool, len(locals))
	for name := range locals {
		copied[name] = true
	}
	return copied
}

// bindPatternNames adds a match pattern's bindings to the local set.
func bindPatternNames(pattern ast.Node, locals map[string]bool) {
	switch p := pattern.(type) {
	case *ast.BindingPattern:
		if p.Name != nil {
			locals[p.Name.Value] = true
		}
	case *ast.VariantPattern:
		if p.Payload != nil {
			bindPatternNames(p.Payload, locals)
		}
	}
}
