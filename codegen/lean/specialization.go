package lean

import (
	"fmt"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/modules"
)

// callRoute is a first-order application: function-valued arguments have
// become bindings on the target definition, leaving only value arguments.
type callRoute struct {
	target    string
	arguments []ast.Expression
}

// routeCalls resolves the body's calls under this instance's named function
// bindings. Instances share the original body and its checked type metadata;
// neither extraction nor specializing a second call rewrites the program.
// This runs before dependency ordering and state analysis, so both see the
// callbacks' actual call graph, including writes through spans and globals.
func (em *emitter) routeCalls(fn *ast.FunctionStatement, candidates map[string]*ast.FunctionStatement) error {
	if em.routes == nil {
		em.routes = map[string]map[*ast.InvocationExpression]callRoute{}
		em.bindings = map[string]map[string]string{}
	}
	key := functionKey(fn)
	bindings := em.bindings[key]
	routes := map[*ast.InvocationExpression]callRoute{}
	em.routes[key] = routes
	var routeErr error
	locals := map[string]bool{}
	for _, p := range functionParams(fn) {
		locals[p.Name.Value] = true
	}
	// A specialization is valid only while its function bindings are fixed.
	walkStatements(fn.Body, func(stmt ast.Statement) {
		if decl, ok := stmt.(*ast.VariableDeclaration); ok && decl.Name != nil {
			locals[decl.Name.Value] = true
		}
		if s, ok := stmt.(*ast.AssignmentStatement); ok && bindings[s.Name.Value] != "" {
			routeErr = fmt.Errorf("lean: %s: reassigning function parameter %s is outside the extracted subset", key, s.Name.Value)
		}
	})
	walkExpressions(fn.Body, func(e ast.Expression) {
		call, ok := e.(*ast.InvocationExpression)
		if !ok || routeErr != nil {
			return
		}
		target := call.ResolvedMethod
		arguments := call.Arguments
		if target != "" {
			access, ok := call.Function.(*ast.IndexExpression)
			if !ok || !access.Dot {
				routeErr = fmt.Errorf("lean: %s: method call %s is outside the extracted subset", key, call.Function.String())
				return
			}
			arguments = append([]ast.Expression{access.Left}, arguments...)
		} else if id, ok := call.Function.(*ast.Identifier); ok {
			target = id.Value
			if bound := bindings[target]; bound != "" {
				target = bound
			} else if locals[target] {
				routeErr = fmt.Errorf("lean: %s: call through local function value %s is outside the extracted subset", key, target)
				return
			}
		}
		callee := candidates[target]
		if callee == nil {
			// Builtins and unsupported dynamic calls are handled by call.
			return
		}
		params := functionParams(callee)
		if len(params) != len(arguments) {
			routeErr = fmt.Errorf("lean: %s: call to %s passes %d arguments for %d parameters", key, target, len(arguments), len(params))
			return
		}
		bound := map[string]string{}
		var remaining []ast.Expression
		for i, p := range params {
			if _, function := p.Type.(*ast.FunctionTypeExpression); !function {
				remaining = append(remaining, arguments[i])
				continue
			}
			argument, ok := arguments[i].(*ast.Identifier)
			name := ""
			if ok {
				name = argument.Value
				if binding := bindings[name]; binding != "" {
					name = binding
				} else if locals[name] {
					// A local may shadow a bootstrap-library declaration;
					// it is not the named callback in candidates.
					name = ""
				}
			}
			callback := candidates[name]
			if callback == nil || callback.Receiver != nil || len(callback.TypeParams) != 0 || callback.ExternSymbol != "" || callback.Body == nil {
				routeErr = fmt.Errorf("lean: %s: argument %s to %s must be a named Oak function (or a bound function parameter)", key, p.Name.Value, target)
				return
			}
			bound[p.Name.Value] = name
		}
		if len(bound) != 0 {
			target = em.specialize(callee, bound, candidates)
		}
		routes[call] = callRoute{target: target, arguments: remaining}
	})
	return routeErr
}

// specialize interns a shallow declaration with the function slots removed.
// Its body remains the checked body's identity. Escaped components separated
// by '__' distinguish parameter positions, targets, and underscore spellings.
func (em *emitter) specialize(fn *ast.FunctionStatement, bound map[string]string, candidates map[string]*ast.FunctionStatement) string {
	parts := []string{"oak_apply", modules.Escape(functionKey(fn))}
	var params []*ast.FunctionParameter
	for _, p := range functionParams(fn) {
		if target := bound[p.Name.Value]; target != "" {
			parts = append(parts, modules.Escape(p.Name.Value), modules.Escape(target))
		} else {
			params = append(params, p)
		}
	}
	key := strings.Join(parts, "__")
	if candidates[key] == nil {
		instance := *fn
		name := *fn.Name
		name.Value = key
		instance.Name = &name
		instance.Receiver = nil
		instance.Parameters = params
		candidates[key] = &instance
		em.bindings[key] = bound
	}
	return key
}
