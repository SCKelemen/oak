package compiler

// Effect clauses (docs/spec/60-effects-allocation.md section 2). A function
// may declare the effects it performs (`effects { Memory.Allocate }`) and
// forbid classes of effect (`forbids { Memory.Allocate, Os.Syscall }`). The
// forbidden set is checked against everything reachable through the call
// graph, after specialization, so the check sees concrete callees. Facts
// are never guessed: an extern or asm-backed function without an `effects`
// clause has unknown effects and violates any `forbids` that reaches it
// (declare `effects { }` to assert none), and a call through a function
// value cannot be followed and is treated the same way.

import (
	"fmt"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
)

const (
	// CodeEffectForbidden reports a forbidden effect reachable from the
	// forbidding function, with the call path that carries it.
	CodeEffectForbidden = "OAK-E0101"
	// CodeEffectContradiction reports a function that declares an effect it
	// also forbids.
	CodeEffectContradiction = "OAK-E0102"
	// CodeEffectUnknown reports a forbidding function that reaches code whose
	// effects the compiler cannot know: an extern or asm-backed declaration
	// without an effects clause, or a call through a function value.
	CodeEffectUnknown = "OAK-E0103"
)

type effectSet map[string]bool

func effectKey(e *ast.EffectName) string { return e.Namespace + "." + e.Name }

// effectFacts is what the analysis knows about one function.
type effectFacts struct {
	fn       *ast.FunctionStatement
	declared effectSet
	// unknownSites are the reasons the function's effects are not fully
	// known: its own undeclared foreign body, or calls through values.
	unknownSites []string
	callees      []string
}

// analyzeEffects checks every forbids clause in the program.
func analyzeEffects(program *ast.Program) []*diagnostic.Diagnostic {
	functions := map[string]*ast.FunctionStatement{}
	var order []string
	anyForbids := false
	for _, stmt := range program.Statements {
		fn, ok := stmt.(*ast.FunctionStatement)
		if !ok || fn.Name == nil || fn.Receiver != nil {
			continue
		}
		if _, seen := functions[fn.Name.Value]; seen {
			continue
		}
		functions[fn.Name.Value] = fn
		order = append(order, fn.Name.Value)
		if len(fn.Forbids) > 0 {
			anyForbids = true
		}
	}
	if !anyForbids {
		return nil
	}
	facts := map[string]*effectFacts{}
	for _, name := range order {
		facts[name] = collectEffectFacts(functions[name], functions)
	}
	var diags []*diagnostic.Diagnostic
	report := func(code string, node ast.Node, format string, args ...interface{}) {
		diags = append(diags, diagnostic.NewDiagnosticFromNodeWithCode(node, "compiler", code, fmt.Sprintf(format, args...)))
	}
	for _, name := range order {
		fn := functions[name]
		if len(fn.Forbids) == 0 {
			continue
		}
		own := facts[name]
		for _, forbidden := range fn.Forbids {
			key := effectKey(forbidden)
			if own.declared[key] {
				report(CodeEffectContradiction, forbidden, "%s declares %s and forbids it", name, key)
				continue
			}
			if path := effectPath(name, key, facts); path != nil {
				report(CodeEffectForbidden, forbidden, "%s forbids %s, which %s performs: %s", name, key, path[len(path)-1], strings.Join(path, " -> "))
			}
		}
		if site, path := unknownPath(name, facts); site != "" {
			report(CodeEffectUnknown, fn.Name, "%s forbids effects, but the compiler cannot know the effects of %s (%s); declare them with an effects clause", name, site, strings.Join(path, " -> "))
		}
	}
	return diags
}

// collectEffectFacts gathers a function's declared effects, its callees by
// name, and the sites whose effects cannot be known.
func collectEffectFacts(fn *ast.FunctionStatement, functions map[string]*ast.FunctionStatement) *effectFacts {
	f := &effectFacts{fn: fn, declared: effectSet{}}
	for _, e := range fn.Effects {
		f.declared[effectKey(e)] = true
	}
	foreign := fn.ExternSymbol != "" || fn.AsmBacked || fn.Body == nil
	if foreign && !fn.EffectsDeclared {
		kind := "an extern"
		if fn.AsmBacked || (fn.ExternSymbol == "" && fn.Body == nil) {
			kind = "an asm-backed declaration"
		}
		f.unknownSites = append(f.unknownSites, kind+" "+fn.Name.Value)
	}
	if fn.Body == nil {
		return f
	}
	// Names that hold function values in this body: parameters of function
	// type and locals bound to function types or literals.
	valueNames := map[string]bool{}
	for _, p := range fn.Parameters {
		if _, isFn := p.Type.(*ast.FunctionTypeExpression); isFn {
			valueNames[p.Name.Value] = true
		}
	}
	seen := map[string]bool{}
	walkNodes(fn.Body, func(n ast.Node) {
		switch v := n.(type) {
		case *ast.VariableDeclaration:
			if _, isFn := v.Type.(*ast.FunctionTypeExpression); isFn {
				valueNames[v.Name.Value] = true
			}
			if _, isLit := v.Value.(*ast.FunctionLiteral); isLit {
				valueNames[v.Name.Value] = true
			}
		}
	})
	walkNodes(fn.Body, func(n ast.Node) {
		inv, ok := n.(*ast.InvocationExpression)
		if !ok {
			return
		}
		switch callee := inv.Function.(type) {
		case *ast.Identifier:
			if valueNames[callee.Value] {
				f.unknownSites = append(f.unknownSites, "a call through the function value "+callee.Value)
				return
			}
			if _, known := functions[callee.Value]; known && !seen[callee.Value] {
				seen[callee.Value] = true
				f.callees = append(f.callees, callee.Value)
			}
			// Builtins and conversions (assert, span, u32, ...) carry no effect.
		case *ast.IndexExpression:
			// c.UInt32(x) and friends are conversions; anything else spelled
			// as a member call is a value the analysis cannot follow.
			if base, isIdent := callee.Left.(*ast.Identifier); isIdent && callee.Dot && (base.Value == "c" || base.Value == "simd" || base.Value == "arm64") {
				return
			}
			f.unknownSites = append(f.unknownSites, "a call through a value at "+inv.Token.Literal)
		case *ast.FunctionLiteral:
			// An immediately invoked literal: its body is walked like ours.
		default:
			f.unknownSites = append(f.unknownSites, "a call through a function value")
		}
	})
	sort.Strings(f.callees)
	return f
}

// effectPath finds a call path from start to a function that declares the
// effect, or nil.
func effectPath(start, effect string, facts map[string]*effectFacts) []string {
	type item struct {
		name string
		path []string
	}
	visited := map[string]bool{start: true}
	queue := []item{{start, []string{start}}}
	for len(queue) > 0 {
		cur := queue[0]
		queue = queue[1:]
		f := facts[cur.name]
		if f == nil {
			continue
		}
		if cur.name != start && f.declared[effect] {
			return cur.path
		}
		for _, callee := range f.callees {
			if !visited[callee] {
				visited[callee] = true
				queue = append(queue, item{callee, append(append([]string{}, cur.path...), callee)})
			}
		}
	}
	return nil
}

// unknownPath finds the first reachable site whose effects are unknown.
func unknownPath(start string, facts map[string]*effectFacts) (string, []string) {
	type item struct {
		name string
		path []string
	}
	visited := map[string]bool{start: true}
	queue := []item{{start, []string{start}}}
	for len(queue) > 0 {
		cur := queue[0]
		queue = queue[1:]
		f := facts[cur.name]
		if f == nil {
			continue
		}
		if len(f.unknownSites) > 0 {
			return f.unknownSites[0], cur.path
		}
		for _, callee := range f.callees {
			if !visited[callee] {
				visited[callee] = true
				queue = append(queue, item{callee, append(append([]string{}, cur.path...), callee)})
			}
		}
	}
	return "", nil
}

// walkNodes visits every syntax node under root, depth first.
func walkNodes(root ast.Node, visit func(ast.Node)) {
	walkSyntaxNodes(root, visit)
}
