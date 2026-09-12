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
	"github.com/SCKelemen/oak/typechecker"
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
	// CodeSteadyAllocation reports a steady-state entry point (oak.mod
	// `steady`, docs/spec/85-discipline.md section 4) that reaches an
	// allocation, or code whose effects cannot be known.
	CodeSteadyAllocation = "OAK-E0104"
	// CodeEffectRow reports a function value that does not fit the effect
	// row of the function type it is passed or bound to
	// (docs/spec/60-effects-allocation.md section 2a): it performs an
	// effect outside the row, or its effects cannot be known.
	CodeEffectRow = "OAK-E0105"
)

const allocateEffect = "Memory.Allocate"

type effectSet map[string]bool

func effectKey(e *ast.EffectName) string { return e.Namespace + "." + e.Name }

// effectFacts is what the analysis knows about one function.
type effectFacts struct {
	fn       *ast.FunctionStatement
	declared effectSet
	// carried maps each effect a call through a rowed function value may
	// perform to the value's name: the row is the fact the call contributes.
	carried map[string]string
	// unknownSites are the reasons the function's effects are not fully
	// known: its own undeclared foreign body, or calls through values.
	unknownSites []string
	callees      []string
	// valueNames are the names holding function values in the body;
	// valueRows are the rows of those whose declared type carries one.
	valueNames map[string]bool
	valueRows  map[string]effectSet
}

// rowOf returns the effect row of a function type, if it declares one.
func rowOf(typ ast.Expression) (effectSet, bool) {
	ft, ok := typ.(*ast.FunctionTypeExpression)
	if !ok || !ft.EffectsDeclared {
		return nil, false
	}
	row := effectSet{}
	for _, e := range ft.Effects {
		row[effectKey(e)] = true
	}
	return row, true
}

func rowText(row effectSet) string {
	keys := make([]string, 0, len(row))
	for k := range row {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	return strings.Join(keys, ", ")
}

// applySteadyEntries gives each steady-state entry point (internal name ->
// source spelling) the implicit forbids { Memory.Allocate }, keeping any
// clause it declares itself. Returns the entry points found.
func applySteadyEntries(program *ast.Program, steady map[string]string) map[string]string {
	found := map[string]string{}
	if len(steady) == 0 {
		return found
	}
	for _, stmt := range program.Statements {
		fn, ok := stmt.(*ast.FunctionStatement)
		if !ok || fn.Name == nil || fn.Receiver != nil {
			continue
		}
		label, isEntry := steady[fn.Name.Value]
		if !isEntry {
			continue
		}
		found[fn.Name.Value] = label
		declared := false
		for _, e := range fn.Forbids {
			if effectKey(e) == allocateEffect {
				declared = true
			}
		}
		if !declared {
			fn.Forbids = append(fn.Forbids, &ast.EffectName{Token: fn.Name.Token, Namespace: "Memory", Name: "Allocate"})
		}
	}
	return found
}

// analyzeEffects checks every forbids clause in the program. `steady` names
// the entry points whose Memory.Allocate clause the manifest implied; their
// findings carry the steady-state diagnostic and spelling.
func analyzeEffects(program *ast.Program, steady map[string]string) []*diagnostic.Diagnostic {
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
	anyRows := false
	walkNodes(program, func(n ast.Node) {
		if ft, ok := n.(*ast.FunctionTypeExpression); ok && ft.EffectsDeclared {
			anyRows = true
		}
	})
	if !anyForbids && !anyRows {
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
		label, isSteady := steady[name]
		for _, forbidden := range fn.Forbids {
			key := effectKey(forbidden)
			if own.declared[key] {
				if isSteady && key == allocateEffect {
					report(CodeSteadyAllocation, forbidden, "steady-state entry point %s (oak.mod: steady %s) declares %s itself", name, label, key)
				} else {
					report(CodeEffectContradiction, forbidden, "%s declares %s and forbids it", name, key)
				}
				continue
			}
			if value := own.carried[key]; value != "" {
				report(CodeEffectForbidden, forbidden, "%s forbids %s, which it may perform through the function value %s (its type allows it)", name, key, value)
				continue
			}
			if path := effectPath(name, key, facts); path != nil {
				last := path[len(path)-1]
				performs := fmt.Sprintf("which %s performs", last)
				if value := facts[last].carried[key]; value != "" && !facts[last].declared[key] {
					performs = fmt.Sprintf("which %s may perform through the function value %s", last, value)
				}
				if isSteady && key == allocateEffect {
					report(CodeSteadyAllocation, forbidden, "steady-state entry point %s (oak.mod: steady %s) reaches %s, %s: %s", name, label, key, performs, strings.Join(path, " -> "))
				} else {
					report(CodeEffectForbidden, forbidden, "%s forbids %s, %s: %s", name, key, performs, strings.Join(path, " -> "))
				}
			}
		}
		if site, path := unknownPath(name, facts); site != "" {
			if isSteady {
				report(CodeSteadyAllocation, fn.Name, "steady-state entry point %s (oak.mod: steady %s) reaches %s (%s), whose effects the compiler cannot know; declare them with an effects clause", name, label, site, strings.Join(path, " -> "))
			} else {
				report(CodeEffectUnknown, fn.Name, "%s forbids effects, but the compiler cannot know the effects of %s (%s); declare them with an effects clause", name, site, strings.Join(path, " -> "))
			}
		}
	}
	if anyRows {
		diags = append(diags, checkEffectRows(functions, order, facts)...)
	}
	return diags
}

// checkEffectRows checks every function value that flows into a rowed
// function type — an argument for a parameter of that type, or the
// initializer of a declaration with that type — against the row
// (docs/spec/60-effects-allocation.md section 2a): the value's reachable
// effects must be known and inside the row. Assignment positions beyond
// these two are not checked and are documented as such.
func checkEffectRows(functions map[string]*ast.FunctionStatement, order []string, facts map[string]*effectFacts) []*diagnostic.Diagnostic {
	var diags []*diagnostic.Diagnostic
	report := func(node ast.Node, format string, args ...interface{}) {
		diags = append(diags, diagnostic.NewDiagnosticFromNodeWithCode(node, "compiler", CodeEffectRow, fmt.Sprintf(format, args...)))
	}
	for _, name := range order {
		fn := functions[name]
		if fn.Body == nil {
			continue
		}
		own := facts[name]
		check := func(node ast.Node, value ast.Expression, row effectSet, slot string) {
			effects, unknown, path := valueEffects(value, own, facts, functions)
			at := ""
			if len(path) > 0 {
				at = " (" + strings.Join(path, " -> ") + ")"
			}
			if unknown != "" {
				report(node, "%s: the value for %s, whose type allows effects { %s }, has effects the compiler cannot know: %s%s", name, slot, rowText(row), unknown, at)
				return
			}
			keys := make([]string, 0, len(effects))
			for k := range effects {
				keys = append(keys, k)
			}
			sort.Strings(keys)
			for _, key := range keys {
				if !row[key] {
					report(node, "%s: the value for %s, whose type allows effects { %s }, performs %s: %s", name, slot, rowText(row), key, strings.Join(effects[key], " -> "))
					return
				}
			}
		}
		walkNodes(fn.Body, func(n ast.Node) {
			switch v := n.(type) {
			case *ast.InvocationExpression:
				callee, ok := v.Function.(*ast.Identifier)
				if !ok {
					return
				}
				target := functions[callee.Value]
				if target == nil {
					return
				}
				for i, param := range target.Parameters {
					if i >= len(v.Arguments) || param == nil || param.Variadic {
						continue
					}
					if row, rowed := rowOf(param.Type); rowed {
						check(v.Arguments[i], v.Arguments[i], row, fmt.Sprintf("parameter %s of %s", param.Name.Value, callee.Value))
					}
				}
			case *ast.VariableDeclaration:
				if v.Value == nil || v.Name == nil {
					return
				}
				if row, rowed := rowOf(v.Type); rowed {
					check(v, v.Value, row, "the declaration of "+v.Name.Value)
				}
			}
		})
	}
	return diags
}

// valueEffects computes what a function-valued expression may perform: the
// effects (each with the call path that reaches it) and, when they cannot
// all be known, the first unknown site with its path.
func valueEffects(value ast.Expression, own *effectFacts, facts map[string]*effectFacts, functions map[string]*ast.FunctionStatement) (map[string][]string, string, []string) {
	switch v := value.(type) {
	case *ast.Identifier:
		if own.valueNames[v.Value] {
			row, rowed := own.valueRows[v.Value]
			if !rowed {
				return nil, "the function value " + v.Value + " has no effect row", nil
			}
			effects := map[string][]string{}
			for key := range row {
				effects[key] = []string{v.Value}
			}
			return effects, "", nil
		}
		if _, known := functions[v.Value]; known {
			return closureEffects(v.Value, facts)
		}
		return nil, "the function value " + v.Value + " cannot be followed", nil
	case *ast.FunctionLiteral:
		if v.Body == nil {
			return nil, "the function literal has no body to analyze", nil
		}
		lit := &effectFacts{declared: effectSet{}, carried: map[string]string{}, valueNames: map[string]bool{}, valueRows: map[string]effectSet{}}
		for _, arg := range v.Arguments {
			if arg != nil {
				lit.valueNames[arg.Value] = true
			}
		}
		collectBodyFacts(lit, v.Parameters, v.Body, functions)
		return closureFrom("the function literal", lit, facts)
	}
	return nil, "the expression is not a function name, a rowed value, or a literal", nil
}

// closureEffects is valueEffects for a function named in the program.
func closureEffects(start string, facts map[string]*effectFacts) (map[string][]string, string, []string) {
	return closureFrom(start, facts[start], facts)
}

// closureFrom walks the call graph from a root's facts, collecting every
// declared or carried effect with the path that first reaches it, and the
// first unknown site.
func closureFrom(root string, rootFacts *effectFacts, facts map[string]*effectFacts) (map[string][]string, string, []string) {
	type item struct {
		f    *effectFacts
		path []string
	}
	effects := map[string][]string{}
	visited := map[string]bool{root: true}
	queue := []item{{rootFacts, []string{root}}}
	for len(queue) > 0 {
		cur := queue[0]
		queue = queue[1:]
		if cur.f == nil {
			continue
		}
		if len(cur.f.unknownSites) > 0 {
			return nil, cur.f.unknownSites[0], cur.path
		}
		for key := range cur.f.declared {
			if _, seen := effects[key]; !seen {
				effects[key] = cur.path
			}
		}
		for key, value := range cur.f.carried {
			if _, seen := effects[key]; !seen {
				effects[key] = append(append([]string{}, cur.path...), "the function value "+value)
			}
		}
		for _, callee := range cur.f.callees {
			if !visited[callee] {
				visited[callee] = true
				queue = append(queue, item{facts[callee], append(append([]string{}, cur.path...), callee)})
			}
		}
	}
	return effects, "", nil
}

// collectEffectFacts gathers a function's declared effects, its callees by
// name, and the sites whose effects cannot be known.
func collectEffectFacts(fn *ast.FunctionStatement, functions map[string]*ast.FunctionStatement) *effectFacts {
	f := &effectFacts{fn: fn, declared: effectSet{}, carried: map[string]string{}, valueNames: map[string]bool{}, valueRows: map[string]effectSet{}}
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
	collectBodyFacts(f, fn.Parameters, fn.Body, functions)
	return f
}

// collectBodyFacts walks one body — a function's or a literal's — for its
// callees by name, the sites whose effects cannot be known, and the effects
// carried by calls through rowed function values.
func collectBodyFacts(f *effectFacts, params []*ast.FunctionParameter, body ast.Node, functions map[string]*ast.FunctionStatement) {
	// Names that hold function values in this body: parameters of function
	// type and locals bound to function types or literals. A declared row
	// makes a call through the name a known fact; no row leaves it unknown.
	valueNames := f.valueNames
	for _, p := range params {
		if p == nil || p.Name == nil {
			continue
		}
		if _, isFn := p.Type.(*ast.FunctionTypeExpression); isFn {
			valueNames[p.Name.Value] = true
			if row, rowed := rowOf(p.Type); rowed {
				f.valueRows[p.Name.Value] = row
			}
		}
	}
	seen := map[string]bool{}
	walkNodes(body, func(n ast.Node) {
		switch v := n.(type) {
		case *ast.VariableDeclaration:
			if v.Name == nil {
				return
			}
			if _, isFn := v.Type.(*ast.FunctionTypeExpression); isFn {
				valueNames[v.Name.Value] = true
				if row, rowed := rowOf(v.Type); rowed {
					f.valueRows[v.Name.Value] = row
				}
			}
			// A foreign function pointer (docs/spec/92-ffi.md section
			// 2.10) is a function value whose effects nothing declares:
			// a call through it fails closed like any other.
			if _, isForeign := typechecker.CFnTypeExpression(v.Type); isForeign {
				valueNames[v.Name.Value] = true
			}
			if _, isLit := v.Value.(*ast.FunctionLiteral); isLit {
				valueNames[v.Name.Value] = true
			}
		}
	})
	walkNodes(body, func(n ast.Node) {
		inv, ok := n.(*ast.InvocationExpression)
		if !ok {
			return
		}
		switch callee := inv.Function.(type) {
		case *ast.Identifier:
			if valueNames[callee.Value] {
				if row, rowed := f.valueRows[callee.Value]; rowed {
					for key := range row {
						if _, have := f.carried[key]; !have {
							f.carried[key] = callee.Value
						}
					}
					return
				}
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
		if cur.name != start && (f.declared[effect] || f.carried[effect] != "") {
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
