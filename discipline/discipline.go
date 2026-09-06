// Package discipline implements the bounded-execution analyses of the strict
// discipline profile (docs/spec/85-discipline.md), targeting MISRA C, NASA
// Power of Ten, and TigerStyle program shapes.
//
// Oak does not ban recursion; it requires recursion to be safe. Call ranks
// must strictly decrease across stack-consuming calls and never increase
// across tail calls — Oak.Discipline (spec/lean/Oak/Discipline.lean) proves
// this certificate bounds stack depth by the start's rank and forces every
// call cycle to be tail-only, hence eliminable. Self tail recursion in
// loop-lowerable position compiles to a loop in the backend; remaining
// tail-only cycles are accepted with a recorded obligation (OAK-D0102);
// stack-consuming cycles are rejected (OAK-D0101).
package discipline

import (
	"fmt"
	"sort"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
)

const (
	// CodeStackRecursion rejects call cycles that consume stack frames:
	// recursion without a tail-only shape (or a future declared bound) has
	// no static stack bound.
	CodeStackRecursion diagnostic.Code = "OAK-D0101"
	// CodeTailRecursionObligation records tail-only cycles the backend does
	// not yet lower to loops (mutual tail recursion, tail calls inside match
	// arms): safe only once tail-call elimination is guaranteed.
	CodeTailRecursionObligation diagnostic.Code = "OAK-D0102"
)

// builtin call targets that never form call-graph edges.
var builtinCallees = map[string]bool{
	"view": true, "span": true, "subslice": true,
	"view_as": true, "span_as": true, "assert": true,
	"is_valid_utf8": true,
}

type callEdge struct {
	callee string
	tail   bool
	site   ast.Node
}

// Result carries the analysis outcome.
type Result struct {
	// Ranks is the certificate: for every stack call rank(callee) < rank(caller),
	// for every tail call rank(callee) <= rank(caller) (Oak.Discipline.Ranked).
	Ranks map[string]int
	// LoopLowered names functions whose recursion is exactly self tail calls
	// in loop-lowerable position; the C backend compiles these to loops.
	LoopLowered map[string]bool
	// TrampolineGroups are all-tail cycles of two or more functions with
	// identical signatures whose member calls all sit in result position;
	// the C backend merges each group into one state-machine loop, so the
	// whole cycle runs in a single frame. Members are sorted.
	TrampolineGroups [][]string
	diagnostics      []*diagnostic.Diagnostic
}

// Diagnostics returns the discipline findings, errors first.
func (r *Result) Diagnostics() []*diagnostic.Diagnostic {
	return r.diagnostics
}

// AnalyzeProgram checks the bounded-execution discipline of every top-level
// function in the program.
func AnalyzeProgram(program *ast.Program) *Result {
	result := &Result{
		Ranks:       make(map[string]int),
		LoopLowered: make(map[string]bool),
	}
	if program == nil {
		return result
	}

	names := make([]string, 0)
	functions := make(map[string]*ast.FunctionStatement)
	for _, stmt := range program.Statements {
		fn, ok := stmt.(*ast.FunctionStatement)
		if !ok || fn.Name == nil {
			continue
		}
		if _, seen := functions[fn.Name.Value]; !seen {
			names = append(names, fn.Name.Value)
		}
		functions[fn.Name.Value] = fn
	}

	edges := make(map[string][]callEdge)
	for _, name := range names {
		edges[name] = collectCallEdges(functions[name], functions)
	}

	components := stronglyConnectedComponents(names, edges)

	// Tarjan emits components callees-first, which is exactly the certificate
	// order: rank(callee SCC) < rank(caller SCC), equal ranks inside an SCC.
	for rank, component := range components {
		for _, name := range component {
			result.Ranks[name] = rank
		}
	}

	for _, component := range components {
		result.classifyComponent(component, functions, edges)
	}

	result.analyzeLoops(program)
	return result
}

// classifyComponent applies the recursion policy to one strongly connected
// component of the call graph.
func (r *Result) classifyComponent(component []string, functions map[string]*ast.FunctionStatement, edges map[string][]callEdge) {
	members := make(map[string]bool, len(component))
	for _, name := range component {
		members[name] = true
	}

	var internalStack, internalTail []struct {
		caller string
		edge   callEdge
	}
	for _, caller := range component {
		for _, edge := range edges[caller] {
			if !members[edge.callee] {
				continue
			}
			labeled := struct {
				caller string
				edge   callEdge
			}{caller, edge}
			if edge.tail {
				internalTail = append(internalTail, labeled)
			} else {
				internalStack = append(internalStack, labeled)
			}
		}
	}

	if len(internalStack) == 0 && len(internalTail) == 0 {
		return // not recursive
	}

	sorted := append([]string(nil), component...)
	sort.Strings(sorted)

	if len(internalStack) > 0 {
		first := internalStack[0]
		d := diagnostic.NewDiagnosticFromNodeWithCode(first.edge.site, "discipline", string(CodeStackRecursion),
			fmt.Sprintf("recursion through %v consumes stack frames without a static bound", sorted))
		for _, call := range internalStack {
			d.AddSecondary(diagnostic.NodeToRange(call.edge.site),
				fmt.Sprintf("%s calls %s outside tail position, so each iteration consumes a frame", call.caller, call.edge.callee))
		}
		d.AddNote("the strict profile requires statically bounded stack depth (docs/spec/85-discipline.md)")
		d.AddHelp("make the recursive calls tail calls so they compile to loops, or restructure into an explicit loop")
		r.diagnostics = append(r.diagnostics, d)
		return
	}

	// Tail-only cycle. A single function whose self tail calls all sit in
	// loop-lowerable position compiles to a loop: safe, silent.
	if len(component) == 1 && selfTailLoop(functions[component[0]]) {
		r.LoopLowered[component[0]] = true
		return
	}

	// A multi-function all-tail cycle with matching signatures and
	// result-position calls compiles to one trampoline: safe, silent.
	if len(component) >= 2 && TrampolineLowerable(sorted, functions) {
		r.TrampolineGroups = append(r.TrampolineGroups, sorted)
		return
	}

	first := internalTail[0]
	d := diagnostic.NewDiagnosticFromNodeWithCode(first.edge.site, "discipline", string(CodeTailRecursionObligation),
		fmt.Sprintf("tail recursion through %v relies on tail-call elimination the backend does not guarantee yet", sorted))
	d.Severity = diagnostic.SeverityWarning
	d.AddNote("every call in this cycle is a tail call, so the cycle is eliminable; direct self tail recursion in result position already compiles to a loop")
	d.AddHelp("restructure into direct self tail recursion or an explicit loop until mutual tail-call lowering lands")
	r.diagnostics = append(r.diagnostics, d)
}

// SelfTailLoop reports whether fn recurses exactly through self tail calls in
// loop-lowerable (body result) position. The C backend compiles such a
// function's body to a loop, reusing the frame (Oak.Discipline: tail steps
// consume no stack depth).
func SelfTailLoop(fn *ast.FunctionStatement) bool {
	return selfTailLoop(fn)
}

// TrampolineLowerable reports whether a group of mutually tail-recursive
// functions can be merged into one state-machine loop by the backend: every
// member exists, all signatures are syntactically identical (equal syntax
// implies equal type), and each member's calls to group members are exactly
// one invocation in its body's result position. This is the single decision
// procedure shared by the analyzer and the backend, so no cycle is accepted
// as lowered without actually being lowered.
func TrampolineLowerable(members []string, functions map[string]*ast.FunctionStatement) bool {
	if len(members) < 2 {
		return false
	}
	memberSet := make(map[string]bool, len(members))
	for _, name := range members {
		if functions[name] == nil || functions[name].Name == nil {
			return false
		}
		memberSet[name] = true
	}
	reference := functions[members[0]]
	for _, name := range members {
		fn := functions[name]
		if fn.Receiver != nil || len(fn.TypeParams) > 0 {
			return false
		}
		if !sameSignature(reference, fn) {
			return false
		}
		// Every call to a group member must sit at a lowerable tail site.
		lowerable := 0
		for _, inv := range lowerableTailInvocations(fn.Body) {
			if ident, ok := inv.Function.(*ast.Identifier); ok && memberSet[ident.Value] {
				lowerable++
			}
		}
		if lowerable == 0 {
			return false
		}
		total := 0
		for member := range memberSet {
			total += countCalls(fn.Body, member)
		}
		if total != lowerable {
			return false
		}
	}
	return true
}

// sameSignature compares parameter lists and return types syntactically.
// Parameter names must also match: the trampoline engine shares one set of
// parameter slots across all members' bodies.
func sameSignature(a, b *ast.FunctionStatement) bool {
	if len(a.Parameters) != len(b.Parameters) {
		return false
	}
	for i := range a.Parameters {
		if typeSyntax(a.Parameters[i].Type) != typeSyntax(b.Parameters[i].Type) {
			return false
		}
		if a.Parameters[i].Name == nil || b.Parameters[i].Name == nil ||
			a.Parameters[i].Name.Value != b.Parameters[i].Name.Value {
			return false
		}
	}
	return typeSyntax(a.ReturnType) == typeSyntax(b.ReturnType)
}

func typeSyntax(expr ast.Expression) string {
	if expr == nil {
		return "()"
	}
	return expr.String()
}

// resultInvocationOfAny returns the invocation of any member sitting in the
// body's result position, if any.
func resultInvocationOfAny(body ast.Expression, members map[string]bool) *ast.InvocationExpression {
	expr := body
	if block, ok := body.(*ast.BlockExpression); ok {
		expr = block.Result()
	}
	inv, ok := expr.(*ast.InvocationExpression)
	if !ok {
		return nil
	}
	if ident, ok := inv.Function.(*ast.Identifier); ok && members[ident.Value] {
		return inv
	}
	return nil
}

func selfTailLoop(fn *ast.FunctionStatement) bool {
	if fn == nil || fn.Name == nil || fn.Body == nil {
		return false
	}
	name := fn.Name.Value
	// Every self call must sit at a lowerable tail site, so the backend can
	// replace each with parameter rebinding plus continue.
	lowerable := 0
	for _, inv := range lowerableTailInvocations(fn.Body) {
		if ident, ok := inv.Function.(*ast.Identifier); ok && ident.Value == name {
			lowerable++
		}
	}
	return lowerable >= 1 && countCalls(fn.Body, name) == lowerable
}

// LowerableMatchShape reports whether the backend can lower this match to
// guarded statements in return position: the scrutinee is an identifier
// (safe to re-evaluate per arm) and every arm pattern is a literal or the
// wildcard. This is the single decision procedure shared by the analyzer
// and the backend.
func LowerableMatchShape(m *ast.MatchExpression) bool {
	if m == nil {
		return false
	}
	if _, ok := m.Scrutinee.(*ast.Identifier); !ok {
		return false
	}
	for _, arm := range m.Arms {
		switch pattern := arm.Pattern.(type) {
		case *ast.LiteralPattern, *ast.WildcardPattern:
		case *ast.BindingPattern:
			// `_` parses as a binding named "_": semantically the wildcard.
			if pattern.Name == nil || pattern.Name.Value != "_" {
				return false
			}
		default:
			return false
		}
	}
	return true
}

// lowerableTailInvocations returns the invocations at positions the backend
// lowers to rebind-plus-continue: the body result, block trailing
// expressions, and arm bodies of lowerable-shape matches in those positions.
func lowerableTailInvocations(body ast.Expression) []*ast.InvocationExpression {
	var out []*ast.InvocationExpression
	var visit func(expr ast.Expression)
	visit = func(expr ast.Expression) {
		switch e := expr.(type) {
		case *ast.InvocationExpression:
			out = append(out, e)
		case *ast.BlockExpression:
			if result := e.Result(); result != nil {
				visit(result)
			}
		case *ast.MatchExpression:
			if !LowerableMatchShape(e) {
				return
			}
			for _, arm := range e.Arms {
				visit(arm.Body)
			}
		}
	}
	visit(body)
	return out
}

// collectCallEdges walks one function body and records every call to another
// analyzed function, labeled tail or stack by position.
func collectCallEdges(fn *ast.FunctionStatement, functions map[string]*ast.FunctionStatement) []callEdge {
	var edges []callEdge
	if fn == nil || fn.Body == nil {
		return edges
	}

	record := func(inv *ast.InvocationExpression, tail bool) {
		ident, ok := inv.Function.(*ast.Identifier)
		if !ok {
			return
		}
		if builtinCallees[ident.Value] {
			return
		}
		if _, known := functions[ident.Value]; !known {
			return
		}
		edges = append(edges, callEdge{callee: ident.Value, tail: tail, site: inv})
	}

	var walkExpr func(expr ast.Expression, tail bool)
	var walkStmt func(stmt ast.Statement)

	walkExpr = func(expr ast.Expression, tail bool) {
		switch e := expr.(type) {
		case *ast.InvocationExpression:
			record(e, tail)
			walkExpr(e.Function, false)
			for _, arg := range e.Arguments {
				walkExpr(arg, false)
			}
		case *ast.BlockExpression:
			if e.Block == nil {
				return
			}
			result := e.Result()
			for _, stmt := range e.Block.Statements {
				if exprStmt, ok := stmt.(*ast.ExpressionStatement); ok && exprStmt.Expression == result && result != nil {
					walkExpr(result, tail)
					continue
				}
				walkStmt(stmt)
			}
		case *ast.MatchExpression:
			walkExpr(e.Scrutinee, false)
			for _, arm := range e.Arms {
				walkExpr(arm.Body, tail)
			}
		case *ast.InfixExpression:
			walkExpr(e.Left, false)
			walkExpr(e.Right, false)
		case *ast.PrefixExpression:
			walkExpr(e.Right, false)
		case *ast.IndexExpression:
			walkExpr(e.Left, false)
			walkExpr(e.Index, false)
		case *ast.SliceExpression:
			walkExpr(e.Seq, false)
			if e.Low != nil {
				walkExpr(e.Low, false)
			}
			if e.High != nil {
				walkExpr(e.High, false)
			}
		case *ast.ArrayLiteral:
			for _, elem := range e.Elements {
				walkExpr(elem, false)
			}
		case *ast.RecordLiteral:
			for _, field := range e.OrderedFields() {
				walkExpr(field.Value, false)
			}
		}
	}

	walkStmt = func(stmt ast.Statement) {
		switch s := stmt.(type) {
		case *ast.ExpressionStatement:
			walkExpr(s.Expression, false)
		case *ast.VariableDeclaration:
			if s.Value != nil {
				walkExpr(s.Value, false)
			}
		case *ast.AssignmentStatement:
			walkExpr(s.Value, false)
		case *ast.WhileStatement:
			walkExpr(s.Condition, false)
			if s.Body != nil {
				for _, inner := range s.Body.Statements {
					walkStmt(inner)
				}
			}
		case *ast.BlockStatement:
			for _, inner := range s.Statements {
				walkStmt(inner)
			}
		case *ast.UnsafeBlock:
			if s.Body != nil {
				for _, inner := range s.Body.Statements {
					walkStmt(inner)
				}
			}
		}
	}

	walkExpr(fn.Body, true)
	return edges
}

// countCalls counts invocations of name anywhere inside expr.
func countCalls(expr ast.Expression, name string) int {
	count := 0
	var walkExpr func(ast.Expression)
	var walkStmt func(ast.Statement)
	walkExpr = func(e ast.Expression) {
		switch n := e.(type) {
		case *ast.InvocationExpression:
			if ident, ok := n.Function.(*ast.Identifier); ok && ident.Value == name {
				count++
			}
			walkExpr(n.Function)
			for _, arg := range n.Arguments {
				walkExpr(arg)
			}
		case *ast.BlockExpression:
			if n.Block != nil {
				for _, stmt := range n.Block.Statements {
					walkStmt(stmt)
				}
			}
		case *ast.MatchExpression:
			walkExpr(n.Scrutinee)
			for _, arm := range n.Arms {
				walkExpr(arm.Body)
			}
		case *ast.InfixExpression:
			walkExpr(n.Left)
			walkExpr(n.Right)
		case *ast.PrefixExpression:
			walkExpr(n.Right)
		case *ast.IndexExpression:
			walkExpr(n.Left)
			walkExpr(n.Index)
		case *ast.SliceExpression:
			walkExpr(n.Seq)
			if n.Low != nil {
				walkExpr(n.Low)
			}
			if n.High != nil {
				walkExpr(n.High)
			}
		case *ast.ArrayLiteral:
			for _, elem := range n.Elements {
				walkExpr(elem)
			}
		case *ast.RecordLiteral:
			for _, field := range n.OrderedFields() {
				walkExpr(field.Value)
			}
		}
	}
	walkStmt = func(s ast.Statement) {
		switch n := s.(type) {
		case *ast.ExpressionStatement:
			walkExpr(n.Expression)
		case *ast.VariableDeclaration:
			if n.Value != nil {
				walkExpr(n.Value)
			}
		case *ast.AssignmentStatement:
			walkExpr(n.Value)
		case *ast.WhileStatement:
			walkExpr(n.Condition)
			if n.Body != nil {
				for _, inner := range n.Body.Statements {
					walkStmt(inner)
				}
			}
		case *ast.BlockStatement:
			for _, inner := range n.Statements {
				walkStmt(inner)
			}
		case *ast.UnsafeBlock:
			if n.Body != nil {
				for _, inner := range n.Body.Statements {
					walkStmt(inner)
				}
			}
		}
	}
	if expr != nil {
		walkExpr(expr)
	}
	return count
}

// stronglyConnectedComponents runs Tarjan's algorithm over the call graph.
// Components are emitted callees-first (reverse topological order of the
// condensation), which doubles as the rank certificate order.
func stronglyConnectedComponents(names []string, edges map[string][]callEdge) [][]string {
	index := make(map[string]int)
	lowlink := make(map[string]int)
	onStack := make(map[string]bool)
	var stack []string
	var components [][]string
	next := 0

	var strongConnect func(name string)
	strongConnect = func(name string) {
		index[name] = next
		lowlink[name] = next
		next++
		stack = append(stack, name)
		onStack[name] = true

		for _, edge := range edges[name] {
			callee := edge.callee
			if _, visited := index[callee]; !visited {
				strongConnect(callee)
				if lowlink[callee] < lowlink[name] {
					lowlink[name] = lowlink[callee]
				}
			} else if onStack[callee] {
				if index[callee] < lowlink[name] {
					lowlink[name] = index[callee]
				}
			}
		}

		if lowlink[name] == index[name] {
			var component []string
			for {
				top := stack[len(stack)-1]
				stack = stack[:len(stack)-1]
				onStack[top] = false
				component = append(component, top)
				if top == name {
					break
				}
			}
			components = append(components, component)
		}
	}

	for _, name := range names {
		if _, visited := index[name]; !visited {
			strongConnect(name)
		}
	}
	return components
}
