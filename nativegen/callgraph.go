package nativegen

import (
	"regexp"
	"sort"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
)

// The program's call graph (docs/notes/optimizer-search-2026-09.md "An
// explicit call graph"): a node per program function, an edge per static
// call site from a caller's body to a program function, and a synthetic
// root whose edges lead to the entry points — `main` and the exported
// functions — as golang.org/x/tools/go/callgraph draws one. Oak's calls
// are static but for dispatch, so the graph is sound and exact for the
// calls the native lane lowers; what it names is the structure the
// verifier's call summaries, the inliner's depth and budget, and the
// destination-passing rule already walk implicitly.

// CallGraph is the program's functions and the calls between them.
type CallGraph struct {
	Root  *CallNode
	Nodes map[string]*CallNode // by function name
}

// CallNode is one function of the graph (Fn nil for the root).
type CallNode struct {
	Name string
	Fn   *ast.FunctionStatement
	In   []*CallEdge // edges into this node (In[i].Callee == this)
	Out  []*CallEdge // edges out of this node (Out[i].Caller == this)
}

// CallEdge is one call site: Site is nil for the root's edges.
type CallEdge struct {
	Caller *CallNode
	Site   *ast.InvocationExpression
	Callee *CallNode
}

// BuildCallGraph draws the graph of the program's functions: every
// invocation of a program function by name is an edge, and the root
// calls `main` and every exported function.
func BuildCallGraph(functions map[string]*ast.FunctionStatement) *CallGraph {
	g := &CallGraph{Root: &CallNode{Name: "<root>"}, Nodes: map[string]*CallNode{}}
	names := make([]string, 0, len(functions))
	for name, fn := range functions {
		if fn == nil || fn.Name == nil {
			continue
		}
		g.Nodes[name] = &CallNode{Name: name, Fn: fn}
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		node := g.Nodes[name]
		if node.Fn.Exported || name == "main" {
			g.addEdge(g.Root, nil, node)
		}
		if node.Fn.Body == nil {
			continue
		}
		walk(node.Fn.Body, func(n ast.Node) {
			call, isCall := n.(*ast.InvocationExpression)
			if !isCall {
				return
			}
			ident, isIdent := call.Function.(*ast.Identifier)
			if !isIdent {
				return
			}
			if callee, known := g.Nodes[ident.Value]; known {
				g.addEdge(node, call, callee)
			}
		})
	}
	return g
}

func (g *CallGraph) addEdge(caller *CallNode, site *ast.InvocationExpression, callee *CallNode) {
	edge := &CallEdge{Caller: caller, Site: site, Callee: callee}
	caller.Out = append(caller.Out, edge)
	callee.In = append(callee.In, edge)
}

// Callees lists the functions a function calls, each once, sorted.
func (g *CallGraph) Callees(name string) []string {
	node := g.Nodes[name]
	if node == nil {
		return nil
	}
	return sortedNames(node.Out, func(e *CallEdge) *CallNode { return e.Callee })
}

// Callers lists the functions calling a function, each once, sorted; the
// root is not among them.
func (g *CallGraph) Callers(name string) []string {
	node := g.Nodes[name]
	if node == nil {
		return nil
	}
	return sortedNames(node.In, func(e *CallEdge) *CallNode { return e.Caller })
}

func sortedNames(edges []*CallEdge, end func(*CallEdge) *CallNode) []string {
	seen := map[string]bool{}
	var out []string
	for _, e := range edges {
		n := end(e)
		if n.Fn == nil || seen[n.Name] {
			continue
		}
		seen[n.Name] = true
		out = append(out, n.Name)
	}
	sort.Strings(out)
	return out
}

// Reachable is the set of functions the root reaches.
func (g *CallGraph) Reachable() map[string]bool {
	seen := map[string]bool{}
	var visit func(n *CallNode)
	visit = func(n *CallNode) {
		for _, e := range n.Out {
			if !seen[e.Callee.Name] {
				seen[e.Callee.Name] = true
				visit(e.Callee)
			}
		}
	}
	visit(g.Root)
	return seen
}

// Unreachable lists the functions the root does not reach, sorted: bodies
// no entry point calls, which the native lane lowers for nothing.
func (g *CallGraph) Unreachable() []string {
	reachable := g.Reachable()
	var out []string
	for name := range g.Nodes {
		if !reachable[name] {
			out = append(out, name)
		}
	}
	sort.Strings(out)
	return out
}

// Components are the graph's strongly connected components in reverse
// topological order — callees before callers — each component's members
// sorted; a component of more than one member, or one calling itself, is
// recursion.
func (g *CallGraph) Components() [][]string {
	// Tarjan's algorithm over the function nodes; the root is left out.
	index := map[string]int{}
	low := map[string]int{}
	onStack := map[string]bool{}
	var stack []string
	var components [][]string
	next := 0
	var strong func(name string)
	strong = func(name string) {
		index[name] = next
		low[name] = next
		next++
		stack = append(stack, name)
		onStack[name] = true
		for _, e := range g.Nodes[name].Out {
			callee := e.Callee.Name
			if _, visited := index[callee]; !visited {
				strong(callee)
				if low[callee] < low[name] {
					low[name] = low[callee]
				}
			} else if onStack[callee] && index[callee] < low[name] {
				low[name] = index[callee]
			}
		}
		if low[name] == index[name] {
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
			sort.Strings(component)
			components = append(components, component)
		}
	}
	names := make([]string, 0, len(g.Nodes))
	for name := range g.Nodes {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		if _, visited := index[name]; !visited {
			strong(name)
		}
	}
	return components
}

// Recursive reports the functions in a cycle of the graph.
func (g *CallGraph) Recursive() map[string]bool {
	out := map[string]bool{}
	for _, component := range g.Components() {
		if len(component) > 1 {
			for _, name := range component {
				out[name] = true
			}
			continue
		}
		name := component[0]
		for _, e := range g.Nodes[name].Out {
			if e.Callee.Name == name {
				out[name] = true
			}
		}
	}
	return out
}

// VerdictRoot is a trusted function whose own reason names no callee,
// with the trusted functions that inherit their verdict from it along the
// graph's call edges — the fix that unlocks the most callers.
type VerdictRoot struct {
	Name    string
	Reason  string
	Blocked []string // callers trusted through this root, sorted
}

var calleeInReason = regexp.MustCompile(`a call to ([A-Za-z0-9_]+)`)

// VerdictRoots follows every trusted verdict whose reason names a callee
// ("a call to X …", X the callee's native symbol) to the callee whose
// reason names none, and groups the callers under it. symbolNames maps a
// native symbol to the function's name.
func VerdictRoots(verdicts map[string]asm.Verdict, symbolNames map[string]string) []VerdictRoot {
	blockedBy := map[string][]string{}
	reasons := map[string]string{}
	for name, verdict := range verdicts {
		if verdict.Kind != asm.VerdictTrusted {
			continue
		}
		reasons[name] = verdict.Message
	}
	for name, verdict := range verdicts {
		if verdict.Kind != asm.VerdictTrusted {
			continue
		}
		root, seen := name, map[string]bool{name: true}
		for {
			m := calleeInReason.FindStringSubmatch(reasons[root])
			if m == nil {
				break
			}
			callee, known := symbolNames[m[1]]
			if !known {
				callee = m[1]
			}
			if _, trusted := reasons[callee]; !trusted || seen[callee] {
				break
			}
			seen[callee] = true
			root = callee
		}
		if root != name {
			blockedBy[root] = append(blockedBy[root], name)
		}
	}
	var out []VerdictRoot
	for root, blocked := range blockedBy {
		sort.Strings(blocked)
		out = append(out, VerdictRoot{Name: root, Reason: reasons[root], Blocked: blocked})
	}
	sort.Slice(out, func(i, j int) bool {
		if len(out[i].Blocked) != len(out[j].Blocked) {
			return len(out[i].Blocked) > len(out[j].Blocked)
		}
		return out[i].Name < out[j].Name
	})
	return out
}

