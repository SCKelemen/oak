package prove

import (
	"fmt"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/typechecker"
)

// Protocol liveness (docs/spec/125-verification.md section 2b). A
// protocol's `eventually` entries are checked over the reachable states of
// its projection: the interpreter runs name_initial, name_legal, and
// name_next over every step value (payloads enumerated like a theorem's
// parameters), the graph is labeled by step and by whether the step changed
// the state, and each entry is a fair-trap search — `<>T` fails when a fair
// behavior avoiding T exists from the initial state, `P ~> T` when one
// exists from a reachable P-state. A behavior may stutter forever, so every
// state is a candidate trap; a strongly connected set is fair when every
// weakly fair step is disabled somewhere in it or taken inside it, and
// every strongly fair step is disabled everywhere in it or taken inside it
// (refining by removing the states where a failing strongly fair step is
// enabled, as Emerson and Lei do). The verdict is about the projection —
// the first line whose guard holds — which is the executable meaning; the
// TLA+ module states the same entries over the declaration's every-line
// reading for TLC.

type liveState struct {
	key   string
	state object.Object
	data  object.Object // nil for a machine without data
}

type liveEdge struct {
	step    string // the step's variant name
	to      int
	changes bool // the step changed the state or the data
}

type liveGraph struct {
	states []liveState
	edges  [][]liveEdge
	index  map[string]int
}

// protocolLiveness reports one row per `eventually` entry of every
// protocol that declares one.
func protocolLiveness(model *compiler.SemanticModel, env *object.Environment, cases int) []Result {
	var results []Result
	for _, decl := range compiler.Protocols(model.Tree) {
		if decl.Name == nil || len(decl.Liveness) == 0 {
			continue
		}
		results = append(results, checkProtocolLiveness(model.TypeChecker, env, decl, cases)...)
	}
	return results
}

func entryText(entry *ast.ProtocolLiveness) string {
	if entry.From != nil {
		return fmt.Sprintf("eventually %s -> %s", entry.From.String(), entry.Target.String())
	}
	return "eventually " + entry.Target.String()
}

func checkProtocolLiveness(tc *typechecker.TypeChecker, env *object.Environment, decl *ast.ProtocolDeclaration, cases int) []Result {
	name := decl.Name.Value
	prefix := compiler.ProtocolPrefix(name)
	rows := func(status Status, detail string) []Result {
		results := make([]Result, 0, len(decl.Liveness))
		for k, entry := range decl.Liveness {
			results = append(results, Result{Name: fmt.Sprintf("%s_live%d", prefix, k+1), Status: status,
				Detail: entryText(entry) + ": " + detail})
		}
		return results
	}
	graph, reason := exploreProtocol(tc, env, decl, cases)
	if reason != "" {
		return rows(Open, reason)
	}
	weak, strong := map[string]bool{}, map[string]bool{}
	var fairness []string
	for _, f := range decl.Fairness {
		variant := stepVariant(f.Step.Value)
		if f.Strong {
			strong[variant] = true
			fairness = append(fairness, "strongly fair "+f.Step.Value)
		} else {
			weak[variant] = true
			fairness = append(fairness, "fair "+f.Step.Value)
		}
	}
	under := "with no fairness declared"
	if len(fairness) > 0 {
		under = "under " + strings.Join(fairness, ", ")
	}
	var results []Result
	for k, entry := range decl.Liveness {
		rowName := fmt.Sprintf("%s_live%d", prefix, k+1)
		text := entryText(entry)
		target, reason := graph.evaluate(env, compiler.ProtocolLivenessName(name, k+1, "to"))
		if reason != "" {
			results = append(results, Result{Name: rowName, Status: Open, Detail: text + ": " + reason})
			continue
		}
		var starts []int
		if entry.From == nil {
			if !target[0] {
				starts = []int{0}
			}
		} else {
			from, reason := graph.evaluate(env, compiler.ProtocolLivenessName(name, k+1, "from"))
			if reason != "" {
				results = append(results, Result{Name: rowName, Status: Open, Detail: text + ": " + reason})
				continue
			}
			for i := range graph.states {
				if from[i] && !target[i] {
					starts = append(starts, i)
				}
			}
		}
		if entry, trap := graph.fairTrap(starts, target, weak, strong); trap != nil {
			results = append(results, Result{Name: rowName, Status: Refuted,
				Detail: fmt.Sprintf("%s: counterexample %s: from %s a fair behavior never reaches the target, staying within %s",
					text, under, graph.describe(entry), graph.describeSet(trap))})
			continue
		}
		results = append(results, Result{Name: rowName, Status: Decided,
			Detail: fmt.Sprintf("%s: holds on all %d reachable states %s", text, len(graph.states), under)})
	}
	return results
}

// stepVariant spells a step name as its NameStep variant: tick -> Tick.
func stepVariant(step string) string {
	if step == "" {
		return step
	}
	return strings.ToUpper(step[:1]) + step[1:]
}

// exploreProtocol enumerates the reachable states of the projection, at
// most cases of them.
func exploreProtocol(tc *typechecker.TypeChecker, env *object.Environment, decl *ast.ProtocolDeclaration, cases int) (*liveGraph, string) {
	name := decl.Name.Value
	prefix := compiler.ProtocolPrefix(name)
	lookup := func(fn string) (object.Object, string) {
		value, found := env.Get(fn)
		if !found {
			return nil, fmt.Sprintf("the projection %s is not loaded", fn)
		}
		return value, ""
	}
	initialFn, reason := lookup(prefix + "_initial")
	if reason != "" {
		return nil, reason
	}
	legalFn, reason := lookup(prefix + "_legal")
	if reason != "" {
		return nil, reason
	}
	nextFn, reason := lookup(prefix + "_next")
	if reason != "" {
		return nil, reason
	}
	withData := decl.Data != nil
	var initialDataFn object.Object
	if withData {
		if initialDataFn, reason = lookup(prefix + "_initial_data"); reason != "" {
			return nil, reason
		}
	}
	stepType := tc.ParseTypeExpression(&ast.Identifier{Value: name + "Step"})
	if stepType == nil {
		return nil, "the step type does not resolve"
	}
	steps, reason := valuesOf(tc, env, stepType)
	if reason != "" {
		return nil, "steps: " + reason
	}
	call := func(fn object.Object, args ...object.Object) (object.Object, string) {
		outcome := evaluator.Apply(fn, args)
		if e, isErr := outcome.(*object.Error); isErr {
			return nil, "evaluation failed: " + e.Message
		}
		return outcome, ""
	}
	graph := &liveGraph{index: map[string]int{}}
	s0, reason := call(initialFn)
	if reason != "" {
		return nil, reason
	}
	var d0 object.Object
	if withData {
		if d0, reason = call(initialDataFn); reason != "" {
			return nil, reason
		}
	}
	graph.add(s0, d0)
	for at := 0; at < len(graph.states); at++ {
		current := graph.states[at]
		for _, step := range steps {
			var legal object.Object
			if withData {
				legal, reason = call(legalFn, current.state, deepCopy(current.data), step)
			} else {
				legal, reason = call(legalFn, current.state, step)
			}
			if reason != "" {
				return nil, reason
			}
			if flag, isBool := legal.(*object.Boolean); !isBool || !flag.Value {
				continue
			}
			var next, nextData object.Object
			if withData {
				buffer := &object.Array{Elements: []object.Object{deepCopy(current.data)}}
				span := &object.View{Array: buffer, Start: 0, Len: 1, Writable: true}
				if next, reason = call(nextFn, current.state, span, step); reason != "" {
					return nil, reason
				}
				nextData = buffer.Elements[0]
			} else if next, reason = call(nextFn, current.state, step); reason != "" {
				return nil, reason
			}
			to := graph.add(next, nextData)
			if len(graph.states) > cases {
				return nil, fmt.Sprintf("more than %d reachable states (raise -cases)", cases)
			}
			variant := ""
			if adt, isADT := step.(*object.ADTValue); isADT {
				variant = adt.Variant
			}
			graph.edges[at] = append(graph.edges[at], liveEdge{step: variant, to: to, changes: to != at})
		}
	}
	return graph, ""
}

func (g *liveGraph) add(state, data object.Object) int {
	key := canonicalKey(state)
	if data != nil {
		key += "|" + canonicalKey(data)
	}
	if at, seen := g.index[key]; seen {
		return at
	}
	g.index[key] = len(g.states)
	g.states = append(g.states, liveState{key: key, state: state, data: data})
	g.edges = append(g.edges, nil)
	return len(g.states) - 1
}

// evaluate applies a projected predicate to every reachable state.
func (g *liveGraph) evaluate(env *object.Environment, predicate string) ([]bool, string) {
	fn, found := env.Get(predicate)
	if !found {
		return nil, fmt.Sprintf("the projection %s is not loaded", predicate)
	}
	out := make([]bool, len(g.states))
	for i, st := range g.states {
		args := []object.Object{st.state}
		if st.data != nil {
			args = append(args, deepCopy(st.data))
		}
		switch v := evaluator.Apply(fn, args).(type) {
		case *object.Boolean:
			out[i] = v.Value
		case *object.Error:
			return nil, "evaluation failed: " + v.Message
		default:
			return nil, "the predicate did not evaluate to a Bool"
		}
	}
	return out, ""
}

// fairTrap searches, from the start states and within the states that do
// not satisfy target, for a fair strongly connected set; it returns the
// start state that reaches it and the set.
func (g *liveGraph) fairTrap(starts []int, target []bool, weak, strong map[string]bool) (int, []int) {
	for _, start := range starts {
		// The states reachable from start without passing through the target.
		reach := map[int]bool{start: true}
		queue := []int{start}
		for len(queue) > 0 {
			at := queue[0]
			queue = queue[1:]
			for _, edge := range g.edges[at] {
				if !target[edge.to] && !reach[edge.to] {
					reach[edge.to] = true
					queue = append(queue, edge.to)
				}
			}
		}
		if trap := g.fairComponent(reach, weak, strong); trap != nil {
			return start, trap
		}
	}
	return -1, nil
}

// fairComponent finds a fair strongly connected set inside the given set
// of states, or nil.
func (g *liveGraph) fairComponent(set map[int]bool, weak, strong map[string]bool) []int {
	for _, component := range g.components(set) {
		inside := map[int]bool{}
		for _, at := range component {
			inside[at] = true
		}
		enabledIn := func(at int, step string) bool {
			for _, edge := range g.edges[at] {
				if edge.step == step && edge.changes {
					return true
				}
			}
			return false
		}
		takenInside := func(step string) bool {
			for _, at := range component {
				for _, edge := range g.edges[at] {
					if edge.step == step && edge.changes && inside[edge.to] {
						return true
					}
				}
			}
			return false
		}
		dead := false
		for step := range weak {
			everywhere := true
			for _, at := range component {
				if !enabledIn(at, step) {
					everywhere = false
					break
				}
			}
			if everywhere && !takenInside(step) {
				dead = true // no sub-cycle can escape a step that is enabled throughout
				break
			}
		}
		if dead {
			continue
		}
		var failing []string
		for step := range strong {
			somewhere := false
			for _, at := range component {
				if enabledIn(at, step) {
					somewhere = true
					break
				}
			}
			if somewhere && !takenInside(step) {
				failing = append(failing, step)
			}
		}
		if len(failing) == 0 {
			sort.Ints(component)
			return component
		}
		// A strongly fair step enabled somewhere but never taken: a smaller
		// trap may avoid the states where it is enabled.
		smaller := map[int]bool{}
		for _, at := range component {
			keep := true
			for _, step := range failing {
				if enabledIn(at, step) {
					keep = false
				}
			}
			if keep {
				smaller[at] = true
			}
		}
		if len(smaller) > 0 && len(smaller) < len(component) {
			if trap := g.fairComponent(smaller, weak, strong); trap != nil {
				return trap
			}
		}
	}
	return nil
}

// components lists the strongly connected components of the subgraph on
// set (Tarjan), singletons included.
func (g *liveGraph) components(set map[int]bool) [][]int {
	index := map[int]int{}
	low := map[int]int{}
	onStack := map[int]bool{}
	var stack []int
	var out [][]int
	counter := 0
	var visit func(at int)
	visit = func(at int) {
		index[at] = counter
		low[at] = counter
		counter++
		stack = append(stack, at)
		onStack[at] = true
		for _, edge := range g.edges[at] {
			if !set[edge.to] {
				continue
			}
			if _, seen := index[edge.to]; !seen {
				visit(edge.to)
				if low[edge.to] < low[at] {
					low[at] = low[edge.to]
				}
			} else if onStack[edge.to] && index[edge.to] < low[at] {
				low[at] = index[edge.to]
			}
		}
		if low[at] == index[at] {
			var component []int
			for {
				top := stack[len(stack)-1]
				stack = stack[:len(stack)-1]
				onStack[top] = false
				component = append(component, top)
				if top == at {
					break
				}
			}
			out = append(out, component)
		}
	}
	nodes := make([]int, 0, len(set))
	for at := range set {
		nodes = append(nodes, at)
	}
	sort.Ints(nodes)
	for _, at := range nodes {
		if _, seen := index[at]; !seen {
			visit(at)
		}
	}
	return out
}

func (g *liveGraph) describe(at int) string {
	st := g.states[at]
	if st.data == nil {
		return canonicalKey(st.state)
	}
	return canonicalKey(st.state) + " with " + canonicalKey(st.data)
}

func (g *liveGraph) describeSet(set []int) string {
	parts := make([]string, 0, len(set))
	for i, at := range set {
		if i == 4 {
			parts = append(parts, fmt.Sprintf("... (%d states)", len(set)))
			break
		}
		parts = append(parts, g.describe(at))
	}
	return "{" + strings.Join(parts, "; ") + "}"
}

// canonicalKey renders a value deterministically (record fields sorted),
// as the identity of a state.
func canonicalKey(value object.Object) string {
	switch v := value.(type) {
	case *object.Record:
		names := make([]string, 0, len(v.Fields))
		for name := range v.Fields {
			names = append(names, name)
		}
		sort.Strings(names)
		parts := make([]string, len(names))
		for i, name := range names {
			parts[i] = name + ": " + canonicalKey(v.Fields[name])
		}
		return "{" + strings.Join(parts, ", ") + "}"
	case *object.Array:
		parts := make([]string, len(v.Elements))
		for i, element := range v.Elements {
			parts[i] = canonicalKey(element)
		}
		return "[" + strings.Join(parts, ", ") + "]"
	case *object.ADTValue:
		if v.Value != nil {
			return v.Variant + "(" + canonicalKey(v.Value) + ")"
		}
		return v.Variant
	case nil:
		return "()"
	}
	return value.Inspect()
}

// deepCopy duplicates the mutable structure of a value, so a projection
// that writes through its span never reaches an explored state.
func deepCopy(value object.Object) object.Object {
	switch v := value.(type) {
	case *object.Record:
		fields := make(map[string]object.Object, len(v.Fields))
		for name, field := range v.Fields {
			fields[name] = deepCopy(field)
		}
		return &object.Record{Fields: fields}
	case *object.Array:
		elements := make([]object.Object, len(v.Elements))
		for i, element := range v.Elements {
			elements[i] = deepCopy(element)
		}
		return &object.Array{Elements: elements}
	case *object.ADTValue:
		if v.Value == nil {
			return v
		}
		return &object.ADTValue{TypeName: v.TypeName, Variant: v.Variant, Value: deepCopy(v.Value)}
	}
	return value
}

// exploreInvariants gives an invariant candidate the inductive check left
// short of `decided` — a data domain too large to enumerate, or an
// inductive step that fails only at a state no run reaches — a verdict
// over the reachable states themselves: the candidate is evaluated on
// every state the projection reaches (prove/liveness.go's exploration,
// bounded by cases). The reachable graph of a machine over a u32 budget
// is small even though the domain is not, so the row is decided or
// refuted with a reachable counterexample; a graph beyond the bound keeps
// the inductive summary.
func exploreInvariants(results []Result, model *compiler.SemanticModel, env *object.Environment, cases int) []Result {
	candidates := invariantCandidates(model.Tree)
	if len(candidates) == 0 {
		return results
	}
	graphs := map[string]*liveGraph{}
	reasons := map[string]string{}
	for i, r := range results {
		decl, isCandidate := candidates[r.Name]
		if !isCandidate || r.Status == Decided {
			continue
		}
		name := decl.Name.Value
		graph, explored := graphs[name]
		if !explored {
			if _, failed := reasons[name]; failed {
				continue
			}
			var reason string
			graph, reason = exploreProtocol(model.TypeChecker, env, decl, cases)
			if reason != "" {
				reasons[name] = reason
				results[i].Detail += " (reachable states: " + reason + ")"
				continue
			}
			graphs[name] = graph
		}
		holds, reason := graph.evaluate(env, r.Name)
		if reason != "" {
			results[i].Detail += " (reachable states: " + reason + ")"
			continue
		}
		failing := -1
		for at, ok := range holds {
			if !ok {
				failing = at
				break
			}
		}
		if failing >= 0 {
			results[i] = Result{Name: r.Name, Status: Refuted,
				Detail: fmt.Sprintf("invariant fails at the reachable state %s (%s)", graph.describe(failing), r.Detail)}
			continue
		}
		results[i] = Result{Name: r.Name, Status: Decided,
			Detail: fmt.Sprintf("invariant: holds on all %d reachable states (%s)", len(graph.states), r.Detail)}
	}
	return results
}
