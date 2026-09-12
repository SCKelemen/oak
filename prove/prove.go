// Package prove discharges a checked program's theorems
// (docs/spec/125-verification.md). A theorem is a Bool-valued function whose
// parameters are universally quantified; this package runs the ladder the
// spec states — the compiler's own deciders first, the Lean projection for
// the rest — and reports one status per theorem. Nothing here is trusted
// beyond what it computes: a `decided` theorem was evaluated on every
// element of its finite domain by the interpreter that the differential
// witnesses hold to the compiled program, and an `open` theorem carries the
// reason it is open.
package prove

import (
	"fmt"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/token"
	"github.com/SCKelemen/oak/typechecker"
)

// Status is where a theorem stands on the ladder.
type Status string

const (
	// Decided: the compiler evaluated the statement on every element of its
	// finite parameter domain and every case held.
	Decided Status = "decided"
	// Refuted: the compiler found a counterexample; the theorem is false.
	Refuted Status = "refuted"
	// Open: no decider applies; the Lean projection carries the statement.
	Open Status = "open"
	// Pending marks a theorem whose bit-level decision is deferred to the
	// Oak solver (TheoremsWith with deferred set): the result carries its
	// problems and ResolvePending settles it.
	Pending Status = "pending"
)

// Result is one theorem's outcome.
type Result struct {
	Name   string
	Status Status
	// Detail says how the status was reached: the number of cases decided,
	// the counterexample, or why the deciders do not apply.
	Detail string
	// Order and Nodes are set for a theorem decided at the bit level: the
	// variable order that proved it and the diagram's size, which the Oak
	// solver replays (ProblemFor).
	Order string
	Nodes int
	// Problems are a pending theorem's serializations, one per variable
	// order, for the Oak solver; fallback is what stands when the solver
	// cannot decide (enumeration, or the open result with its reason).
	Problems []asm.Problem
	// Syntax is the theorem serialized for the lowering written in Oak
	// (asm.ExportSyntax), when it is in that lowering's subset.
	Syntax []uint32
	// LeafNames are the theorem's parameter leaves in the decider's name
	// order, which the Oak lowering's counterexamples (leaf and bit) name.
	LeafNames []string
	fallback  func() Result
}

// SolverVerdict is what the Oak solver reports for one theorem: the
// status (0 proven, 1 refuted, 2 budget exceeded, 3 unsupported), which
// variant (variable order) decided, its node count, and, for a refuted
// theorem, the variables set on a path to the failing root.
type SolverVerdict struct {
	Status int
	Winner int
	Nodes  int
	Vars   []uint32
	// Lowered is set when the Oak lowering produced the terms (the
	// interleaved order), not the Go lowering's serialized problem.
	Lowered bool
}

// DefaultCases bounds the exhaustive decider: the product of the parameter
// domains a theorem is evaluated over.
const DefaultCases = 1 << 16

// Theorems discharges every theorem of the checked model, in source order.
// cases bounds the exhaustive decider (DefaultCases when zero).
func Theorems(model *compiler.SemanticModel, cases int) ([]Result, error) {
	return TheoremsWith(model, cases, false)
}

// TheoremsWith is Theorems with the bit-level rung deferred when asked:
// a theorem the exhaustive decider does not reach is returned Pending
// with its problems (asm.ExportProblems) for the Oak solver, after the
// Go decider's witness pass has had its say, and ResolvePending settles it
// from the solver's verdict.
func TheoremsWith(model *compiler.SemanticModel, cases int, deferred bool) ([]Result, error) {
	if model == nil || model.Tree == nil || model.Tree.Root == nil || model.TypeChecker == nil {
		return nil, fmt.Errorf("prove: no checked program")
	}
	if cases <= 0 {
		cases = DefaultCases
	}
	theorems := typechecker.Theorems(model.Tree.Root)
	liveness := 0
	for _, decl := range compiler.Protocols(model.Tree) {
		liveness += len(decl.Liveness)
	}
	if len(theorems) == 0 && liveness == 0 {
		return nil, nil
	}
	env := object.NewEnvironment()
	env.SetArithmeticWidths(model.TypeChecker.ArithmeticType)
	if evaluated := evaluator.Eval(model.Tree.Root, env); evaluated != nil {
		if e, isErr := evaluated.(*object.Error); isErr {
			return nil, fmt.Errorf("prove: loading the program in the interpreter: %s", e.Message)
		}
	}
	functions := map[string]*ast.FunctionStatement{}
	for _, stmt := range model.Tree.Root.Statements {
		if fn, isFn := stmt.(*ast.FunctionStatement); isFn && fn.Name != nil {
			functions[fn.Name.Value] = fn
		}
	}
	decls := declarationsOf(model.Tree.Root)
	var results []Result
	for _, theorem := range theorems {
		results = append(results, decide(env, model.TypeChecker, functions, decls, theorem, cases, deferred))
	}
	// A protocol's `eventually` entries are decided over its reachable
	// states (prove/liveness.go), after the theorems.
	results = summarizeInvariants(results)
	results = exploreInvariants(results, model, env, cases)
	return append(results, protocolLiveness(model, env, cases)...), nil
}

// summarizeInvariants folds the generated obligations of an invariant
// candidate into the candidate's own row: an invariant is a claim about
// the reachable states, not every state, so the candidate is reported by
// its base and step obligations rather than as a universal statement.
func summarizeInvariants(results []Result) []Result {
	byName := map[string]Result{}
	for _, r := range results {
		byName[r.Name] = r
	}
	for i, r := range results {
		base, hasBase := byName[r.Name+BaseSuffix]
		step, hasStep := byName[r.Name+StepSuffix]
		if !hasBase || !hasStep {
			continue
		}
		switch {
		case base.Status == Decided && step.Status == Decided:
			results[i] = Result{Name: r.Name, Status: Decided,
				Detail: fmt.Sprintf("invariant: base %s, step %s", base.Detail, step.Detail)}
		case base.Status == Refuted:
			results[i] = Result{Name: r.Name, Status: Refuted, Detail: "invariant fails initially: " + base.Detail}
		case step.Status == Refuted:
			results[i] = Result{Name: r.Name, Status: Refuted, Detail: "invariant is not preserved: " + step.Detail}
		default:
			results[i] = Result{Name: r.Name, Status: Open,
				Detail: fmt.Sprintf("invariant: base %s (%s), step %s (%s)", base.Status, base.Detail, step.Status, step.Detail)}
		}
	}
	return results
}

// domainSize is the number of values valuesOf would materialize for a
// type, computed before any of them is built so a wide record or sum is
// refused against the cases bound rather than enumerated. A refinement
// counts exactly the base values its constructor admits (one pass over an
// 8- or 16-bit base), so `Replica: type = u8 where value < u8(2)` is two
// values, not 256. The reason is valuesOf's.
func domainSize(tc *typechecker.TypeChecker, env *object.Environment, typ typechecker.Type) (int64, string) {
	switch t := typ.(type) {
	case *typechecker.BoolType:
		return 2, ""
	case *typechecker.PrimitiveType:
		var base int64
		switch t.Name {
		case "u8", "i8":
			base = 256
		case "u16", "i16":
			base = 65536
		default:
			return 0, fmt.Sprintf("%s is not a finite scalar, enum, or record type", typ.String())
		}
		if t.Refinement == "" {
			return base, ""
		}
		values, reason := valuesOf(tc, env, typ)
		if reason != "" {
			return 0, reason
		}
		return int64(len(values)), ""
	case *typechecker.ADTType:
		variants, ok := tc.ADTVariants(t.Name)
		if !ok {
			return 0, fmt.Sprintf("%s is generic or unknown", t.Name)
		}
		var total int64
		for _, variant := range variants {
			if variant.Payload != nil {
				if _, isUnit := variant.Payload.(*typechecker.UnitType); !isUnit {
					n, reason := domainSize(tc, env, variant.Payload)
					if reason != "" {
						return 0, fmt.Sprintf("%s.%s: payload: %s", t.Name, variant.Name, reason)
					}
					total += n
					continue
				}
			}
			total++
		}
		return total, ""
	case *typechecker.RecordType:
		if t.Name == "" {
			return 0, "an anonymous record shape is not enumerated"
		}
		order, fields, ok := tc.RecordFields(t.Name)
		if !ok {
			return 0, fmt.Sprintf("%s is not a declared record", t.Name)
		}
		total := int64(1)
		for _, field := range order {
			n, reason := domainSize(tc, env, fields[field])
			if reason != "" {
				return 0, fmt.Sprintf("field %s: %s", field, reason)
			}
			total *= n
			if total > 1<<40 {
				return total, ""
			}
		}
		return total, ""
	}
	return 0, fmt.Sprintf("%s is not a finite scalar, enum, or record type", typ.String())
}

// domain is the finite set of values a parameter type ranges over.
type domain struct {
	name   string
	values []object.Object
}

// domainOf enumerates a parameter's type, or says why it cannot: `Bool`,
// the 8- and 16-bit integers, payload-free sum types, and declared records
// of those (the product of the field domains) are finite; anything else is
// stated for Lean.
func domainOf(tc *typechecker.TypeChecker, env *object.Environment, param *ast.FunctionParameter) (domain, string) {
	typ := tc.ParseTypeExpression(param.Type)
	if typ == nil {
		return domain{}, fmt.Sprintf("parameter %s: %s does not resolve to a type", param.Name.Value, param.Type.String())
	}
	values, reason := valuesOf(tc, env, typ)
	if reason != "" {
		return domain{}, fmt.Sprintf("parameter %s: %s", param.Name.Value, reason)
	}
	return domain{name: param.Name.Value, values: values}, ""
}

func valuesOf(tc *typechecker.TypeChecker, env *object.Environment, typ typechecker.Type) ([]object.Object, string) {
	switch t := typ.(type) {
	case *typechecker.BoolType:
		return []object.Object{evaluator.Bool(false), evaluator.Bool(true)}, ""
	case *typechecker.PrimitiveType:
		var base []object.Object
		switch t.Name {
		case "u8":
			base = integers(0, 255)
		case "i8":
			base = integers(-128, 127)
		case "u16":
			base = integers(0, 65535)
		case "i16":
			base = integers(-32768, 32767)
		default:
			return nil, fmt.Sprintf("%s is not a finite scalar, enum, or record type", typ.String())
		}
		if t.Refinement == "" {
			return base, ""
		}
		// A refinement's values: the base values its construction accepts.
		construct, found := env.Get(t.Refinement)
		if !found {
			return nil, fmt.Sprintf("refinement %s is not loaded", t.Refinement)
		}
		var values []object.Object
		for _, v := range base {
			if _, failed := evaluator.Apply(construct, []object.Object{v}).(*object.Error); !failed {
				values = append(values, v)
			}
		}
		return values, ""
	case *typechecker.ADTType:
		variants, ok := tc.ADTVariants(t.Name)
		if !ok {
			return nil, fmt.Sprintf("%s is generic or unknown", t.Name)
		}
		// Every variant, and for a variant with a payload every payload
		// value: a protocol's steps with their scalar payloads enumerate.
		var values []object.Object
		for _, variant := range variants {
			if variant.Payload != nil {
				if _, isUnit := variant.Payload.(*typechecker.UnitType); !isUnit {
					payloads, reason := valuesOf(tc, env, variant.Payload)
					if reason != "" {
						return nil, fmt.Sprintf("%s.%s: payload: %s", t.Name, variant.Name, reason)
					}
					for _, payload := range payloads {
						values = append(values, &object.ADTValue{TypeName: t.Name, Variant: variant.Name, Value: payload})
					}
					continue
				}
			}
			values = append(values, &object.ADTValue{TypeName: t.Name, Variant: variant.Name})
		}
		return values, ""
	case *typechecker.RecordType:
		if t.Name == "" {
			return nil, "an anonymous record shape is not enumerated"
		}
		order, fields, ok := tc.RecordFields(t.Name)
		if !ok {
			return nil, fmt.Sprintf("%s is not a declared record", t.Name)
		}
		// The product of the field domains, one record per tuple.
		values := []object.Object{&object.Record{Fields: map[string]object.Object{}}}
		for _, field := range order {
			fieldValues, reason := valuesOf(tc, env, fields[field])
			if reason != "" {
				return nil, fmt.Sprintf("field %s: %s", field, reason)
			}
			var next []object.Object
			for _, partial := range values {
				for _, value := range fieldValues {
					record := &object.Record{Fields: map[string]object.Object{}}
					for k, v := range partial.(*object.Record).Fields {
						record.Fields[k] = v
					}
					record.Fields[field] = value
					next = append(next, record)
				}
			}
			values = next
		}
		return values, ""
	}
	return nil, fmt.Sprintf("%s is not a finite scalar, enum, or record type", typ.String())
}

func integers(low, high int64) []object.Object {
	values := make([]object.Object, 0, high-low+1)
	for v := low; v <= high; v++ {
		values = append(values, &object.Integer{Value: v})
	}
	return values
}

// decide runs the exhaustive decider on one theorem.
func decide(env *object.Environment, tc *typechecker.TypeChecker, functions map[string]*ast.FunctionStatement, decls asm.Declarations, theorem *ast.FunctionStatement, cases int, deferred bool) Result {
	name := theorem.Name.Value
	fn, found := env.Get(name)
	if !found {
		return Result{Name: name, Status: Open, Detail: "the interpreter did not load the theorem"}
	}
	// A protocol obligation's row is folded into its invariant's before the
	// deferred verdicts land (exploreInvariants), so it stays with the Go
	// decider.
	deferred = deferred && !strings.Contains(name, "__")
	var domains []domain
	total := 1
	for _, param := range theorem.Parameters {
		// Size before materializing: a payload record of two u8 fields is
		// 65536 values, and the product of several is refused here rather
		// than built.
		if typ := tc.ParseTypeExpression(param.Type); typ != nil {
			if size, reason := domainSize(tc, env, typ); reason == "" && int64(total)*size > int64(cases) {
				return bitLevel(deferred, tc, decls, theorem, functions, Result{Name: name, Status: Open,
					Detail: fmt.Sprintf("the domain exceeds %d cases; stated for Lean", cases)})
			}
		}
		d, reason := domainOf(tc, env, param)
		if reason != "" {
			return bitLevel(deferred, tc, decls, theorem, functions, Result{Name: name, Status: Open, Detail: reason + "; stated for Lean"})
		}
		domains = append(domains, d)
		total *= len(d.values)
		if total > cases {
			return bitLevel(deferred, tc, decls, theorem, functions, Result{Name: name, Status: Open,
				Detail: fmt.Sprintf("the domain exceeds %d cases; stated for Lean", cases)})
		}
	}
	// A body with a counted loop goes to the bit-level decider first: the
	// unrolled loop is one term there and the interpreter's costly case
	// (a 64-step product evaluated 65536 times). Enumeration remains the
	// answer when the bit level does not apply.
	if loopHeavy(theorem, functions) {
		r := bitLevel(deferred, tc, decls, theorem, functions, Result{Name: name, Status: Open})
		if r.Status == Pending {
			// Enumeration stands when the solver cannot decide.
			r.fallback = func() Result { return enumerate(name, fn, domains, total) }
			return r
		}
		if r.Status != Open {
			return r
		}
	}
	return enumerate(name, fn, domains, total)
}

// enumerate runs the theorem on every element of its parameter domains.
func enumerate(name string, fn object.Object, domains []domain, total int) Result {
	args := make([]object.Object, len(domains))
	indices := make([]int, len(domains))
	for {
		for i, d := range domains {
			args[i] = d.values[indices[i]]
		}
		outcome := evaluator.Apply(fn, args)
		switch v := outcome.(type) {
		case *object.Boolean:
			if !v.Value {
				return Result{Name: name, Status: Refuted, Detail: "counterexample " + assignment(domains, args)}
			}
		case *object.Error:
			return Result{Name: name, Status: Open, Detail: fmt.Sprintf("evaluation failed at %s: %s", assignment(domains, args), v.Message)}
		default:
			return Result{Name: name, Status: Open, Detail: fmt.Sprintf("the statement evaluated to %s, not a Bool", outcome.Inspect())}
		}
		// Advance the odometer.
		i := len(indices) - 1
		for ; i >= 0; i-- {
			indices[i]++
			if indices[i] < len(domains[i].values) {
				break
			}
			indices[i] = 0
		}
		if i < 0 {
			break
		}
	}
	return Result{Name: name, Status: Decided, Detail: fmt.Sprintf("all %d cases", total)}
}

// loopHeavy reports whether a theorem's body, or the body of a program
// function it names, contains a `while`.
func loopHeavy(theorem *ast.FunctionStatement, functions map[string]*ast.FunctionStatement) bool {
	if theorem.Body == nil {
		return false
	}
	body := theorem.Body.String()
	if strings.Contains(body, "while") {
		return true
	}
	seen := map[string]bool{}
	pending := []string{body}
	for len(pending) > 0 {
		text := pending[0]
		pending = pending[1:]
		for name, fn := range functions {
			if seen[name] || fn.Body == nil || !strings.Contains(text, name) {
				continue
			}
			seen[name] = true
			callee := fn.Body.String()
			if strings.Contains(callee, "while") {
				return true
			}
			pending = append(pending, callee)
		}
	}
	return false
}

// bitLevel is the bit-level rung: the Go decider (blastOr), or, when
// deferred, the witness pass now and the Oak solver later — a Pending
// result carrying the problems and, as fallback, the open result.
func bitLevel(deferred bool, tc *typechecker.TypeChecker, decls asm.Declarations, theorem *ast.FunctionStatement, functions map[string]*ast.FunctionStatement, open Result) Result {
	if !deferred {
		return blastOr(tc, decls, theorem, functions, open)
	}
	stated, callees, guards, reason := forDecider(tc, theorem, functions)
	if reason != "" {
		return Result{Name: open.Name, Status: Open, Detail: open.Detail + " (bit-level: " + reason + ")"}
	}
	if decision, settled := asm.WitnessRefutation(stated, callees, guards, decls); settled {
		if decision.Kind == asm.DecisionRefuted {
			return Result{Name: open.Name, Status: Refuted, Detail: decision.Message}
		}
		return Result{Name: open.Name, Status: Open, Detail: open.Detail + " (bit-level: " + decision.Message + ")"}
	}
	problems, reason, ok := asm.ExportProblems(stated, callees, guards, decls, asm.NodeBudget)
	if !ok {
		return Result{Name: open.Name, Status: Open, Detail: open.Detail + " (bit-level: " + reason + ")"}
	}
	fallback := Result{Name: open.Name, Status: Open, Detail: open.Detail}
	syntax, leafNames, _, inSubset := asm.ExportSyntax(stated, callees, decls)
	if !inSubset {
		syntax, leafNames = nil, nil
	}
	return Result{Name: open.Name, Status: Pending, Problems: problems, Syntax: syntax, LeafNames: leafNames, fallback: func() Result { return fallback }}
}

// ResolvePending settles the pending results from the Oak solver's
// verdicts (by theorem name): proven becomes decided at the bit level with
// the winning order and node count, refuted carries the counterexample
// read through the problem's owner map, and a budget exceeded or an
// unsupported term falls back — to the Go decider under every order for
// the unsupported (goDecider), else to the pending result's fallback.
func ResolvePending(results []Result, verdicts map[string]SolverVerdict, goDecider func(name string) (Result, bool)) []Result {
	for i, r := range results {
		if r.Status != Pending {
			continue
		}
		v, has := verdicts[r.Name]
		settled := Result{Name: r.Name}
		switch {
		case has && v.Lowered && v.Status == 0:
			order := []string{"interleaved", "blocks", "control"}[v.Winner%3]
			label := ""
			if order != "interleaved" {
				label = ", " + map[string]string{"blocks": "parameters in blocks", "control": "control bits first"}[order]
			}
			settled = Result{Name: r.Name, Status: Decided, Detail: fmt.Sprintf("at the bit level (%d BDD nodes%s; lowered and decided in Oak)", v.Nodes, label), Order: order, Nodes: v.Nodes}
		case has && v.Lowered && v.Status == 1:
			settled = Result{Name: r.Name, Status: Refuted, Detail: "counterexample " + leafCounterexample(r.LeafNames, v.Vars) + " (lowered and decided in Oak)"}
		case has && v.Status == 0 && v.Winner >= 0 && v.Winner < len(r.Problems):
			order := r.Problems[v.Winner].Order
			label := ""
			if order != "interleaved" {
				label = ", " + map[string]string{"blocks": "parameters in blocks", "control": "control bits first"}[order]
			}
			settled = Result{Name: r.Name, Status: Decided, Detail: fmt.Sprintf("at the bit level (%d BDD nodes%s; the Oak solver)", v.Nodes, label), Order: order, Nodes: v.Nodes}
		case has && v.Status == 1 && v.Winner >= 0 && v.Winner < len(r.Problems):
			settled = Result{Name: r.Name, Status: Refuted, Detail: "counterexample " + r.Problems[v.Winner].Counterexample(v.Vars) + " (the Oak solver)"}
		case has && v.Status == 3 && goDecider != nil:
			if fromGo, ok := goDecider(r.Name); ok {
				settled = fromGo
			} else {
				settled = r.fallback()
			}
		default:
			settled = r.fallback()
			if settled.Status == Open {
				settled.Detail += " (bit-level: the Oak solver exceeded its node budget)"
			}
		}
		results[i] = settled
	}
	return results
}

// leafCounterexample renders the Oak lowering's witness — the leaf bits set
// on a path to the failing root, each as leaf * 64 + bit — over the
// theorem's leaves, every unset bit zero.
func leafCounterexample(leafNames []string, setBits []uint32) string {
	values := make([]uint64, len(leafNames))
	for _, lb := range setBits {
		leaf, bit := int(lb/64), lb%64
		if leaf < len(values) {
			values[leaf] |= uint64(1) << bit
		}
	}
	parts := make([]string, 0, len(leafNames))
	for i, name := range leafNames {
		parts = append(parts, fmt.Sprintf("%s=%d", name, values[i]))
	}
	return strings.Join(parts, ", ")
}

// GoDecision runs the Go decider on the named theorem: the cross-check of
// the Oak solver, under one order when given (the node counts must match)
// or under every order.
func GoDecision(model *compiler.SemanticModel, name, order string) (Result, bool) {
	stated, callees, guards, decls, reason, err := deciderInputs(model, name)
	if err != nil || reason != "" {
		return Result{}, false
	}
	var decision asm.Decision
	if order != "" {
		decision = asm.DecideWithOrder(stated, callees, guards, decls, order)
	} else {
		decision = asm.DecideTheoremWith(stated, callees, guards, decls)
	}
	switch decision.Kind {
	case asm.DecisionProven:
		return Result{Name: name, Status: Decided, Detail: decision.Message, Order: decision.Order, Nodes: decision.Nodes}, true
	case asm.DecisionRefuted:
		return Result{Name: name, Status: Refuted, Detail: decision.Message}, true
	}
	return Result{Name: name, Status: Open, Detail: decision.Message}, true
}

// blastOr runs the bit-level decider (asm.DecideTheorem) on a theorem the
// exhaustive decider does not reach, and keeps the given open result when
// the decider does not apply either.
func blastOr(tc *typechecker.TypeChecker, decls asm.Declarations, theorem *ast.FunctionStatement, functions map[string]*ast.FunctionStatement, open Result) Result {
	stated, callees, guards, reason := forDecider(tc, theorem, functions)
	if reason != "" {
		return Result{Name: open.Name, Status: Open, Detail: open.Detail + " (bit-level: " + reason + ")"}
	}
	decision := asm.DecideTheoremWith(stated, callees, guards, decls)
	switch decision.Kind {
	case asm.DecisionProven:
		return Result{Name: open.Name, Status: Decided, Detail: decision.Message, Order: decision.Order, Nodes: decision.Nodes}
	case asm.DecisionRefuted:
		return Result{Name: open.Name, Status: Refuted, Detail: decision.Message}
	}
	return Result{Name: open.Name, Status: Open, Detail: open.Detail + " (bit-level: " + decision.Message + ")"}
}

// forDecider restates a theorem and the program's functions for the
// bit-level decider, which knows fixed-width scalars and nothing of
// refinements (docs/spec/20-types.md section 12): a refined parameter is
// its base with the predicate as a hypothesis (`!pred || body`, so the
// claim is about the values the construction admits), a refined
// parameter or return type of a callee is its base, and each refinement
// is handed over as a guard so a construction in a body is a trap
// obligation. reason is set when a predicate cannot be restated.
func forDecider(tc *typechecker.TypeChecker, theorem *ast.FunctionStatement, functions map[string]*ast.FunctionStatement) (*ast.FunctionStatement, map[string]*ast.FunctionStatement, map[string]asm.Guard, string) {
	baseOf := func(typ ast.Expression) (ast.Expression, string, bool) {
		ident, isIdent := typ.(*ast.Identifier)
		if !isIdent {
			return typ, "", false
		}
		base, _, isRefinement := tc.Refinement(ident.Value)
		if !isRefinement {
			return typ, "", false
		}
		return &ast.Identifier{Token: ident.Token, Value: base}, ident.Value, true
	}
	retype := func(fn *ast.FunctionStatement) (*ast.FunctionStatement, []string) {
		var refined []string
		changed := false
		params := make([]*ast.FunctionParameter, len(fn.Parameters))
		for i, p := range fn.Parameters {
			params[i] = p
			if p == nil || p.Type == nil {
				refined = append(refined, "")
				continue
			}
			base, name, isRefined := baseOf(p.Type)
			refined = append(refined, name)
			if isRefined {
				clone := *p
				clone.Type = base
				params[i] = &clone
				changed = true
			}
		}
		out := fn
		ret := fn.ReturnType
		if fn.ReturnType != nil {
			if base, _, isRefined := baseOf(fn.ReturnType); isRefined {
				ret = base
				changed = true
			}
		}
		if changed {
			clone := *fn
			clone.Parameters = params
			clone.ReturnType = ret
			out = &clone
		}
		return out, refined
	}
	stated, refined := retype(theorem)
	body := stated.Body
	for i := len(refined) - 1; i >= 0; i-- {
		if refined[i] == "" {
			continue
		}
		param := theorem.Parameters[i]
		hypothesis, ok := tc.RefinementPredicateOver(refined[i], param.Name.Value)
		if !ok {
			return nil, nil, nil, fmt.Sprintf("the predicate of %s cannot be stated over %s", refined[i], param.Name.Value)
		}
		body = underHypothesis(theorem.Token, hypothesis, body)
	}
	if body != stated.Body {
		if stated == theorem {
			clone := *theorem
			stated = &clone
		}
		stated.Body = body
	}
	callees := make(map[string]*ast.FunctionStatement, len(functions))
	for name, fn := range functions {
		callees[name], _ = retype(fn)
	}
	guards := map[string]asm.Guard{}
	for _, name := range tc.Refinements() {
		base, predicate, _ := tc.Refinement(name)
		guards[name] = asm.Guard{Base: &ast.Identifier{Value: base}, Predicate: predicate}
	}
	return stated, callees, guards, ""
}

// declarationsOf collects the checked program's record and sum-type
// declarations for the decider, which binds parameters of those types as
// aggregates of scalar leaves.
func declarationsOf(program *ast.Program) asm.Declarations {
	decls := asm.Declarations{Records: map[string]*ast.RecordLiteral{}, ADTs: map[string]*ast.ADTType{}}
	if program == nil {
		return decls
	}
	for _, stmt := range program.Statements {
		adt, isADT := stmt.(*ast.ADTType)
		if !isADT || adt.Name == nil || len(adt.TypeParams) != 0 || adt.Refinement != nil {
			continue
		}
		if len(adt.Variants) == 1 && adt.Variants[0].Literal != nil {
			if literal, isRecord := adt.Variants[0].Literal.(*ast.RecordLiteral); isRecord {
				decls.Records[adt.Name.Value] = literal
				continue
			}
		}
		decls.ADTs[adt.Name.Value] = adt
	}
	return decls
}

// underHypothesis states `!hypothesis || body`. A block body keeps its
// statements and takes the disjunction on its final expression, so the
// decider still sees the locals before the claim.
func underHypothesis(tok token.Token, hypothesis, body ast.Expression) ast.Expression {
	if block, isBlock := body.(*ast.BlockExpression); isBlock && block.Block != nil && len(block.Block.Statements) > 0 {
		last := len(block.Block.Statements) - 1
		if final, isExpr := block.Block.Statements[last].(*ast.ExpressionStatement); isExpr {
			statements := append([]ast.Statement(nil), block.Block.Statements...)
			finalClone := *final
			finalClone.Expression = underHypothesis(tok, hypothesis, final.Expression)
			statements[last] = &finalClone
			inner := *block.Block
			inner.Statements = statements
			outer := *block
			outer.Block = &inner
			return &outer
		}
	}
	return &ast.InfixExpression{Token: tok, Operator: "||",
		Left:  &ast.PrefixExpression{Token: tok, Operator: "!", Right: hypothesis},
		Right: body}
}

// assignment renders one argument tuple as `x = 3, y = Red`.
func assignment(domains []domain, args []object.Object) string {
	if len(domains) == 0 {
		return "(no parameters)"
	}
	parts := make([]string, len(domains))
	for i, d := range domains {
		parts[i] = d.name + " = " + args[i].Inspect()
	}
	return strings.Join(parts, ", ")
}

// Names lists theorem names in source order; the roots the Lean projection
// extracts.
func Names(model *compiler.SemanticModel) []string {
	var names []string
	for _, theorem := range typechecker.Theorems(model.Tree.Root) {
		names = append(names, theorem.Name.Value)
	}
	return names
}

// Summary counts the statuses, for the command's last line.
func Summary(results []Result) string {
	counts := map[Status]int{}
	for _, r := range results {
		counts[r.Status]++
	}
	var keys []string
	for status := range counts {
		keys = append(keys, string(status))
	}
	sort.Strings(keys)
	var parts []string
	for _, key := range keys {
		parts = append(parts, fmt.Sprintf("%d %s", counts[Status(key)], key))
	}
	return strings.Join(parts, ", ")
}
