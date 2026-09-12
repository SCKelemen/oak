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
)

// Result is one theorem's outcome.
type Result struct {
	Name   string
	Status Status
	// Detail says how the status was reached: the number of cases decided,
	// the counterexample, or why the deciders do not apply.
	Detail string
}

// DefaultCases bounds the exhaustive decider: the product of the parameter
// domains a theorem is evaluated over.
const DefaultCases = 1 << 16

// Theorems discharges every theorem of the checked model, in source order.
// cases bounds the exhaustive decider (DefaultCases when zero).
func Theorems(model *compiler.SemanticModel, cases int) ([]Result, error) {
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
	var results []Result
	for _, theorem := range theorems {
		results = append(results, decide(env, model.TypeChecker, functions, theorem, cases))
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
func decide(env *object.Environment, tc *typechecker.TypeChecker, functions map[string]*ast.FunctionStatement, theorem *ast.FunctionStatement, cases int) Result {
	name := theorem.Name.Value
	fn, found := env.Get(name)
	if !found {
		return Result{Name: name, Status: Open, Detail: "the interpreter did not load the theorem"}
	}
	var domains []domain
	total := 1
	for _, param := range theorem.Parameters {
		d, reason := domainOf(tc, env, param)
		if reason != "" {
			return blastOr(tc, theorem, functions, Result{Name: name, Status: Open, Detail: reason + "; stated for Lean"})
		}
		domains = append(domains, d)
		total *= len(d.values)
		if total > cases {
			return blastOr(tc, theorem, functions, Result{Name: name, Status: Open,
				Detail: fmt.Sprintf("the domain exceeds %d cases; stated for Lean", cases)})
		}
	}
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

// blastOr runs the bit-level decider (asm.DecideTheorem) on a theorem the
// exhaustive decider does not reach, and keeps the given open result when
// the decider does not apply either.
func blastOr(tc *typechecker.TypeChecker, theorem *ast.FunctionStatement, functions map[string]*ast.FunctionStatement, open Result) Result {
	stated, callees, guards, reason := forDecider(tc, theorem, functions)
	if reason != "" {
		return Result{Name: open.Name, Status: Open, Detail: open.Detail + " (bit-level: " + reason + ")"}
	}
	decision := asm.DecideTheoremWith(stated, callees, guards)
	switch decision.Kind {
	case asm.DecisionProven:
		return Result{Name: open.Name, Status: Decided, Detail: decision.Message}
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
