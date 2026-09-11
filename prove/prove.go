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
	if len(theorems) == 0 {
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
	return results, nil
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
func domainOf(tc *typechecker.TypeChecker, param *ast.FunctionParameter) (domain, string) {
	typ := tc.ParseTypeExpression(param.Type)
	if typ == nil {
		return domain{}, fmt.Sprintf("parameter %s: %s does not resolve to a type", param.Name.Value, param.Type.String())
	}
	values, reason := valuesOf(tc, typ)
	if reason != "" {
		return domain{}, fmt.Sprintf("parameter %s: %s", param.Name.Value, reason)
	}
	return domain{name: param.Name.Value, values: values}, ""
}

func valuesOf(tc *typechecker.TypeChecker, typ typechecker.Type) ([]object.Object, string) {
	switch t := typ.(type) {
	case *typechecker.BoolType:
		return []object.Object{evaluator.Bool(false), evaluator.Bool(true)}, ""
	case *typechecker.PrimitiveType:
		switch t.Name {
		case "u8":
			return integers(0, 255), ""
		case "i8":
			return integers(-128, 127), ""
		case "u16":
			return integers(0, 65535), ""
		case "i16":
			return integers(-32768, 32767), ""
		}
	case *typechecker.ADTType:
		variants, ok := tc.ADTVariants(t.Name)
		if !ok {
			return nil, fmt.Sprintf("%s is generic or unknown", t.Name)
		}
		var values []object.Object
		for _, variant := range variants {
			if variant.Payload != nil {
				if _, isUnit := variant.Payload.(*typechecker.UnitType); !isUnit {
					return nil, fmt.Sprintf("%s carries a payload in %s; only payload-free sum types are enumerated", t.Name, variant.Name)
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
			fieldValues, reason := valuesOf(tc, fields[field])
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
		d, reason := domainOf(tc, param)
		if reason != "" {
			return blastOr(theorem, functions, Result{Name: name, Status: Open, Detail: reason + "; stated for Lean"})
		}
		domains = append(domains, d)
		total *= len(d.values)
		if total > cases {
			return blastOr(theorem, functions, Result{Name: name, Status: Open,
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
func blastOr(theorem *ast.FunctionStatement, functions map[string]*ast.FunctionStatement, open Result) Result {
	decision := asm.DecideTheorem(theorem, functions)
	switch decision.Kind {
	case asm.DecisionProven:
		return Result{Name: open.Name, Status: Decided, Detail: decision.Message}
	case asm.DecisionRefuted:
		return Result{Name: open.Name, Status: Refuted, Detail: decision.Message}
	}
	return Result{Name: open.Name, Status: Open, Detail: open.Detail + " (bit-level: " + decision.Message + ")"}
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
