package compiler

import (
	"fmt"
	"reflect"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/semir"
	"github.com/SCKelemen/oak/typechecker"
)

// SimulationBinding describes an explicitly trusted scalar C boundary. Native
// implementations remain a trust boundary: the compiler cannot prove their
// determinism. Names, symbols and exact ABI types must all match.
type SimulationBinding struct {
	Name       string   `json:"name"`
	Symbol     string   `json:"symbol"`
	Parameters []string `json:"parameters"`
	Return     string   `json:"return"`
}

// WithSimulation enables a conservative whole-package boundary check before
// type checking/specialization. Dead functions, generic templates, closures and
// global initializers are covered too. This is not a reachability/effect proof.
func (comp Compilation) WithSimulation(bindings []SimulationBinding) Compilation {
	comp.simulation = true
	comp.simulationBindings = make([]SimulationBinding, len(bindings))
	for i, binding := range bindings {
		comp.simulationBindings[i] = binding
		comp.simulationBindings[i].Parameters = append([]string(nil), binding.Parameters...)
	}
	return comp
}

func simulationABI(expr ast.Expression) string {
	// Type-position qualification is stored as a single identifier; value
	// member access uses IndexExpression. CheckProgram validates legal types.
	if id, ok := expr.(*ast.Identifier); ok && (id.Value == "()" || strings.HasPrefix(id.Value, "c.")) {
		return id.Value
	}
	return ""
}

func matchesSimulationBinding(fn *ast.FunctionStatement, b SimulationBinding) bool {
	if fn.Name == nil || fn.Name.Value != b.Name || fn.ExternSymbol != b.Symbol || fn.Receiver != nil || len(fn.TypeParams) != 0 || len(fn.Parameters) != len(b.Parameters) || simulationABI(fn.ReturnType) != b.Return || b.Return == "" {
		return false
	}
	for i, p := range fn.Parameters {
		if p.Variadic || b.Parameters[i] == "" || simulationABI(p.Type) != b.Parameters[i] {
			return false
		}
	}
	return true
}

func checkSimulation(root *ast.Program, bindings []SimulationBinding) error {
	reporters := []SimulationBinding{
		{Name: "testing_fail_host", Symbol: "oak_test_host_fail", Parameters: []string{"c.UInt32"}, Return: "()"},
		{Name: "testing_fail_values_host", Symbol: "oak_test_host_fail_values", Parameters: []string{"c.UInt32", "c.UInt64", "c.UInt64", "c.UInt32"}, Return: "()"},
		{Name: "testing_discard", Symbol: "oak_test_host_discard", Return: "()"},
		{Name: "testing_classify_host", Symbol: "oak_test_host_classify", Parameters: []string{"c.UInt32"}, Return: "()"},
		{Name: "testing_trace_host", Symbol: "oak_test_host_trace", Parameters: []string{"c.UInt32", "c.UInt64", "c.UInt64"}, Return: "()"},
		{Name: "testing_command_host", Symbol: "oak_test_host_command", Parameters: []string{"c.UInt32", "c.UInt32", "c.UInt32"}, Return: "()"},
		{Name: "testing_command_limit_host", Symbol: "oak_test_host_command_limit", Return: "c.UInt32"},
	}
	return walkSimulation(reflect.ValueOf(root), func(value any) error {
		switch n := value.(type) {
		case *ast.UnsafeBlock:
			return fmt.Errorf("simulation boundary: unsafe blocks are not permitted; move hardware effects behind a trusted adapter")
		case *ast.Identifier:
			// Reject names even when they occur in uncalled code or are used as
			// values. Conservative shadowing rejection avoids resolution holes.
			_, atomic := semir.LookupAtomicBuiltin(n.Value)
			if atomic || n.Value == "Atomic" || typechecker.CompilerKnownLibrary(n.Value) && n.Value != "c" && n.Value != "simd" {
				return fmt.Errorf("simulation boundary: %s requires an explicit simulated adapter", n.Value)
			}
		case *ast.FunctionStatement:
			if n.ExternSymbol == "" {
				return nil
			}
			if n.Token.SemanticContext == "testing-host" {
				for _, b := range reporters {
					if matchesSimulationBinding(n, b) {
						return nil
					}
				}
			}
			for _, b := range bindings {
				if matchesSimulationBinding(n, b) {
					return nil
				}
			}
			return fmt.Errorf("simulation boundary: undeclared extern %s (%s), or adapter ABI mismatch", n.Name.Value, n.ExternSymbol)
		}
		return nil
	})
}

// Unlike transformSyntax this visits statements as well as expressions. Only
// exported AST data is walked; no trivia, semantic environments or cycles.
func walkSimulation(v reflect.Value, visit func(any) error) error {
	if !v.IsValid() {
		return nil
	}
	switch v.Kind() {
	case reflect.Interface, reflect.Pointer:
		if v.IsNil() {
			return nil
		}
		if v.Kind() == reflect.Pointer && v.CanInterface() {
			if err := visit(v.Interface()); err != nil {
				return err
			}
		}
		return walkSimulation(v.Elem(), visit)
	case reflect.Struct:
		for i := 0; i < v.NumField(); i++ {
			if v.Type().Field(i).IsExported() {
				if err := walkSimulation(v.Field(i), visit); err != nil {
					return err
				}
			}
		}
	case reflect.Slice:
		for i := 0; i < v.Len(); i++ {
			if err := walkSimulation(v.Index(i), visit); err != nil {
				return err
			}
		}
	case reflect.Map:
		keys := v.MapKeys()
		sort.Slice(keys, func(i, j int) bool { return keys[i].String() < keys[j].String() })
		for _, key := range keys {
			if err := walkSimulation(v.MapIndex(key), visit); err != nil {
				return err
			}
		}
	}
	return nil
}
