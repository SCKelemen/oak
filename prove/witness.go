package prove

import (
	"fmt"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/typechecker"
)

// The compiled witness (docs/spec/125-verification.md section 4). An
// exhaustively decided theorem was evaluated by the interpreter; `oak
// prove -witness` evaluates it in the compiled program as well, so a law
// about the backend's own lowering (a protocol's table, an intrinsic's
// portable form) is checked where it runs. The witness is a syntax
// rewrite: `main` is replaced by a driver that loops over the same domains
// through the width-conversion rows, calls each theorem, and exits with
// the 1-based index of the first theorem that fails, zero when all hold.
// Parameters the driver can enumerate are u8, u16, i8, i16, Bool, and
// payload-free sum types (declared, or a protocol's state type); a theorem
// with any other parameter is left to the interpreter's verdict.

// WitnessPlan is what the rewrite covered, in the order the driver checks.
type WitnessPlan struct {
	Covered []string
	Skipped map[string]string
}

// WitnessRewrite builds the rewrite that installs the driver for the
// exhaustively decided theorems among results, reporting into plan.
func WitnessRewrite(results []Result, plan *WitnessPlan) func(*compiler.SyntaxTree) error {
	exhaustive := map[string]bool{}
	for _, r := range results {
		if r.Status == Decided && strings.HasPrefix(r.Detail, "all ") {
			exhaustive[r.Name] = true
		}
	}
	return func(tree *compiler.SyntaxTree) error {
		plan.Skipped = map[string]string{}
		enums := enumDomains(tree)
		var driver strings.Builder
		driver.WriteString("main: (): i32 {\n  witness_failing: u32 = 0\n")
		index := 0
		kept := make([]ast.Statement, 0, len(tree.Root.Statements))
		for _, stmt := range tree.Root.Statements {
			fn, isFn := stmt.(*ast.FunctionStatement)
			if isFn && fn.Name != nil && fn.Name.Value == "main" && fn.Receiver == nil {
				continue // the driver is the program's main
			}
			kept = append(kept, stmt)
			if !isFn || !fn.Theorem || fn.Name == nil || !exhaustive[fn.Name.Value] {
				continue
			}
			body, reason := theoremDriver(fn, enums, index+1)
			if reason != "" {
				plan.Skipped[fn.Name.Value] = reason
				continue
			}
			index++
			plan.Covered = append(plan.Covered, fn.Name.Value)
			driver.WriteString(body)
		}
		driver.WriteString("  i32_bits_u32(witness_failing)\n}\n")
		p := parser.New(layout.New(scanner.New(driver.String())))
		program := p.ParseProgram()
		if errs := p.Errors(); len(errs) != 0 {
			return fmt.Errorf("prove: witness driver: %s", strings.Join(errs, "; "))
		}
		tree.Root.Statements = append(kept, program.Statements...)
		return nil
	}
}

// enumDomains lists the payload-free sum types the driver can enumerate:
// declared ADTs and each protocol's state type, variants in order.
func enumDomains(tree *compiler.SyntaxTree) map[string][]string {
	domains := map[string][]string{}
	for _, stmt := range tree.Root.Statements {
		switch decl := stmt.(type) {
		case *ast.ADTType:
			if decl.Name == nil || len(decl.TypeParams) != 0 || decl.Refinement != nil {
				continue
			}
			var variants []string
			plain := len(decl.Variants) > 0
			for _, v := range decl.Variants {
				if v.Name == nil || v.Payload != nil || v.Literal != nil {
					plain = false
					break
				}
				variants = append(variants, v.Name.Value)
			}
			if plain {
				domains[decl.Name.Value] = variants
			}
		case *ast.ProtocolDeclaration:
			if decl.Name == nil || decl.Initial == nil {
				continue
			}
			seen := map[string]bool{}
			var states []string
			add := func(id *ast.Identifier) {
				if id != nil && !seen[id.Value] {
					seen[id.Value] = true
					states = append(states, id.Value)
				}
			}
			add(decl.Initial)
			for _, t := range decl.Transitions {
				add(t.From)
				add(t.To)
			}
			domains[decl.Name.Value+"State"] = states
		}
	}
	return domains
}

// theoremDriver writes the nested loops that call one theorem on every
// element of its parameter domains.
func theoremDriver(fn *ast.FunctionStatement, enums map[string][]string, index int) (string, string) {
	var out strings.Builder
	indent := "  "
	out.WriteString(indent + "{\n")
	indent += "  "
	var args []string
	for i, param := range fn.Parameters {
		typeName, isIdent := param.Type.(*ast.Identifier)
		if !isIdent || param.Variadic {
			return "", fmt.Sprintf("parameter %s: %s is not enumerable by the driver", param.Name.Value, param.Type.String())
		}
		counter := fmt.Sprintf("witness_k%d", i)
		name := param.Name.Value
		var count int
		var binding string
		switch typeName.Value {
		case "u8":
			count, binding = 256, fmt.Sprintf("%s: u8 = u8_trunc_u32(%s)", name, counter)
		case "u16":
			count, binding = 65536, fmt.Sprintf("%s: u16 = u16_trunc_u32(%s)", name, counter)
		case "i8":
			count, binding = 256, fmt.Sprintf("%s: i8 = i8_bits_u8(u8_trunc_u32(%s))", name, counter)
		case "i16":
			count, binding = 65536, fmt.Sprintf("%s: i16 = i16_bits_u16(u16_trunc_u32(%s))", name, counter)
		case "Bool":
			count, binding = 2, fmt.Sprintf("%s: Bool = %s == u32(1)", name, counter)
		default:
			variants, isEnum := enums[typeName.Value]
			if !isEnum {
				return "", fmt.Sprintf("parameter %s: %s is not enumerable by the driver", name, typeName.Value)
			}
			count = len(variants)
			var chain strings.Builder
			for k, variant := range variants {
				if k == len(variants)-1 {
					fmt.Fprintf(&chain, "%s.%s", typeName.Value, variant)
				} else {
					fmt.Fprintf(&chain, "%s == u32(%d) ? %s.%s | ", counter, k, typeName.Value, variant)
				}
			}
			binding = fmt.Sprintf("%s: %s = %s", name, typeName.Value, chain.String())
		}
		fmt.Fprintf(&out, "%s%s: u32 = 0\n%swhile %s < u32(%d) {\n", indent, counter, indent, counter, count)
		indent += "  "
		fmt.Fprintf(&out, "%s%s\n", indent, binding)
		args = append(args, name)
	}
	fmt.Fprintf(&out, "%s%s(%s) ? { } | { witness_failing = witness_failing == u32(0) ? u32(%d) | witness_failing }\n",
		indent, fn.Name.Value, strings.Join(args, ", "), index)
	for i := len(fn.Parameters) - 1; i >= 0; i-- {
		counter := fmt.Sprintf("witness_k%d", i)
		fmt.Fprintf(&out, "%s%s = %s + u32(1)\n", indent, counter, counter)
		indent = indent[:len(indent)-2]
		out.WriteString(indent + "}\n")
	}
	indent = indent[:len(indent)-2]
	out.WriteString(indent + "}\n")
	return out.String(), ""
}

// ApplyWitness folds the compiled run into the results: exit is the
// driver's status (the 1-based index of the first failing theorem, zero
// when all hold).
func ApplyWitness(results []Result, plan WitnessPlan, exit int) []Result {
	covered := map[string]bool{}
	for _, name := range plan.Covered {
		covered[name] = true
	}
	failing := ""
	if exit > 0 && exit <= len(plan.Covered) {
		failing = plan.Covered[exit-1]
	}
	for i, r := range results {
		switch {
		case r.Name == failing:
			results[i] = Result{Name: r.Name, Status: Refuted,
				Detail: "the compiled program disagrees with the interpreter (" + r.Detail + ")"}
		case covered[r.Name] && exit >= 0:
			results[i].Detail += "; witnessed in the compiled program"
		}
	}
	return results
}

// WitnessSkips renders the theorems the driver left to the interpreter.
func WitnessSkips(plan WitnessPlan) string {
	if len(plan.Skipped) == 0 {
		return ""
	}
	names := make([]string, 0, len(plan.Skipped))
	for name := range plan.Skipped {
		names = append(names, name)
	}
	sort.Strings(names)
	parts := make([]string, len(names))
	for i, name := range names {
		parts[i] = name + " (" + plan.Skipped[name] + ")"
	}
	return strings.Join(parts, ", ")
}

var _ = typechecker.Theorems
