package prove

import (
	"fmt"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

// Protocol invariants (docs/spec/125-verification.md §2a). A theorem whose
// parameters are exactly a protocol's projected state and data — `(s:
// NameState, d: NameData)`, or `(s: NameState)` for a machine without data
// — is an invariant candidate. The prover writes the two obligations the
// declaration determines, as ordinary theorems over the projections, and
// checks them on the same ladder:
//
//	inv__base: theorem () { inv(name_initial(), name_initial_data()) }
//	inv__step: theorem (s: NameState, d: NameData, step: NameStep) {
//	  buf: [1]NameData = [1]NameData{ d }
//	  !(inv(s, d) && name_legal(s, d, step)) || inv(name_next(s, span(&buf), step), buf[0])
//	}
//
// Nothing is added to the language: the obligations are the theorems a
// programmer would write, generated so the preservation shape is never
// misspelled.

// ObligationSuffixes name the two generated theorems of an invariant.
const (
	BaseSuffix = "__base"
	StepSuffix = "__step"
)

// invariantCandidates pairs each candidate theorem with its protocol.
func invariantCandidates(tree *compiler.SyntaxTree) map[string]*ast.ProtocolDeclaration {
	protocols := map[string]*ast.ProtocolDeclaration{}
	for _, decl := range compiler.Protocols(tree) {
		if decl.Name != nil {
			protocols[decl.Name.Value] = decl
		}
	}
	candidates := map[string]*ast.ProtocolDeclaration{}
	for _, stmt := range tree.Root.Statements {
		fn, isFn := stmt.(*ast.FunctionStatement)
		if !isFn || !fn.Theorem || fn.Name == nil || len(fn.Parameters) == 0 || len(fn.Parameters) > 2 {
			continue
		}
		state, isIdent := fn.Parameters[0].Type.(*ast.Identifier)
		if !isIdent || !strings.HasSuffix(state.Value, "State") {
			continue
		}
		name := strings.TrimSuffix(state.Value, "State")
		decl, isProtocol := protocols[name]
		if !isProtocol {
			continue
		}
		hasData := decl.Data != nil
		if hasData != (len(fn.Parameters) == 2) {
			continue
		}
		if hasData {
			data, isIdent := fn.Parameters[1].Type.(*ast.Identifier)
			if !isIdent || data.Value != name+"Data" {
				continue
			}
		}
		candidates[fn.Name.Value] = decl
	}
	return candidates
}

// obligationSource writes the two obligations of one invariant.
func obligationSource(theorem string, decl *ast.ProtocolDeclaration) string {
	name := decl.Name.Value
	prefix := compiler.ProtocolPrefix(name)
	var out strings.Builder
	if decl.Data == nil {
		fmt.Fprintf(&out, "%s%s: theorem () { %s(%s_initial()) }\n", theorem, BaseSuffix, theorem, prefix)
		fmt.Fprintf(&out, "%s%s: theorem (s: %sState, step: %sStep) { !(%s(s) && %s_legal(s, step)) || %s(%s_next(s, step)) }\n",
			theorem, StepSuffix, name, name, theorem, prefix, theorem, prefix)
		return out.String()
	}
	fmt.Fprintf(&out, "%s%s: theorem () { %s(%s_initial(), %s_initial_data()) }\n", theorem, BaseSuffix, theorem, prefix, prefix)
	fmt.Fprintf(&out, "%s%s: theorem (s: %sState, d: %sData, step: %sStep) {\n", theorem, StepSuffix, name, name, name)
	fmt.Fprintf(&out, "  buf: [1]%sData = [1]%sData{ d }\n", name, name)
	fmt.Fprintf(&out, "  !(%s(s, d) && %s_legal(s, d, step)) || %s(%s_next(s, span(&buf), step), buf[0])\n", theorem, prefix, theorem, prefix)
	out.WriteString("}\n")
	return out.String()
}

// ProtocolObligations is the syntax rewrite that adds the obligations of
// every invariant candidate to the program, in source order of the
// candidates, right after the last declaration.
func ProtocolObligations(tree *compiler.SyntaxTree) error {
	candidates := invariantCandidates(tree)
	if len(candidates) == 0 {
		return nil
	}
	var source strings.Builder
	for _, stmt := range tree.Root.Statements {
		fn, isFn := stmt.(*ast.FunctionStatement)
		if !isFn || fn.Name == nil {
			continue
		}
		if decl, isCandidate := candidates[fn.Name.Value]; isCandidate {
			source.WriteString(obligationSource(fn.Name.Value, decl))
		}
	}
	p := parser.New(layout.New(scanner.New(source.String())))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		return fmt.Errorf("prove: protocol obligations: %s", strings.Join(errs, "; "))
	}
	tree.Root.Statements = append(tree.Root.Statements, program.Statements...)
	return nil
}

// IsObligation reports whether a theorem name is a generated obligation,
// and the invariant it belongs to.
func IsObligation(name string) (string, bool) {
	for _, suffix := range []string{BaseSuffix, StepSuffix} {
		if strings.HasSuffix(name, suffix) {
			return strings.TrimSuffix(name, suffix), true
		}
	}
	return "", false
}
