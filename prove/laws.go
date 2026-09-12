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

// Declared operator laws become theorems (docs/spec/10-syntax.md section
// 14a; docs/notes/algebraic-semantics-2026-09.md): `laws { associative }`
// on `operator(+) add` states `law_add_associative: theorem (a: T, b: T,
// c: T) = add(add(a, b), c) == add(a, add(b, c))`, and the ladder decides
// it over a small domain, refutes it with a counterexample, or leaves it
// for Lean — the author's claim put to the same test as any theorem.
//
// The obligations are generated only where `==` is defined and finite: an
// operand type that is a declared record whose fields are fixed-width
// integers or Bool. Records with other fields (floats, views) keep their
// laws stated by the REPL's :lean alone.

// lawTheoremSuffixes are the theorem names a law states, per law.
var lawTheoremSuffixes = map[string][]string{
	"associative": {"associative"},
	"commutative": {"commutative"},
	"idempotent":  {"idempotent"},
	"identity":    {"identity_left", "identity_right"},
}

// IsLawObligation reports whether a theorem name is a generated law
// theorem, and the operator function it is about.
func IsLawObligation(name string) (string, bool) {
	if !strings.HasPrefix(name, "law_") {
		return "", false
	}
	rest := strings.TrimPrefix(name, "law_")
	for _, suffixes := range lawTheoremSuffixes {
		for _, suffix := range suffixes {
			if strings.HasSuffix(rest, "_"+suffix) {
				return strings.TrimSuffix(rest, "_"+suffix), true
			}
		}
	}
	return "", false
}

var decidableFieldTypes = map[string]bool{"u8": true, "u16": true, "u32": true, "u64": true, "i8": true, "i16": true, "i32": true, "i64": true, "Bool": true}

// lawOperandDecidable reports whether the operand type is a declared record
// of decidable scalar fields, so `==` is defined on it.
func lawOperandDecidable(typ ast.Expression, records map[string]*ast.RecordLiteral) bool {
	name, isIdent := typ.(*ast.Identifier)
	if !isIdent {
		return false
	}
	record, isRecord := records[name.Value]
	if !isRecord || len(record.FieldOrder) == 0 {
		return false
	}
	for _, field := range record.FieldOrder {
		fieldType, ok := field.Value.(*ast.Identifier)
		if !ok || !decidableFieldTypes[fieldType.Value] {
			return false
		}
	}
	return true
}

// lawSource is the theorem text for one operator definition's laws.
func lawSource(fn *ast.FunctionStatement) string {
	name := fn.Name.Value
	typ := fn.Parameters[0].Type.String()
	var out strings.Builder
	for _, law := range fn.Laws {
		switch law.Name {
		case "associative":
			fmt.Fprintf(&out, "law_%s_associative: theorem (a: %s, b: %s, c: %s) = %s(%s(a, b), c) == %s(a, %s(b, c))\n", name, typ, typ, typ, name, name, name, name)
		case "commutative":
			fmt.Fprintf(&out, "law_%s_commutative: theorem (a: %s, b: %s) = %s(a, b) == %s(b, a)\n", name, typ, typ, name, name)
		case "idempotent":
			fmt.Fprintf(&out, "law_%s_idempotent: theorem (a: %s) = %s(a, a) == a\n", name, typ, name)
		case "identity":
			if law.Argument == nil {
				continue
			}
			element := law.Argument.String()
			fmt.Fprintf(&out, "law_%s_identity_left: theorem (a: %s) = %s(%s, a) == a\n", name, typ, name, element)
			fmt.Fprintf(&out, "law_%s_identity_right: theorem (a: %s) = %s(a, %s) == a\n", name, typ, name, element)
		}
	}
	return out.String()
}

// LawObligations is the syntax rewrite that states every declared operator
// law over a decidable record type as a theorem, right after the last
// declaration.
func LawObligations(tree *compiler.SyntaxTree) error {
	records := compiler.RecordDeclarations(tree.Root)
	var source strings.Builder
	for _, stmt := range tree.Root.Statements {
		fn, isFn := stmt.(*ast.FunctionStatement)
		if !isFn || fn.Name == nil || fn.Operator == "" || len(fn.Laws) == 0 || len(fn.Parameters) != 2 || fn.Parameters[0] == nil {
			continue
		}
		if !lawOperandDecidable(fn.Parameters[0].Type, records) {
			continue
		}
		source.WriteString(lawSource(fn))
	}
	if source.Len() == 0 {
		return nil
	}
	p := parser.New(layout.New(scanner.New(source.String())))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		return fmt.Errorf("prove: law obligations: %s", strings.Join(errs, "; "))
	}
	tree.Root.Statements = append(tree.Root.Statements, program.Statements...)
	return nil
}

// Obligations is every generated theorem the prover adds before checking:
// the protocol invariants' base and step obligations, then the operator
// laws.
func Obligations(tree *compiler.SyntaxTree) error {
	if err := ProtocolObligations(tree); err != nil {
		return err
	}
	return LawObligations(tree)
}
