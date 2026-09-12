package compiler

// Declared layout claims (docs/spec/40-records.md section 6a): a record
// spelled `struct(no_padding)` claims that its natural placement is dense —
// every byte of the record is a field byte, no padding between fields and
// none after the last. The claim is checked here, in the Check stage, so a
// false one is a diagnostic naming the padded field and the bytes rather
// than the backend failing closed; the C backend then emits the same
// identity as a compile-time assertion for the C compiler to ratify.
//
// The claim also restricts what a field may be: a wire record holds
// fixed-width scalars, Bool, owned arrays of those, and nested records that
// themselves declare no_padding or packed — never a view, span, string,
// buffer, atomic cell, function pointer, or a platform-width integer whose
// size the target chooses.

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/token"
)

// CodeLayoutClaim reports a record whose declared layout claim does not hold:
// padding where no_padding was declared, a field shape a wire record cannot
// carry, or a clause combination without a meaning.
const CodeLayoutClaim = "OAK-R0301"

// wireScalars are the field types whose bytes are all value bytes on every
// recorded target: the fixed-width integers and floats, their aliases, and
// Bool (an int-sized enum, docs/spec/92-ffi.md section 2.4).
var wireScalars = map[string]bool{
	"u8": true, "u16": true, "u32": true, "u64": true, "u128": true,
	"i8": true, "i16": true, "i32": true, "i64": true,
	"f32": true, "f64": true, "f16": true, "bf16": true, "f8e4m3": true, "f8e5m2": true,
	"byte": true, "rune": true, "Bool": true,
}

// checkLayoutClaims measures every struct declared no_padding and reports
// each broken claim as a diagnostic.
func checkLayoutClaims(tree *SyntaxTree, options Options) error {
	program := tree.Root
	structs := map[string]*ast.ADTType{}
	var claimed []*ast.ADTType
	for _, statement := range program.Statements {
		declaration, ok := statement.(*ast.ADTType)
		if !ok || declaration.Name == nil || len(declaration.Variants) != 1 {
			continue
		}
		record, ok := declaration.Variants[0].Literal.(*ast.RecordLiteral)
		if !ok || record.Token.TokenKind != token.STRUCT {
			continue
		}
		structs[declaration.Name.Value] = declaration
		if record.Layout != nil && record.Layout.NoPadding {
			claimed = append(claimed, declaration)
		}
	}
	if len(claimed) == 0 {
		return nil
	}
	var diags []*diagnostic.Diagnostic
	report := func(node ast.Node, format string, args ...interface{}) {
		diags = append(diags, diagnostic.NewDiagnosticFromNodeWithCode(node, "compiler", CodeLayoutClaim, fmt.Sprintf(format, args...)))
	}
	// Layouts resolve in dependency order over every non-generic struct;
	// a struct that cannot be placed (a view field, a generic member) is
	// left unresolved, and only the claimed records are judged.
	resolved := map[string]resolvedRecordLayout{}
	failures := map[string]error{}
	pending := make([]*ast.ADTType, 0, len(structs))
	for _, declaration := range structs {
		if len(declaration.TypeParams) == 0 {
			pending = append(pending, declaration)
		}
	}
	for len(pending) != 0 {
		progress := false
		next := pending[:0]
		for _, declaration := range pending {
			record := declaration.Variants[0].Literal.(*ast.RecordLiteral)
			layout, spec, ok, err := resolveRecordLayout(record, resolved, options, program)
			if err != nil {
				failures[declaration.Name.Value] = err
				progress = true
				continue
			}
			if !ok {
				next = append(next, declaration)
				continue
			}
			resolved[declaration.Name.Value] = resolvedRecordLayout{representation: layout, spec: spec}
			progress = true
		}
		if !progress {
			break
		}
		pending = next
	}
	for _, declaration := range claimed {
		name := declaration.Name.Value
		record := declaration.Variants[0].Literal.(*ast.RecordLiteral)
		if len(declaration.TypeParams) != 0 {
			report(declaration.Name, "record %s: no_padding is declared on a template; the claim is about one placement, so state it on a record of concrete fields", name)
			continue
		}
		if record.Layout.Packed {
			report(declaration.Name, "record %s: packed is dense by construction; no_padding states that the natural placement is dense — declare one", name)
			continue
		}
		shapeOK := true
		for _, field := range record.FieldOrder {
			if reason := wireFieldShape(field.Value, structs); reason != "" {
				report(field.Value, "record %s declares no_padding, but field %s %s", name, field.Name, reason)
				shapeOK = false
			}
		}
		if !shapeOK {
			continue
		}
		if err, failed := failures[name]; failed {
			report(declaration.Name, "record %s declares no_padding, but %v; order the fields by descending alignment, or pad explicitly with a reserved field", name, err)
			continue
		}
		if _, ok := resolved[name]; !ok {
			report(declaration.Name, "record %s declares no_padding, but its layout cannot be resolved: a field's type has no placement here", name)
		}
	}
	if len(diags) != 0 {
		return &DiagnosticError{Phase: "layout", Diagnostics: diags}
	}
	return nil
}

// wireFieldShape reports why a field type cannot appear in a no_padding
// record, or "" when it can.
func wireFieldShape(expr ast.Expression, structs map[string]*ast.ADTType) string {
	switch t := expr.(type) {
	case *ast.Identifier:
		if wireScalars[t.Value] {
			return ""
		}
		switch t.Value {
		case "int", "uint", "ptr", "uptr":
			return fmt.Sprintf("is %s, whose width the target chooses; a wire record spells its widths", t.Value)
		case "string":
			return "is a string, a view whose bytes live elsewhere"
		}
		if declaration, isStruct := structs[t.Value]; isStruct {
			nested := declaration.Variants[0].Literal.(*ast.RecordLiteral)
			if nested.Layout != nil && (nested.Layout.NoPadding || nested.Layout.Packed) {
				return ""
			}
			return fmt.Sprintf("is a %s, which does not itself declare no_padding or packed", t.Value)
		}
		return fmt.Sprintf("is a %s, not a fixed-width scalar, Bool, an owned array of those, or a no_padding record", t.Value)
	case *ast.IndexExpression:
		if _, isFixed := t.Index.(*ast.IntegerLiteral); isFixed {
			return wireFieldShape(t.Left, structs)
		}
		if marker, isMarker := t.Index.(*ast.Identifier); isMarker && (marker.Value == "" || marker.Value == "*") {
			return "is a view or span: a pointer and a length, not the bytes themselves"
		}
		return "is a generic or library type whose placement a wire record cannot claim"
	case *ast.FunctionTypeExpression:
		return "is a function pointer"
	}
	return "has a shape a wire record cannot carry"
}
