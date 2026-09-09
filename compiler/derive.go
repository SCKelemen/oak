package compiler

// Derived declarations (docs/spec/83-modules.md section 6.6): a
// declaration-form function whose definition is `derive.equal` or
// `derive.hash` receives a compiler-synthesized body computed from the
// structure of its parameter type — the same pattern as `c.extern("sym")`
// (a typed interface whose body the compiler supplies) and the tag-driven
// codec derivation of docs/spec/71-codecs.md. The body is generated as Oak
// source text from the type's field order and variant list (one fact: the
// declaration), parsed by the ordinary parser, and checked by every gate
// like handwritten code. Derivation is admitted only in the package that
// declares the type (the orphan rule), so opaque types stay opaque and a
// derived operation always has exactly one definition.
//
// Generated helper names contain `__`, the reserved sequence, so they can
// never collide with user identifiers; only validated identifiers and
// integer constants enter the generated text.

import (
	"fmt"
	"reflect"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/modules"
)

// Diagnostic codes of the derive subfamily (docs/spec/83-modules.md
// section 8).
const (
	// CodeDeriveUnknown rejects `derive.<kind>` for a kind the compiler
	// does not implement.
	CodeDeriveUnknown = "OAK-M0201"
	// CodeDeriveSignature rejects a derived declaration whose signature does
	// not match the kind (equal: (T, T) -> Bool; hash: (T) -> u64).
	CodeDeriveSignature = "OAK-M0202"
	// CodeDeriveUnsupported rejects derivation over a type the generator
	// cannot traverse: non-declared types, generic instantiations, views,
	// spans, strings, atomics, and fields of those types.
	CodeDeriveUnsupported = "OAK-M0203"
	// CodeDeriveOrphan rejects derivation outside the package declaring the
	// type.
	CodeDeriveOrphan = "OAK-M0204"
)

// deriveLibrary is the reserved qualifier of derived definitions.
const deriveLibrary = "derive"

// derivePrimitives are the field types a derived body compares or hashes
// directly.
var derivePrimitives = map[string]bool{
	"i8": true, "i16": true, "i32": true, "i64": true,
	"u8": true, "u16": true, "u32": true, "u64": true,
	"int": true, "uint": true, "byte": true, "rune": true, "Bool": true,
}

type deriver struct {
	program   *ast.Program
	types     map[string]*ast.ADTType
	generated map[string]bool
	helpers   []string
	diags     []*diagnostic.Diagnostic
}

// lowerDerived replaces every `derive.<kind>` definition with a call to a
// generated helper and appends the helpers to the program.
func lowerDerived(tree *SyntaxTree, comp Compilation) error {
	program := tree.Root
	d := &deriver{program: program, types: map[string]*ast.ADTType{}, generated: map[string]bool{}}
	for _, stmt := range program.Statements {
		if adt, ok := stmt.(*ast.ADTType); ok && adt.Name != nil {
			d.types[adt.Name.Value] = adt
		}
	}
	var requests []*ast.FunctionStatement
	for _, stmt := range program.Statements {
		fn, ok := stmt.(*ast.FunctionStatement)
		if !ok || fn.Body == nil {
			continue
		}
		if _, isDerive := deriveKind(fn.Body); isDerive {
			requests = append(requests, fn)
		}
	}
	if len(requests) == 0 {
		return nil
	}
	for _, fn := range requests {
		d.lowerRequest(fn)
	}
	if len(d.diags) != 0 {
		return &DiagnosticError{Phase: "derive", Diagnostics: d.diags}
	}
	if len(d.helpers) == 0 {
		return nil
	}
	helperTree, err := New().WithSource("<derived>", strings.Join(d.helpers, "\n\n")).Parse().Get()
	if err != nil {
		return fmt.Errorf("derive: generated helpers failed to parse: %w", err)
	}
	// Helpers project the fields of their type: they belong to the type's
	// package for the opaque-projection rule.
	for _, stmt := range helperTree.Root.Statements {
		fn, ok := stmt.(*ast.FunctionStatement)
		if !ok || fn.Name == nil {
			continue
		}
		if owner, known := d.helperOwner(fn.Name.Value); known {
			stampSemanticContext(reflect.ValueOf(fn), owner)
		}
	}
	// Helpers precede the declarations that call them so that a
	// sequential evaluator (the REPL's interpreter) sees definitions before
	// uses; the checker and backend are order-independent.
	head := 0
	for head < len(program.Statements) {
		switch program.Statements[head].(type) {
		case *ast.PackageStatement, *ast.ImportStatement:
			head++
			continue
		}
		break
	}
	merged := make([]ast.Statement, 0, len(program.Statements)+len(helperTree.Root.Statements))
	merged = append(merged, program.Statements[:head]...)
	merged = append(merged, helperTree.Root.Statements...)
	merged = append(merged, program.Statements[head:]...)
	program.Statements = merged
	return nil
}

// deriveKind recognizes `derive.<kind>` as a whole definition.
func deriveKind(body ast.Expression) (string, bool) {
	access, ok := body.(*ast.IndexExpression)
	if !ok || !access.Dot {
		return "", false
	}
	base, okBase := access.Left.(*ast.Identifier)
	kind, okKind := access.Index.(*ast.Identifier)
	if !okBase || !okKind || base.Value != deriveLibrary {
		return "", false
	}
	return kind.Value, true
}

func (d *deriver) report(code string, node ast.Node, format string, args ...interface{}) *diagnostic.Diagnostic {
	diag := diagnostic.NewDiagnosticFromNodeWithCode(node, "compiler", code, modules.DemangleText(fmt.Sprintf(format, args...)))
	d.diags = append(d.diags, diag)
	return diag
}

func (d *deriver) lowerRequest(fn *ast.FunctionStatement) {
	kind, _ := deriveKind(fn.Body)
	switch kind {
	case "equal":
		if len(fn.Parameters) != 2 || fn.Receiver != nil || len(fn.TypeParams) != 0 || !sameIdentifierType(fn.Parameters[0].Type, fn.Parameters[1].Type) || !isIdentifierType(fn.ReturnType, "Bool") {
			d.report(CodeDeriveSignature, fn.Name, "derive.equal requires the signature (a: T, b: T): Bool")
			return
		}
	case "hash":
		if len(fn.Parameters) != 1 || fn.Receiver != nil || len(fn.TypeParams) != 0 || !isIdentifierType(fn.ReturnType, "u64") {
			d.report(CodeDeriveSignature, fn.Name, "derive.hash requires the signature (v: T): u64")
			return
		}
	case "compare":
		if len(fn.Parameters) != 2 || fn.Receiver != nil || len(fn.TypeParams) != 0 || !sameIdentifierType(fn.Parameters[0].Type, fn.Parameters[1].Type) || !isIdentifierType(fn.ReturnType, d.orderingName()) {
			d.report(CodeDeriveSignature, fn.Name, "derive.compare requires the signature (a: T, b: T): Ordering, with Ordering: type = Less | Equal | Greater in scope")
			return
		}
	case "test_generate", "test_encode", "test_decode":
		// Signature and target type are checked together: the type is the
		// return type (generate), the parameter (encode), or Option's
		// argument (decode).
	default:
		diag := d.report(CodeDeriveUnknown, fn.Body, "derive.%s is not a derivable operation", kind)
		diag.AddHelp("derivable operations: derive.equal, derive.hash, derive.compare, derive.test_generate, derive.test_encode, derive.test_decode")
		return
	}
	var typeName *ast.Identifier
	if strings.HasPrefix(kind, "test_") {
		ident, ok := d.testCommandType(kind, fn)
		if !ok {
			return
		}
		typeName = ident
	} else {
		ident, ok := fn.Parameters[0].Type.(*ast.Identifier)
		if !ok {
			d.report(CodeDeriveUnsupported, fn.Parameters[0].Type, "derive.%s: the parameter type must be a declared record or ADT", kind)
			return
		}
		typeName = ident
	}
	decl, declared := d.types[typeName.Value]
	if !declared {
		d.report(CodeDeriveUnsupported, typeName, "derive.%s: %s is not a declared record or ADT", kind, typeName.Value)
		return
	}
	if len(decl.TypeParams) != 0 {
		d.report(CodeDeriveUnsupported, typeName, "derive.%s: generic type %s cannot be derived over; derive for a concrete instantiation is not supported", kind, typeName.Value)
		return
	}
	if owner, user := packageContext(decl.Name.Token.SemanticContext), packageContext(fn.Token.SemanticContext); owner != user {
		diag := d.report(CodeDeriveOrphan, fn.Name, "derive.%s for %s must be declared in the package that declares the type", kind, typeName.Value)
		diag.AddNote("derivation reads the type's definition; only its own package may do that (opaque types stay opaque)")
		return
	}
	helper, ok := d.helper(kind, typeName.Value, typeName)
	if !ok {
		return
	}
	var call strings.Builder
	call.WriteString(helper)
	call.WriteString("(")
	for i, param := range fn.Parameters {
		if i > 0 {
			call.WriteString(", ")
		}
		call.WriteString(param.Name.Value)
	}
	call.WriteString(")")
	body, err := parseGeneratedExpression(call.String())
	if err != nil {
		d.report(CodeDeriveUnsupported, fn.Body, "derive.%s: %v", kind, err)
		return
	}
	stampSemanticContext(reflect.ValueOf(body), fn.Token.SemanticContext)
	fn.Body = body
}

// helper returns the generated helper's name for (kind, type), generating it
// and its dependencies on first use.
func (d *deriver) helper(kind, typeName string, node ast.Node) (string, bool) {
	name := "__derive_" + kind + "_" + typeName
	if d.generated[name] {
		return name, true
	}
	d.generated[name] = true
	decl := d.types[typeName]
	if decl == nil {
		d.report(CodeDeriveUnsupported, node, "derive.%s: %s is not a declared record or ADT", kind, typeName)
		return "", false
	}
	var text string
	var ok bool
	switch kind {
	case "equal":
		text, ok = d.equalHelper(name, typeName, decl, node)
	case "hash":
		text, ok = d.hashHelper(name, typeName, decl, node)
	case "compare":
		text, ok = d.compareHelper(name, typeName, decl, node)
	case "test_generate":
		text, ok = d.testGenerateHelper(name, typeName, decl, node)
	case "test_encode":
		text, ok = d.testEncodeHelper(name, typeName, decl, node)
	case "test_decode":
		text, ok = d.testDecodeHelper(name, typeName, decl, node)
	}
	if !ok {
		return "", false
	}
	d.helpers = append(d.helpers, text)
	return name, true
}

func (d *deriver) helperOwner(helper string) (string, bool) {
	for _, prefix := range []string{"__derive_equal_", "__derive_hash_", "__derive_compare_", "__derive_test_generate_", "__derive_test_encode_", "__derive_test_decode_"} {
		if strings.HasPrefix(helper, prefix) {
			if decl := d.types[strings.TrimPrefix(helper, prefix)]; decl != nil {
				return decl.Name.Token.SemanticContext, true
			}
		}
	}
	return "", false
}

// recordShape returns the record literal of a record declaration.
func recordShape(decl *ast.ADTType) (*ast.RecordLiteral, bool) {
	if len(decl.Variants) != 1 || decl.Variants[0].Literal == nil {
		return nil, false
	}
	shape, ok := decl.Variants[0].Literal.(*ast.RecordLiteral)
	return shape, ok
}

// fieldKind classifies a field or payload type expression.
func (d *deriver) fieldKind(expr ast.Expression) (primitive bool, declared string, ok bool) {
	ident, isIdent := expr.(*ast.Identifier)
	if !isIdent {
		return false, "", false
	}
	if derivePrimitives[ident.Value] {
		return true, "", true
	}
	if decl, isDeclared := d.types[ident.Value]; isDeclared && len(decl.TypeParams) == 0 {
		return false, ident.Value, true
	}
	return false, "", false
}

func (d *deriver) equalHelper(name, typeName string, decl *ast.ADTType, node ast.Node) (string, bool) {
	var body strings.Builder
	if shape, isRecord := recordShape(decl); isRecord {
		if len(shape.FieldOrder) == 0 {
			body.WriteString("true")
		}
		for i, field := range shape.FieldOrder {
			if i > 0 {
				body.WriteString(" && ")
			}
			term, ok := d.equalTerm("a."+field.Name, "b."+field.Name, field.Value, node, typeName, field.Name)
			if !ok {
				return "", false
			}
			body.WriteString(term)
		}
	} else {
		body.WriteString("a ?")
		for i, variant := range decl.Variants {
			if variant.Name == nil {
				return "", false
			}
			if i > 0 {
				body.WriteString(" |")
			}
			if variant.Payload == nil {
				fmt.Fprintf(&body, " .%s => (b ? .%s => true | _ => false)", variant.Name.Value, variant.Name.Value)
				continue
			}
			term, ok := d.equalTerm("x", "y", variant.Payload, node, typeName, variant.Name.Value)
			if !ok {
				return "", false
			}
			fmt.Fprintf(&body, " .%s(x) => (b ? .%s(y) => %s | _ => false)", variant.Name.Value, variant.Name.Value, term)
		}
	}
	return fmt.Sprintf("%s: (a: %s, b: %s): Bool = %s", name, typeName, typeName, body.String()), true
}

func (d *deriver) equalTerm(left, right string, typeExpr ast.Expression, node ast.Node, typeName, member string) (string, bool) {
	primitive, declared, ok := d.fieldKind(typeExpr)
	if !ok {
		d.report(CodeDeriveUnsupported, node, "derive.equal for %s: member %s has a type the generator cannot compare (fixed-width integers, Bool, and declared records/ADTs are supported)", typeName, member)
		return "", false
	}
	if primitive {
		return fmt.Sprintf("%s == %s", left, right), true
	}
	helper, ok := d.helper("equal", declared, node)
	if !ok {
		return "", false
	}
	return fmt.Sprintf("%s(%s, %s)", helper, left, right), true
}

func (d *deriver) hashHelper(name, typeName string, decl *ast.ADTType, node ast.Node) (string, bool) {
	var body strings.Builder
	if shape, isRecord := recordShape(decl); isRecord {
		body.WriteString("{\n  h: u64 = 1469598103934665603\n")
		for _, field := range shape.FieldOrder {
			term, ok := d.hashTerm("v."+field.Name, field.Value, node, typeName, field.Name)
			if !ok {
				return "", false
			}
			fmt.Fprintf(&body, "  h = h ^ %s\n  h = h ^ (h << 13)\n  h = h ^ (h >> 7)\n  h = h ^ (h << 17)\n", term)
		}
		body.WriteString("  h\n}")
	} else {
		body.WriteString("v ?")
		for i, variant := range decl.Variants {
			if variant.Name == nil {
				return "", false
			}
			if i > 0 {
				body.WriteString(" |")
			}
			if variant.Payload == nil {
				fmt.Fprintf(&body, " .%s => u64(%d)", variant.Name.Value, i+1)
				continue
			}
			term, ok := d.hashTerm("x", variant.Payload, node, typeName, variant.Name.Value)
			if !ok {
				return "", false
			}
			fmt.Fprintf(&body, " .%s(x) => (%s ^ u64(%d))", variant.Name.Value, term, (i+1)*2654435761%4294967296)
		}
	}
	return fmt.Sprintf("%s: (v: %s): u64 = %s", name, typeName, body.String()), true
}

func (d *deriver) hashTerm(value string, typeExpr ast.Expression, node ast.Node, typeName, member string) (string, bool) {
	primitive, declared, ok := d.fieldKind(typeExpr)
	if !ok {
		d.report(CodeDeriveUnsupported, node, "derive.hash for %s: member %s has a type the generator cannot hash (fixed-width integers, Bool, and declared records/ADTs are supported)", typeName, member)
		return "", false
	}
	if primitive {
		if ident, _ := typeExpr.(*ast.Identifier); ident.Value == "Bool" {
			return fmt.Sprintf("u64(%s ? 1 | 0)", value), true
		}
		return fmt.Sprintf("u64(%s)", value), true
	}
	helper, ok := d.helper("hash", declared, node)
	if !ok {
		return "", false
	}
	return fmt.Sprintf("%s(%s)", helper, value), true
}

func sameIdentifierType(a, b ast.Expression) bool {
	left, okLeft := a.(*ast.Identifier)
	right, okRight := b.(*ast.Identifier)
	return okLeft && okRight && left.Value == right.Value
}

func isIdentifierType(expr ast.Expression, name string) bool {
	ident, ok := expr.(*ast.Identifier)
	return ok && ident.Value == name
}

// packageContext reads the package part of a token's SemanticContext.
func packageContext(context string) string {
	if index := strings.IndexByte(context, '|'); index >= 0 {
		context = context[:index]
	}
	if index := strings.IndexByte(context, '#'); index >= 0 {
		context = context[:index]
	}
	if context == "std" {
		return ""
	}
	return context
}

// parseGeneratedExpression parses a single generated expression.
func parseGeneratedExpression(text string) (ast.Expression, error) {
	tree, err := New().WithSource("<derived>", "__derive_value := "+text+"\n").Parse().Get()
	if err != nil {
		return nil, err
	}
	if len(tree.Root.Statements) != 1 {
		return nil, fmt.Errorf("generated expression parsed to %d statements", len(tree.Root.Statements))
	}
	decl, ok := tree.Root.Statements[0].(*ast.VariableDeclaration)
	if !ok || decl.Value == nil {
		return nil, fmt.Errorf("generated expression did not parse as a value")
	}
	return decl.Value, nil
}

// orderingName finds the ADT `Ordering: type = Less | Equal | Greater` in
// scope — the program's own or the standard library's; "" when absent.
func (d *deriver) orderingName() string {
	best := ""
	for name, decl := range d.types {
		if len(decl.Variants) != 3 {
			continue
		}
		names := map[string]bool{}
		for _, variant := range decl.Variants {
			if variant.Name != nil && variant.Payload == nil {
				names[variant.Name.Value] = true
			}
		}
		if !(names["Less"] && names["Equal"] && names["Greater"]) {
			continue
		}
		demangled := modules.DemangleText(name)
		if demangled == "Ordering" || strings.HasSuffix(demangled, ".Ordering") {
			if best == "" || name < best {
				best = name
			}
		}
	}
	return best
}

func (d *deriver) compareHelper(name, typeName string, decl *ast.ADTType, node ast.Node) (string, bool) {
	ordering := d.orderingName()
	if ordering == "" {
		d.report(CodeDeriveUnsupported, node, "derive.compare requires Ordering: type = Less | Equal | Greater in scope")
		return "", false
	}
	less, equal, greater := ordering+".Less", ordering+".Equal", ordering+".Greater"
	var body string
	if shape, isRecord := recordShape(decl); isRecord {
		// Lexicographic: the first non-Equal field decides. Each field's
		// comparison is bound to a local and matched; the Equal arm nests
		// the next field.
		body = equal
		for i := len(shape.FieldOrder) - 1; i >= 0; i-- {
			field := shape.FieldOrder[i]
			term, ok := d.compareTerm("a."+field.Name, "b."+field.Name, field.Value, node, typeName, field.Name, less, equal, greater)
			if !ok {
				return "", false
			}
			body = fmt.Sprintf("{\n  c%d: %s = %s\n  c%d ? .Less => %s | .Greater => %s | .Equal => %s\n}", i, ordering, term, i, less, greater, body)
		}
	} else {
		// Variants order by declaration index, then by payload.
		var sb strings.Builder
		sb.WriteString("a ?")
		for i, variant := range decl.Variants {
			if variant.Name == nil {
				return "", false
			}
			if i > 0 {
				sb.WriteString(" |")
			}
			if variant.Payload == nil {
				fmt.Fprintf(&sb, " .%s => (b ?", variant.Name.Value)
			} else {
				fmt.Fprintf(&sb, " .%s(x) => (b ?", variant.Name.Value)
			}
			for j, other := range decl.Variants {
				if j > 0 {
					sb.WriteString(" |")
				}
				pattern := "." + other.Name.Value
				if other.Payload != nil {
					pattern += "(y)"
				}
				switch {
				case j < i:
					fmt.Fprintf(&sb, " %s => %s", pattern, greater)
				case j > i:
					fmt.Fprintf(&sb, " %s => %s", pattern, less)
				case variant.Payload == nil:
					fmt.Fprintf(&sb, " %s => %s", pattern, equal)
				default:
					term, ok := d.compareTerm("x", "y", variant.Payload, node, typeName, variant.Name.Value, less, equal, greater)
					if !ok {
						return "", false
					}
					fmt.Fprintf(&sb, " %s => %s", pattern, term)
				}
			}
			sb.WriteString(")")
		}
		body = sb.String()
	}
	return fmt.Sprintf("%s: (a: %s, b: %s): %s = %s", name, typeName, typeName, ordering, body), true
}

func (d *deriver) compareTerm(left, right string, typeExpr ast.Expression, node ast.Node, typeName, member, less, equal, greater string) (string, bool) {
	primitive, declared, ok := d.fieldKind(typeExpr)
	if !ok {
		d.report(CodeDeriveUnsupported, node, "derive.compare for %s: member %s has a type the generator cannot order (fixed-width integers, Bool, and declared records/ADTs are supported)", typeName, member)
		return "", false
	}
	if primitive {
		if ident, _ := typeExpr.(*ast.Identifier); ident.Value == "Bool" {
			left, right = fmt.Sprintf("u64(%s ? 1 | 0)", left), fmt.Sprintf("u64(%s ? 1 | 0)", right)
		}
		return fmt.Sprintf("(%s < %s ? %s | (%s > %s ? %s | %s))", left, right, less, left, right, greater, equal), true
	}
	helper, ok := d.helper("compare", declared, node)
	if !ok {
		return "", false
	}
	return fmt.Sprintf("%s(%s, %s)", helper, left, right), true
}
