package compiler

// Derived declarations (docs/spec/83-modules.md section 6.6): a
// declaration-form function whose definition is `derive.equal` or
// `derive.hash` receives a compiler-synthesized body computed from the
// structure of its parameter type — the same pattern as `c.extern("sym")`
// (a typed interface whose body the compiler supplies) and the tag-driven
// codec derivation of docs/spec/71-codecs.md. The body is built as typed
// syntax (compiler/synth.go) from the type's field order and variant list
// (one fact: the declaration) and checked by every gate like handwritten
// code. Derivation is admitted only in the package that declares the type
// (the orphan rule), so opaque types stay opaque and a derived operation
// always has exactly one definition.
//
// Generated helper names contain `__`, the reserved sequence, so they can
// never collide with user identifiers; only validated identifiers and
// integer constants enter the generated syntax.

import (
	"fmt"
	"reflect"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/modules"
	"github.com/SCKelemen/oak/typechecker"
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
	helpers   []*ast.FunctionStatement
	diags     []*diagnostic.Diagnostic
	// spellings maps an instantiation's mangled name to the type
	// application text (`Ring[u8, 8]`) a rendered type name shows, and
	// applications to the application syntax generated signatures rebuild.
	spellings    map[string]string
	applications map[string]ast.Expression
}

// lowerDerived replaces every `derive.<kind>` definition with a call to a
// generated helper and appends the helpers to the program.
func lowerDerived(tree *SyntaxTree, comp Compilation) error {
	program := tree.Root
	d := &deriver{program: program, types: map[string]*ast.ADTType{}, generated: map[string]bool{}, spellings: map[string]string{}, applications: map[string]ast.Expression{}}
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
	// Helpers carry their owning type's package in their resolution
	// context (helperContext), so the opaque-projection rule sees them as
	// the type's own package. They precede the declarations that call them
	// so that a sequential evaluator (the REPL's interpreter) sees
	// definitions before uses; the checker and backend are order-independent.
	head := 0
	for head < len(program.Statements) {
		switch program.Statements[head].(type) {
		case *ast.PackageStatement, *ast.ImportStatement:
			head++
			continue
		}
		break
	}
	merged := make([]ast.Statement, 0, len(program.Statements)+len(d.helpers))
	merged = append(merged, program.Statements[:head]...)
	for _, helper := range d.helpers {
		merged = append(merged, helper)
	}
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
	case "format":
		if len(fn.Parameters) != 2 || fn.Receiver != nil || len(fn.TypeParams) != 0 || !isSpanOfU8(fn.Parameters[1].Type) || !d.isTextResult(fn.ReturnType) {
			d.report(CodeDeriveSignature, fn.Name, "derive.format requires the signature (v: T, dst: [*]u8): Result[u32, TextError] (the strings library's TextError)")
			return
		}
	case "reserved_zero":
		if len(fn.Parameters) != 1 || fn.Receiver != nil || len(fn.TypeParams) != 0 || !isIdentifierType(fn.ReturnType, "Bool") {
			d.report(CodeDeriveSignature, fn.Name, "derive.reserved_zero requires the signature (v: T): Bool")
			return
		}
	case "test_generate", "test_encode", "test_decode":
		// Signature and target type are checked together: the type is the
		// return type (generate), the parameter (encode), or Option's
		// argument (decode).
	default:
		diag := d.report(CodeDeriveUnknown, fn.Body, "derive.%s is not a derivable operation", kind)
		diag.AddHelp("derivable operations: derive.equal, derive.hash, derive.compare, derive.format, derive.reserved_zero, derive.test_generate, derive.test_encode, derive.test_decode")
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
			// A generic instantiation (`Ring[u8, 8]`): derive over the
			// substituted shape under the instantiation's identity.
			mangled, instantiated := d.instantiate(fn.Parameters[0].Type)
			if !instantiated {
				d.report(CodeDeriveUnsupported, fn.Parameters[0].Type, "derive.%s: the parameter type must be a declared record or ADT, or a concrete instantiation of a generic one", kind)
				return
			}
			ident = &ast.Identifier{Token: fn.Token, Value: mangled}
		}
		typeName = ident
	}
	decl, declared := d.types[typeName.Value]
	if !declared {
		d.report(CodeDeriveUnsupported, typeName, "derive.%s: %s is not a declared record or ADT", kind, typeName.Value)
		return
	}
	if len(decl.TypeParams) != 0 {
		d.report(CodeDeriveUnsupported, typeName, "derive.%s: %s is a generic template; derive over a concrete instantiation such as %s[u8]", kind, typeName.Value, typeName.Value)
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
	// The body is one call, in the request's own package context (its
	// name keeps positions distinct from other requests' bodies).
	s := newSynth(helperContext(fn.Token.SemanticContext, "derive-body:"+fn.Name.Value))
	if kind == "format" {
		// The formatter threads a text builder over the caller's span and
		// finishes it: derived bodies use the library's flat spellings, which
		// the library sugar resolves afterwards (compiler/stdlib.go).
		fn.Body = s.call("finish_text", s.call(helper, s.call("text_builder"), s.id(fn.Parameters[1].Name.Value), s.id(fn.Parameters[0].Name.Value)))
		return
	}
	args := make([]ast.Expression, 0, len(fn.Parameters))
	for _, param := range fn.Parameters {
		args = append(args, s.id(param.Name.Value))
	}
	fn.Body = s.call(helper, args...)
}

// helperContext is the resolution context of generated syntax: the owning
// package's context (the checker reads the package before the first `|` or
// `#`, typechecker/modules.go) qualified by a name, so position-keyed
// records never alias between generated functions.
func helperContext(owner, name string) string {
	if owner == "" {
		return "#" + name
	}
	return owner + "|" + name
}

// helperContext for a helper of a declared type: the type's own package.
func (d *deriver) helperContext(decl *ast.ADTType, helper string) string {
	return helperContext(decl.Name.Token.SemanticContext, helper)
}

// typeExpr is the type a generated signature names for typeName: the
// rebuilt application for an instantiation, the name otherwise.
func (d *deriver) typeExpr(s *synth, typeName string) ast.Expression {
	if application, ok := d.applications[typeName]; ok {
		if rebuilt, ok := s.rebuildType(application); ok {
			return rebuilt
		}
	}
	return s.id(typeName)
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
	var fn *ast.FunctionStatement
	var ok bool
	switch kind {
	case "equal":
		fn, ok = d.equalHelper(name, typeName, decl, node)
	case "hash":
		fn, ok = d.hashHelper(name, typeName, decl, node)
	case "compare":
		fn, ok = d.compareHelper(name, typeName, decl, node)
	case "format":
		fn, ok = d.formatHelper(name, typeName, decl, node)
	case "reserved_zero":
		fn, ok = d.reservedZeroHelper(name, typeName, decl, node)
	case "test_generate":
		fn, ok = d.testGenerateHelper(name, typeName, decl, node)
	case "test_encode":
		fn, ok = d.testEncodeHelper(name, typeName, decl, node)
	case "test_decode":
		fn, ok = d.testDecodeHelper(name, typeName, decl, node)
	}
	if !ok {
		return "", false
	}
	d.helpers = append(d.helpers, fn)
	return name, true
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
		if mangled, instantiated := d.instantiate(expr); instantiated {
			return false, mangled, true
		}
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

func (d *deriver) equalHelper(name, typeName string, decl *ast.ADTType, node ast.Node) (*ast.FunctionStatement, bool) {
	s := newSynth(d.helperContext(decl, name))
	var body ast.Expression
	if shape, isRecord := recordShape(decl); isRecord {
		terms := make([]ast.Expression, 0, len(shape.FieldOrder))
		for _, field := range shape.FieldOrder {
			term, ok := d.equalTerm(s, s.field(s.id("a"), field.Name), s.field(s.id("b"), field.Name), field.Value, node, typeName, field.Name)
			if !ok {
				return nil, false
			}
			terms = append(terms, term)
		}
		if len(terms) == 0 {
			body = s.boolean(true)
		} else {
			body = s.and(terms...)
		}
	} else {
		// a ? .V => (b ? .V => true | _ => false) | .W(x) => (b ? .W(y) => x == y | _ => false)
		arms := make([]*ast.MatchArm, 0, len(decl.Variants))
		for _, variant := range decl.Variants {
			if variant.Name == nil {
				return nil, false
			}
			if variant.Payload == nil {
				arms = append(arms, s.arm(variant.Name.Value, "", s.match(s.id("b"), s.arm(variant.Name.Value, "", s.boolean(true)), s.wildcardArm(s.boolean(false)))))
				continue
			}
			term, ok := d.equalTerm(s, s.id("x"), s.id("y"), variant.Payload, node, typeName, variant.Name.Value)
			if !ok {
				return nil, false
			}
			arms = append(arms, s.arm(variant.Name.Value, "x", s.match(s.id("b"), s.arm(variant.Name.Value, "y", term), s.wildcardArm(s.boolean(false)))))
		}
		body = s.match(s.id("a"), arms...)
	}
	return s.fnExpr(name, []*ast.FunctionParameter{s.param("a", d.typeExpr(s, typeName)), s.param("b", d.typeExpr(s, typeName))}, s.id("Bool"), body), true
}

func (d *deriver) equalTerm(s *synth, left, right ast.Expression, typeExpr ast.Expression, node ast.Node, typeName, member string) (ast.Expression, bool) {
	primitive, declared, ok := d.fieldKind(typeExpr)
	if !ok {
		d.report(CodeDeriveUnsupported, node, "derive.equal for %s: member %s has a type the generator cannot compare (fixed-width integers, Bool, and declared records/ADTs are supported)", typeName, member)
		return nil, false
	}
	if primitive {
		return s.eq(left, right), true
	}
	helper, ok := d.helper("equal", declared, node)
	if !ok {
		return nil, false
	}
	return s.call(helper, left, right), true
}

func (d *deriver) hashHelper(name, typeName string, decl *ast.ADTType, node ast.Node) (*ast.FunctionStatement, bool) {
	s := newSynth(d.helperContext(decl, name))
	var body ast.Expression
	if shape, isRecord := recordShape(decl); isRecord {
		// FNV offset basis, then per field: mix in, then xorshift.
		statements := []ast.Statement{s.decl("h", s.id("u64"), s.intLit(1469598103934665603))}
		h := func() ast.Expression { return s.id("h") }
		for _, field := range shape.FieldOrder {
			term, ok := d.hashTerm(s, s.field(s.id("v"), field.Name), field.Value, node, typeName, field.Name)
			if !ok {
				return nil, false
			}
			statements = append(statements,
				s.assign("h", s.infix(h(), "^", term)),
				s.assign("h", s.infix(h(), "^", s.infix(h(), "<<", s.intLit(13)))),
				s.assign("h", s.infix(h(), "^", s.infix(h(), ">>", s.intLit(7)))),
				s.assign("h", s.infix(h(), "^", s.infix(h(), "<<", s.intLit(17)))))
		}
		statements = append(statements, s.expr(h()))
		body = s.block(statements...)
	} else {
		arms := make([]*ast.MatchArm, 0, len(decl.Variants))
		for i, variant := range decl.Variants {
			if variant.Name == nil {
				return nil, false
			}
			if variant.Payload == nil {
				arms = append(arms, s.arm(variant.Name.Value, "", s.conv("u64", s.intLit(int64(i+1)))))
				continue
			}
			term, ok := d.hashTerm(s, s.id("x"), variant.Payload, node, typeName, variant.Name.Value)
			if !ok {
				return nil, false
			}
			salt := int64((i + 1) * 2654435761 % 4294967296)
			arms = append(arms, s.arm(variant.Name.Value, "x", s.infix(term, "^", s.conv("u64", s.intLit(salt)))))
		}
		body = s.match(s.id("v"), arms...)
	}
	return s.fnExpr(name, []*ast.FunctionParameter{s.param("v", d.typeExpr(s, typeName))}, s.id("u64"), body), true
}

func (d *deriver) hashTerm(s *synth, value ast.Expression, typeExpr ast.Expression, node ast.Node, typeName, member string) (ast.Expression, bool) {
	primitive, declared, ok := d.fieldKind(typeExpr)
	if !ok {
		d.report(CodeDeriveUnsupported, node, "derive.hash for %s: member %s has a type the generator cannot hash (fixed-width integers, Bool, and declared records/ADTs are supported)", typeName, member)
		return nil, false
	}
	if primitive {
		if ident, _ := typeExpr.(*ast.Identifier); ident.Value == "Bool" {
			return s.conv("u64", s.cond(value, s.intLit(1), s.intLit(0))), true
		}
		return s.conv("u64", value), true
	}
	helper, ok := d.helper("hash", declared, node)
	if !ok {
		return nil, false
	}
	return s.call(helper, value), true
}

func sameIdentifierType(a, b ast.Expression) bool {
	left, okLeft := a.(*ast.Identifier)
	right, okRight := b.(*ast.Identifier)
	if okLeft && okRight {
		return left.Value == right.Value
	}
	// Instantiations compare by their spelled application.
	if _, okApp := a.(*ast.IndexExpression); okApp {
		if _, okApp2 := b.(*ast.IndexExpression); okApp2 {
			return spellType(a) == spellType(b)
		}
	}
	return false
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

func (d *deriver) compareHelper(name, typeName string, decl *ast.ADTType, node ast.Node) (*ast.FunctionStatement, bool) {
	ordering := d.orderingName()
	if ordering == "" {
		d.report(CodeDeriveUnsupported, node, "derive.compare requires Ordering: type = Less | Equal | Greater in scope")
		return nil, false
	}
	s := newSynth(d.helperContext(decl, name))
	outcome := func(variant string) ast.Expression { return s.qualified(ordering, variant, nil) }
	var body ast.Expression
	if shape, isRecord := recordShape(decl); isRecord {
		// Lexicographic: the first non-Equal field decides. Each field's
		// comparison is bound to a local and matched; the Equal arm nests
		// the next field.
		body = outcome("Equal")
		for i := len(shape.FieldOrder) - 1; i >= 0; i-- {
			field := shape.FieldOrder[i]
			term, ok := d.compareTerm(s, ordering,
				func() ast.Expression { return s.field(s.id("a"), field.Name) },
				func() ast.Expression { return s.field(s.id("b"), field.Name) },
				field.Value, node, typeName, field.Name)
			if !ok {
				return nil, false
			}
			local := fmt.Sprintf("c%d", i)
			body = s.block(
				s.decl(local, s.id(ordering), term),
				s.expr(s.match(s.id(local),
					s.arm("Less", "", outcome("Less")),
					s.arm("Greater", "", outcome("Greater")),
					s.arm("Equal", "", body))))
		}
	} else {
		// Variants order by declaration index, then by payload.
		arms := make([]*ast.MatchArm, 0, len(decl.Variants))
		for i, variant := range decl.Variants {
			if variant.Name == nil {
				return nil, false
			}
			inner := make([]*ast.MatchArm, 0, len(decl.Variants))
			for j, other := range decl.Variants {
				binding := ""
				if other.Payload != nil {
					binding = "y"
				}
				var result ast.Expression
				switch {
				case j < i:
					result = outcome("Greater")
				case j > i:
					result = outcome("Less")
				case variant.Payload == nil:
					result = outcome("Equal")
				default:
					term, ok := d.compareTerm(s, ordering,
						func() ast.Expression { return s.id("x") },
						func() ast.Expression { return s.id("y") },
						variant.Payload, node, typeName, variant.Name.Value)
					if !ok {
						return nil, false
					}
					result = term
				}
				inner = append(inner, s.arm(other.Name.Value, binding, result))
			}
			binding := ""
			if variant.Payload != nil {
				binding = "x"
			}
			arms = append(arms, s.arm(variant.Name.Value, binding, s.match(s.id("b"), inner...)))
		}
		body = s.match(s.id("a"), arms...)
	}
	return s.fnExpr(name, []*ast.FunctionParameter{s.param("a", d.typeExpr(s, typeName)), s.param("b", d.typeExpr(s, typeName))}, s.id(ordering), body), true
}

// compareTerm orders one member: primitives by <, > (Bool as 0/1), declared
// types by their derived comparison. The operands are rebuilt per use.
func (d *deriver) compareTerm(s *synth, ordering string, left, right func() ast.Expression, typeExpr ast.Expression, node ast.Node, typeName, member string) (ast.Expression, bool) {
	primitive, declared, ok := d.fieldKind(typeExpr)
	if !ok {
		d.report(CodeDeriveUnsupported, node, "derive.compare for %s: member %s has a type the generator cannot order (fixed-width integers, Bool, and declared records/ADTs are supported)", typeName, member)
		return nil, false
	}
	if primitive {
		if ident, _ := typeExpr.(*ast.Identifier); ident.Value == "Bool" {
			asWord := func(operand func() ast.Expression) func() ast.Expression {
				return func() ast.Expression { return s.conv("u64", s.cond(operand(), s.intLit(1), s.intLit(0))) }
			}
			left, right = asWord(left), asWord(right)
		}
		return s.cond(s.lt(left(), right()), s.qualified(ordering, "Less", nil),
			s.cond(s.gt(left(), right()), s.qualified(ordering, "Greater", nil), s.qualified(ordering, "Equal", nil))), true
	}
	helper, ok := d.helper("compare", declared, node)
	if !ok {
		return nil, false
	}
	return s.call(helper, left(), right()), true
}

// isSpanOfU8 recognizes the `[*]u8` destination parameter.
func isSpanOfU8(expr ast.Expression) bool {
	index, ok := expr.(*ast.IndexExpression)
	if !ok {
		return false
	}
	element, okElement := index.Left.(*ast.Identifier)
	marker, okMarker := index.Index.(*ast.Identifier)
	return okElement && okMarker && element.Value == "u8" && marker.Value == "*"
}

// isTextResult recognizes `Result[u32, TextError]`, TextError being the
// strings library's error type under its flat or internal spelling.
func (d *deriver) isTextResult(expr ast.Expression) bool {
	outer, ok := expr.(*ast.IndexExpression)
	if !ok {
		return false
	}
	inner, ok := outer.Left.(*ast.IndexExpression)
	if !ok {
		return false
	}
	base, okBase := inner.Left.(*ast.Identifier)
	first, okFirst := inner.Index.(*ast.Identifier)
	second, okSecond := outer.Index.(*ast.Identifier)
	if !okBase || !okFirst || !okSecond || base.Value != "Result" || first.Value != "u32" {
		return false
	}
	return second.Value == "TextError" || strings.HasSuffix(modules.DemangleText(second.Value), ".TextError")
}

// signedFormatHelper is generated once: a two's-complement-safe decimal
// rendering of any signed width widened to i64.
const signedFormatHelper = "__derive_format_signed"

func (d *deriver) formatHelper(name, typeName string, decl *ast.ADTType, node ast.Node) (*ast.FunctionStatement, bool) {
	if !d.generated[signedFormatHelper] {
		d.generated[signedFormatHelper] = true
		g := newSynth(helperContext("", signedFormatHelper))
		// v < 0 ? append_u64(append_rune(b, dst, '-'), dst, u64_bits_i64(0 - (v + 1)) + 1) | append_u64(b, dst, u64_bits_i64(v))
		d.helpers = append(d.helpers, g.fnExpr(signedFormatHelper,
			[]*ast.FunctionParameter{g.param("b", g.id("TextBuilder")), g.param("dst", g.span(g.id("u8"))), g.param("v", g.id("i64"))},
			g.id("TextBuilder"),
			g.cond(g.lt(g.id("v"), g.intLit(0)),
				g.call("append_u64", g.call("append_rune", g.id("b"), g.id("dst"), g.u32(45)), g.id("dst"),
					g.add(g.call("u64_bits_i64", g.sub(g.intLit(0), g.add(g.id("v"), g.intLit(1)))), g.conv("u64", g.intLit(1)))),
				g.call("append_u64", g.id("b"), g.id("dst"), g.call("u64_bits_i64", g.id("v"))))))
	}
	short := modules.DemangleText(d.spell(typeName))
	if index := strings.LastIndexByte(short, '.'); index >= 0 && !strings.Contains(short[:index], "[") {
		short = short[index+1:]
	}
	s := newSynth(d.helperContext(decl, name))
	literal := func(builder func() ast.Expression, text string) ast.Expression {
		return s.call("append_text", builder(), s.id("dst"), s.call("text_literal", s.str(text)))
	}
	var body ast.Expression
	if shape, isRecord := recordShape(decl); isRecord {
		// s0: TextBuilder = append_text(b, ...); s1 = ...; the last step is
		// the result.
		statements := []ast.Statement{}
		current := "b"
		step := 0
		builder := func() ast.Expression { return s.id(current) }
		emit := func(expr ast.Expression) {
			next := fmt.Sprintf("s%d", step)
			statements = append(statements, s.decl(next, s.id("TextBuilder"), expr))
			current = next
			step++
		}
		emit(literal(builder, short+" {"))
		for i, field := range shape.FieldOrder {
			separator := " "
			if i > 0 {
				separator = ", "
			}
			emit(literal(builder, separator+field.Name+": "))
			term, ok := d.formatTerm(s, builder, s.field(s.id("v"), field.Name), field.Value, node, typeName, field.Name)
			if !ok {
				return nil, false
			}
			emit(term)
		}
		emit(literal(builder, " }"))
		statements = append(statements, s.expr(builder()))
		body = s.block(statements...)
	} else {
		arms := make([]*ast.MatchArm, 0, len(decl.Variants))
		for _, variant := range decl.Variants {
			if variant.Name == nil {
				return nil, false
			}
			plain := func() ast.Expression { return s.id("b") }
			if variant.Payload == nil {
				arms = append(arms, s.arm(variant.Name.Value, "", literal(plain, variant.Name.Value)))
				continue
			}
			opened := func() ast.Expression { return literal(plain, variant.Name.Value+"(") }
			term, ok := d.formatTerm(s, opened, s.id("x"), variant.Payload, node, typeName, variant.Name.Value)
			if !ok {
				return nil, false
			}
			arms = append(arms, s.arm(variant.Name.Value, "x", s.call("append_rune", term, s.id("dst"), s.u32(41))))
		}
		body = s.match(s.id("v"), arms...)
	}
	return s.fnExpr(name,
		[]*ast.FunctionParameter{s.param("b", s.id("TextBuilder")), s.param("dst", s.span(s.id("u8"))), s.param("v", d.typeExpr(s, typeName))},
		s.id("TextBuilder"), body), true
}

var signedFormatTypes = map[string]bool{"i8": true, "i16": true, "i32": true, "i64": true, "int": true, "ptr": true}

// formatTerm renders one member onto the builder; the builder expression is
// rebuilt per use.
func (d *deriver) formatTerm(s *synth, builder func() ast.Expression, value ast.Expression, typeExpr ast.Expression, node ast.Node, typeName, member string) (ast.Expression, bool) {
	primitive, declared, ok := d.fieldKind(typeExpr)
	if !ok {
		d.report(CodeDeriveUnsupported, node, "derive.format for %s: member %s has a type the generator cannot render (fixed-width integers, Bool, and declared records/ADTs are supported)", typeName, member)
		return nil, false
	}
	if primitive {
		ident, _ := typeExpr.(*ast.Identifier)
		switch {
		case ident.Value == "Bool":
			return s.cond(value,
				s.call("append_text", builder(), s.id("dst"), s.call("text_literal", s.str("true"))),
				s.call("append_text", builder(), s.id("dst"), s.call("text_literal", s.str("false")))), true
		case signedFormatTypes[ident.Value]:
			return s.call(signedFormatHelper, builder(), s.id("dst"), s.conv("i64", value)), true
		default:
			return s.call("append_u64", builder(), s.id("dst"), s.conv("u64", value)), true
		}
	}
	helper, ok := d.helper("format", declared, node)
	if !ok {
		return nil, false
	}
	return s.call(helper, builder(), s.id("dst"), value), true
}

// spell returns the type text a generated signature uses for a type name:
// the application text for an instantiation, the name otherwise.
func (d *deriver) spell(typeName string) string {
	if text, ok := d.spellings[typeName]; ok {
		return text
	}
	return typeName
}

// instantiate resolves a generic application `Template[args]` to a
// synthetic concrete declaration registered under the instantiation's
// mangled name (typechecker.Instantiation), substituting the arguments into
// the template's shape with the single substitution authority.
func (d *deriver) instantiate(expr ast.Expression) (string, bool) {
	base, args, ok := flattenApplication(expr)
	if !ok {
		return "", false
	}
	template, declared := d.types[base]
	if !declared || len(template.TypeParams) != len(args) || len(args) == 0 {
		return "", false
	}
	atoms := make([]string, 0, len(args))
	for _, arg := range args {
		atom, ok := d.argumentAtom(arg)
		if !ok {
			return "", false
		}
		atoms = append(atoms, atom)
	}
	mangled := typechecker.Instantiation{ADT: base, Args: atoms}.MangledName()
	if _, exists := d.types[mangled]; exists {
		return mangled, true
	}
	bindings := map[string]ast.Expression{}
	for i, param := range template.TypeParams {
		if param.Name == nil {
			return "", false
		}
		bindings[param.Name.Value] = args[i]
	}
	clone, ok := cloneSyntax(reflect.ValueOf(template)).Interface().(*ast.ADTType)
	if !ok {
		return "", false
	}
	clone.TypeParams = nil
	clone.Name = &ast.Identifier{Token: template.Name.Token, Value: mangled}
	for _, variant := range clone.Variants {
		if variant.Payload != nil {
			substituted, ok := typechecker.SubstituteTypeAST(variant.Payload, bindings)
			if !ok {
				return "", false
			}
			variant.Payload = substituted
		}
		if shape, isShape := variant.Literal.(*ast.RecordLiteral); isShape {
			for i := range shape.FieldOrder {
				substituted, ok := typechecker.SubstituteTypeAST(shape.FieldOrder[i].Value, bindings)
				if !ok {
					return "", false
				}
				shape.FieldOrder[i].Value = substituted
				shape.Fields[shape.FieldOrder[i].Name] = substituted
			}
		}
	}
	d.types[mangled] = clone
	spelled := make([]string, 0, len(args))
	for _, arg := range args {
		spelled = append(spelled, spellType(arg))
	}
	d.spellings[mangled] = base + "[" + strings.Join(spelled, ", ") + "]"
	d.applications[mangled] = expr
	return mangled, true
}

// argumentAtom names an instantiation argument: primitives and declared
// types by name, constants by value, nested instantiations by their mangled
// name.
func (d *deriver) argumentAtom(arg ast.Expression) (string, bool) {
	switch a := arg.(type) {
	case *ast.IntegerLiteral:
		return fmt.Sprintf("%d", a.Value), true
	case *ast.Identifier:
		if derivePrimitives[a.Value] || a.Value == "string" {
			return a.Value, true
		}
		if decl, declared := d.types[a.Value]; declared && len(decl.TypeParams) == 0 {
			return a.Value, true
		}
		return "", false
	case *ast.IndexExpression:
		return d.instantiate(a)
	}
	return "", false
}

// flattenApplication decodes `F[A][B]` (the parser's spelling of `F[A, B]`).
func flattenApplication(expr ast.Expression) (string, []ast.Expression, bool) {
	index, ok := expr.(*ast.IndexExpression)
	if !ok || index.Dot || index.Index == nil {
		return "", nil, false
	}
	if marker, isMarker := index.Index.(*ast.Identifier); isMarker && (marker.Value == "" || marker.Value == "*") {
		return "", nil, false
	}
	switch left := index.Left.(type) {
	case *ast.Identifier:
		return left.Value, []ast.Expression{index.Index}, true
	case *ast.IndexExpression:
		base, args, ok := flattenApplication(left)
		if !ok {
			return "", nil, false
		}
		return base, append(args, index.Index), true
	}
	return "", nil, false
}

// spellType renders a type argument as source text.
func spellType(expr ast.Expression) string {
	switch t := expr.(type) {
	case *ast.Identifier:
		return t.Value
	case *ast.IntegerLiteral:
		return fmt.Sprintf("%d", t.Value)
	case *ast.IndexExpression:
		if base, args, ok := flattenApplication(t); ok {
			spelled := make([]string, 0, len(args))
			for _, arg := range args {
				spelled = append(spelled, spellType(arg))
			}
			return base + "[" + strings.Join(spelled, ", ") + "]"
		}
	}
	return expr.String()
}

// --- reserved_zero -----------------------------------------------------
//
// A wire record's reserved bytes are zero on both sides (TigerBeetle's
// `Header.invalid()`; docs/notes/tigerbeetle-2026-09.md lesson 1;
// docs/spec/40-records.md section 6a): asserted before a write and checked
// after a read. derive.reserved_zero reads the declaration for the fields
// named `reserved` or `reserved_*` and returns whether every one of them
// is zero — a scalar against its typed zero, a Bool as false, a fixed
// array of scalars element by element in a canonical bounded loop — and
// asks a nested record that holds reserved fields the same question
// through its own helper.

// isReservedName is the naming convention the derive reads.
func isReservedName(name string) bool {
	return name == "reserved" || strings.HasPrefix(name, "reserved_")
}

// reservedScalars are the field types a reserved field may have, with the
// spelling of their zero.
var reservedScalars = map[string]bool{
	"i8": true, "i16": true, "i32": true, "i64": true,
	"u8": true, "u16": true, "u32": true, "u64": true, "u128": true,
	"int": true, "uint": true, "byte": true, "rune": true, "Bool": true,
}

// hasReservedFields reports whether a declared record names a reserved
// field, directly or inside a nested declared record.
func (d *deriver) hasReservedFields(typeName string, visiting map[string]bool) bool {
	if visiting[typeName] {
		return false
	}
	visiting[typeName] = true
	decl := d.types[typeName]
	if decl == nil {
		return false
	}
	shape, isRecord := recordShape(decl)
	if !isRecord {
		return false
	}
	for _, field := range shape.FieldOrder {
		if isReservedName(field.Name) {
			return true
		}
		if ident, isIdent := field.Value.(*ast.Identifier); isIdent {
			if nested, declared := d.types[ident.Value]; declared && len(nested.TypeParams) == 0 && d.hasReservedFields(ident.Value, visiting) {
				return true
			}
		}
	}
	return false
}

func (d *deriver) reservedZeroHelper(name, typeName string, decl *ast.ADTType, node ast.Node) (*ast.FunctionStatement, bool) {
	shape, isRecord := recordShape(decl)
	if !isRecord {
		d.report(CodeDeriveUnsupported, node, "derive.reserved_zero for %s: reserved fields belong to a record; %s is a sum type", typeName, typeName)
		return nil, false
	}
	s := newSynth(d.helperContext(decl, name))
	statements := []ast.Statement{s.decl("ok", s.id("Bool"), s.boolean(true))}
	found := false
	for _, field := range shape.FieldOrder {
		value := s.field(s.id("v"), field.Name)
		if isReservedName(field.Name) {
			found = true
			more, ok := d.reservedZeroStatements(s, value, field, node, typeName)
			if !ok {
				return nil, false
			}
			statements = append(statements, more...)
			continue
		}
		if ident, isIdent := field.Value.(*ast.Identifier); isIdent {
			if nested, declared := d.types[ident.Value]; declared && len(nested.TypeParams) == 0 && d.hasReservedFields(ident.Value, map[string]bool{}) {
				found = true
				helper, ok := d.helper("reserved_zero", ident.Value, node)
				if !ok {
					return nil, false
				}
				statements = append(statements, s.assign("ok", s.and(s.id("ok"), s.call(helper, value))))
			}
		}
	}
	if !found {
		d.report(CodeDeriveUnsupported, node, "derive.reserved_zero for %s: no field is named reserved or reserved_*, and no nested record has one — there is nothing to check", typeName)
		return nil, false
	}
	statements = append(statements, s.expr(s.id("ok")))
	return s.fnExpr(name, []*ast.FunctionParameter{s.param("v", d.typeExpr(s, typeName))}, s.id("Bool"), s.block(statements...)), true
}

// reservedZeroStatements folds one reserved field into `ok`.
func (d *deriver) reservedZeroStatements(s *synth, value *ast.IndexExpression, field ast.RecordField, node ast.Node, typeName string) ([]ast.Statement, bool) {
	zeroTerm := func(scalar string, element ast.Expression) ast.Expression {
		if scalar == "Bool" {
			return s.not(element)
		}
		return s.eq(element, s.conv(scalar, s.intLit(0)))
	}
	switch t := field.Value.(type) {
	case *ast.Identifier:
		if reservedScalars[t.Value] {
			return []ast.Statement{s.assign("ok", s.and(s.id("ok"), zeroTerm(t.Value, value)))}, true
		}
	case *ast.IndexExpression:
		length, isFixed := t.Index.(*ast.IntegerLiteral)
		element, isIdent := t.Left.(*ast.Identifier)
		if isFixed && !t.Dot && isIdent && reservedScalars[element.Value] && length.Value > 0 {
			// A canonical bounded loop over the array (85-discipline.md
			// section 3): the counter is the field's own, so two reserved
			// arrays in one record do not share one.
			counter := "i_" + field.Name
			return []ast.Statement{
				s.decl(counter, s.id("u32"), s.u32(0)),
				s.loop(s.lt(s.id(counter), s.u32(length.Value)),
					s.assign("ok", s.and(s.id("ok"), zeroTerm(element.Value, s.index(value, s.id(counter))))),
					s.assign(counter, s.add(s.id(counter), s.u32(1)))),
			}, true
		}
	}
	d.report(CodeDeriveUnsupported, node, "derive.reserved_zero for %s: reserved field %s must be a fixed-width integer, Bool, or a fixed array of those; %s is %s", typeName, field.Name, field.Name, spellType(field.Value))
	return nil, false
}
