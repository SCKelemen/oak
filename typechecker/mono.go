package typechecker

// Monomorphization support (docs/spec/20-types.md, docs/spec/30-adts): the
// type checker is the single authority for which concrete instantiations of
// each generic ADT a program uses and which instantiation every variant
// expression and match was checked against. The backend consumes these
// records instead of guessing by variant name — resolution is decided where
// typing happens. Maintained alongside Oak.Monomorphization (Lean), which
// proves payload substitution preserves the variant structure.

import (
	"fmt"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
)

// Instantiation identifies one concrete generic-ADT instantiation: the
// declared name plus its argument atoms in order.
type Instantiation struct {
	ADT  string
	Args []string
}

// MangledName is the instantiation's flat Oak-level name (the backend adds
// its usual oak_ prefix). Built only from parser-validated identifiers and
// the primitive table.
func (inst Instantiation) MangledName() string {
	if len(inst.Args) == 0 {
		return inst.ADT
	}
	return inst.ADT + "_" + strings.Join(inst.Args, "_")
}

// ConstIntType is a compile-time integer used as a type argument — a const
// parameter (Ring[u8, 16] — docs/spec/20-types.md). It is not a value type:
// it exists only inside generic applications.
type ConstIntType struct {
	Value int64
}

func (t *ConstIntType) String() string { return fmt.Sprintf("%d", t.Value) }

func (t *ConstIntType) Equals(other Type) bool {
	if otherConst, ok := other.(*ConstIntType); ok {
		return t.Value == otherConst.Value
	}
	return false
}

// SubstituteTypeAST rewrites type-parameter identifiers inside a type
// expression with the argument spellings — the one substitution both the
// checker's record instantiation and the backend's monomorphization use.
// Unsupported shapes report false (fail closed).
func SubstituteTypeAST(expr ast.Expression, bindings map[string]ast.Expression) (ast.Expression, bool) {
	switch t := expr.(type) {
	case nil:
		return nil, true
	case *ast.Identifier:
		if replacement, isParam := bindings[t.Value]; isParam {
			return replacement, true
		}
		return t, true
	case *ast.IndexExpression:
		left, okLeft := SubstituteTypeAST(t.Left, bindings)
		index, okIndex := SubstituteTypeAST(t.Index, bindings)
		if !okLeft || !okIndex {
			return nil, false
		}
		return &ast.IndexExpression{Token: t.Token, Left: left, Index: index, Dot: t.Dot}, true
	case *ast.FunctionTypeExpression:
		out := &ast.FunctionTypeExpression{Token: t.Token}
		for _, parameter := range t.Parameters {
			substituted, ok := SubstituteTypeAST(parameter, bindings)
			if !ok {
				return nil, false
			}
			out.Parameters = append(out.Parameters, substituted)
		}
		result, ok := SubstituteTypeAST(t.Return, bindings)
		if !ok {
			return nil, false
		}
		out.Return = result
		return out, true
	case *ast.IntegerLiteral:
		return t, true
	}
	return nil, false
}

// ArgumentSpelling renders a concrete type argument back to type-expression
// syntax, for substitution into templates.
func ArgumentSpelling(arg Type) (ast.Expression, bool) {
	if constInt, isConst := arg.(*ConstIntType); isConst {
		return &ast.IntegerLiteral{Value: constInt.Value}, true
	}
	atom, ok := typeAtom(arg)
	if !ok {
		return nil, false
	}
	return &ast.Identifier{Value: atom}, true
}

// typeAtom flattens a concrete type argument into a name atom. Types the
// v1 backend cannot mangle (arrays, views, spans, functions, anonymous
// shapes, unresolved variables) report false, and the instantiation is not
// recorded — the backend then fails closed rather than guessing.
func typeAtom(argType Type) (string, bool) {
	switch t := argType.(type) {
	case *PrimitiveType:
		return normalizePrimitiveName(t.Name), true
	case *BoolType:
		return "Bool", true
	case *StringType:
		return "string", true
	case *ADTType:
		return t.Name, true
	case *RecordType:
		if t.Name != "" {
			return t.Name, true
		}
	case *ConstIntType:
		return fmt.Sprintf("%d", t.Value), true
	case *GenericType:
		inner := make([]string, 0, len(t.TypeArgs))
		for _, arg := range t.TypeArgs {
			atom, ok := typeAtom(arg)
			if !ok {
				return "", false
			}
			inner = append(inner, atom)
		}
		return Instantiation{ADT: t.Name, Args: inner}.MangledName(), true
	}
	return "", false
}

// recordADTInstantiation notes a concrete instantiation and returns its
// mangled name. Unknown ADTs, empty argument lists, and unmangleable
// arguments record nothing.
func (tc *TypeChecker) recordADTInstantiation(name string, args []Type) (string, bool) {
	if len(args) == 0 {
		return "", false
	}
	atoms := make([]string, 0, len(args))
	for _, arg := range args {
		atom, ok := typeAtom(arg)
		if !ok {
			return "", false
		}
		atoms = append(atoms, atom)
	}
	inst := Instantiation{ADT: name, Args: atoms}
	mangled := inst.MangledName()
	if tc.adtInstantiations == nil {
		tc.adtInstantiations = make(map[string]Instantiation)
	}
	tc.adtInstantiations[mangled] = inst
	return mangled, true
}

// recordVariantResolution notes which instantiation a variant expression
// was checked against (called from checkVariantExpression with the
// expected-type context).
func (tc *TypeChecker) recordVariantResolution(expr *ast.VariantExpression, name string, args []Type) {
	if expr == nil {
		return
	}
	mangled, ok := tc.resolutionName(name, args)
	if !ok {
		return
	}
	if tc.variantResolutions == nil {
		tc.variantResolutions = make(map[string]string)
	}
	tc.variantResolutions[positionKey(expr.Token)] = mangled
}

// positionKey identifies a node by source position, so resolutions survive
// the lowering pass's node reconstruction.
func positionKey(tok token.Token) string {
	return fmt.Sprintf("%s:%d:%d:%s", tok.SemanticContext, tok.Line, tok.Column, tok.Literal)
}

// recordShiftWidth notes the operand width of one shift expression, so the
// backend emits the right checked helper without re-deriving types.
func (tc *TypeChecker) recordShiftWidth(expr *ast.InfixExpression, width int) {
	if tc.shiftWidths == nil {
		tc.shiftWidths = make(map[string]int)
	}
	tc.shiftWidths[positionKey(expr.Token)] = width
}

// ShiftWidth reports the recorded operand width of a shift expression.
func (tc *TypeChecker) ShiftWidth(tok token.Token) (int, bool) {
	width, ok := tc.shiftWidths[positionKey(tok)]
	return width, ok
}

// FixedWidthName resolves an integer type name to its fixed-width spelling:
// aliases and the platform-sized int/uint/ptr/uptr map onto u8..i64, and any
// other name yields "" (not a machine integer the backend can wrap).
func (tc *TypeChecker) FixedWidthName(name string) string {
	switch name {
	case "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64":
		return name
	case "byte":
		return "u8"
	case "rune":
		return "u32"
	case "int":
		return fmt.Sprintf("i%d", tc.intSize)
	case "uint":
		return fmt.Sprintf("u%d", tc.intSize)
	case "ptr":
		return fmt.Sprintf("i%d", tc.ptrSize)
	case "uptr":
		return fmt.Sprintf("u%d", tc.ptrSize)
	}
	return ""
}

// recordArithmetic notes the fixed-width result type of one arithmetic
// expression, so the backend emits the total (two's-complement, never-UB)
// helper for that width instead of C's promoted operator. It returns the
// result type unchanged for the caller.
func (tc *TypeChecker) recordArithmetic(expr *ast.InfixExpression, result Type) Type {
	prim, ok := result.(*PrimitiveType)
	if !ok {
		return result
	}
	name := tc.FixedWidthName(prim.Name)
	if name == "" {
		return result
	}
	if tc.arithmeticTypes == nil {
		tc.arithmeticTypes = make(map[string]string)
	}
	tc.arithmeticTypes[positionKey(expr.Token)] = name
	return result
}

// ArithmeticType reports the recorded fixed-width result type of an
// arithmetic expression.
func (tc *TypeChecker) ArithmeticType(tok token.Token) (string, bool) {
	name, ok := tc.arithmeticTypes[positionKey(tok)]
	return name, ok
}

// recordMatchResolution notes which instantiation a match scrutinee has.
func (tc *TypeChecker) recordMatchResolution(match *ast.MatchExpression, name string, args []Type) {
	if match == nil {
		return
	}
	mangled, ok := tc.resolutionName(name, args)
	if !ok {
		return
	}
	if tc.matchResolutions == nil {
		tc.matchResolutions = make(map[string]string)
	}
	tc.matchResolutions[positionKey(match.Token)] = mangled
}

// resolutionName names the concrete type a construct was checked against:
// the declared name for a plain ADT, the mangled instantiation (recorded
// for emission) for a generic application.
func (tc *TypeChecker) resolutionName(name string, args []Type) (string, bool) {
	if len(args) == 0 {
		return name, true
	}
	return tc.recordADTInstantiation(name, args)
}

// lenientFlattenApplication decodes F[A][B]... allowing integer-literal
// arguments (const parameters). The caller disambiguates against array
// syntax by consulting the template registry.
func lenientFlattenApplication(expr ast.Expression) (string, []ast.Expression, bool) {
	switch e := expr.(type) {
	case *ast.Identifier:
		return e.Value, nil, e.Value != ""
	case *ast.IndexExpression:
		name, args, ok := lenientFlattenApplication(e.Left)
		if !ok || e.Index == nil {
			return "", nil, false
		}
		if marker, isIdent := e.Index.(*ast.Identifier); isIdent && (marker.Value == "" || marker.Value == "*") {
			return "", nil, false
		}
		return name, append(args, e.Index), true
	default:
		return "", nil, false
	}
}

// resolveRecordTemplateApplication instantiates Ring[u8, 16]-style
// applications of declared record templates. Template knowledge is the
// disambiguator against array syntax ([16]u8 stays an array; a template
// name applied to its declared parameter count is an application).
func (tc *TypeChecker) resolveRecordTemplateApplication(expr ast.Expression) (Type, bool) {
	name, argExprs, ok := lenientFlattenApplication(expr)
	if !ok || len(argExprs) == 0 {
		return nil, false
	}
	template, isTemplate := tc.recordTemplates[name]
	if !isTemplate || len(template.TypeParams) != len(argExprs) {
		return nil, false
	}
	args := make([]Type, 0, len(argExprs))
	for _, argExpr := range argExprs {
		arg := tc.parseTypeExpression(argExpr)
		if arg == nil {
			return nil, true
		}
		args = append(args, arg)
	}
	if instantiated := tc.instantiateRecordTemplate(template, args); instantiated != nil {
		return instantiated, true
	}
	tc.addError(expr, "cannot instantiate %s with these arguments", name)
	return nil, true
}

// instantiateRecordTemplate builds the nominal record type for one
// template instantiation: field types with parameters substituted, the
// mangled name as identity, cached per instantiation. The backend emits
// the matching struct from the same substitution (codegen/mono.go over
// SubstituteTypeAST — one substitution authority).
func (tc *TypeChecker) instantiateRecordTemplate(template *ast.ADTType, args []Type) *RecordType {
	if template == nil || len(template.TypeParams) != len(args) {
		return nil
	}
	recordLit, isRecord := recordTemplateLiteral(template)
	if !isRecord {
		return nil
	}
	mangled, ok := tc.recordADTInstantiation(template.Name.Value, args)
	if !ok {
		return nil
	}
	if cached, hit := tc.recordInstantiationCache[mangled]; hit {
		return cached
	}

	bindings := make(map[string]ast.Expression, len(args))
	for i, param := range template.TypeParams {
		if param == nil || param.Name == nil {
			return nil
		}
		spelling, okArg := ArgumentSpelling(args[i])
		if !okArg {
			return nil
		}
		bindings[param.Name.Value] = spelling
	}

	fields := make(map[string]Type, len(recordLit.FieldOrder))
	order := make([]string, 0, len(recordLit.FieldOrder))
	for _, field := range recordLit.FieldOrder {
		substituted, okSubst := SubstituteTypeAST(field.Value, bindings)
		if !okSubst {
			return nil
		}
		fieldType := tc.parseTypeExpression(substituted)
		if fieldType == nil {
			return nil
		}
		fields[field.Name] = fieldType
		order = append(order, field.Name)
	}
	// Template instantiations inherit the template's representation
	// commitment: struct templates yield nominal structs (Idx[Thread]).
	instantiated := &RecordType{Name: mangled, Order: order, Fields: fields, Struct: recordLit.Token.TokenKind == token.STRUCT}
	if tc.recordInstantiationCache == nil {
		tc.recordInstantiationCache = make(map[string]*RecordType)
	}
	tc.recordInstantiationCache[mangled] = instantiated
	return instantiated
}

// recordTemplateLiteral extracts the record literal of a template decl.
func recordTemplateLiteral(template *ast.ADTType) (*ast.RecordLiteral, bool) {
	if len(template.Variants) != 1 || template.Variants[0].Literal == nil {
		return nil, false
	}
	recordLit, ok := template.Variants[0].Literal.(*ast.RecordLiteral)
	return recordLit, ok
}

// RecordTemplateInstantiations exposes which recorded instantiations are
// record templates (the backend routes them to struct emission).
func (tc *TypeChecker) RecordTemplate(name string) (*ast.ADTType, bool) {
	template, ok := tc.recordTemplates[name]
	return template, ok
}

// ADTInstantiations returns every recorded concrete instantiation, sorted
// by mangled name for deterministic emission.
func (tc *TypeChecker) ADTInstantiations() []Instantiation {
	names := make([]string, 0, len(tc.adtInstantiations))
	for name := range tc.adtInstantiations {
		names = append(names, name)
	}
	sort.Strings(names)
	instantiations := make([]Instantiation, 0, len(names))
	for _, name := range names {
		instantiations = append(instantiations, tc.adtInstantiations[name])
	}
	return instantiations
}

// VariantResolution reports the mangled instantiation a variant expression
// was checked against, when one was recorded.
func (tc *TypeChecker) VariantResolution(expr *ast.VariantExpression) (string, bool) {
	mangled, ok := tc.variantResolutions[positionKey(expr.Token)]
	return mangled, ok
}

// MatchResolution reports the mangled instantiation of a match scrutinee,
// when one was recorded.
func (tc *TypeChecker) MatchResolution(match *ast.MatchExpression) (string, bool) {
	mangled, ok := tc.matchResolutions[positionKey(match.Token)]
	return mangled, ok
}
