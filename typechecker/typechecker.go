package typechecker

import (
	"fmt"
	"sort"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/lsp"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/token"
)

// Type represents a type in the Oak type system
type Type interface {
	String() string
	Equals(other Type) bool
}

// PrimitiveType represents primitive integer types
type PrimitiveType struct {
	Name string // "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "int", "uint", "ptr", "uptr"
}

func (t *PrimitiveType) String() string {
	return t.Name
}

// normalizePrimitiveName folds the surface aliases onto their carriers so
// alias and carrier are one type: byte = u8, rune = u32 (70-strings §9).
func normalizePrimitiveName(name string) string {
	switch name {
	case "byte":
		return "u8"
	case "rune":
		return "u32"
	default:
		return name
	}
}

func (t *PrimitiveType) Equals(other Type) bool {
	if otherPrim, ok := other.(*PrimitiveType); ok {
		return normalizePrimitiveName(t.Name) == normalizePrimitiveName(otherPrim.Name)
	}
	return false
}

// isArrayTypeSyntax reports whether an IndexExpression is array-type syntax
// ([N]T, []T, [*]T) rather than a generic type application.
func isArrayTypeSyntax(expr ast.Expression) bool {
	indexExpr, ok := expr.(*ast.IndexExpression)
	if !ok {
		return false
	}
	switch index := indexExpr.Index.(type) {
	case *ast.IntegerLiteral:
		return true
	case *ast.Identifier:
		return index.Value == "*" || index.Value == ""
	}
	return false
}

// StringType represents an encoded string type (docs/spec/70-strings.md):
// `string` is Str[Utf8]. Encoding tags are phantom — they distinguish static
// identity while every Str[E] shares one representation — so Equals compares
// encodings and nothing else.
type StringType struct {
	// Encoding is the phantom encoding tag; empty means Utf8, so the
	// canonical `string` type is the zero value.
	Encoding string
}

// encoding returns the normalized phantom tag.
func (t *StringType) encoding() string {
	if t.Encoding == "" {
		return "Utf8"
	}
	return t.Encoding
}

func (t *StringType) String() string {
	if t.encoding() == "Utf8" {
		return "string"
	}
	return "Str[" + t.encoding() + "]"
}

func (t *StringType) Equals(other Type) bool {
	otherString, ok := other.(*StringType)
	return ok && t.encoding() == otherString.encoding()
}

// stringEncodings are the phantom encoding tags of docs/spec/70-strings.md.
var stringEncodings = map[string]bool{
	"Utf8": true, "Utf16": true, "Utf32": true, "Ascii": true,
}

// parseStrEncodingType resolves Str[E] type applications to the
// corresponding phantom-encoded string type; nil when expr is not one.
func (tc *TypeChecker) parseStrEncodingType(indexExpr *ast.IndexExpression) Type {
	base, ok := indexExpr.Left.(*ast.Identifier)
	if !ok || base.Value != "Str" {
		return nil
	}
	arg, ok := indexExpr.Index.(*ast.Identifier)
	if !ok || !stringEncodings[arg.Value] {
		tc.addError(indexExpr, "Str[...] requires an encoding tag (Utf8, Utf16, Utf32, Ascii)")
		// Recover as the canonical encoding so one bad tag does not cascade.
		return &StringType{}
	}
	return &StringType{Encoding: arg.Value}
}

// BoolType represents the boolean type
type BoolType struct{}

func (t *BoolType) String() string {
	return "Bool"
}

func (t *BoolType) Equals(other Type) bool {
	_, ok := other.(*BoolType)
	return ok
}

// UnitType represents the unit type ()
type UnitType struct{}

func (t *UnitType) String() string {
	return "()"
}

func (t *UnitType) Equals(other Type) bool {
	// Unit equals itself
	if _, ok := other.(*UnitType); ok {
		return true
	}
	// Unit equals empty record {}
	if otherRecord, ok := other.(*RecordType); ok {
		return len(otherRecord.Fields) == 0
	}
	return false
}

// NeverType represents the uninhabited bottom type
// Used for non-returning functions and unreachable code
type NeverType struct{}

func (t *NeverType) String() string {
	return "never"
}

func (t *NeverType) Equals(other Type) bool {
	_, ok := other.(*NeverType)
	return ok
}

// AnyType represents the top type
// Can hold any safe Oak value, but requires explicit annotation
type AnyType struct{}

func (t *AnyType) String() string {
	return "any"
}

func (t *AnyType) Equals(other Type) bool {
	_, ok := other.(*AnyType)
	return ok
}

// ADTType represents an ADT type
type ADTType struct {
	Name string
}

func (t *ADTType) String() string {
	return t.Name
}

func (t *ADTType) Equals(other Type) bool {
	if otherADT, ok := other.(*ADTType); ok {
		return t.Name == otherADT.Name
	}
	// Make equality symmetric with NarrowedADTVariantType
	// A narrowed variant is compatible with its parent ADT type
	if narrowed, ok := other.(*NarrowedADTVariantType); ok {
		return t.Name == narrowed.ADTName
	}
	return false
}

// NarrowedADTVariantType represents a narrowed ADT variant type
// Used for type narrowing in pattern matching (TypeScript-style)
type NarrowedADTVariantType struct {
	ADTName     string
	VariantName string
	TypeArgs    []Type
}

func (t *NarrowedADTVariantType) String() string {
	parent := (&GenericType{Name: t.ADTName, TypeArgs: t.TypeArgs}).String()
	return fmt.Sprintf("%s::%s", parent, t.VariantName)
}

func (t *NarrowedADTVariantType) Equals(other Type) bool {
	if otherNarrowed, ok := other.(*NarrowedADTVariantType); ok {
		return t.ADTName == otherNarrowed.ADTName &&
			t.VariantName == otherNarrowed.VariantName &&
			typeListsEqual(t.TypeArgs, otherNarrowed.TypeArgs)
	}
	if otherADT, ok := other.(*ADTType); ok {
		return t.ADTName == otherADT.Name && len(t.TypeArgs) == 0
	}
	if otherGeneric, ok := other.(*GenericType); ok {
		return t.ADTName == otherGeneric.Name && typeListsEqual(t.TypeArgs, otherGeneric.TypeArgs)
	}
	return false
}

// RecordType represents a record/struct type
type RecordType struct {
	Fields map[string]Type // field name -> type
	// Name is the nominal identity of a declared record type
	// (Point: type = struct { ... }); empty for anonymous shapes.
	// Identity for Equals stays structural; Name exists so the backend can
	// emit the declared struct.
	Name string
	// Order preserves declaration order (Oak.SemanticRecord), which is
	// layout-significant for struct representation (docs/spec/40-records.md).
	Order []string
	// Struct marks a representation-committed declaration (the struct
	// keyword). Named STRUCTS are nominal islands (phantom types depend on
	// it); named semantic records remain structural shapes any struct with
	// those fields satisfies, whatever its field order.
	Struct bool
	// Open marks { r | ... }; Row is diagnostic metadata only.
	Open bool
	Row  string
}

// DisplayName is the nominal name when declared, else the structural shape.
func (t *RecordType) DisplayName() string {
	if t.Name != "" {
		return t.Name
	}
	return t.String()
}

// orderedFieldNames returns the declaration order when known, else the
// field names sorted (deterministic diagnostics for anonymous shapes).
func (t *RecordType) orderedFieldNames() []string {
	if len(t.Order) == len(t.Fields) {
		return t.Order
	}
	names := make([]string, 0, len(t.Fields))
	for name := range t.Fields {
		names = append(names, name)
	}
	sort.Strings(names)
	return names
}

func (t *RecordType) String() string {
	// A nominal struct IS its name — printing the shape for Idx[Thread]
	// vs Idx[Timer] would show two identical shapes in a mismatch.
	if t.Name != "" && t.Struct {
		return t.Name
	}
	// Canonical form: struct{ field1: Type1, field2: Type2, ... }
	var out string
	out += "struct{"
	first := true
	for name, typ := range t.Fields {
		if !first {
			out += ", "
		}
		out += fmt.Sprintf(" %s: %s", name, typ.String())
		first = false
	}
	if len(t.Fields) > 0 {
		out += " "
	}
	out += "}"
	return out
}

func (t *RecordType) Equals(other Type) bool {
	// Empty record {} is equivalent to Unit
	if len(t.Fields) == 0 {
		if _, ok := other.(*UnitType); ok {
			return true
		}
		if otherRecord, ok := other.(*RecordType); ok {
			return len(otherRecord.Fields) == 0
		}
		return false
	}

	// Declared STRUCTS are nominal islands: two NAMED struct types are the
	// same type only by name — Idx[Thread] and Idx[Timer] share a shape
	// and are still distinct (phantom-typed indices depend on this).
	// Semantic record types ({ a, b: u8 }, named or not) stay structural:
	// they are shapes, satisfied by any record with those fields in any
	// order, including either ordered struct over them.
	if otherRecord, ok := other.(*RecordType); ok {
		if t.Open != otherRecord.Open {
			return false
		}
		if t.Name != "" && otherRecord.Name != "" && t.Struct && otherRecord.Struct {
			return t.Name == otherRecord.Name
		}
	}

	if otherRecord, ok := other.(*RecordType); ok {
		// If other is empty, we already checked above
		if len(otherRecord.Fields) == 0 {
			return false
		}
		if len(t.Fields) != len(otherRecord.Fields) {
			return false
		}
		for name, typ := range t.Fields {
			if otherTyp, ok := otherRecord.Fields[name]; !ok || !typ.Equals(otherTyp) {
				return false
			}
		}
		return true
	}

	// Empty record equals Unit, but non-empty records don't equal Unit
	if _, ok := other.(*UnitType); ok {
		return false
	}

	return false
}

// InterfaceType represents an interface type
type InterfaceType struct {
	Name    string
	Methods map[string]*FunctionType // method name -> function type
}

func (t *InterfaceType) String() string {
	return t.Name
}

func (t *InterfaceType) Equals(other Type) bool {
	if otherInterface, ok := other.(*InterfaceType); ok {
		return t.Name == otherInterface.Name
	}
	return false
}

// UnionType represents a union of types (A | B | C)
type UnionType struct {
	Types []Type // The types being unioned
}

func (t *UnionType) String() string {
	var out string
	for i, typ := range t.Types {
		if i > 0 {
			out += " | "
		}
		out += typ.String()
	}
	return out
}

func (t *UnionType) Equals(other Type) bool {
	if otherUnion, ok := other.(*UnionType); ok {
		if len(t.Types) != len(otherUnion.Types) {
			return false
		}
		// Check that all types are present (order doesn't matter for equality)
		// Use structural equality (Equals) instead of string-based comparison
		// to avoid non-determinism from map iteration in RecordType.String()
		used := make([]bool, len(otherUnion.Types))
		for _, typ := range t.Types {
			matched := false
			for j, otherTyp := range otherUnion.Types {
				if !used[j] && typ.Equals(otherTyp) {
					used[j] = true
					matched = true
					break
				}
			}
			if !matched {
				return false
			}
		}
		return true
	}
	return false
}

// IntersectionType represents an intersection of types (A & B & C)
type IntersectionType struct {
	Types []Type // The types being intersected
}

func (t *IntersectionType) String() string {
	var out string
	for i, typ := range t.Types {
		if i > 0 {
			out += " & "
		}
		out += typ.String()
	}
	return out
}

func (t *IntersectionType) Equals(other Type) bool {
	if otherIntersection, ok := other.(*IntersectionType); ok {
		if len(t.Types) != len(otherIntersection.Types) {
			return false
		}
		// Check that all types are present (order doesn't matter for equality)
		// Use structural equality (Equals) instead of string-based comparison
		// to avoid non-determinism from map iteration in RecordType.String()
		used := make([]bool, len(otherIntersection.Types))
		for _, typ := range t.Types {
			matched := false
			for j, otherTyp := range otherIntersection.Types {
				if !used[j] && typ.Equals(otherTyp) {
					used[j] = true
					matched = true
					break
				}
			}
			if !matched {
				return false
			}
		}
		return true
	}
	return false
}

// FieldAccessorType is the zero-storage callable denoted by .field.
type FieldAccessorType struct{ Field string }

func (t *FieldAccessorType) String() string { return "." + t.Field }
func (t *FieldAccessorType) Equals(other Type) bool {
	o, ok := other.(*FieldAccessorType)
	return ok && t.Field == o.Field
}

// FunctionType represents a function type
type FunctionType struct {
	Parameters []Type
	ReturnType Type
	// Variadic marks a Go-style trailing parameter: the last Parameters
	// entry is the []element view the body sees; calls supply at least
	// len(Parameters)-1 arguments and each trailing argument checks against
	// the element type.
	Variadic bool
}

func (t *FunctionType) String() string {
	var out string
	out += "fn("
	for i, param := range t.Parameters {
		if i > 0 {
			out += ", "
		}
		out += param.String()
	}
	out += fmt.Sprintf(") -> %s", t.ReturnType.String())
	return out
}

func (t *FunctionType) Equals(other Type) bool {
	if otherFunc, ok := other.(*FunctionType); ok {
		if len(t.Parameters) != len(otherFunc.Parameters) {
			return false
		}
		if !t.ReturnType.Equals(otherFunc.ReturnType) {
			return false
		}
		for i, param := range t.Parameters {
			if !param.Equals(otherFunc.Parameters[i]) {
				return false
			}
		}
		return true
	}
	return false
}

// TypeChecker performs type checking on AST nodes
type TypeChecker struct {
	// Module-system facts (typechecker/modules.go): opaque types by internal
	// name and the loaded package paths.
	opaqueTypes             map[string]string
	packagePaths            map[string]bool
	sealedOpaque            map[string]map[string]bool
	abstractTypes           map[string]string
	adtPayloadTypes         map[string]map[string]Type
	monomorphicTransactions [][]Substitution
	diagnostics             *diagnostic.DiagnosticCollector
	env                     *TypeEnvironment
	adtTypes                map[string]*object.ADTType // ADT type definitions
	intSize                 int                        // Platform size for int/uint (default: 64)
	ptrSize                 int                        // Platform size for ptr/uptr (default: 64)
	// checkedExterns marks extern bindings already validated, so the
	// predeclare pass and the statement pass never double-report.
	checkedExterns map[*ast.FunctionStatement]bool
	// Monomorphization records (typechecker/mono.go): the concrete
	// generic-ADT instantiations the program uses and the instantiation
	// each variant expression / match scrutinee was checked against.
	adtInstantiations  map[string]Instantiation
	variantResolutions map[string]string
	matchResolutions   map[string]string
	// recordTemplates holds generic record declarations (Ring[T, N: u32]);
	// instantiations are cached by mangled name.
	recordTemplates          map[string]*ast.ADTType
	recordInstantiationCache map[string]*RecordType
	// tagSchemas holds declared tag schemas (json: tag = { name: string }) —
	// the closed namespace field tags check against (typechecker/tags.go).
	tagSchemas map[string]*RecordType
	// boolFacts remembers, per Bool binding, the extent facts of the
	// condition assigned to it (typechecker/extents.go).
	boolFacts map[string][]extentFact
	// arithmeticTypes records the fixed-width result type of each arithmetic
	// expression (position-keyed), so the backend emits the total helper.
	arithmeticTypes map[string]string
	// predeclaredGlobals names package-level bindings registered before any
	// body is checked, so functions may mention globals declared later in
	// the file; the defining declaration consumes its entry.
	predeclaredGlobals map[string]bool
	// shiftWidths records the operand width of each shift expression
	// (position-keyed), consumed by the backend's checked-shift emission.
	shiftWidths map[string]int
	// Generic function templates and their monomorphized instantiations
	// (typechecker/genericfn.go).
	globalEnv *TypeEnvironment
	// globalOwners maps each package-level declaration to the package that
	// declares it ("" for the root), so the no-shadowing rule is checked
	// against the declaring package's scope (docs/spec/83-modules.md section 7).
	globalOwners map[string]string
	// externFunctions names the extern bindings (docs/spec/92-ffi.md section 2.3),
	// whose calls may carry boundary spans (section 2.5).
	externFunctions            map[string]bool
	layoutQueries              map[string]LayoutQuery
	checkingSpecialization     bool
	extentFacts                []extentFact
	provenIndices              map[string]bool
	asmBackedFunctions         map[string]bool
	functionTemplates          map[string]*ast.FunctionStatement
	functionInstantiations     map[string]*ast.FunctionStatement
	functionInstantiationOrder []string
	// rowFunctionTemplates marks source functions whose extensible-record
	// parameters are representation-polymorphic. They share the ordinary
	// function monomorphizer after rowfn.go replaces each open parameter
	// with a private synthetic type parameter.
	rowFunctionTemplates            map[string]bool
	functionTemplateRowRequirements map[string]map[string]*RecordType
}

// Env returns the type environment (for use by borrow checker)
func (tc *TypeChecker) Env() *TypeEnvironment {
	return tc.env
}

// TypeEnvironment stores type information for variables
// In HM-style inference, we store TypeSchemes (polymorphic types) for let-bound variables
type TypeEnvironment struct {
	store      map[string]*TypeScheme // Store schemes, not monomorphic types
	outer      *TypeEnvironment
	borrowInfo *borrowTypeInfo
}

func NewTypeEnvironment() *TypeEnvironment {
	return &TypeEnvironment{
		store: make(map[string]*TypeScheme),
		outer: nil,
	}
}

func NewEnclosedTypeEnvironment(outer *TypeEnvironment) *TypeEnvironment {
	env := NewTypeEnvironment()
	env.outer = outer
	return env
}

// Get retrieves a type scheme from the environment
func (e *TypeEnvironment) Get(name string) (*TypeScheme, bool) {
	scheme, ok := e.store[name]
	if !ok && e.outer != nil {
		scheme, ok = e.outer.Get(name)
	}
	return scheme, ok
}

// GetType retrieves a type (for backward compatibility during migration)
// This instantiates the scheme if it exists
func (e *TypeEnvironment) GetType(name string) (Type, bool) {
	scheme, ok := e.Get(name)
	if !ok {
		return nil, false
	}
	// For now, return the underlying type (will be improved with proper instantiation)
	if scheme == nil {
		return nil, false
	}
	return scheme.Type, true
}

// Set stores a type scheme in the environment
func (e *TypeEnvironment) Set(name string, scheme *TypeScheme) {
	e.store[name] = scheme
}

// SetType stores a monomorphic type as a scheme (for backward compatibility)
func (e *TypeEnvironment) SetType(name string, typ Type) {
	// Convert monomorphic type to a scheme with no quantified variables
	e.store[name] = &TypeScheme{
		TypeVars:    []string{},
		Constraints: []Constraint{},
		Type:        typ,
	}
}

func New(env *object.Environment) *TypeChecker {
	return NewWithPlatformSizes(env, 64, 64) // Default to 64-bit
}

func NewWithPlatformSizes(env *object.Environment, intSize, ptrSize int) *TypeChecker {
	tc := &TypeChecker{
		diagnostics:     diagnostic.NewDiagnosticCollector(),
		env:             NewTypeEnvironment(),
		adtTypes:        env.GetAllADTTypes(),
		adtPayloadTypes: make(map[string]map[string]Type),
		intSize:         intSize,
		ptrSize:         ptrSize,
		checkedExterns:  make(map[*ast.FunctionStatement]bool),
	}
	// Add builtin type aliases
	tc.env.borrowInfo = &borrowTypeInfo{
		payloads:     tc.adtPayloadTypes,
		adts:         tc.adtTypes,
		expressions:  make(map[ast.Expression]Type),
		declarations: make(map[*ast.VariableDeclaration]Type),
	}
	tc.addBuiltinTypeAliases()
	return tc
}

// SetIntSize sets the platform size for int/uint types
func (tc *TypeChecker) SetIntSize(size int) {
	if size == 32 || size == 64 {
		tc.intSize = size
	}
}

// GetIntSize returns the platform size for int/uint types
func (tc *TypeChecker) GetIntSize() int {
	return tc.intSize
}

// SetPtrSize sets the platform size for ptr/uptr types
func (tc *TypeChecker) SetPtrSize(size int) {
	if size == 32 || size == 64 {
		tc.ptrSize = size
	}
}

// GetPtrSize returns the platform size for ptr/uptr types
func (tc *TypeChecker) GetPtrSize() int {
	return tc.ptrSize
}

// addBuiltinTypeAliases adds builtin type aliases to the type environment
func (tc *TypeChecker) addBuiltinTypeAliases() {
	// byte is an alias for u8
	tc.env.SetType("byte", &PrimitiveType{Name: "u8"})
}

// Errors returns errors as strings for backward compatibility
func (tc *TypeChecker) Errors() []string {
	errors := []string{}
	for _, d := range tc.diagnostics.Errors() {
		errors = append(errors, d.Message)
	}
	return errors
}

// Diagnostics returns all diagnostics
func (tc *TypeChecker) Diagnostics() []*diagnostic.Diagnostic {
	return tc.diagnostics.Diagnostics()
}

// AddDiagnostic adds a diagnostic to the typechecker
func (tc *TypeChecker) AddDiagnostic(d *diagnostic.Diagnostic) {
	tc.diagnostics.AddDiagnostic(d)
}

func (tc *TypeChecker) ClearErrors() {
	tc.diagnostics.Clear()
}

// addError creates and adds a diagnostic error
// If node is provided, uses its position; otherwise creates a diagnostic with zero range
func (tc *TypeChecker) addError(node ast.Node, format string, args ...interface{}) {
	message := fmt.Sprintf("[type error] "+format, args...)
	var d *diagnostic.Diagnostic
	if node != nil {
		d = diagnostic.NewDiagnosticFromNode(node, "typechecker", message)
	} else {
		// Fallback: create diagnostic with zero range
		d = diagnostic.NewDiagnostic(
			lsp.Range{
				Start: lsp.Position{Line: 0, Character: 0},
				End:   lsp.Position{Line: 0, Character: 0},
			},
			"typechecker",
			message,
		)
	}
	tc.diagnostics.AddDiagnostic(d)
}

// CheckProgram type checks a program
func typeParamsConstrained(params []*ast.TypeParameter) bool {
	for _, param := range params {
		if param != nil && param.Constraint != nil && !isConstParameter(param) {
			return true
		}
	}
	return false
}

// constParameterKinds are the integer kinds a const parameter may declare
// (docs/spec/20-types.md section 11.0): `N: u32` is a value parameter, not
// an interface constraint.
var constParameterKinds = map[string]bool{
	"u8": true, "u16": true, "u32": true, "u64": true,
	"i8": true, "i16": true, "i32": true, "i64": true,
	"int": true, "uint": true, "ptr": true, "uptr": true, "byte": true, "rune": true,
}

// isConstParameter reports whether a type parameter declares an integer
// kind and so ranges over integer constants.
func isConstParameter(param *ast.TypeParameter) bool {
	if param == nil || param.Constraint == nil {
		return false
	}
	kind, isIdent := param.Constraint.(*ast.Identifier)
	return isIdent && constParameterKinds[kind.Value]
}

// constParameterKind returns the declared integer kind of a const parameter.
func constParameterKind(param *ast.TypeParameter) string {
	if kind, isIdent := param.Constraint.(*ast.Identifier); isIdent {
		return kind.Value
	}
	return ""
}

func (tc *TypeChecker) CheckProgram(program *ast.Program) {
	// Resolve declared types before caching function signatures. Otherwise a
	// span of a named record can retain an unresolved type variable.
	for _, stmt := range program.Statements {
		switch stmt.(type) {
		case *ast.ADTType, *ast.TagDeclaration:
			tc.checkStatement(stmt)
		}
	}
	// Fresh abstract types of sealed imports take their identity from the
	// declarations just resolved (typechecker/modules.go).
	tc.registerAbstractTypes()
	// The global scope is the closure of top-level declarations; template
	// instantiations check against it, never a caller's local scope.
	tc.globalEnv = tc.env
	tc.recordGlobalOwners(program)
	// Pre-declare top-level non-generic function signatures so functions can
	// reference one another regardless of declaration order (mutual
	// recursion included); each signature is finalized when its declaration
	// is checked.
	for _, stmt := range program.Statements {
		if fn, ok := stmt.(*ast.FunctionStatement); ok {
			tc.predeclareFunctionSignature(fn)
			if len(fn.TypeParams) > 0 && fn.Receiver == nil && !typeParamsConstrained(fn.TypeParams) {
				if tc.functionTemplates == nil {
					tc.functionTemplates = make(map[string]*ast.FunctionStatement)
				}
				tc.functionTemplates[fn.Name.Value] = fn
			}
		}
	}
	tc.resolvePredeclaredFunctionBarriers(program)
	// Package scope is order-independent for annotated globals: register
	// their declared types now so a body checked earlier may name them.
	tc.predeclaredGlobals = make(map[string]bool)
	for _, stmt := range program.Statements {
		decl, isDecl := stmt.(*ast.VariableDeclaration)
		if !isDecl || decl.Name == nil || decl.Type == nil {
			continue
		}
		if _, exists := tc.env.Get(decl.Name.Value); exists {
			continue // the full check reports the duplicate
		}
		if varType := tc.parseTypeExpression(decl.Type); varType != nil {
			tc.env.SetType(decl.Name.Value, varType)
			tc.predeclaredGlobals[decl.Name.Value] = true
		}
	}
	for _, stmt := range program.Statements {
		switch stmt.(type) {
		case *ast.ADTType, *ast.TagDeclaration:
			continue
		}
		// Top-level bindings are static storage: constant initializers only
		// (typechecker/globals.go).
		if decl, isDecl := stmt.(*ast.VariableDeclaration); isDecl {
			tc.checkGlobalInitializer(decl)
		}
		tc.checkStatement(stmt)
	}

	// Generic function templates are replaced by their monomorphized
	// instantiations, so the borrow checker, discipline analysis, lowering,
	// and codegen see only ordinary functions — every safety gate runs on
	// every instantiation (typechecker/genericfn.go).
	if len(tc.functionTemplates) > 0 {
		kept := make([]ast.Statement, 0, len(program.Statements)+len(tc.functionInstantiationOrder))
		for _, stmt := range program.Statements {
			if fn, isFn := stmt.(*ast.FunctionStatement); isFn && fn.Name != nil {
				_, isTemplate := tc.functionTemplates[fn.Name.Value]
				if isTemplate && (len(fn.TypeParams) > 0 || tc.rowFunctionTemplates[fn.Name.Value]) {
					continue
				}
			}
			kept = append(kept, stmt)
		}
		for _, specialized := range tc.InstantiatedFunctions() {
			kept = append(kept, specialized)
		}
		program.Statements = kept
	}
}

// recordGlobalOwners notes, for every package-level function and binding,
// the package that declares it (docs/spec/83-modules.md section 7: the root
// package is spelled "").
func (tc *TypeChecker) recordGlobalOwners(program *ast.Program) {
	tc.globalOwners = make(map[string]string)
	for _, stmt := range program.Statements {
		switch s := stmt.(type) {
		case *ast.FunctionStatement:
			if s.Name != nil {
				tc.globalOwners[s.Name.Value] = tc.packageOf(s.Name.Token)
			}
		case *ast.VariableDeclaration:
			if s.Name != nil {
				tc.globalOwners[s.Name.Value] = tc.packageOf(s.Name.Token)
			}
		}
	}
}

// shadowsVisibleBinding reports whether declaring name at tok would shadow
// a binding that is in scope at that declaration.
//
// The elaborated program is one flat tree (docs/spec/83-modules.md section
// 7): imported packages' declarations carry their mangled internal names,
// which no user identifier can spell, but the root package keeps its source
// names. Without this rule a root `pub rank` would make `rank: u32 = ...`
// illegal in every other package, the prelude included, so a package's
// legal local names would depend on which package happens to be the build
// root (ml finding F5). A package-level declaration of a *different*
// package is therefore not in scope for a local declaration in a non-root
// package. Root-package code keeps the whole rule: everything visible to
// the root is unqualified there, prelude exports included.
func (tc *TypeChecker) shadowsVisibleBinding(name string, tok token.Token) bool {
	if _, exists := tc.env.Get(name); !exists {
		return false
	}
	owner, isGlobal := tc.globalOwners[name]
	if !isGlobal || tc.globalEnv == nil {
		return true
	}
	// Only the package-level binding may be out of scope: a local of the
	// same name in an enclosing block still shadows.
	for env := tc.env; env != nil && env != tc.globalEnv; env = env.outer {
		if _, local := env.store[name]; local {
			return true
		}
	}
	declaring := tc.packageOf(tok)
	return declaring == "" || declaring == owner
}

// predeclareFunctionSignature registers a function's declared type before any
// body is checked. Generic functions and methods are skipped: their schemes
// depend on constraint machinery that runs during the full check.
func (tc *TypeChecker) predeclareFunctionSignature(fn *ast.FunctionStatement) {
	if fn == nil || fn.Name == nil || fn.Receiver != nil {
		return
	}
	if hasOpenRowParameters(fn) {
		tc.registerRowFunctionTemplate(fn)
		return
	}
	// Extern bindings are validated and registered by their own path
	// (docs/spec/92-ffi.md section 2.3), predeclared here so calls may
	// precede the binding in source order.
	if fn.ExternSymbol != "" {
		if !tc.checkedExterns[fn] {
			tc.checkedExterns[fn] = true
			tc.checkExternFunction(fn)
		}
		return
	}
	if _, exists := tc.env.Get(fn.Name.Value); exists {
		return
	}

	// Bind declared type parameters in an isolated signature environment so
	// generic callables participate in forward-reference summary resolution.
	typeVars := make([]string, 0, len(fn.TypeParams))
	constraints := make([]Constraint, 0, len(fn.TypeParams))
	for _, parameter := range fn.TypeParams {
		if parameter == nil || parameter.Name == nil {
			return // full check reports the malformed declaration
		}
		typeVars = append(typeVars, parameter.Name.Value)
		if parameter.Constraint != nil && !isConstParameter(parameter) {
			interfaces := tc.extractInterfacesFromConstraint(parameter.Constraint)
			if len(interfaces) > 0 {
				constraints = append(constraints, Constraint{
					Var:        parameter.Name.Value,
					Interfaces: interfaces,
				})
			}
		}
	}
	signatureEnv := NewEnclosedTypeEnvironment(tc.env)
	bindConstrainedTypeVars(signatureEnv, typeVars, constraints)

	paramTypes := make([]Type, 0, len(fn.Parameters))
	for _, param := range fn.Parameters {
		paramType := tc.parseTypeExpressionInEnv(param.Type, signatureEnv)
		if paramType == nil {
			return // full check reports the error with context
		}
		if param.Variadic {
			paramType = &ArrayType{Length: -1, IsSlice: true, ElementType: paramType}
		}
		paramTypes = append(paramTypes, paramType)
	}
	returnType := tc.parseTypeExpressionInEnv(fn.ReturnType, signatureEnv)
	if returnType == nil {
		returnType = &UnitType{}
	}
	isVariadic := len(fn.Parameters) > 0 && fn.Parameters[len(fn.Parameters)-1].Variadic
	tc.env.Set(fn.Name.Value, &TypeScheme{
		TypeVars:    typeVars,
		Constraints: constraints,
		Type: &FunctionType{
			Parameters: paramTypes,
			ReturnType: returnType,
			Variadic:   isVariadic,
		},
	})
}

// resolvePredeclaredFunctionBarriers computes transitive authority summaries
// for every function whose signature can be predeclared. Barriers
// only accumulate, so iteration terminates over the finite barrier bitset.
func (tc *TypeChecker) resolvePredeclaredFunctionBarriers(program *ast.Program) {
	if program == nil {
		return
	}
	// Methods are not ordinary forward-call bindings, but their authority
	// summaries must exist while function bodies containing selectors are
	// analyzed. Full method checking later replaces these placeholders.
	for _, statement := range program.Statements {
		fn, ok := statement.(*ast.FunctionStatement)
		if !ok || fn == nil || fn.Name == nil || fn.Receiver == nil {
			continue
		}
		if key := methodBarrierKey(fn); key != "" {
			if _, exists := tc.env.Get(key); !exists {
				if scheme := tc.predeclaredMethodBarrierScheme(fn); scheme != nil {
					tc.env.Set(key, scheme)
				}
			}
		}
	}
	for {
		changed := false
		for _, statement := range program.Statements {
			fn, ok := statement.(*ast.FunctionStatement)
			if !ok || fn == nil || fn.Name == nil {
				continue
			}
			key := fn.Name.Value
			if fn.Receiver != nil {
				key = methodBarrierKey(fn)
			}
			if key == "" {
				continue
			}
			scheme, ok := tc.env.Get(key)
			if !ok || scheme == nil {
				continue
			}
			factsEnv := NewEnclosedTypeEnvironment(tc.env)
			if signature, ok := scheme.Type.(*FunctionType); ok &&
				len(signature.Parameters) == len(fn.Parameters) {
				for i, parameter := range fn.Parameters {
					if parameter != nil && parameter.Name != nil {
						factsEnv.SetType(parameter.Name.Value, signature.Parameters[i])
					}
				}
			}
			if fn.Receiver != nil && fn.Receiver.Name != nil {
				if receiverName, ok := fn.Receiver.Type.(*ast.Identifier); ok {
					factsEnv.SetType(fn.Receiver.Name.Value, &ADTType{Name: receiverName.Value})
				}
			}
			facts := functionStatementCaptureFacts(fn, factsEnv)
			joined := scheme.GeneralizationBarriers | facts.Barriers
			if joined != scheme.GeneralizationBarriers {
				scheme.GeneralizationBarriers = joined
				changed = true
			}
		}
		if !changed {
			break
		}
	}

	// Forward callers run before the declaration's full check. Barred generic
	// schemes must therefore share one persistent substitution now; retaining
	// quantified TypeVars here would freshen every forward use independently.
	for _, statement := range program.Statements {
		fn, ok := statement.(*ast.FunctionStatement)
		if !ok || fn == nil || fn.Name == nil || fn.Receiver != nil {
			continue
		}
		scheme, ok := tc.env.Get(fn.Name.Value)
		if !ok || scheme == nil || scheme.GeneralizationBarriers == 0 ||
			len(scheme.TypeVars) == 0 || scheme.Monomorphic != nil {
			continue
		}
		wanted := make(map[string]bool, len(scheme.TypeVars))
		for _, name := range scheme.TypeVars {
			wanted[name] = true
		}
		variables := make([]*TypeVar, 0, len(scheme.TypeVars))
		for _, variable := range typeVarsIn(scheme.Type) {
			if wanted[variable.Name] {
				variables = append(variables, variable)
			}
		}
		monomorphic := makeMonomorphicSchemeFor(scheme.Type, scheme.Constraints, variables)
		monomorphic.GeneralizationBarriers = scheme.GeneralizationBarriers
		tc.env.Set(fn.Name.Value, monomorphic)
	}
}

func (tc *TypeChecker) predeclaredMethodBarrierScheme(fn *ast.FunctionStatement) *TypeScheme {
	typeVars := make([]string, 0, len(fn.TypeParams))
	constraints := make([]Constraint, 0, len(fn.TypeParams))
	for _, parameter := range fn.TypeParams {
		if parameter == nil || parameter.Name == nil {
			return nil
		}
		typeVars = append(typeVars, parameter.Name.Value)
		if parameter.Constraint != nil && !isConstParameter(parameter) {
			interfaces := tc.extractInterfacesFromConstraint(parameter.Constraint)
			if len(interfaces) > 0 {
				constraints = append(constraints, Constraint{
					Var: parameter.Name.Value, Interfaces: interfaces,
				})
			}
		}
	}
	signatureEnv := NewEnclosedTypeEnvironment(tc.env)
	bindConstrainedTypeVars(signatureEnv, typeVars, constraints)

	parameters := make([]Type, 0, len(fn.Parameters))
	for _, parameter := range fn.Parameters {
		if parameter == nil {
			return nil
		}
		typ := tc.parseTypeExpressionInEnv(parameter.Type, signatureEnv)
		if typ == nil {
			return nil
		}
		if parameter.Variadic {
			typ = &ArrayType{Length: -1, IsSlice: true, ElementType: typ}
		}
		parameters = append(parameters, typ)
	}
	result := tc.parseTypeExpressionInEnv(fn.ReturnType, signatureEnv)
	if result == nil {
		result = &UnitType{}
	}
	return &TypeScheme{
		TypeVars: typeVars, Constraints: constraints,
		Type: &FunctionType{
			Parameters: parameters,
			ReturnType: result,
			Variadic:   len(fn.Parameters) > 0 && fn.Parameters[len(fn.Parameters)-1].Variadic,
		},
	}
}

func methodBarrierKey(fn *ast.FunctionStatement) string {
	if fn == nil || fn.Name == nil || fn.Receiver == nil {
		return ""
	}
	receiver, ok := fn.Receiver.Type.(*ast.Identifier)
	if !ok || receiver.Value == "" {
		return ""
	}
	return receiver.Value + "::" + fn.Name.Value
}

// CheckExpression type checks a single expression and returns its type
// This is useful for REPL inspection commands like :typeof()
func (tc *TypeChecker) CheckExpression(expr ast.Expression) (result Type) {
	before := len(tc.Errors())
	tc.beginMonomorphicTransaction()
	defer func() {
		tc.finishMonomorphicTransaction(result != nil && len(tc.Errors()) == before)
	}()
	return tc.checkExpression(expr)
}

// ParseTypeExpression parses a type expression and returns its type
// This is useful for REPL inspection commands like :typeof() with type expressions
func (tc *TypeChecker) ParseTypeExpression(expr ast.Expression) Type {
	return tc.parseTypeExpression(expr)
}

// checkStatement type checks a statement
func (tc *TypeChecker) checkStatement(stmt ast.Statement) {
	before := len(tc.Errors())
	tc.beginMonomorphicTransaction()
	defer func() {
		tc.finishMonomorphicTransaction(len(tc.Errors()) == before)
	}()

	switch s := stmt.(type) {
	case *ast.VariableDeclaration:
		tc.checkVariableDeclaration(s)
	case *ast.AssignmentStatement:
		tc.checkAssignmentStatement(s)
	case *ast.IndexAssignmentStatement:
		tc.checkIndexAssignmentStatement(s)
	case *ast.FunctionStatement:
		tc.checkFunctionStatement(s)
	case *ast.ADTType:
		// ADT type definitions are already in the environment
		// Just verify they're well-formed
		tc.checkADTType(s)
	case *ast.InterfaceType:
		// Interface type definitions
		tc.checkInterfaceType(s)
	case *ast.ExpressionStatement:
		resultType := tc.checkExpression(s.Expression)
		if ContainsAtomicStorage(resultType) {
			tc.addError(s.Expression, "Atomic[T] is storage identity, not a value; use an atomic_load_* operation")
		}
		if s.Discard {
			// `_ = expr` exists to drop a result on purpose
			// (docs/spec/85-discipline.md section 6); discarding unit
			// says nothing and is rejected so the form stays meaningful.
			if _, isUnit := resultType.(*UnitType); isUnit {
				tc.addError(s.Expression, "discard of a unit value: `_ = expr` drops a non-unit result; write the expression alone")
			}
		}
	case *ast.WhileStatement:
		tc.checkWhileStatement(s)
	case *ast.IfStatement:
		tc.checkIfStatement(s)
	case *ast.UnsafeBlock:
		tc.checkUnsafeBlock(s)
	case *ast.PackageStatement:
		// Package statements don't need type checking
		// They're just metadata
	case *ast.ImportStatement:
		// Import statements don't need type checking
		// They're just metadata
	case *ast.TagDeclaration:
		tc.checkTagDeclaration(s)
	case *ast.BlockStatement:
		// Block statements are checked as part of function bodies, while loops, etc.
		tc.checkBlockStatement(s)
	case *ast.REPLCommand:
		// REPL commands are handled in the REPL itself, not in type checking
		// They don't need type checking
		return
	default:
		tc.addError(stmt, "unknown statement type: %T", stmt)
	}
}

// checkExpression type checks an expression and returns its type
// expectedType is optional - if provided, it's used for context-based type inference (e.g., for literals)
func (tc *TypeChecker) checkExpression(expr ast.Expression, expectedType ...Type) (result Type) {
	defer func() {
		if info := tc.env.borrowMetadata(); info != nil && expr != nil && result != nil {
			info.expressions[expr] = result
		}
	}()
	var expected Type
	if len(expectedType) > 0 {
		expected = expectedType[0]
	}

	switch e := expr.(type) {
	case *ast.IntegerLiteral:
		// Integer literals take the expected integer type from their context:
		// declarations, assignments, arguments, returns, indices, and the peer
		// operand of an arithmetic, comparison, or bitwise operator. A literal
		// that does not fit that type is an error rather than a silent
		// fallback to int, so `at + 1` has exactly the range and overflow
		// rules of `at + u32(1)`.
		if expected != nil {
			if primType, ok := expected.(*PrimitiveType); ok {
				if IsFloatName(primType.Name) {
					// An integer literal is not a float (docs/spec/20-types.md
					// section 11.3.2): the program spells `1.0`.
					tc.addError(e, "integer literal %d in floating-point context %s; spell it %d.0", e.Value, primType.Name, e.Value)
					return primType
				}
				if tc.literalFits(e, primType.Name) {
					return primType
				}
				if tc.isNumericType(primType) {
					tc.addError(e, "literal %s does not fit in type %s", e.Token.Literal, primType.Name)
					return primType
				}
				// Non-integer primitive context: fall through to default inference
			}
		}
		// No context: default to int (signed native word integer)
		// This matches the platform-dependent default integer type
		return &PrimitiveType{Name: "int"}
	case *ast.FloatLiteral:
		// Floating-point literals take the float type of their context and
		// are f64 without one (docs/spec/20-types.md section 11.3.2).
		return tc.checkFloatLiteral(e, expected)
	case *ast.StringLiteral:
		return &StringType{}
	case *ast.Boolean:
		return &BoolType{}
	case *ast.Identifier:
		return tc.checkIdentifier(e)
	case *ast.PrefixExpression:
		return tc.checkPrefixExpression(e, expected)
	case *ast.InfixExpression:
		return tc.checkInfixExpression(e, expected)
	case *ast.FunctionLiteral:
		return tc.checkFunctionLiteral(e)
	case *ast.FieldAccessorExpression:
		return tc.checkFieldAccessorExpression(e, expected)
	case *ast.InvocationExpression:
		return tc.checkInvocationExpression(e)
	case *ast.MatchExpression:
		return tc.checkMatchExpression(e, expected)
	case *ast.VariantExpression:
		return tc.checkVariantExpression(e, expected)
	case *ast.RecordLiteral:
		return tc.checkRecordLiteral(e, expected)
	case *ast.IndexExpression:
		return tc.checkIndexExpression(e)
	case *ast.SliceExpression:
		return tc.checkSliceExpression(e)
	case *ast.BlockExpression:
		return tc.checkBlockExpression(e.Block, expected)
	case *ast.ArrayLiteral:
		return tc.checkArrayLiteral(e, expected)
	case nil:
		// Nil expression - likely a parser error, but don't crash
		tc.addError(nil, "nil expression encountered (parser error)")
		return nil
	default:
		tc.addError(expr, "unknown expression type: %T", expr)
		return nil
	}
}

// checkFieldAccessorExpression specializes Elm-style .field when context
// supplies a concrete unary function type. The source construct remains
// structurally polymorphic; only its zero-storage backend representation is
// tied to the concrete record layout selected at this use site.
func (tc *TypeChecker) checkFieldAccessorExpression(expr *ast.FieldAccessorExpression, expected Type) Type {
	if expected == nil {
		return &FieldAccessorType{Field: expr.Field.Value}
	}
	fn, ok := expected.(*FunctionType)
	if !ok || fn.Variadic || len(fn.Parameters) != 1 {
		tc.addError(expr, "field accessor .%s requires a unary function context, got %s", expr.Field.Value, expected)
		return nil
	}
	record, ok := fn.Parameters[0].(*RecordType)
	if !ok {
		tc.addError(expr, "field accessor .%s requires a record parameter, got %s", expr.Field.Value, fn.Parameters[0])
		return nil
	}
	fieldType, found := record.Fields[expr.Field.Value]
	if !found {
		tc.addError(expr, "field %s not found in record type %s", expr.Field.Value, record)
		return nil
	}
	if record.Name == "" || !record.Struct {
		tc.addError(expr, "first-class field accessor .%s needs a concrete declared struct context", expr.Field.Value)
		return nil
	}
	// Function-pointer ABIs are invariant: even a value-level numeric
	// widening would give the helper a different C function type.
	if !fieldType.Equals(fn.ReturnType) {
		tc.addError(expr, "field accessor .%s returns %s, not %s", expr.Field.Value, fieldType, fn.ReturnType)
		return nil
	}
	expr.ResolvedRecord = record.Name
	return fn
}

// Helper functions for type checking specific expression types
func (tc *TypeChecker) checkIdentifier(ident *ast.Identifier) Type {
	scheme, ok := tc.env.Get(ident.Value)
	if !ok {
		// Unbound library names get the library explanation, not
		// "undefined variable" (a local named c still shadows normally).
		if CompilerKnownLibrary(ident.Value) {
			tc.addError(ident, "%s is a compiler-known library, not a value (docs/spec/92-ffi.md)", ident.Value)
			return nil
		}
	}
	if !ok {
		tc.addError(ident, "undefined variable: %s", ident.Value)
		return nil
	}
	// Instantiate the scheme to get a fresh type, then overlay equations staged
	// by enclosing transactions so sibling uses share one monomorphic view.
	unifier := NewUnifier()
	return tc.applyPendingMonomorphic(Instantiate(scheme, unifier))
}

func (tc *TypeChecker) checkPrefixExpression(expr *ast.PrefixExpression, expectedType ...Type) Type {
	var expected Type
	if len(expectedType) > 0 {
		expected = expectedType[0]
	}
	// A negated literal is one constant: range-check the negated value against
	// the expected integer type so `x: i8 = -128` types as i8 and `at + -1`
	// with at: u32 is rejected as a literal that does not fit.
	if expr.Operator == "-" {
		if lit, isLiteral := expr.Right.(*ast.IntegerLiteral); isLiteral {
			if prim, ok := expected.(*PrimitiveType); ok && tc.isNumericType(prim) {
				if !lit.Wide && tc.literalFitsInType(-lit.Value, prim.Name) {
					return prim
				}
				tc.addError(expr, "literal -%s does not fit in type %s", lit.Token.Literal, prim.Name)
				return prim
			}
		}
	}
	var operandExpected Type
	if prim, ok := expected.(*PrimitiveType); ok && (tc.isNumericType(prim) || IsFloatName(prim.Name)) {
		// Negation keeps a signed type and complement keeps an unsigned type, so
		// the operand shares the expected type in both well-typed cases.
		operandExpected = prim
	}
	rightType := tc.checkExpression(expr.Right, operandExpected)
	if rightType == nil {
		return nil
	}
	if ContainsAtomicStorage(rightType) {
		tc.addError(expr.Right, "Atomic[T] cannot be used with prefix operators; load the cell explicitly")
		return nil
	}

	switch expr.Operator {
	case "!":
		if !rightType.Equals(&BoolType{}) {
			tc.addError(expr, "operator ! requires bool, got %s", rightType)
			return nil
		}
		return &BoolType{}
	case "^":
		// Bitwise complement (Go-style unary ^), unsigned-only.
		if prim, ok := rightType.(*PrimitiveType); ok && prim.Name[0] == 'u' {
			return rightType
		}
		tc.addError(expr, "operator ^ (complement) requires an unsigned fixed-width operand, got %s", rightType)
		return nil
	case "-":
		// Negation is total in the operand's own width: two's-complement
		// negation mod 2^N for signed and unsigned alike (docs/spec/20-types.md
		// section 11.1). No implicit move between signednesses: `-x` with
		// x: u32 is a u32, and `i32_bits_u32(x)` is the explicit route.
		if prim, ok := rightType.(*PrimitiveType); ok && tc.isNumericType(prim) {
			return tc.recordNegation(expr, prim)
		}
		if prim, ok := rightType.(*PrimitiveType); ok && IsFloatName(prim.Name) {
			// Negation flips the sign bit, including of NaN and zero
			// (docs/spec/20-types.md section 11.3.5); the backend's plain
			// unary minus is exactly that.
			return prim
		}
		tc.addError(expr, "operator - requires a numeric type, got %s", rightType)
		return nil
	default:
		tc.addError(expr, "unknown prefix operator: %s", expr.Operator)
		return nil
	}
}

func (tc *TypeChecker) checkInfixExpression(expr *ast.InfixExpression, expectedType ...Type) Type {
	var expected Type
	if len(expectedType) > 0 {
		expected = expectedType[0]
	}

	// Operands infer through the operator. For arithmetic and bitwise
	// operators the outer expected type flows into both operands, and for
	// every numeric operator the typed operand types a literal-only peer, in
	// either order: `at + 1`, `2 * at`, `1 < at`, `at * 2 + 1`, and
	// `hcr & 0x19` need no literal annotations and keep the precise type.
	bitwise := expr.Operator == "&" || expr.Operator == "|" || expr.Operator == "^" ||
		expr.Operator == "<<" || expr.Operator == ">>"
	arithmetic := expr.Operator == "+" || expr.Operator == "-" || expr.Operator == "*" ||
		expr.Operator == "/" || expr.Operator == "%"
	var operandExpected Type
	if (arithmetic || bitwise) && expected != nil && (tc.isNumericType(expected) || tc.isFloatType(expected)) {
		operandExpected = expected
	}
	peerContext := func(typ Type) Type {
		if typ != nil && (tc.isNumericType(typ) || tc.isFloatType(typ)) {
			return typ
		}
		return operandExpected
	}
	var leftType, rightType Type
	if IsLiteralOnlyExpression(expr.Left) && !IsLiteralOnlyExpression(expr.Right) {
		rightType = tc.checkExpression(expr.Right, operandExpected)
		leftType = tc.checkExpression(expr.Left, peerContext(rightType))
	} else {
		leftType = tc.checkExpression(expr.Left, operandExpected)
		// The right operand of && runs only when the left held, so it sees
		// the facts the left establishes (typechecker/extents.go); no
		// expression can reassign a local in between.
		var guard int
		if expr.Operator == "&&" {
			guard = tc.enterFactScope(expr.Left)
		}
		rightType = tc.checkExpression(expr.Right, peerContext(leftType))
		if expr.Operator == "&&" {
			tc.popExtentFacts(guard)
		}
	}
	if leftType == nil || rightType == nil {
		return nil
	}
	if ContainsAtomicStorage(leftType) || ContainsAtomicStorage(rightType) {
		tc.addError(expr, "Atomic[T] cells cannot participate in ordinary operators; use explicit atomic_load_*/store_*/fetch_add_* operations")
		return nil
	}

	switch expr.Operator {
	case "+":
		// Addition: numeric + numeric, or string + string
		if leftType.Equals(&StringType{}) && rightType.Equals(&StringType{}) {
			return &StringType{}
		}
		if tc.isFloatType(leftType) || tc.isFloatType(rightType) {
			return tc.checkFloatArithmetic(expr, leftType, rightType)
		}
		if tc.isNumericType(leftType) && tc.isNumericType(rightType) {
			return tc.recordArithmetic(expr, tc.promoteNumericTypes(expr, leftType, rightType))
		}
		tc.addError(expr, "operator + requires numeric types or strings, got %s and %s", leftType, rightType)
		return nil
	case "-", "*", "/", "%":
		if tc.isFloatType(leftType) || tc.isFloatType(rightType) {
			return tc.checkFloatArithmetic(expr, leftType, rightType)
		}
		// Arithmetic operators require numeric types
		if !tc.isNumericType(leftType) || !tc.isNumericType(rightType) {
			tc.addError(expr, "operator %s requires numeric types, got %s and %s", expr.Operator, leftType, rightType)
			return nil
		}
		return tc.recordArithmetic(expr, tc.promoteNumericTypes(expr, leftType, rightType))
	case "==", "!=":
		if tc.isFloatType(leftType) || tc.isFloatType(rightType) {
			return tc.checkFloatComparison(expr, leftType, rightType)
		}
		// Equality on machine integers follows the arithmetic rule: one
		// signedness, widths promote; otherwise operands must be compatible.
		if tc.isNumericType(leftType) && tc.isNumericType(rightType) {
			// Recorded so the interpreter compares in the operands' width
			// and signedness, as the compiled comparison does.
			if tc.recordArithmetic(expr, tc.promoteNumericTypes(expr, leftType, rightType)) == nil {
				return nil
			}
			return &BoolType{}
		}
		if !tc.areCompatibleTypes(leftType, rightType) {
			tc.addError(expr, "operator %s requires compatible types, got %s and %s", expr.Operator, leftType, rightType)
			return nil
		}
		return &BoolType{}
	case "&&", "||":
		// Short-circuit Boolean connectives (docs/spec/10-syntax.md): both
		// operands are Bool; the right operand evaluates only when needed.
		bool_ := &BoolType{}
		if !leftType.Equals(bool_) || !rightType.Equals(bool_) {
			tc.addError(expr, "operator %s requires Bool operands, got %s and %s", expr.Operator, leftType, rightType)
			return nil
		}
		return bool_
	case "&", "|", "^", "<<", ">>":
		// Bitwise operators are unsigned-only and same-width — MISRA-style:
		// no signed bitwise, no C promotion rules, no mixed widths
		// (docs/spec/10-syntax.md §3b). Shifts with a constant count are
		// statically bounds-checked; variable counts trap at runtime when
		// the count reaches the operand width (never-UB).
		leftPrim, leftIsPrim := leftType.(*PrimitiveType)
		rightPrim, rightIsPrim := rightType.(*PrimitiveType)
		if !leftIsPrim || !rightIsPrim || leftPrim.Name[0] != 'u' || rightPrim.Name[0] != 'u' {
			tc.addError(expr, "operator %s requires unsigned fixed-width operands, got %s and %s (bitwise on signed values is a modeling smell: convert explicitly)", expr.Operator, leftType, rightType)
			return nil
		}
		if leftPrim.Name != rightPrim.Name {
			tc.addError(expr, "operator %s requires same-width operands, got %s and %s (no implicit promotion)", expr.Operator, leftType, rightType)
			return nil
		}
		if expr.Operator == "<<" || expr.Operator == ">>" {
			width := tc.getBitWidth(leftPrim.Name)
			if lit, isLit := expr.Right.(*ast.IntegerLiteral); isLit {
				if lit.Value < 0 || lit.Value >= int64(width) {
					tc.addError(expr, "shift count %d out of range for %s (width %d)", lit.Value, leftPrim.Name, width)
					return nil
				}
			}
			tc.recordShiftWidth(expr, width)
		}
		return leftType
	case "<", ">", "<=", ">=":
		if tc.isFloatType(leftType) || tc.isFloatType(rightType) {
			return tc.checkFloatComparison(expr, leftType, rightType)
		}
		// Ordering compares machine integers of one signedness; widths
		// promote as in arithmetic, mixed signedness is rejected.
		if !tc.isNumericType(leftType) || !tc.isNumericType(rightType) {
			tc.addError(expr, "operator %s requires numeric types, got %s and %s", expr.Operator, leftType, rightType)
			return nil
		}
		if tc.recordArithmetic(expr, tc.promoteNumericTypes(expr, leftType, rightType)) == nil {
			return nil
		}
		return &BoolType{}
	default:
		tc.addError(expr, "unknown infix operator: %s", expr.Operator)
		return nil
	}
}

func (tc *TypeChecker) isNumericType(typ Type) bool {
	if prim, ok := typ.(*PrimitiveType); ok {
		return prim.Name[0] == 'i' || prim.Name[0] == 'u'
	}
	return false
}

// IsLiteralOnlyExpression reports whether an expression is built only from
// integer literals, unary signs, arithmetic, and bitwise operators, so its
// type comes entirely from context rather than from any typed operand.
func IsLiteralOnlyExpression(expr ast.Expression) bool {
	switch e := expr.(type) {
	case *ast.IntegerLiteral, *ast.FloatLiteral:
		return true
	case *ast.PrefixExpression:
		return (e.Operator == "-" || e.Operator == "+") && IsLiteralOnlyExpression(e.Right)
	case *ast.InfixExpression:
		switch e.Operator {
		case "+", "-", "*", "/", "%", "&", "|", "^", "<<", ">>":
			return IsLiteralOnlyExpression(e.Left) && IsLiteralOnlyExpression(e.Right)
		}
	}
	return false
}

// promoteNumericTypes returns the wider of two numeric types
// Implements widening conversions: u8 -> u16 -> u32 -> u64, i8 -> i16 -> i32 -> i64
// No implicit conversion between signed and unsigned
func (tc *TypeChecker) promoteNumericTypes(node ast.Node, left, right Type) Type {
	leftPrim, leftOk := left.(*PrimitiveType)
	rightPrim, rightOk := right.(*PrimitiveType)

	if !leftOk || !rightOk {
		return left // Fallback
	}

	// If types are the same, return that type
	if leftPrim.Name == rightPrim.Name {
		return left
	}

	// Check if both are signed or both are unsigned
	leftIsSigned := leftPrim.Name[0] == 'i'
	rightIsSigned := rightPrim.Name[0] == 'i'

	// No implicit conversion between signed and unsigned
	if leftIsSigned != rightIsSigned {
		tc.addError(node, "cannot mix signed and unsigned types: %s and %s", left, right)
		return left
	}

	// Get bit widths
	leftWidth := tc.getBitWidth(leftPrim.Name)
	rightWidth := tc.getBitWidth(rightPrim.Name)

	// Return the wider type
	if leftWidth >= rightWidth {
		return left
	}
	return right
}

// getBitWidth returns the bit width of a primitive type
func (tc *TypeChecker) getBitWidth(typeName string) int {
	switch typeName {
	case "i8", "u8":
		return 8
	case "i16", "u16":
		return 16
	case "i32", "u32":
		return 32
	case "i64", "u64":
		return 64
	default:
		return 0
	}
}

// areCompatibleTypes checks if two types are compatible for equality/comparison
func (tc *TypeChecker) areCompatibleTypes(left, right Type) bool {
	// Same types are always compatible
	if left.Equals(right) {
		return true
	}

	// Numeric types can be compared (with coercion); floats only with floats
	if tc.isNumericType(left) && tc.isNumericType(right) {
		return true
	}
	if tc.isFloatType(left) && tc.isFloatType(right) {
		return true
	}

	// Strings are compatible with strings
	if left.Equals(&StringType{}) && right.Equals(&StringType{}) {
		return true
	}

	// ADT types with the same name are compatible
	if leftADT, ok := left.(*ADTType); ok {
		if rightADT, ok := right.(*ADTType); ok {
			return leftADT.Name == rightADT.Name
		}
	}

	return false
}

// checkBorrowBuiltin types view(&owner) -> []T and span(&owner) -> [*]T.
func (tc *TypeChecker) checkBorrowBuiltin(name string, expr *ast.InvocationExpression) Type {
	if len(expr.Arguments) != 1 {
		tc.addError(expr, "%s expects exactly one argument: &owner of an owned array", name)
		return nil
	}
	prefix, ok := expr.Arguments[0].(*ast.PrefixExpression)
	if !ok || prefix.Operator != "&" {
		tc.addError(expr.Arguments[0], "%s argument must be &owner of an owned array", name)
		return nil
	}
	ownerType := tc.checkExpression(prefix.Right)
	if ownerType == nil {
		return nil
	}
	arrType, ok := ownerType.(*ArrayType)
	if !ok || arrType.IsSlice || arrType.IsSpan || arrType.Length < 0 {
		tc.addError(prefix.Right, "%s requires an owned array [N]T, got %s", name, ownerType)
		return nil
	}
	return &ArrayType{
		Length:      -1,
		IsSlice:     name == "view",
		IsSpan:      name == "span",
		ElementType: arrType.ElementType,
	}
}

// checkSubsliceBuiltin types subslice(v, start, len): the derived borrow has
// the source's view/span type.
func (tc *TypeChecker) checkSubsliceBuiltin(expr *ast.InvocationExpression) Type {
	if len(expr.Arguments) != 3 {
		tc.addError(expr, "subslice expects exactly three arguments (view/span, start, len)")
		return nil
	}
	srcType := tc.checkExpression(expr.Arguments[0])
	if srcType == nil {
		return nil
	}
	arrType, ok := srcType.(*ArrayType)
	if !ok || (!arrType.IsSlice && !arrType.IsSpan) {
		tc.addError(expr.Arguments[0], "subslice first argument must be a view or span, got %s", srcType)
		return nil
	}
	for _, bound := range expr.Arguments[1:] {
		boundType := tc.checkExpression(bound, &PrimitiveType{Name: "int"})
		if boundType == nil {
			continue
		}
		if prim, ok := boundType.(*PrimitiveType); !ok || !tc.isNumericType(prim) {
			tc.addError(bound, "subslice bounds must be integers, got %s", boundType)
		}
	}
	return srcType
}

func (tc *TypeChecker) checkFieldAccessorInvocation(field string, expr *ast.InvocationExpression) Type {
	if len(expr.Arguments) != 1 {
		tc.addError(expr, "field accessor .%s expects exactly one record argument", field)
		return nil
	}
	argType := tc.checkExpression(expr.Arguments[0])
	if record, ok := argType.(*RecordType); ok {
		if result, found := record.Fields[field]; found {
			return result
		}
		tc.addError(expr, "field %s not found in record type %s", field, record)
		return nil
	}
	if typeVar, ok := argType.(*TypeVar); ok {
		if result, guaranteed := tc.constrainedFieldType(typeVar, field); guaranteed {
			return result
		}
		tc.addError(expr, "field %s is not guaranteed by constraints on type parameter %s", field, typeVar.Name)
		return nil
	}
	if argType != nil {
		tc.addError(expr, "field accessor .%s requires a record, got %s", field, argType)
	}
	return nil
}

func (tc *TypeChecker) checkFunctionLiteral(fn *ast.FunctionLiteral) Type {
	// Capture discipline (docs/spec/60-effects-allocation.md section 10):
	// capturing closures need explicitly justified environment storage,
	// which has no surface yet — reject rather than silently drop or
	// heap-promote the environment.
	tc.checkClosureCaptures(fn)

	// Create new environment for function parameters
	funcEnv := NewEnclosedTypeEnvironment(tc.env)

	// Type check parameters (for anonymous functions, infer from usage)
	// For now, assume they're all i32 if we can't infer
	// Note: Type inference for anonymous function parameters is limited
	// Parameters default to i32 if types cannot be inferred from context
	paramTypes := []Type{}
	for _, param := range fn.Arguments {
		// Default to i32 for now (type inference would be better)
		paramType := &PrimitiveType{Name: "i32"}
		paramTypes = append(paramTypes, paramType)
		// Store as a monomorphic scheme
		funcEnv.SetType(param.Value, paramType)
	}

	// Save current environment and switch to function environment
	oldEnv := tc.env
	tc.env = funcEnv

	// Type check function body (BlockStatement - check last expression)
	returnType := tc.checkBlockExpression(fn.Body)
	if returnType == nil {
		returnType = &UnitType{}
	}

	// Restore environment
	tc.env = oldEnv

	return &FunctionType{
		Parameters: paramTypes,
		ReturnType: returnType,
	}
}

func (tc *TypeChecker) checkInvocationExpression(expr *ast.InvocationExpression) (result Type) {
	beforeInvocation := len(tc.Errors())
	tc.beginMonomorphicTransaction()
	defer func() {
		tc.finishMonomorphicTransaction(result != nil && len(tc.Errors()) == beforeInvocation)
	}()
	if accessor, ok := expr.Function.(*ast.FieldAccessorExpression); ok {
		return tc.checkFieldAccessorInvocation(accessor.Field.Value, expr)
	}
	if ident, ok := expr.Function.(*ast.Identifier); ok {
		if atomicType, recognized := tc.checkAtomicInvocation(ident.Value, expr); recognized {
			return atomicType
		}
		if coerced, recognized := tc.checkAbstractCoercion(ident.Value, expr); recognized {
			return coerced
		}
	}
	// Compiler-known library calls: c conversions, misplaced c.extern, and
	// arm64 instruction functions (docs/spec/92-ffi.md).
	if libraryType, isLibrary := tc.checkLibraryInvocation(expr); isLibrary {
		return libraryType
	}

	// Layout introspection, static_assert, address_of
	// (typechecker/layout_builtins.go).
	if layoutType, isLayout := tc.resolveLayoutBuiltin(expr); isLayout {
		return layoutType
	}

	// Generic function calls monomorphize here: the call site is rewritten
	// to the specialized name and re-typed (typechecker/genericfn.go).
	if genericType, isGeneric := tc.resolveGenericInvocation(expr); isGeneric {
		return genericType
	}

	// Check if this is a primitive type constructor: u32(x), u64(y), etc.
	if ident, ok := expr.Function.(*ast.Identifier); ok {
		if constructorType := tc.checkPrimitiveConstructor(ident.Value, expr.Arguments); constructorType != nil {
			return constructorType
		}
		// Check if this is a narrowing function: u8_trunc_u32(x), u8_checked_u32(x), etc.
		if narrowingType := tc.checkNarrowingFunction(ident.Value, expr.Arguments); narrowingType != nil {
			return narrowingType
		}
		// Floating-point intrinsics (docs/spec/20-types.md section 11.3.5):
		// fma, sqrt, min, max, is_nan, ... unless a program binding shadows
		// the name.
		if floatType := tc.checkFloatIntrinsic(ident.Value, expr); floatType != nil {
			return floatType
		}
		// Check if this is a Castable constructor: string(x), byte(x), etc.
		if castableType := tc.checkCastableConstructor(ident.Value, expr.Arguments); castableType != nil {
			return castableType
		}
	}

	// Check if this is a builtin reinterpret cast: view_as[U](src) or span_as[U](src)
	if ident, ok := expr.Function.(*ast.Identifier); ok {
		if ident.Value == "view_as" || ident.Value == "span_as" {
			return tc.checkReinterpretCast(ident.Value, expr.Arguments)
		}
		// Borrow-creation builtins (docs/spec/50-borrowing.md): view(&owner)
		// and span(&owner) borrow an owned array; subslice derives from an
		// existing view/span. The borrow checker enforces the aliasing laws;
		// here we type the access paths.
		if ident.Value == "view" || ident.Value == "span" {
			return tc.checkBorrowBuiltin(ident.Value, expr)
		}
		if ident.Value == "subslice" {
			return tc.checkSubsliceBuiltin(expr)
		}
		if ident.Value == "str_from_utf8" || ident.Value == "str_bytes" {
			return tc.checkStringViewBuiltin(ident.Value, expr)
		}
		// len: element/byte count of a container. v1 representation counts
		// are u32, matching the view/span structs.
		if ident.Value == "len" {
			if len(expr.Arguments) != 1 {
				tc.addError(expr, "len expects exactly one argument")
				return &PrimitiveType{Name: "u32"}
			}
			argType := tc.checkExpression(expr.Arguments[0])
			switch argType.(type) {
			case *ArrayType, *StringType, nil:
			default:
				tc.addError(expr.Arguments[0], "len requires an array, view, span, or string, got %s", argType)
			}
			return &PrimitiveType{Name: "u32"}
		}
		// is_valid_utf8 (docs/spec/70-strings.md): zero-allocation byte
		// validation against the well-formed sequences of Oak.Utf8Validity.
		if ident.Value == "is_valid_utf8" {
			if len(expr.Arguments) != 1 {
				tc.addError(expr, "is_valid_utf8 expects exactly one []u8 argument")
				return &BoolType{}
			}
			argType := tc.checkExpression(expr.Arguments[0])
			arr, ok := argType.(*ArrayType)
			elemOK := ok && arr.IsSlice
			if elemOK {
				prim, isPrim := arr.ElementType.(*PrimitiveType)
				elemOK = isPrim && normalizePrimitiveName(prim.Name) == "u8"
			}
			if argType != nil && !elemOK {
				tc.addError(expr.Arguments[0], "is_valid_utf8 requires a []u8 view, got %s", argType)
			}
			return &BoolType{}
		}
		// assert (docs/spec/85-discipline.md section 5): a Bool condition,
		// compiled in and never elided by build mode.
		if ident.Value == "assert" {
			if len(expr.Arguments) != 1 {
				tc.addError(expr, "assert expects exactly one Bool argument")
				return &UnitType{}
			}
			condType := tc.checkExpression(expr.Arguments[0])
			if condType != nil && !condType.Equals(&BoolType{}) {
				tc.addError(expr.Arguments[0], "assert condition must be Bool, got %s", condType)
			}
			return &UnitType{}
		}
	}

	// Check if this is a method call: recv.method(args)
	if indexExpr, ok := expr.Function.(*ast.IndexExpression); ok {
		if methodName, ok := indexExpr.Index.(*ast.Identifier); ok {
			// This is a method call
			return tc.checkMethodCall(indexExpr.Left, methodName.Value, expr.Arguments)
		}
	}

	// Regular function call
	// Get the function identifier to retrieve the scheme for constraint checking
	var funcScheme *TypeScheme
	if funcIdent, ok := expr.Function.(*ast.Identifier); ok {
		if scheme, ok := tc.env.Get(funcIdent.Value); ok {
			funcScheme = scheme
		}
	}

	beforeCall := len(tc.Errors())
	funcType := tc.checkExpression(expr.Function)
	if funcType == nil {
		return nil
	}

	if accessor, ok := funcType.(*FieldAccessorType); ok {
		return tc.checkFieldAccessorInvocation(accessor.Field, expr)
	}
	fnType, ok := funcType.(*FunctionType)
	if !ok {
		tc.addError(expr, "attempting to call non-function type: %s", funcType)
		return nil
	}

	// Boundary spans (docs/spec/92-ffi.md section 2.5): in a call to an
	// extern binding, c.span_of(v) / c.span_mut_of(s) stands for two
	// consecutive parameters (c.Ptr, c.Size). paramPos maps each argument to
	// the parameter position it starts at; effectiveArgs counts positions.
	isExtern := false
	if funcIdent, ok := expr.Function.(*ast.Identifier); ok {
		isExtern = tc.externFunctions[funcIdent.Value]
	}
	paramPos := make([]int, len(expr.Arguments))
	effectiveArgs := 0
	spansValid := true
	for i, arg := range expr.Arguments {
		paramPos[i] = effectiveArgs
		if member, operand, isSpan := tc.BoundarySpanArgument(arg); isSpan {
			if !isExtern {
				d := tc.addTypeDiagnostic(arg, CodeExternOutsideDefinition,
					fmt.Sprintf("c.%s is only an argument to an extern binding", member))
				d.AddNote("a boundary span yields a c.Ptr, c.Size pair for the duration of one foreign call; Oak functions take the view or span itself (docs/spec/92-ffi.md section 2.5.2)")
				return nil
			}
			// The pair rule is checked before the arity, so a misplaced span
			// is reported as such rather than as a count mismatch.
			if !tc.checkBoundarySpan(arg, member, operand, fnType.Parameters, effectiveArgs) {
				spansValid = false
			}
			effectiveArgs += 2
			continue
		}
		effectiveArgs++
	}
	if !spansValid {
		return nil
	}

	// Check argument count. A variadic function requires at least its fixed
	// arity; every trailing argument checks against the element type.
	fixedParams := len(fnType.Parameters)
	var variadicElement Type
	if fnType.Variadic {
		fixedParams--
		if viewType, ok := fnType.Parameters[fixedParams].(*ArrayType); ok {
			variadicElement = viewType.ElementType
		}
		if len(expr.Arguments) < fixedParams {
			tc.addError(expr, "function expects at least %d arguments, got %d", fixedParams, len(expr.Arguments))
			return nil
		}
	} else if effectiveArgs != len(fnType.Parameters) {
		tc.addError(expr, "function expects %d arguments, got %d", len(fnType.Parameters), effectiveArgs)
		return nil
	}

	// Infer one substitution while checking arguments. Generic parameters are
	// unified first; ordinary Oak assignability remains the fallback for concrete
	// types (for example, numeric widening).
	argTypes := make([]Type, len(expr.Arguments))
	bindings := make(Substitution)
	unifier := NewUnifier()
	validCall := len(tc.Errors()) == beforeCall
	beforeArguments := len(tc.Errors())
	for i, arg := range expr.Arguments {
		if _, _, isSpan := tc.BoundarySpanArgument(arg); isSpan {
			// Validated in the pre-pass above; it stands for the pair.
			argTypes[i] = &CType{Name: "Ptr"}
			continue
		}
		pos := paramPos[i]
		var parameterType Type
		if fnType.Variadic && pos >= fixedParams {
			if variadicElement == nil {
				continue
			}
			parameterType = variadicElement
		} else {
			parameterType = fnType.Parameters[pos]
		}
		expectedType := bindings.Apply(parameterType)
		argType := tc.checkExpression(arg, expectedType)
		if argType == nil {
			validCall = false
			continue
		}
		argTypes[i] = argType

		if argSub := unifier.Unify(expectedType, argType); argSub != nil {
			merged, compatible := mergeMonomorphicBindings([]Substitution{bindings, argSub})
			if !compatible {
				validCall = false
				tc.addError(expr.Arguments[i], "argument %d conflicts with an earlier type specialization", i+1)
				continue
			}
			bindings = merged
			continue
		}

		if !tc.isAssignable(argType, expectedType) {
			validCall = false
			tc.addError(expr.Arguments[i], "argument %d: expected %s, got %s", i+1, expectedType, argType)
		}
	}
	if len(tc.Errors()) != beforeArguments {
		validCall = false
	}

	if funcScheme != nil && len(funcScheme.Constraints) > 0 {
		before := len(tc.Errors())
		tc.checkFunctionConstraintBindings(funcScheme, bindings, expr)
		if len(tc.Errors()) != before {
			validCall = false
		}
	}

	// A satisfied call to a constrained generic specializes it for emission
	// and is rewritten to the instantiation (typechecker/genericfn.go).
	if validCall && funcScheme != nil && len(funcScheme.Constraints) > 0 {
		if funcIdent, ok := expr.Function.(*ast.Identifier); ok {
			if template, isTemplate := tc.functionTemplates[funcIdent.Value]; isTemplate {
				tc.specializeConstrainedCall(expr, template, funcScheme, bindings)
			}
		}
	}

	// Commit every tagged variable participating in this direct or indirect
	// use only after the entire call, including constraints, succeeds.
	if validCall {
		tc.stageMonomorphicBindings(bindings)
	}

	return bindings.Apply(fnType.ReturnType)
}

// checkReinterpretCast checks view_as[U](src: []T) and span_as[U](src: [*]T) calls
// These functions reinterpret views/spans to different element types
func (tc *TypeChecker) checkReinterpretCast(funcName string, args []ast.Expression) Type {
	// For now, we'll use a simplified syntax: view_as[U](src) or span_as[U](src)
	// In the future, we might support explicit generic syntax
	if len(args) != 1 {
		// Use first argument if available, otherwise nil
		var node ast.Node
		if len(args) > 0 {
			node = args[0]
		}
		tc.addError(node, "%s expects exactly one argument", funcName)
		return nil
	}

	srcType := tc.checkExpression(args[0])
	if srcType == nil {
		return nil
	}

	// Check if source is a view or span
	if arrayType, ok := srcType.(*ArrayType); ok {
		if funcName == "view_as" && arrayType.IsSlice {
			// view_as[U]([]T) -> []U
			// For now, without generics, we'll require type annotation at call site
			// The actual target type will be inferred from context or explicit annotation
			// Return a placeholder type that indicates reinterpret is needed
			// In practice, the target type would come from the generic parameter [U]
			tc.addError(args[0], "view_as requires generic type parameter (e.g., view_as[u32](src)). Generic syntax not yet implemented. Use type annotation: v: []u32 = view_as(src)")
			// Return a placeholder - in full implementation, this would be []U where U is from generic param
			return &ArrayType{
				ElementType: arrayType.ElementType, // Placeholder - would be U in full implementation
				Length:      -1,
				IsSlice:     true,
				IsSpan:      false,
			}
		} else if funcName == "span_as" && arrayType.IsSpan {
			// span_as[U]([*]T) -> [*]U
			tc.addError(args[0], "span_as requires generic type parameter (e.g., span_as[u32](src)). Generic syntax not yet implemented. Use type annotation: s: [*]u32 = span_as(src)")
			// Return a placeholder
			return &ArrayType{
				ElementType: arrayType.ElementType, // Placeholder - would be U in full implementation
				Length:      -1,
				IsSlice:     false,
				IsSpan:      true,
			}
		} else {
			tc.addError(args[0], "%s type mismatch: view_as requires []T, span_as requires [*]T, got %s", funcName, srcType)
			return nil
		}
	} else {
		tc.addError(args[0], "%s requires a view ([]T) or span ([*]T), got %s", funcName, srcType)
		return nil
	}
}

// checkPrimitiveConstructor checks if an invocation is a primitive type constructor
// (e.g., u32(x), u64(y)) and returns the target type if valid
func (tc *TypeChecker) checkPrimitiveConstructor(typeName string, args []ast.Expression) Type {
	// Check if it's a primitive type name (including aliases and platform types)
	primitiveTypes := map[string]bool{
		"u8": true, "u16": true, "u32": true, "u64": true,
		"i8": true, "i16": true, "i32": true, "i64": true,
		"int": true, "uint": true, "ptr": true, "uptr": true, // platform types
		"byte": true,              // alias of u8
		"rune": true,              // alias of u32 (docs/spec/70-strings.md section 9)
		"f32":  true, "f64": true, // floating point (docs/spec/20-types.md section 11.3)
	}
	if !primitiveTypes[typeName] {
		return nil // Not a primitive constructor
	}

	// Constructors take exactly one argument
	if len(args) != 1 {
		var node ast.Node
		if len(args) > 0 {
			node = args[0]
		}
		tc.addError(node, "primitive constructor %s expects 1 argument, got %d", typeName, len(args))
		return nil
	}

	if IsFloatName(typeName) {
		return tc.checkFloatConstructor(typeName, args[0])
	}

	// Check if argument is an integer literal (untyped)
	if intLit, ok := args[0].(*ast.IntegerLiteral); ok {
		// Check if literal fits in target type
		if !tc.literalFits(intLit, typeName) {
			tc.addError(intLit, "literal %s does not fit in type %s", intLit.Token.Literal, typeName)
			return nil
		}
		// Literal fits - return target type
		return &PrimitiveType{Name: typeName}
	}

	// Check argument type for typed values
	argType := tc.checkExpression(args[0])
	if argType == nil {
		return nil
	}

	// A matching c.* value converts back explicitly along the invertible
	// rows of the conversion table (docs/spec/92-ffi.md section 2.2).
	if cConversionToOak(typeName, argType) {
		return &PrimitiveType{Name: typeName}
	}

	// Untyped arithmetic over literals infers against the constructed type
	// (the same expected-type threading literals get elsewhere).
	if argPrimitive, isPrimitive := argType.(*PrimitiveType); isPrimitive && argPrimitive.Name == "int" {
		rechecked := tc.checkExpression(args[0], &PrimitiveType{Name: typeName})
		if rechecked != nil {
			argType = rechecked
		}
	}

	// Check if argument is a primitive type
	argPrim, ok := argType.(*PrimitiveType)
	if !ok {
		tc.addError(args[0], "primitive constructor %s requires a primitive integer argument, got %s", typeName, argType)
		return nil
	}

	// Normalize aliases for widening check
	normalizedTarget := typeName
	if typeName == "byte" {
		normalizedTarget = "u8"
	} else if typeName == "rune" {
		normalizedTarget = "u32"
	}

	// Check if widening is valid (same signedness, source is narrower or equal)
	if !tc.isValidWidening(argPrim.Name, normalizedTarget) {
		tc.addError(args[0], "cannot widen %s to %s (must be same signedness and source must be narrower or equal); narrowing is explicit: %s_trunc_%s(x) wraps, %s_saturating_%s(x) clamps, %s_checked_%s(x) returns Result, and %s_bits_%s(x) reinterprets same-width bits",
			argPrim.Name, typeName, typeName, argPrim.Name, typeName, argPrim.Name, typeName, argPrim.Name, typeName, argPrim.Name)
		return nil
	}

	// Return the target type (preserve alias name if used)
	return &PrimitiveType{Name: typeName}
}

// literalFits checks whether an integer literal node fits the given primitive
// type; a wide literal (above 2^63 - 1) fits only the 64-bit unsigned types.
func (tc *TypeChecker) literalFits(lit *ast.IntegerLiteral, typeName string) bool {
	if lit.Wide {
		switch typeName {
		case "u64":
			return true
		case "uint", "uptr":
			return tc.intSize == 64
		}
		return false
	}
	return tc.literalFitsInType(lit.Value, typeName)
}

// literalFitsInType checks if an integer literal value fits in the given primitive type
func (tc *TypeChecker) literalFitsInType(value int64, typeName string) bool {
	// Normalize aliases
	if typeName == "byte" {
		typeName = "u8"
	} else if typeName == "rune" {
		typeName = "u32"
	}
	switch typeName {
	case "u8":
		return value >= 0 && value <= 255
	case "u16":
		return value >= 0 && value <= 65535
	case "u32":
		return value >= 0 && value <= 4294967295
	case "u64":
		return value >= 0 // u64 can hold any non-negative int64
	case "i8":
		return value >= -128 && value <= 127
	case "i16":
		return value >= -32768 && value <= 32767
	case "i32":
		return value >= -2147483648 && value <= 2147483647
	case "i64":
		return true // i64 can hold any int64
	case "int", "ptr":
		// Platform-dependent signed types: can hold any int64
		// On 32-bit: int == i32, ptr == i32
		// On 64-bit: int == i64, ptr == i64
		return true
	case "uint", "uptr":
		// Platform-dependent unsigned types: can hold any non-negative int64
		// On 32-bit: uint == u32, uptr == u32
		// On 64-bit: uint == u64, uptr == u64
		return value >= 0
	default:
		return false
	}
}

// isValidWidening checks if widening from sourceType to targetType is valid
// Widening is valid if:
// - Both types have the same signedness (both signed or both unsigned)
// - Source type is narrower than or equal to target type
func (tc *TypeChecker) isValidWidening(sourceType, targetType string) bool {
	// Normalize aliases
	if sourceType == "byte" {
		sourceType = "u8"
	} else if sourceType == "rune" {
		sourceType = "u32"
	}
	if targetType == "byte" {
		targetType = "u8"
	} else if targetType == "rune" {
		targetType = "u32"
	}

	// A lossless cross-sign conversion is a valid explicit widening: an
	// unsigned source fits any strictly wider signed target.
	if !tc.isSignedType(sourceType) && tc.isSignedType(targetType) {
		return tc.getTypeWidth(sourceType) < tc.getTypeWidth(targetType)
	}

	// Check signedness using helper function
	sourceSigned := tc.isSignedType(sourceType)
	targetSigned := tc.isSignedType(targetType)
	if sourceSigned != targetSigned {
		return false
	}

	// Get widths
	sourceWidth := tc.getTypeWidth(sourceType)
	targetWidth := tc.getTypeWidth(targetType)

	// Source must be narrower than or equal to target
	return sourceWidth <= targetWidth
}

// getTypeWidth returns the bit width of a primitive type
// For platform types, assumes 64-bit platform (can be made configurable later)
func (tc *TypeChecker) getTypeWidth(typeName string) int {
	// Normalize aliases
	if typeName == "byte" {
		typeName = "u8"
	} else if typeName == "rune" {
		typeName = "u32"
	}
	switch typeName {
	case "u8", "i8":
		return 8
	case "u16", "i16":
		return 16
	case "u32", "i32":
		return 32
	case "u64", "i64":
		return 64
	case "int", "uint":
		// Platform types: use configured int size
		return tc.intSize
	case "ptr", "uptr":
		// Platform types: use configured ptr size
		return tc.ptrSize
	default:
		return 0
	}
}

// isSignedType checks if a type is signed
func (tc *TypeChecker) isSignedType(typeName string) bool {
	// Normalize aliases
	if typeName == "byte" {
		typeName = "u8"
	} else if typeName == "rune" {
		typeName = "u32"
	}
	// Fixed-width types
	if len(typeName) >= 2 && typeName[0] == 'i' {
		return true
	}
	if len(typeName) >= 2 && typeName[0] == 'u' {
		return false
	}
	// Platform types
	switch typeName {
	case "int", "ptr":
		return true
	case "uint", "uptr":
		return false
	}
	return false
}

// checkNarrowingFunction checks if an invocation is a narrowing function
// (e.g., u8_trunc_u32(x), u8_checked_u32(x), u8_saturating_u32(x))
// Pattern: {target}_{operation}_{source}
// Operations: trunc, checked, saturating
func (tc *TypeChecker) checkNarrowingFunction(funcName string, args []ast.Expression) Type {
	// Parse function name: target_operation_source
	// Examples: u8_trunc_u32, u16_checked_u64, i8_saturating_i32
	parts := splitNarrowingFunctionName(funcName)
	if parts == nil {
		return nil // Not a narrowing function
	}

	targetType := parts[0]
	operation := parts[1]
	sourceType := parts[2]

	// Validate that target and source are primitive types
	primitiveTypes := map[string]bool{
		"u8": true, "u16": true, "u32": true, "u64": true,
		"i8": true, "i16": true, "i32": true, "i64": true,
	}
	targetFloat, sourceFloat := IsFloatName(targetType), IsFloatName(sourceType)
	if (!primitiveTypes[targetType] && !targetFloat) || (!primitiveTypes[sourceType] && !sourceFloat) {
		return nil
	}

	// Validate operation. `bits` is the same-width cross-sign
	// reinterpretation (two's complement bit pattern, total): the explicit
	// path between u32 and i32 that widening/narrowing deliberately lack.
	// `round` belongs to the floating-point rows (section 11.3.4).
	validOperations := map[string]bool{
		"trunc":      true,
		"checked":    true,
		"saturating": true,
		"bits":       true,
		"round":      true,
	}
	if !validOperations[operation] {
		return nil
	}

	// Narrowing functions take exactly one argument
	if len(args) != 1 {
		var node ast.Node
		if len(args) > 0 {
			node = args[0]
		}
		tc.addError(node, "narrowing function %s expects 1 argument, got %d", funcName, len(args))
		return nil
	}

	if targetFloat || sourceFloat {
		return tc.checkFloatConversion(funcName, targetType, operation, sourceType, args[0])
	}
	if operation == "round" {
		tc.addError(args[0], "%s: round converts to a floating-point type; integers narrow with trunc, saturating, or checked", funcName)
		return nil
	}

	// Check the pair against the operation's own rule: narrowing ops need
	// a strictly wider same-signedness source; bits needs the same width
	// and opposite signedness.
	if operation == "bits" {
		sameWidth := tc.getTypeWidth(sourceType) == tc.getTypeWidth(targetType)
		crossSign := (sourceType[0] == 'i') != (targetType[0] == 'i')
		if !sameWidth || !crossSign {
			tc.addError(args[0], "invalid reinterpretation: %s_bits_%s requires the same width and opposite signedness", targetType, sourceType)
			return nil
		}
	} else if !tc.isValidNarrowing(sourceType, targetType) {
		tc.addError(args[0], "invalid narrowing: cannot narrow %s to %s (must be same signedness and source must be wider)", sourceType, targetType)
		return nil
	}

	// Check argument type matches source type, inferring untyped literals
	// against it.
	sourcePrim := &PrimitiveType{Name: sourceType}
	argType := tc.checkExpression(args[0], sourcePrim)
	if argType == nil {
		return nil
	}

	argPrim, ok := argType.(*PrimitiveType)
	if !ok || normalizePrimitiveName(argPrim.Name) != sourceType {
		tc.addError(args[0], "narrowing function %s expects argument of type %s, got %s", funcName, sourceType, argType)
		return nil
	}

	// Return type depends on operation
	if operation == "checked" {
		// Checked operations return Result[target, Overflow]
		// Create target type
		targetPrimType := &PrimitiveType{Name: targetType}

		// Create Overflow error type (ADT type)
		overflowType := &ADTType{Name: "Overflow"}

		// The backend monomorphizes this instantiation like any other
		// (typechecker/mono.go); usable once the program declares
		// Result[T, E] and Overflow.
		tc.recordADTInstantiation("Result", []Type{targetPrimType, overflowType})

		// Return Result[target, Overflow]
		return &GenericType{
			Name:     "Result",
			TypeArgs: []Type{targetPrimType, overflowType},
		}
	}

	// Trunc and saturating return the target type directly
	return &PrimitiveType{Name: targetType}
}

// checkCastableConstructor checks if an invocation is a Castable constructor
// (e.g., string(x), byte(x)) where x implements Castable[target]
// Castable[T]: interface = fn (self) into() -> T
func (tc *TypeChecker) checkCastableConstructor(typeName string, args []ast.Expression) Type {
	// Check if it's a type that supports Castable constructors
	castableTypes := map[string]bool{
		"string": true,
		"byte":   true, // byte is alias for u8
	}
	if !castableTypes[typeName] {
		return nil // Not a Castable constructor
	}

	// Constructors take exactly one argument
	if len(args) != 1 {
		var node ast.Node
		if len(args) > 0 {
			node = args[0]
		}
		tc.addError(node, "Castable constructor %s expects 1 argument, got %d", typeName, len(args))
		return nil
	}

	// Check argument type
	argType := tc.checkExpression(args[0])
	if argType == nil {
		return nil
	}

	// Determine target type
	var targetType Type
	if typeName == "string" {
		targetType = &StringType{}
	} else if typeName == "byte" {
		targetType = &PrimitiveType{Name: "u8"}
	} else {
		return nil
	}

	// Check if argument type implements Castable[targetType]
	// For now, we'll check if the type has an `into()` method that returns the target type
	// In a full implementation, we'd check for the Castable interface constraint
	if !tc.implementsCastable(argType, targetType) {
		tc.addError(args[0], "type %s does not implement Castable[%s] (missing into() method)", argType, typeName)
		return nil
	}

	return targetType
}

// implementsCastable checks if a type implements Castable[T]
// Castable[T]: interface = fn (self) into() -> T
func (tc *TypeChecker) implementsCastable(argType, targetType Type) bool {
	// String implements Castable[string] (identity conversion)
	if _, ok := argType.(*StringType); ok {
		if _, ok := targetType.(*StringType); ok {
			return true
		}
	}

	// Check if the argument type has an `into()` method that returns the target type
	// This is a structural check: the type must have a method `into()` -> targetType
	var typeName string
	switch t := argType.(type) {
	case *ADTType:
		typeName = t.Name
	case *PrimitiveType:
		// Primitive types don't have methods
		return false
	case *RecordType:
		// Record types don't have methods (yet)
		return false
	default:
		return false
	}

	// Look up the `into()` method on the argument type
	methodKey := fmt.Sprintf("%s::into", typeName)
	methodScheme, ok := tc.env.Get(methodKey)
	if !ok {
		// Method not found - type doesn't implement Castable
		return false
	}

	// Instantiate the method scheme to get the actual method type
	unifier := NewUnifier()
	methodType := Instantiate(methodScheme, unifier)
	fnType, ok := methodType.(*FunctionType)
	if !ok {
		// Method is not a function type - invalid
		return false
	}

	// Check that the method takes no arguments (just self) and returns targetType
	if len(fnType.Parameters) != 0 {
		// Method should take no arguments (self is implicit in method call)
		return false
	}

	// Check that return type matches target type
	return fnType.ReturnType.Equals(targetType)
}

// splitNarrowingFunctionName parses a narrowing function name into [target, operation, source]
// Returns nil if the name doesn't match the pattern
func splitNarrowingFunctionName(name string) []string {
	// Pattern: {target}_{operation}_{source}
	// Examples: u8_trunc_u32, u16_checked_u64, i8_saturating_i32

	// Find the last underscore (separates operation and source)
	lastUnderscore := -1
	for i := len(name) - 1; i >= 0; i-- {
		if name[i] == '_' {
			lastUnderscore = i
			break
		}
	}
	if lastUnderscore == -1 {
		return nil
	}

	source := name[lastUnderscore+1:]
	remaining := name[:lastUnderscore]

	// Find the first underscore (separates target and operation)
	firstUnderscore := -1
	for i := 0; i < len(remaining); i++ {
		if remaining[i] == '_' {
			firstUnderscore = i
			break
		}
	}
	if firstUnderscore == -1 {
		return nil
	}

	target := remaining[:firstUnderscore]
	operation := remaining[firstUnderscore+1:]

	return []string{target, operation, source}
}

// isValidNarrowing checks if narrowing from sourceType to targetType is valid
// Narrowing is valid if:
// - Both types have the same signedness (both signed or both unsigned)
// - Source type is wider than target type
func (tc *TypeChecker) isValidNarrowing(sourceType, targetType string) bool {
	// Check signedness
	sourceSigned := sourceType[0] == 'i'
	targetSigned := targetType[0] == 'i'
	if sourceSigned != targetSigned {
		return false
	}

	// Get widths
	sourceWidth := tc.getTypeWidth(sourceType)
	targetWidth := tc.getTypeWidth(targetType)

	// Source must be wider than target (not equal)
	return sourceWidth > targetWidth
}

// checkMethodCall type checks a method call: recv.method(args)
func (tc *TypeChecker) checkMethodCall(recvExpr ast.Expression, methodName string, args []ast.Expression) Type {
	// Check receiver type
	recvType := tc.checkExpression(recvExpr)
	if recvType == nil {
		return nil
	}

	// Determine receiver type name
	var receiverTypeName string
	if adtType, ok := recvType.(*ADTType); ok {
		receiverTypeName = adtType.Name
	} else {
		tc.addError(recvExpr, "method calls only supported for ADT types, got %s", recvType)
		return nil
	}

	// Look up method: TypeName::methodName
	methodKey := fmt.Sprintf("%s::%s", receiverTypeName, methodName)
	methodScheme, ok := tc.env.Get(methodKey)
	if !ok {
		tc.addError(recvExpr, "method %s not found for type %s", methodName, receiverTypeName)
		return nil
	}

	// Instantiate the method scheme
	unifier := NewUnifier()
	methodType := Instantiate(methodScheme, unifier)
	fnType, ok := methodType.(*FunctionType)
	if !ok {
		tc.addError(recvExpr, "method %s is not a function type", methodName)
		return nil
	}

	// Check argument count (method has receiver as first parameter, so args should match parameters)
	if len(args) != len(fnType.Parameters) {
		tc.addError(recvExpr, "method %s expects %d arguments, got %d", methodName, len(fnType.Parameters), len(args))
		return nil
	}

	// Check argument types
	for i, arg := range args {
		argType := tc.checkExpression(arg)
		if argType == nil {
			continue
		}
		expectedType := fnType.Parameters[i]
		if !tc.isAssignable(argType, expectedType) {
			tc.addError(arg, "method %s argument %d: expected %s, got %s", methodName, i+1, expectedType, argType)
		}
	}

	return fnType.ReturnType
}

func (tc *TypeChecker) checkIndexAssignmentStatement(stmt *ast.IndexAssignmentStatement) {
	if stmt == nil || stmt.Target == nil {
		return
	}
	seqType := tc.checkExpression(stmt.Target.Left)
	if seqType == nil {
		return
	}
	if arr, isArray := seqType.(*ArrayType); isArray && !stmt.Target.Dot {
		tc.recordIndexProof(stmt.Target, arr)
	}
	// Record field assignment: p.x = value (docs/spec/40-records.md).
	if stmt.Target.Dot {
		record, isRecord := seqType.(*RecordType)
		fieldIdent, isIdent := stmt.Target.Index.(*ast.Identifier)
		if !isRecord || !isIdent {
			tc.addError(stmt.Target.Left, "cannot assign a field of %s", seqType)
			return
		}
		fieldType, declared := record.Fields[fieldIdent.Value]
		if !declared {
			tc.addError(stmt.Target.Index, "field %s not found in %s", fieldIdent.Value, record.DisplayName())
			return
		}
		valueType := tc.checkExpression(stmt.Value, fieldType)
		if valueType != nil && !tc.isAssignable(valueType, fieldType) {
			tc.addError(stmt.Value, "cannot assign %s to field %s of type %s", valueType, fieldIdent.Value, fieldType)
		}
		return
	}

	arrType, ok := seqType.(*ArrayType)
	if !ok {
		tc.addError(stmt.Target.Left, "cannot index-assign into %s", seqType)
		return
	}
	if arrType.IsSlice {
		tc.addError(stmt.Target.Left, "cannot write through a read-only view []%s; use a span ([*]T) or the owner", arrType.ElementType)
		return
	}
	indexType := tc.checkExpression(stmt.Target.Index, &PrimitiveType{Name: "u32"})
	if indexType != nil {
		if prim, isPrim := indexType.(*PrimitiveType); !isPrim || !tc.isNumericType(prim) {
			tc.addError(stmt.Target.Index, "index must be an integer, got %s", indexType)
		}
	}
	valueType := tc.checkExpression(stmt.Value, arrType.ElementType)
	if valueType != nil && !tc.isAssignable(valueType, arrType.ElementType) {
		tc.addError(stmt.Value, "cannot assign %s to element type %s", valueType, arrType.ElementType)
	}
}

func (tc *TypeChecker) checkMatchExpression(expr *ast.MatchExpression, expectedType ...Type) Type {
	var expected Type
	if len(expectedType) > 0 {
		expected = expectedType[0]
	}
	scrutineeType := tc.checkExpression(expr.Scrutinee)
	if scrutineeType == nil {
		return nil
	}
	if ContainsAtomicStorage(scrutineeType) {
		tc.addError(expr.Scrutinee, "Atomic[T] cells cannot be matched as values; load the cell explicitly")
		return nil
	}
	// Record the scrutinee's concrete type for the backend
	// (typechecker/mono.go): matches over Option[i32] dispatch on the
	// monomorphized type; matches over binding locals resolve without
	// name scans.
	if name, _, args, isADT := adtInstantiation(scrutineeType); isADT {
		tc.recordMatchResolution(expr, name, args)
	}

	// Check that match expression has at least one arm
	if len(expr.Arms) == 0 {
		tc.addError(expr, "match expression must have at least one arm")
		return nil
	}

	analysis := tc.analyzeMatch(expr, scrutineeType)
	tc.emitMatchAnalysisDiagnostics(expr, analysis)

	// Type check only reachable arms and collect their result types.
	// Redundant or refinement-impossible arms are semantically never and
	// must not widen the result type or create cascaded body errors.
	armTypes := []Type{}
	armsBefore := tc.deadSnapshot()
	armsAfter := armsBefore
	for armIndex, arm := range expr.Arms {
		// Create a new scoped environment for this match arm to support type narrowing
		armEnv := NewEnclosedTypeEnvironment(tc.env)
		oldEnv := tc.env
		tc.env = armEnv

		// Type check pattern and get narrowed type
		patternType := tc.checkPattern(arm.Pattern, scrutineeType)
		if patternType == nil {
			tc.env = oldEnv
			continue
		}
		if armIndex < len(analysis.Arms) && !analysis.Arms[armIndex].Reachable {
			armTypes = append(armTypes, &NeverType{})
			tc.env = oldEnv
			continue
		}

		// Type narrowing: use lattice narrowing
		narrowedType := NarrowType(scrutineeType, arm.Pattern)

		// If pattern narrowed the type, bind it in the environment
		// This allows the arm body to use the narrowed type
		if narrowedVariant, ok := narrowedType.(*NarrowedADTVariantType); ok {
			// Store the narrowed variant type for potential use in the arm body
			// The scrutinee variable (if it's an identifier) would be narrowed
			if ident, ok := expr.Scrutinee.(*ast.Identifier); ok {
				tc.env.SetType(ident.Value, narrowedVariant)
			}
		}

		// Type check arm body expression with narrowed type context,
		// inferring literals against the expected result type.
		var armType Type
		// Arms are alternatives: each starts from the facts live before the
		// match, and the union of their kills applies afterwards.
		tc.restoreDead(armsBefore)
		armMark := tc.enterArmFacts(expr, arm)
		if expected != nil {
			armType = tc.checkExpression(arm.Body, expected)
		} else {
			armType = tc.checkExpression(arm.Body)
		}
		tc.popExtentFacts(armMark)
		armsAfter = unionDead(armsAfter, tc.deadSnapshot())
		if armType == nil {
			// Unreachable or error - use never type
			armType = &NeverType{}
		}
		armTypes = append(armTypes, armType)

		// Restore environment
		tc.env = oldEnv
	}

	// Compute join of all arm types (lattice-based)
	tc.restoreDead(armsAfter)
	returnType := Join(armTypes...)

	// Strict mode: if join is any and we didn't explicitly request any, it's an error
	// (This prevents accidental type widening)
	if _, isAny := returnType.(*AnyType); isAny {
		// Check if all non-never types are the same
		nonNeverTypes := []Type{}
		for _, at := range armTypes {
			if _, ok := at.(*NeverType); !ok {
				nonNeverTypes = append(nonNeverTypes, at)
			}
		}

		if len(nonNeverTypes) > 1 {
			// Multiple different types - this is an error in strict mode
			tc.addError(expr, "match expression has branches with incompatible types. Use explicit 'any' return type if intentional.")
		}
	}

	if returnType == nil {
		return &NeverType{} // No branches matched - unreachable
	}
	return returnType
}

func (tc *TypeChecker) checkPattern(pattern ast.Pattern, expectedType Type) Type {
	switch p := pattern.(type) {
	case *ast.WildcardPattern:
		return expectedType
	case *ast.BindingPattern:
		tc.env.SetType(p.Name.Value, expectedType)
		return expectedType
	case *ast.LiteralPattern:
		// Integer pattern literals infer from the scrutinee's type, exactly
		// like expression literals infer from their expected type.
		if intLit, ok := p.Value.(*ast.IntegerLiteral); ok {
			if prim, ok := expectedType.(*PrimitiveType); ok {
				if tc.literalFits(intLit, prim.Name) {
					return expectedType
				}
				tc.addError(p.Value, "pattern literal %d does not fit in scrutinee type %s", intLit.Value, expectedType)
				return nil
			}
		}
		litType := tc.checkExpression(p.Value)
		if litType == nil {
			return nil
		}
		if !litType.Equals(expectedType) {
			tc.addError(p.Value, "pattern literal type %s does not match expected type %s", litType, expectedType)
			return nil
		}
		return expectedType
	case *ast.VariantPattern:
		adtName, _, typeArgs, isADT := adtInstantiation(expectedType)
		if isADT {
			if p.TypeName != nil && p.TypeName.Value != adtName {
				tc.addError(p.TypeName, "pattern constructor %s.%s does not belong to scrutinee type %s", p.TypeName.Value, p.Variant.Value, adtName)
				return nil
			}
			adtDef, exists := tc.adtTypes[adtName]
			if !exists {
				tc.addError(p, "ADT type %s not found", adtName)
				return nil
			}
			if !tc.checkOpaqueProjection(p.Token, adtName, p, "match") {
				return nil
			}
			variant, found := tc.findADTVariant(adtName, p.Variant.Value)
			if !found {
				tc.addError(p, "variant %s not found in ADT %s", p.Variant.Value, adtName)
				return nil
			}
			bindings, _, reachable := tc.variantIndexBindings(adtDef, variant, typeArgs)
			if !reachable {
				bindings = map[string]Type{}
			}
			if p.Payload != nil {
				if variant.Payload == "" {
					tc.addError(p, "variant %s of ADT %s does not accept a payload", variant.Name, adtName)
					return nil
				}
				expectedPayload := tc.instantiatedVariantPayload(adtName, variant, bindings)
				if expectedPayload == nil || tc.checkPattern(p.Payload, expectedPayload) == nil {
					return nil
				}
			} else if variant.Payload != "" {
				tc.addError(p, "variant %s of ADT %s requires a payload of type %s", variant.Name, adtName, variant.Payload)
				return nil
			}
			return &NarrowedADTVariantType{ADTName: adtName, VariantName: variant.Name, TypeArgs: typeArgs}
		}

		// Literal-tag ADTs may still narrow primitive scrutinees.
		if tc.isNumericType(expectedType) || expectedType.Equals(&StringType{}) {
			for adtName, adtDef := range tc.adtTypes {
				for _, variant := range adtDef.Variants {
					if variant.Name == p.Variant.Value && variant.Literal != nil {
						litType := tc.getLiteralType(variant.Literal)
						if litType != nil && litType.Equals(expectedType) {
							return &NarrowedADTVariantType{ADTName: adtName, VariantName: variant.Name}
						}
					}
				}
			}
		}
		tc.addError(p, "variant pattern used on non-ADT type: %s", expectedType)
		return nil
	default:
		if node, ok := pattern.(ast.Node); ok {
			tc.addError(node, "unknown pattern type: %T", pattern)
		} else {
			tc.addError(nil, "unknown pattern type: %T", pattern)
		}
		return nil
	}
}

func (tc *TypeChecker) checkVariantExpression(expr *ast.VariantExpression, expected Type) Type {
	adtTypeName := ""
	if expr.TypeName != nil {
		adtTypeName = expr.TypeName.Value
	} else if name, _, _, ok := adtInstantiation(expected); ok {
		adtTypeName = name
	} else {
		for name, adtDef := range tc.adtTypes {
			for _, variant := range adtDef.Variants {
				if variant.Name == expr.Variant.Value {
					if adtTypeName != "" && adtTypeName != name {
						tc.addError(expr, "cannot infer ADT type for ambiguous variant .%s", expr.Variant.Value)
						return nil
					}
					adtTypeName = name
				}
			}
		}
	}
	if adtTypeName == "" {
		tc.addError(expr, "cannot infer ADT type for variant .%s", expr.Variant.Value)
		return nil
	}

	adtDef, ok := tc.adtTypes[adtTypeName]
	if !ok {
		tc.addError(expr, "ADT type %s not found", adtTypeName)
		return nil
	}
	if !tc.checkOpaqueProjection(expr.Token, adtTypeName, expr, "construct") {
		return nil
	}
	variant, found := tc.findADTVariant(adtTypeName, expr.Variant.Value)
	if !found {
		tc.addError(expr, "variant %s not found in ADT %s", expr.Variant.Value, adtTypeName)
		return nil
	}

	var bindings map[string]Type
	refinedExpected := expected
	if name, _, args, hasExpectedADT := adtInstantiation(expected); hasExpectedADT && name == adtTypeName {
		// Record the type this constructor was checked against
		// (typechecker/mono.go), so the backend calls the right
		// constructor without name guessing.
		tc.recordVariantResolution(expr, adtTypeName, args)
		var resultSubstitution Substitution
		var reachable bool
		bindings, resultSubstitution, reachable = tc.variantIndexBindings(adtDef, variant, args)
		if !reachable {
			d := tc.addTypeDiagnostic(expr, CodeGADTResultMismatch, "constructor result does not inhabit the expected indexed ADT")
			d.AddNote(fmt.Sprintf("%s.%s is declared to produce %s, but this context expects %s",
				adtTypeName, variant.Name, variantResultString(adtDef, variant), expected))
			d.AddHelp("choose a constructor whose declared result indices match the expected type")
			return nil
		}
		refinedExpected = resultSubstitution.Apply(expected)
	}

	if expr.Payload != nil {
		if variant.Payload == "" {
			tc.addError(expr, "variant %s of ADT %s does not accept a payload", variant.Name, adtTypeName)
			return nil
		}
		expectedPayload := tc.instantiatedVariantPayload(adtTypeName, variant, bindings)
		actualPayload := tc.checkExpression(expr.Payload, expectedPayload)
		if expectedPayload == nil || actualPayload == nil || !tc.isAssignable(actualPayload, expectedPayload) {
			tc.addError(expr.Payload, "variant %s payload: expected %s, got %s", variant.Name, expectedPayload, actualPayload)
			return nil
		}
	} else if variant.Payload != "" {
		tc.addError(expr, "variant %s of ADT %s requires a payload of type %s", variant.Name, adtTypeName, variant.Payload)
		return nil
	}

	return tc.variantResultType(adtDef, variant, refinedExpected)
}

func (tc *TypeChecker) checkRecordLiteral(expr *ast.RecordLiteral, expectedType ...Type) Type {
	if expr.Extension != nil {
		tc.addError(expr, "extensible record syntax is a type constraint, not a record value")
		return nil
	}
	// If this is a type-qualified literal (TypeName{ ... }), look up the type
	if expr.TypeName != nil {
		typeName := expr.TypeName.Value
		namedType, ok := tc.env.GetType(typeName)
		if !ok {
			tc.addError(expr.TypeName, "type %s not found", typeName)
			return nil
		}
		if !tc.checkOpaqueProjection(expr.Token, typeName, expr.TypeName, "construct") {
			return nil
		}
		// Convert the named type to a RecordType if possible
		// Record types defined as "Name: type = { ... }" are stored as RecordType in the environment
		// ADT types with a single record variant are also stored as RecordType
		if recordType, ok := namedType.(*RecordType); ok {
			// Direct record type
			expectedType = []Type{recordType}
		}
	}

	// If expected type is a RecordType, use it for context-based inference
	var expectedRecord *RecordType
	if len(expectedType) > 0 {
		if recType, ok := expectedType[0].(*RecordType); ok {
			expectedRecord = recType
		}
	}

	fields := make(map[string]Type)
	for name, fieldExpr := range expr.Fields {
		// Check if this looks like a type definition context
		// In type definitions, field expressions are type annotations (identifiers like u8, i32)
		// In value contexts, field expressions are values
		// If the field expression is an identifier and we have an expected type, try parsing as type first
		if ident, ok := fieldExpr.(*ast.Identifier); ok {
			// Check if it's a primitive type name
			primitiveTypes := map[string]bool{
				"i8": true, "i16": true, "i32": true, "i64": true,
				"u8": true, "u16": true, "u32": true, "u64": true,
				"f32": true, "f64": true,
				"string": true, "Bool": true, "byte": true, "()": true,
			}
			if primitiveTypes[ident.Value] {
				// This is a type annotation, not a value - parse as type
				fieldType := tc.parseTypeExpression(fieldExpr)
				if fieldType != nil {
					fields[name] = fieldType
					continue
				}
			}
		}

		// Use expected field type for context-based inference
		var expectedFieldType Type
		if expectedRecord != nil {
			if fieldType, ok := expectedRecord.Fields[name]; ok {
				expectedFieldType = fieldType
			}
		}
		// An owned-array field is initialized from an array literal; copying
		// an array binding into a record has no C lowering yet (by-value
		// arrays, roadmap item 4), so it is rejected instead of emitted.
		if arr, isArray := expectedFieldType.(*ArrayType); isArray && arr.Length >= 0 && !arr.IsSlice && !arr.IsSpan {
			if _, isLiteral := fieldExpr.(*ast.ArrayLiteral); !isLiteral {
				tc.addError(fieldExpr, "record field %s: an owned array field must be initialized from an array literal; copying an array binding into a record is not lowered yet (wrap the array in a record to pass it by value)", name)
				continue
			}
		}
		fieldType := tc.checkExpression(fieldExpr, expectedFieldType)
		if fieldType == nil {
			continue
		}
		// Check for duplicate field names
		if _, exists := fields[name]; exists {
			tc.addError(expr, "record literal: duplicate field name %s", name)
			continue
		}
		fields[name] = fieldType
	}

	// Against a declared record type, the literal must cover the fields
	// exactly: no unknown fields, no missing fields, each value at its
	// declared type. The literal's type is the declared type (nominal name
	// and declaration order flow to the backend).
	if expectedRecord != nil {
		valid := true
		unknown := make([]string, 0)
		for name := range fields {
			if _, declared := expectedRecord.Fields[name]; !declared {
				unknown = append(unknown, name)
			}
		}
		sort.Strings(unknown)
		for _, name := range unknown {
			tc.addError(expr, "record literal: %s has no field %s", expectedRecord.DisplayName(), name)
			valid = false
		}
		for _, name := range expectedRecord.orderedFieldNames() {
			declared := expectedRecord.Fields[name]
			given, present := fields[name]
			if !present {
				tc.addError(expr, "record literal: missing field %s of %s", name, expectedRecord.DisplayName())
				valid = false
				continue
			}
			if given != nil && !given.Equals(declared) {
				tc.addError(expr, "record literal: field %s expects %s, got %s", name, declared, given)
				valid = false
			}
		}
		if !valid {
			return nil
		}
		return expectedRecord
	}

	// Canonicalize empty record {} to Unit
	if len(fields) == 0 {
		return &UnitType{}
	}

	return &RecordType{Fields: fields}
}

func (tc *TypeChecker) checkIndexExpression(expr *ast.IndexExpression) Type {
	// Check if this is Type.Variant (ADT constructor) rather than field access
	// If left is an identifier (type name) and we have an ADT with that name, treat as variant
	// We check this BEFORE checking leftType because type names aren't in the value environment
	if leftIdent, ok := expr.Left.(*ast.Identifier); ok {
		adtTypeName := leftIdent.Value
		if adtDef, ok := tc.adtTypes[adtTypeName]; ok {
			if !tc.checkOpaqueProjection(expr.Token, adtTypeName, expr, "name a variant of") {
				return nil
			}
			// This is Type.Variant - convert to VariantExpression for checking
			if variantIdent, ok := expr.Index.(*ast.Identifier); ok {
				variantName := variantIdent.Value
				// Check if this variant exists in the ADT
				// adtDef is *object.ADTType, variants are []*object.ADTVariantDef
				for _, v := range adtDef.Variants {
					if v.Name == variantName {
						// Valid variant - return the ADT type
						return &ADTType{Name: adtTypeName}
					}
				}
				tc.addError(expr, "variant %s not found in ADT %s", variantName, adtTypeName)
				return nil
			}
		}
	}

	// Not an ADT constructor, check as normal index expression
	leftType := tc.checkExpression(expr.Left)
	if leftType == nil {
		return nil
	}
	if arr, isArray := leftType.(*ArrayType); isArray && !expr.Dot {
		tc.recordIndexProof(expr, arr)
	}

	// A constrained type variable exposes only fields guaranteed by its semantic
	// record-shape requirements, never fields that happen to exist on one caller.
	if typeVar, ok := leftType.(*TypeVar); ok {
		ident, isIdent := expr.Index.(*ast.Identifier)
		if !isIdent {
			tc.addError(expr, "generic record field access requires identifier, got %T", expr.Index)
			return nil
		}
		if fieldType, guaranteed := tc.constrainedFieldType(typeVar, ident.Value); guaranteed {
			return fieldType
		}
		tc.addError(expr, "field %s is not guaranteed by constraints on type parameter %s", ident.Value, typeVar.Name)
		return nil
	}

	// Handle record field access: record.field
	if recordType, ok := leftType.(*RecordType); ok {
		if recordType.Name != "" && !tc.checkOpaqueProjection(expr.Token, recordType.Name, expr, "read a field of") {
			return nil
		}
		if ident, ok := expr.Index.(*ast.Identifier); ok {
			fieldName := ident.Value
			if fieldType, ok := recordType.Fields[fieldName]; ok {
				return fieldType
			}
			tc.addError(expr, "field %s not found in record type %s", fieldName, recordType)
			return nil
		}
		tc.addError(expr, "record field access requires identifier, got %T", expr.Index)
		return nil
	}

	// Handle array indexing: array[index]
	if arrayType, ok := leftType.(*ArrayType); ok {
		indexType := tc.checkExpression(expr.Index, &PrimitiveType{Name: "u32"})
		if indexType == nil {
			return nil
		}
		// Index must be an integer type
		if !tc.isNumericType(indexType) {
			tc.addError(expr.Index, "array index must be numeric type, got %s", indexType)
			return nil
		}
		// Index should ideally be unsigned, but we allow any numeric for now
		// In the future, we could require u32 specifically for array indices
		return arrayType.ElementType
	}

	tc.addError(expr, "index expression not supported for type: %s", leftType)
	return nil
}

func (tc *TypeChecker) checkSliceExpression(expr *ast.SliceExpression) Type {
	seqType := tc.checkExpression(expr.Seq)
	if seqType == nil {
		return nil
	}

	// Check low and high bounds if provided
	if expr.Low != nil {
		lowType := tc.checkExpression(expr.Low, &PrimitiveType{Name: "u32"})
		if lowType == nil {
			return nil
		}
		if !tc.isNumericType(lowType) {
			tc.addError(expr.Low, "slice low bound must be numeric type, got %s", lowType)
			return nil
		}
	}

	if expr.High != nil {
		highType := tc.checkExpression(expr.High, &PrimitiveType{Name: "u32"})
		if highType == nil {
			return nil
		}
		if !tc.isNumericType(highType) {
			tc.addError(expr.High, "slice high bound must be numeric type, got %s", highType)
			return nil
		}
	}

	// Handle slicing of arrays, views, and spans
	if arrayType, ok := seqType.(*ArrayType); ok {
		// Slicing an owned array [N]T produces a View []T
		// Slicing a View []T produces a View []T
		// Slicing a Span [*]T produces a Span [*]T
		if arrayType.IsSpan {
			// Span -> Span
			return &ArrayType{
				ElementType: arrayType.ElementType,
				Length:      -1,
				IsSlice:     false,
				IsSpan:      true,
			}
		} else if arrayType.IsSlice {
			// View -> View
			return &ArrayType{
				ElementType: arrayType.ElementType,
				Length:      -1,
				IsSlice:     true,
				IsSpan:      false,
			}
		} else {
			// Owned array [N]T -> View []T
			return &ArrayType{
				ElementType: arrayType.ElementType,
				Length:      -1,
				IsSlice:     true,
				IsSpan:      false,
			}
		}
	}

	tc.addError(expr, "slice expression not supported for type: %s", seqType)
	return nil
}

func (tc *TypeChecker) checkVariableDeclaration(stmt *ast.VariableDeclaration) {
	defer func() {
		if stmt != nil && stmt.Name != nil {
			if info := tc.env.borrowMetadata(); info != nil {
				if scheme, ok := tc.env.Get(stmt.Name.Value); ok && scheme != nil {
					info.declarations[stmt] = scheme.Type
				}
			}
		}
	}()
	beforeDeclaration := len(tc.Errors())
	tc.beginMonomorphicTransaction()
	defer func() {
		tc.finishMonomorphicTransaction(len(tc.Errors()) == beforeDeclaration)
	}()

	if stmt == nil || stmt.Name == nil {
		// Defense in depth against parser error-recovery artifacts.
		return
	}
	// The defining declaration of a predeclared global is not a redeclaration.
	if tc.env == tc.globalEnv && tc.predeclaredGlobals[stmt.Name.Value] {
		delete(tc.predeclaredGlobals, stmt.Name.Value)
	} else if tc.shadowsVisibleBinding(stmt.Name.Value, stmt.Name.Token) {
		// Check if variable already exists in the declaring package's scope
		// (docs/spec/83-modules.md section 7; shadowsVisibleBinding).
		// Variable already exists - redefinition is not allowed
		// Use assignment statement (x = value) instead of variable declaration (x: type = value)
		if stmt.Type != nil {
			tc.addError(stmt.Name, "variable %s already declared; cannot redeclare with type annotation. Use assignment (x = value) instead", stmt.Name.Value)
		} else {
			tc.addError(stmt.Name, "variable %s already declared; Oak does not allow shadowing or redefinition", stmt.Name.Value)
		}
		return
	}

	// Variable doesn't exist - check if this is a declaration without type annotation
	// If it has no type and no value, that's an error
	if stmt.Type == nil && stmt.Value == nil {
		tc.addError(stmt.Name, "variable %s: no type annotation and no initializer", stmt.Name.Value)
		return
	}

	// Variable doesn't exist - this is a declaration
	// HM-style: let-bound variables get generalized types
	if stmt.Type != nil {
		// Explicit type annotation: parse and use it
		varType := tc.parseTypeExpression(stmt.Type)
		if varType == nil {
			tc.addError(stmt.Type, "variable %s: invalid type annotation", stmt.Name.Value)
			return
		}

		if ContainsAtomicStorage(varType) {
			// Atomic-bearing storage (a cell, a record with cell fields, an
			// array of cells) is zero-initialized declaration only: it is
			// storage identity, never a copied value.
			if stmt.Value != nil {
				tc.addError(stmt, "Atomic[T] storage is zero-initialized at declaration; initialize with atomic_store_* afterward, and never copy it")
				return
			}
		}

		// If there's an initializer, check that it matches the type (with coercion)
		// Pass expected type for context-based inference (e.g., for integer literals)
		var initializerBindings Substitution
		beforeInitializer := len(tc.Errors())
		if stmt.Value != nil {
			valueType := tc.checkExpression(stmt.Value, varType)
			if valueType != nil {
				// Use unification to check compatibility
				unifier := NewUnifier()
				sub := unifier.Unify(valueType, varType)
				if sub == nil {
					// Try assignability check as fallback
					if !tc.isAssignable(valueType, varType) {
						tc.addError(stmt, "variable %s: expected type %s, got %s", stmt.Name.Value, varType, valueType)
					}
				} else {
					// Apply substitution to get the unified type. Commit equations
					// for a blocked initializer only after the complete declaration succeeds.
					varType = sub.Apply(varType)
					initializerBindings = sub
				}
			}
		}

		if initializerBindings != nil && len(tc.Errors()) == beforeInitializer {
			tc.stageMonomorphicBindings(initializerBindings)
		}

		// Generalize the type (quantify over free type variables)
		scheme := GeneralizeWithFacts(varType, tc.env, deriveGeneralizationFacts(varType, stmt.Value, tc.env, tc))
		tc.env.Set(stmt.Name.Value, scheme)
	} else {
		// Type inference from initializer (HM-style)
		if stmt.Value != nil {
			inferredType := tc.checkExpression(stmt.Value)
			if inferredType != nil {
				if accessor, unresolved := inferredType.(*FieldAccessorType); unresolved {
					tc.addError(stmt.Value, "field accessor .%s needs an explicit function type or a contextual function argument", accessor.Field)
					return
				}
				if ContainsAtomicStorage(inferredType) {
					tc.addError(stmt.Value, "Atomic[T] storage cannot be inferred/copied into a value binding; declare a named Atomic[T] cell")
					return
				}
				// Generalize: convert to a type scheme
				scheme := GeneralizeWithFacts(inferredType, tc.env, deriveGeneralizationFacts(inferredType, stmt.Value, tc.env, tc))
				tc.env.Set(stmt.Name.Value, scheme)
			}
		} else {
			tc.addError(stmt.Name, "variable %s: no type annotation and no initializer", stmt.Name.Value)
		}
	}
}

// isAssignable checks if a value type can be assigned to a variable type
// Allows widening conversions (u8 -> u16, etc.) but not narrowing or sign changes
func (tc *TypeChecker) isAssignable(valueType, varType Type) bool {
	// Open targets use width matching; source representation remains intact.
	if target, ok := varType.(*RecordType); ok && target.Open {
		if source, ok := valueType.(*RecordType); ok {
			for name, required := range target.Fields {
				actual, present := source.Fields[name]
				if !present || !actual.Equals(required) {
					return false
				}
			}
			return true
		}
	}

	// Exact match
	if valueType.Equals(varType) {
		return true
	}

	// Numeric widening conversions
	if tc.isNumericType(valueType) && tc.isNumericType(varType) {
		valuePrim := valueType.(*PrimitiveType)
		varPrim := varType.(*PrimitiveType)

		// Same sign family
		if (valuePrim.Name[0] == 'i') == (varPrim.Name[0] == 'i') {
			valueWidth := tc.getBitWidth(valuePrim.Name)
			varWidth := tc.getBitWidth(varPrim.Name)
			// Widening is allowed (value can be narrower)
			return valueWidth <= varWidth
		}
	}

	return false
}

func (tc *TypeChecker) checkAssignmentStatement(stmt *ast.AssignmentStatement) {
	before := len(tc.Errors())
	tc.beginMonomorphicTransaction()
	defer func() {
		tc.finishMonomorphicTransaction(len(tc.Errors()) == before)
	}()

	// Assignment: x = expr
	// Rule: x must already be bound in the current scope, otherwise it's a compile-time error
	// This prevents accidental "silent declaration by typo" (e.g., cont = 1 vs count = 1)
	varScheme, ok := tc.env.Get(stmt.Name.Value)
	if !ok {
		tc.addError(stmt.Name, "undefined variable: %s", stmt.Name.Value)
		return
	}

	// Variable exists - this is a real assignment
	// Instantiate the scheme to get the actual type
	unifier := NewUnifier()
	varType := Instantiate(varScheme, unifier)
	if _, atomic := varType.(*AtomicType); atomic {
		tc.addError(stmt, "Atomic[T] cells are not assignable; use an atomic_store_* operation")
		return
	}

	// Check that assigned value matches variable type (with coercion)
	valueType := tc.checkExpression(stmt.Value, varType) // Pass expected type for context-based inference
	if valueType != nil {
		if !tc.isAssignable(valueType, varType) {
			// Provide helpful error message with suggestion for narrowing
			if varPrim, ok := varType.(*PrimitiveType); ok {
				if valuePrim, ok := valueType.(*PrimitiveType); ok {
					// Both are primitives - check if this is a narrowing case
					if varPrim.Name[0] == valuePrim.Name[0] { // Same signedness
						varWidth := tc.getTypeWidth(varPrim.Name)
						valueWidth := tc.getTypeWidth(valuePrim.Name)
						if varWidth < valueWidth {
							// This is a narrowing case - suggest narrowing function
							tc.addError(stmt, "assignment: variable %s has type %s, cannot assign %s (use %s_trunc_%s(...) or %s_checked_%s(...) for narrowing)",
								stmt.Name.Value, varType, valueType, varPrim.Name, valuePrim.Name, varPrim.Name, valuePrim.Name)
							return
						}
					}
				}
			}
			tc.addError(stmt, "assignment: variable %s has type %s, cannot assign %s", stmt.Name.Value, varType, valueType)
		}
	}
}

func (tc *TypeChecker) checkFunctionStatement(stmt *ast.FunctionStatement) {
	if stmt != nil && stmt.Name != nil && (stmt.Name.Value == "str_from_utf8" || stmt.Name.Value == "str_bytes") {
		tc.addError(stmt.Name, "%s is a reserved string-view builtin", stmt.Name.Value)
		return
	}
	before := len(tc.Errors())
	tc.beginMonomorphicTransaction()
	defer func() {
		tc.finishMonomorphicTransaction(len(tc.Errors()) == before)
	}()

	// Check for nil function statement
	if stmt == nil {
		return
	}

	// Check for nil function name
	if stmt.Name == nil {
		tc.addError(stmt, "function statement: missing function name")
		return
	}

	// Extern bindings have no Oak body: validate the boundary signature and
	// register the declared type (docs/spec/92-ffi.md section 2.3). Nested
	// bindings that the predeclare pass never saw are validated here.
	if stmt.ExternSymbol != "" {
		if !tc.checkedExterns[stmt] {
			tc.checkedExterns[stmt] = true
			tc.checkExternFunction(stmt)
		}
		return
	}

	// An extensible-record parameter describes a family of concrete ABIs,
	// not one layout. Register a representation template and check each
	// concrete call-site specialization through the ordinary safety gates.
	if stmt.Receiver == nil && hasOpenRowParameters(stmt) {
		tc.registerRowFunctionTemplate(stmt)
		return
	}

	// A definition-less declaration is legal only as the typed interface of
	// an asm unit's function (docs/spec/94-assembler.md §2); the compilation
	// marks it AsmBacked when the unit's matching signature exists.
	if stmt.Body == nil {
		if stmt.AsmBacked {
			tc.checkAsmBoundary(stmt)
			return
		}
		tc.addError(stmt, "function %s needs a definition ('= expression', a brace block) or an asm unit providing its body", stmt.Name.Value)
		return
	}
	if stmt.AsmBacked {
		// An Oak fallback body beside an asm unit: the signature must still
		// be an asm-boundary signature; the body is checked as usual below.
		tc.checkAsmBoundary(stmt)
	}

	// An UNCONSTRAINED generic function declaration is a template:
	// registered, never checked generically — each instantiation is
	// specialized and checked with concrete types
	// (typechecker/genericfn.go), the record-template precedent applied to
	// functions. Constraint-carrying generics ([T: Position]) keep the
	// constraint-checking path and its structured diagnostics; their
	// monomorphization is the recorded next step.
	if len(stmt.TypeParams) > 0 && stmt.Receiver == nil && !typeParamsConstrained(stmt.TypeParams) {
		tc.registerFunctionTemplate(stmt)
		return
	}
	// A CONSTRAINED generic function keeps the contract path below — its
	// body is checked once against the constraint (a field outside the
	// contract is a declaration-time error) and every call checks its
	// argument (OAK-T0104) — and is additionally a template: each satisfied
	// call specializes it for emission (typechecker/genericfn.go).
	if len(stmt.TypeParams) > 0 && stmt.Receiver == nil {
		tc.registerFunctionTemplate(stmt)
	}

	// Extract type parameters and constraints
	typeVars := []string{}
	constraints := []Constraint{}

	if stmt.TypeParams != nil {
		for _, tp := range stmt.TypeParams {
			typeVars = append(typeVars, tp.Name.Value)

			// Extract constraint if present
			// Constraints can be single interfaces or intersections (A & B & C)
			if tp.Constraint != nil && !isConstParameter(tp) {
				interfaces := tc.extractInterfacesFromConstraint(tp.Constraint)
				if len(interfaces) > 0 {
					constraints = append(constraints, Constraint{
						Var:        tp.Name.Value,
						Interfaces: interfaces,
					})
				}
			}
		}
	}

	// Create new environment for function parameters and bind source-level
	// type variables before resolving the signature. Constraint metadata stays
	// checker-local and does not participate in representation or type identity.
	funcEnv := NewEnclosedTypeEnvironment(tc.env)
	bindConstrainedTypeVars(funcEnv, typeVars, constraints)
	if !tc.validateGenericConstraints(constraints, funcEnv, stmt) {
		return
	}

	// If this is a method, add receiver to the environment
	if stmt.Receiver != nil {
		// Check for shadowing: receiver name must not conflict with outer scope
		if tc.shadowsVisibleBinding(stmt.Receiver.Name.Value, stmt.Receiver.Name.Token) {
			tc.addError(stmt.Receiver.Name, "receiver '%s' already declared in outer scope; Oak does not allow shadowing", stmt.Receiver.Name.Value)
			return
		}
		receiverType := tc.parseTypeExpressionInEnv(stmt.Receiver.Type, funcEnv)
		if receiverType == nil {
			tc.addError(stmt.Receiver.Type, "method %s: invalid receiver type", stmt.Name.Value)
			return
		}
		funcEnv.SetType(stmt.Receiver.Name.Value, receiverType)
	}

	// Parse parameter types from function signature
	paramTypes := []Type{}
	paramNames := make(map[string]bool)
	for _, param := range stmt.Parameters {
		// Check for shadowing: parameter name must not conflict with outer scope or other parameters.
		// A specialization re-checks a template body that already passed
		// this rule in its own declaration scope; globals declared between
		// the template and the instantiating call are not shadowing.
		if !tc.checkingSpecialization && tc.shadowsVisibleBinding(param.Name.Value, param.Name.Token) {
			tc.addError(param.Name, "parameter '%s' already declared in outer scope; Oak does not allow shadowing", param.Name.Value)
			return
		}
		if paramNames[param.Name.Value] {
			tc.addError(param.Name, "duplicate parameter name '%s'; Oak does not allow shadowing", param.Name.Value)
			return
		}
		paramNames[param.Name.Value] = true
		paramType := tc.parseTypeExpressionInEnv(param.Type, funcEnv)
		if paramType == nil {
			// Default to i32 if type parsing fails
			paramType = &PrimitiveType{Name: "i32"}
		}
		if ContainsAtomicStorage(paramType) {
			tc.addError(param.Type, "Atomic[T] storage cannot be passed by value in v1; use package/local cells until an AtomicRef borrowing contract exists")
			return
		}
		if param.Variadic {
			// The body sees the trailing parameter as a read-only view of a
			// caller-owned argument array (docs/spec/10-syntax.md).
			paramType = &ArrayType{Length: -1, IsSlice: true, ElementType: paramType}
		}
		paramTypes = append(paramTypes, paramType)
		funcEnv.SetType(param.Name.Value, paramType)
	}
	isVariadic := len(stmt.Parameters) > 0 && stmt.Parameters[len(stmt.Parameters)-1].Variadic

	// Parse return type
	returnType := tc.parseTypeExpressionInEnv(stmt.ReturnType, funcEnv)
	if returnType == nil {
		returnType = &UnitType{}
	}
	if ContainsAtomicStorage(returnType) {
		tc.addError(stmt.ReturnType, "Atomic[T] storage cannot be returned by value in v1")
		return
	}

	// Pre-bind the declared signature so the body can reference itself:
	// recursion is legal, with its stack discipline governed separately
	// (docs/spec/85-discipline.md).
	funcEnv.SetType(stmt.Name.Value, &FunctionType{
		Parameters: paramTypes,
		ReturnType: returnType,
		Variadic:   isVariadic,
	})

	// Save current environment and switch to function environment
	oldEnv := tc.env
	tc.env = funcEnv

	// An owned array cannot be returned by value yet (C returns no arrays;
	// by-value arrays are roadmap item 4): say so instead of emitting
	// invalid C, and point at the record wrapper that works today.
	if arr, isArray := returnType.(*ArrayType); isArray && arr.Length >= 0 && !arr.IsSlice && !arr.IsSpan {
		tc.addError(stmt.ReturnType, "function %s: returning an owned array by value is not lowered yet; return it inside a record", stmt.Name.Value)
	}

	// Type check function body, inferring literals against the declared
	// return type.
	bodyType := tc.checkExpression(stmt.Body, returnType)
	if bodyType == nil {
		bodyType = &UnitType{}
	}

	// Check that body type matches return type
	if !bodyType.Equals(returnType) {
		tc.addError(stmt, "function %s: expected return type %s, got %s", stmt.Name.Value, returnType, bodyType)
	}

	// Restore environment
	tc.env = oldEnv

	// Preserve any persistent state committed by callers that appeared before
	// this declaration; finalization must not reopen a barred generic.
	predeclared, _ := tc.env.Get(stmt.Name.Value)

	// Store function type in environment
	funcType := &FunctionType{
		Parameters: paramTypes,
		ReturnType: returnType,
		Variadic:   isVariadic,
	}

	// A named function is a closure binding too. Captured authority and unsafe
	// assumptions gate both inferred and explicitly declared quantification.
	functionFacts := functionStatementCaptureFacts(stmt, funcEnv)
	funcScheme := GeneralizeWithFacts(funcType, tc.env, functionFacts)

	// Explicit type parameters remain quantified only when the closure evidence
	// permits generalization; annotations never erase authority barriers.
	if len(typeVars) > 0 || len(constraints) > 0 {
		quantified := typeVars
		if !functionFacts.Safe() {
			quantified = nil
		}
		funcScheme = &TypeScheme{
			TypeVars:               quantified,
			Constraints:            constraints,
			Type:                   funcScheme.Type,
			GeneralizationBarriers: funcScheme.GeneralizationBarriers,
			Monomorphic:            funcScheme.Monomorphic,
		}
	}

	if predeclared != nil && predeclared.Monomorphic != nil &&
		funcScheme.GeneralizationBarriers != 0 {
		predeclared.Constraints = constraints
		predeclared.GeneralizationBarriers |= funcScheme.GeneralizationBarriers
		funcScheme = predeclared
	}
	tc.env.Set(stmt.Name.Value, funcScheme)

	// If this is a method, also store it with TypeName::methodName key
	if stmt.Receiver != nil {
		receiverType := tc.parseTypeExpressionInEnv(stmt.Receiver.Type, funcEnv)
		if receiverType != nil {
			// For ADT types, use the type name
			if adtType, ok := receiverType.(*ADTType); ok {
				methodKey := fmt.Sprintf("%s::%s", adtType.Name, stmt.Name.Value)
				tc.env.Set(methodKey, funcScheme)
			}
		}
	}
}

func (tc *TypeChecker) checkADTType(stmt *ast.ADTType) {
	// Check if this is a record type definition: Name: type = { field: Type, ... }
	// Record type definitions are parsed as ADTType with a single variant that has a record literal
	if len(stmt.Variants) == 1 {
		variant := stmt.Variants[0]
		// Check if the variant has a record literal (this indicates a record type definition)
		if variant.Literal != nil {
			if recordLit, ok := variant.Literal.(*ast.RecordLiteral); ok {
				// A generic record declaration is a template: fields are
				// validated per instantiation (typechecker/mono.go).
				if len(stmt.TypeParams) > 0 {
					if tc.recordTemplates == nil {
						tc.recordTemplates = make(map[string]*ast.ADTType)
					}
					tc.recordTemplates[stmt.Name.Value] = stmt
					return
				}
				// This is a record type definition
				tc.checkRecordTypeDefinition(stmt.Name.Value, recordLit)
				// Store the record type in the environment with its nominal
				// name, so the backend can emit the declared struct.
				recordType := tc.parseRecordTypeFromLiteral(recordLit)
				if named, isRecord := recordType.(*RecordType); isRecord {
					named.Name = stmt.Name.Value
				}
				if recordType != nil {
					recordScheme := Generalize(recordType, tc.env)
					tc.env.Set(stmt.Name.Value, recordScheme)
				}
				return
			}
			// Check if this is an intersection expression (type composition)
			if infixExpr, ok := variant.Literal.(*ast.InfixExpression); ok && infixExpr.Operator == "&" {
				// This is an intersection type: Type1 & Type2 & { ... }
				// Parse it as a type expression and normalize to a record type
				intersectionType := tc.parseTypeExpression(variant.Literal)
				if intersectionType == nil {
					return
				}
				// If it's an IntersectionType, we need to normalize it to a RecordType
				if intersection, ok := intersectionType.(*IntersectionType); ok {
					// Collect all record types from the intersection and merge them
					recordType := tc.normalizeIntersectionToRecord(intersection)
					if recordType != nil {
						recordScheme := Generalize(recordType, tc.env)
						tc.env.Set(stmt.Name.Value, recordScheme)
					}
				} else if recordType, ok := intersectionType.(*RecordType); ok {
					// Already a record type
					recordScheme := Generalize(recordType, tc.env)
					tc.env.Set(stmt.Name.Value, recordScheme)
				}
				return
			}
		}
		// Check if this is a type alias: Name: type = TypeName
		// If the variant has no name or the name matches the type name, it might be an alias
		if variant.Name.Value == stmt.Name.Value && variant.Payload != nil && variant.Literal == nil {
			// This might be a type alias, but we'll handle it as an ADT for now
		}
	}

	// Register the ADT type in the typechecker's adtTypes map FIRST
	// This allows variant checking to reference the ADT type
	adtType := &object.ADTType{
		Name:       stmt.Name.Value,
		TypeParams: make([]string, 0, len(stmt.TypeParams)),
		Variants:   []*object.ADTVariantDef{},
	}
	for _, param := range stmt.TypeParams {
		adtType.TypeParams = append(adtType.TypeParams, param.Name.Value)
	}

	for _, variant := range stmt.Variants {
		variantDef := &object.ADTVariantDef{Name: variant.Name.Value}
		if variant.Payload != nil {
			variantDef.Payload = variant.Payload.String()
		}

		if variant.Result == nil {
			variantDef.ResultName = stmt.Name.Value
			variantDef.ResultIndices = append([]string(nil), adtType.TypeParams...)
		} else {
			resultName, indices, err := constructorResultSyntax(variant.Result)
			if err != nil || resultName != stmt.Name.Value || len(indices) != len(adtType.TypeParams) {
				d := tc.addTypeDiagnostic(variant.Result, CodeGADTResultInvalid, "invalid indexed constructor result")
				d.AddNote(fmt.Sprintf("constructor %s must return %s with %d type indices", variant.Name.Value, stmt.Name.Value, len(adtType.TypeParams)))
				d.AddHelp("write the result as the enclosing ADT applied to exactly its declared type indices")
			} else {
				variantDef.ResultName = resultName
				variantDef.ResultIndices = indices
			}
		}
		adtType.Variants = append(adtType.Variants, variantDef)
	}

	tc.adtTypes[stmt.Name.Value] = adtType
	tc.adtPayloadTypes[stmt.Name.Value] = make(map[string]Type)

	// Now verify the ADT is well-formed (after registration)
	variantNames := make(map[string]bool)

	for _, variant := range stmt.Variants {
		variantName := variant.Name.Value

		// Check for duplicate variants
		if variantNames[variantName] {
			tc.addError(stmt, "ADT %s: duplicate variant %s", stmt.Name.Value, variantName)
			continue
		}
		variantNames[variantName] = true

		// Check payload type if present
		if variant.Payload != nil {
			payloadType := tc.parseTypeExpression(variant.Payload)
			if ContainsAtomicStorage(payloadType) {
				tc.addError(variant.Payload, "Atomic[T] cannot be embedded in ADT payloads in v1")
			}
			if payloadType == nil {
				tc.addError(variant.Payload, "ADT %s variant %s: invalid payload type", stmt.Name.Value, variantName)
			} else {
				tc.adtPayloadTypes[stmt.Name.Value][variantName] = payloadType
			}
		}

		// Check literal tag if present
		// Skip if this is a record type definition (record literal in type context)
		if variant.Literal != nil {
			// Don't check record literals as expressions - they're type definitions
			if _, isRecordLiteral := variant.Literal.(*ast.RecordLiteral); isRecordLiteral {
				// This is a record type definition, skip expression checking
				continue
			}
			// Don't check intersection expressions as value expressions - they're type compositions
			if infixExpr, ok := variant.Literal.(*ast.InfixExpression); ok && infixExpr.Operator == "&" {
				// This is an intersection type expression - skip expression checking
				// It will be handled when we process the type definition
				continue
			}
			literalType := tc.checkExpression(variant.Literal)
			if literalType == nil {
				tc.addError(variant.Literal, "ADT %s variant %s: invalid literal tag", stmt.Name.Value, variantName)
			} else {
				// Verify literal tag type consistency across variants
				tc.checkADTVariantLiteralTag(stmt.Name.Value, variantName, variant.Literal, literalType)
			}
		}
	}

	// Check that ADT has at least one variant
	if len(stmt.Variants) == 0 {
		tc.addError(stmt, "ADT %s: must have at least one variant", stmt.Name.Value)
		return
	}
}

// checkRecordTypeDefinition type checks a record type definition
func (tc *TypeChecker) checkRecordTypeDefinition(typeName string, recordLit *ast.RecordLiteral) {
	// A packed container places fields densely; a raised member alignment
	// contradicts that placement. Rejected here, fail-closed in the backend.
	if recordLit.Layout != nil && recordLit.Layout.Packed {
		for _, field := range recordLit.FieldOrder {
			if field.Align != 0 {
				tc.addError(field.Value, "record type %s: field %s declares align inside a packed record; packing and raised member alignment contradict", typeName, field.Name)
			}
		}
	}
	// Typed field tags check against declared schemas (typechecker/tags.go).
	for _, field := range recordLit.FieldOrder {
		tc.checkFieldTags(typeName, field)
	}
	// Check that all fields have valid type annotations
	fieldNames := make(map[string]bool)
	for fieldName, fieldExpr := range recordLit.Fields {
		// Check for duplicate field names
		if fieldNames[fieldName] {
			// Use the record literal as the node if available, otherwise nil
			tc.addError(nil, "record type %s: duplicate field name %s", typeName, fieldName)
			continue
		}
		fieldNames[fieldName] = true

		// Parse field type from the expression
		// In a record type definition, fieldExpr should be a type expression (identifier)
		fieldType := tc.parseTypeExpression(fieldExpr)
		if !atomicFieldShapeLegal(fieldType) {
			tc.addError(fieldExpr, "Atomic[T] may be a field or an owned array of cells; deeper embeddings are not supported in v1")
		}
		// A packed record places fields densely, so an Atomic[T] field can
		// land unaligned — misaligned C11 _Atomic access is undefined
		// behavior and never lock-free. Rejected outright.
		if recordLit.Layout != nil && recordLit.Layout.Packed && fieldType != nil && ContainsAtomicStorage(fieldType) {
			tc.addError(fieldExpr, "record type %s: packed records cannot contain atomic storage (field %s); misaligned atomics are undefined behavior", typeName, fieldName)
		}
		if fieldType == nil {
			// fieldExpr might be an expression, try to use it as a node
			if node, ok := fieldExpr.(ast.Node); ok {
				tc.addError(node, "record type %s field %s: invalid type", typeName, fieldName)
			} else {
				tc.addError(nil, "record type %s field %s: invalid type", typeName, fieldName)
			}
		}
	}
}

// parseRecordTypeFromLiteral parses a RecordType from a record literal used
// in a type definition, preserving declaration order (layout-significant:
// docs/spec/40-records.md).
func (tc *TypeChecker) parseRecordTypeFromLiteral(recordLit *ast.RecordLiteral) Type {
	fields := make(map[string]Type)
	order := make([]string, 0, len(recordLit.FieldOrder))
	for _, field := range recordLit.FieldOrder {
		fieldType := tc.parseTypeExpression(field.Value)
		if fieldType == nil {
			return nil
		}
		fields[field.Name] = fieldType
		order = append(order, field.Name)
	}
	// Defense in depth: fields that reached the map without an order entry
	// (older construction paths) are appended deterministically.
	if len(order) < len(recordLit.Fields) {
		missing := make([]string, 0)
		for fieldName := range recordLit.Fields {
			if _, present := fields[fieldName]; !present {
				missing = append(missing, fieldName)
			}
		}
		sort.Strings(missing)
		for _, fieldName := range missing {
			fieldType := tc.parseTypeExpression(recordLit.Fields[fieldName])
			if fieldType == nil {
				return nil
			}
			fields[fieldName] = fieldType
			order = append(order, fieldName)
		}
	}

	// Canonicalize empty record {} to Unit
	if len(fields) == 0 {
		return &UnitType{}
	}

	// The struct keyword commits the declaration to concrete ordered
	// representation — and, once named, to nominal identity. A plain
	// { ... } declaration stays a structural shape.
	return &RecordType{Fields: fields, Order: order, Struct: recordLit.Token.TokenKind == token.STRUCT}
}

// checkADTVariantLiteralTag checks that literal tags in ADT variants are consistent
func (tc *TypeChecker) checkADTVariantLiteralTag(adtName, variantName string, literal ast.Expression, literalType Type) {
	// Check if this ADT already has variants with literal tags
	// All literal tags in an ADT must have the same type
	if adtDef, ok := tc.adtTypes[adtName]; ok {
		var expectedLiteralType Type
		for _, variant := range adtDef.Variants {
			if variant.Literal != nil {
				// We need to get the type of the literal
				// For now, we'll check consistency when we encounter multiple variants
				if expectedLiteralType == nil {
					expectedLiteralType = literalType
				} else if !literalType.Equals(expectedLiteralType) {
					tc.addError(literal, "ADT %s: variant %s literal tag type %s does not match expected type %s",
						adtName, variantName, literalType, expectedLiteralType)
					return
				}
			}
		}
	}
}

// checkIfStatement types the statement-position conditional
// (docs/spec/10-syntax.md): Bool condition, both branches checked.
func (tc *TypeChecker) checkIfStatement(stmt *ast.IfStatement) {
	conditionType := tc.checkExpression(stmt.Condition)
	if conditionType != nil && !conditionType.Equals(&BoolType{}) {
		tc.addError(stmt.Condition, "if condition must be Bool, got %s", conditionType)
	}
	// Each branch starts from the same fact state; kills in one branch do
	// not reach the other, and their union applies after the statement.
	before := tc.deadSnapshot()
	after := before
	if stmt.Consequence != nil {
		mark := tc.enterFactScope(stmt.Condition)
		tc.checkBlockStatement(stmt.Consequence)
		tc.popExtentFacts(mark)
		after = unionDead(after, tc.deadSnapshot())
		tc.restoreDead(before)
	}
	switch alternative := stmt.Alternative.(type) {
	case nil:
	case *ast.IfStatement:
		tc.checkIfStatement(alternative)
	case *ast.BlockStatement:
		tc.checkBlockStatement(alternative)
	default:
		tc.addError(stmt, "if statement: invalid else branch %T", stmt.Alternative)
	}
	tc.restoreDead(unionDead(after, tc.deadSnapshot()))
}

func (tc *TypeChecker) checkWhileStatement(stmt *ast.WhileStatement) {
	before := len(tc.Errors())
	tc.beginMonomorphicTransaction()
	defer func() {
		tc.finishMonomorphicTransaction(len(tc.Errors()) == before)
	}()

	// The condition's facts are derived with the bindings as they are on
	// entry; a loop that assigns a binding anywhere then invalidates the
	// enclosing facts about it before the condition runs, because an
	// earlier statement of the body executes again after the assignment
	// (typechecker/extents.go).
	conditionFacts := tc.loopConditionFacts(stmt)
	tc.killFactsAssignedBy(stmt)
	conditionType := tc.checkExpression(stmt.Condition)
	if conditionType != nil && !conditionType.Equals(&BoolType{}) {
		tc.addError(stmt.Condition, "while condition must be bool, got %s", conditionType)
	}

	// The loop condition dominates the body on every iteration: `i < len(v)`
	// bounds v[i] until the body assigns i (typechecker/extents.go).
	mark := tc.pushExtentFacts(conditionFacts)
	// The body is its own scope: a name declared inside the loop is not
	// visible after it, so a later block may declare the same name.
	outerEnv := tc.env
	tc.env = NewEnclosedTypeEnvironment(outerEnv)
	tc.checkBlockStatement(stmt.Body)
	tc.env = outerEnv
	tc.popExtentFacts(mark)
}

func (tc *TypeChecker) checkBlockStatement(block *ast.BlockStatement) {
	// Type check all statements in the block. A view/span declaration with
	// literal bounds establishes its extent for the rest of the block
	// (typechecker/extents.go); the facts pop with the block.
	mark := len(tc.extentFacts)
	defer tc.popExtentFacts(mark)
	for i, stmt := range block.Statements {
		tc.checkStatement(stmt)
		tc.killFactsAfterStatement(stmt)
		if decl, isDecl := stmt.(*ast.VariableDeclaration); isDecl {
			tc.enterDeclarationFacts(decl, block.Statements[i+1:])
		}
	}
}

// killFactsAfterStatement invalidates the facts an assignment statement
// breaks, once its right-hand side (which still saw them) is checked.
// Loops kill on entry (checkWhileStatement) and branches kill inside their
// own blocks, so only direct assignments are handled here.
func (tc *TypeChecker) killFactsAfterStatement(stmt ast.Statement) {
	switch s := stmt.(type) {
	case *ast.AssignmentStatement:
		remembered := tc.factsFromCondition(s.Value) // the right-hand side saw the old binding
		tc.killFactsAssignedBy(stmt)
		tc.rememberBoolFacts(s.Name, remembered)
	case *ast.VariableDeclaration:
		var remembered []extentFact
		if s.Value != nil {
			remembered = tc.factsFromCondition(s.Value)
		}
		tc.killFactsAssignedBy(stmt)
		tc.rememberBoolFacts(s.Name, remembered)
	case *ast.IndexAssignmentStatement:
		tc.killFactsAssignedBy(stmt)
	}
}

// checkBlockExpression type checks a block expression and returns the type of
// the last expression, inferring it against the expected type when given.
func (tc *TypeChecker) checkBlockExpression(block *ast.BlockStatement, expectedType ...Type) Type {
	var expected Type
	if len(expectedType) > 0 {
		expected = expectedType[0]
	}
	if len(block.Statements) == 0 {
		return &UnitType{}
	}

	// Type check all statements except the last. Declarations with literal
	// extents establish facts for the rest of the block, tail included
	// (typechecker/extents.go); the facts pop with the block.
	mark := len(tc.extentFacts)
	defer tc.popExtentFacts(mark)
	for i := 0; i < len(block.Statements)-1; i++ {
		tc.checkStatement(block.Statements[i])
		tc.killFactsAfterStatement(block.Statements[i])
		if decl, isDecl := block.Statements[i].(*ast.VariableDeclaration); isDecl {
			tc.enterDeclarationFacts(decl, block.Statements[i+1:])
		}
	}

	// The last statement should be an expression statement. A trailing
	// discard (`_ = expr`, docs/spec/85-discipline.md section 6) is a
	// statement, never the block's value: the block is unit.
	lastStmt := block.Statements[len(block.Statements)-1]
	if exprStmt, ok := lastStmt.(*ast.ExpressionStatement); ok && !exprStmt.Discard {
		if expected != nil {
			return tc.checkExpression(exprStmt.Expression, expected)
		}
		return tc.checkExpression(exprStmt.Expression)
	}

	// If the last statement is not an expression, return unit
	tc.checkStatement(lastStmt)
	tc.killFactsAfterStatement(lastStmt)
	return &UnitType{}
}

func (tc *TypeChecker) checkUnsafeBlock(stmt *ast.UnsafeBlock) {
	// Type check body (same as regular block)
	// Unsafe blocks don't change type checking rules, they just bypass borrow checking
	tc.checkBlockStatement(stmt.Body)
}

func (tc *TypeChecker) checkArrayLiteral(expr *ast.ArrayLiteral, expectedType ...Type) Type {
	var expected Type
	if len(expectedType) > 0 {
		expected = expectedType[0]
	}

	// Check if this is a typed array literal: [N]Type{ ... }
	if expr.Type != nil {
		// Parse the array type from the Type field (which is an IndexExpression)
		expectedArrayType := tc.parseTypeExpression(expr.Type)
		if expectedArrayType == nil {
			return nil
		}

		expectedArray, ok := expectedArrayType.(*ArrayType)
		if !ok {
			tc.addError(expr, "expected array type in typed array literal, got %s", expectedArrayType)
			return nil
		}

		// Check that the number of elements matches the array size
		if !expectedArray.IsSlice && int64(len(expr.Elements)) != expectedArray.Length {
			tc.addError(expr, "array literal has %d elements, expected %d", len(expr.Elements), expectedArray.Length)
			return nil
		}

		// Check each element type matches the expected element type
		for i, elem := range expr.Elements {
			elemType := tc.checkExpression(elem, expectedArray.ElementType)
			if elemType == nil {
				continue
			}

			// Check if element type is assignable to expected element type
			if !tc.isAssignable(elemType, expectedArray.ElementType) {
				if i < len(expr.Elements) {
					tc.addError(expr.Elements[i], "array element %d: expected type %s, got %s", i, expectedArray.ElementType, elemType)
				} else {
					tc.addError(expr, "array element %d: expected type %s, got %s", i, expectedArray.ElementType, elemType)
				}
			}
		}

		return expectedArray
	}

	// An untyped literal inherits an expected array/view shape. This gives
	// every element the declared context (notably sized integer literals) and
	// preserves owned-array length instead of degrading [N]T to []T.
	if expectedArray, ok := expected.(*ArrayType); ok {
		if !expectedArray.IsSlice && !expectedArray.IsSpan &&
			int64(len(expr.Elements)) != expectedArray.Length {
			tc.addError(expr, "array literal has %d elements, expected %d", len(expr.Elements), expectedArray.Length)
			return nil
		}
		for i, elem := range expr.Elements {
			elemType := tc.checkExpression(elem, expectedArray.ElementType)
			if elemType != nil && !tc.isAssignable(elemType, expectedArray.ElementType) {
				tc.addError(elem, "array element %d: expected type %s, got %s", i, expectedArray.ElementType, elemType)
			}
		}
		return expectedArray
	}

	// Untyped array literal: [ expr1, expr2, ... ] or []
	// For empty array [], use expected type if available
	if len(expr.Elements) == 0 {
		// Empty array [] - must have type annotation or expected type
		if expected != nil {
			// Check if expected type is an array/slice type
			if arrayType, ok := expected.(*ArrayType); ok {
				// [] is syntactic sugar for []Type{} - set the type on the AST node
				// Create the type expression for []Type
				elementTypeIdent := &ast.Identifier{
					Token: expr.Token,
					Value: arrayType.ElementType.String(),
				}
				// Create IndexExpression for []Type (empty index means slice)
				sliceTypeExpr := &ast.IndexExpression{
					Token: expr.Token,
					Left:  elementTypeIdent,
					Index: &ast.Identifier{Token: expr.Token, Value: ""}, // empty string = slice
				}
				expr.Type = sliceTypeExpr
				return arrayType
			} else {
				tc.addError(expr, "empty array literal [] cannot be assigned to non-array type %s", expected)
				return nil
			}
		} else {
			// No type annotation and no expected type - error
			tc.addError(expr, "empty array literal [] requires type annotation (e.g., []u8{} or a: []u8 = [])")
			return nil
		}
	}

	// Check all elements have compatible types
	firstType := tc.checkExpression(expr.Elements[0])
	if firstType == nil {
		return nil
	}

	// Promote to the widest type if needed
	commonType := firstType
	for i := 1; i < len(expr.Elements); i++ {
		elemType := tc.checkExpression(expr.Elements[i])
		if elemType == nil {
			continue
		}
		if !elemType.Equals(commonType) {
			// Try to find a common type (promotion)
			if tc.isNumericType(elemType) && tc.isNumericType(commonType) {
				commonType = tc.promoteNumericTypes(expr.Elements[i], commonType, elemType)
				if commonType == nil {
					if i+1 < len(expr.Elements) {
						tc.addError(expr.Elements[i+1], "array element %d: incompatible types %s and %s", i+1, firstType, elemType)
					} else {
						tc.addError(expr, "array element %d: incompatible types %s and %s", i+1, firstType, elemType)
					}
					commonType = firstType // Fallback
				}
			} else {
				if i+1 < len(expr.Elements) {
					tc.addError(expr.Elements[i+1], "array element %d: expected type %s, got %s", i+1, commonType, elemType)
				} else {
					tc.addError(expr, "array element %d: expected type %s, got %s", i+1, commonType, elemType)
				}
			}
		}
	}

	return &ArrayType{
		ElementType: commonType,
		IsSlice:     true, // Array literals create slices for now
	}
}

// ArrayType represents array or slice types
type ArrayType struct {
	ElementType Type
	Length      int64 // >= 0 for fixed arrays, -1 for slices/spans
	IsSlice     bool  // true for []T, false for [N]T or [*]T
	IsSpan      bool  // true for [*]T, false otherwise
}

func (t *ArrayType) String() string {
	if t.IsSpan {
		return fmt.Sprintf("[*]%s", t.ElementType.String())
	}
	if t.IsSlice {
		return fmt.Sprintf("[]%s", t.ElementType.String())
	}
	return fmt.Sprintf("[%d]%s", t.Length, t.ElementType.String())
}

func (t *ArrayType) Equals(other Type) bool {
	if otherArray, ok := other.(*ArrayType); ok {
		if t.IsSpan != otherArray.IsSpan {
			return false
		}
		return t.ElementType.Equals(otherArray.ElementType) &&
			t.Length == otherArray.Length &&
			t.IsSlice == otherArray.IsSlice
	}
	return false
}

// GenericType represents a generic type application: Option[T], Result[T, E], etc.
type GenericType struct {
	Name     string // "Option", "Result", etc.
	TypeArgs []Type // Type arguments: [T], [T, E], etc.
}

func (t *GenericType) String() string {
	var out string
	out += t.Name
	if len(t.TypeArgs) > 0 {
		out += "["
		for i, arg := range t.TypeArgs {
			if i > 0 {
				out += ", "
			}
			out += arg.String()
		}
		out += "]"
	}
	return out
}

func (t *GenericType) Equals(other Type) bool {
	if otherGen, ok := other.(*GenericType); ok {
		if t.Name != otherGen.Name || len(t.TypeArgs) != len(otherGen.TypeArgs) {
			return false
		}
		for i, arg := range t.TypeArgs {
			if !arg.Equals(otherGen.TypeArgs[i]) {
				return false
			}
		}
		return true
	}
	return false
}

// parseTypeExpression parses a type from an AST expression
// Handles identifiers, intersections (A & B), and other type expressions
func (tc *TypeChecker) parseTypeExpression(expr ast.Expression) Type {
	// Phantom-encoded strings resolve before generic ADT application:
	// Str[Utf8] is a built-in phantom type, not a user generic.
	if indexExpr, ok := expr.(*ast.IndexExpression); ok {
		if strType := tc.parseStrEncodingType(indexExpr); strType != nil {
			return strType
		}
		// Record-template applications (Ring[u8, 16]) resolve before array
		// syntax: template knowledge is the const-parameter disambiguator
		// (typechecker/mono.go).
		if instantiated, isTemplate := tc.resolveRecordTemplateApplication(indexExpr); isTemplate {
			return instantiated
		}
	}
	// Array-type syntax is never a generic application: its index position
	// holds a size or the span/slice marker, not a type argument.
	if !isArrayTypeSyntax(expr) {
		if generic, recognized := tc.parseGenericTypeApplication(expr); recognized {
			return generic
		}
	}

	// Handle intersection types: A & B & C
	// Use collectIntersectionTypes to properly flatten nested intersections
	if infix, ok := expr.(*ast.InfixExpression); ok && infix.Operator == "&" {
		types := []Type{}
		tc.collectIntersectionTypes(expr, &types)
		if len(types) == 0 {
			return nil
		}
		// If only one type after collection, return it directly (not an intersection)
		if len(types) == 1 {
			return types[0]
		}
		return &IntersectionType{Types: types}
	}

	// Const parameters: integer literals appear as type arguments
	// (Ring[u8, 16] — docs/spec/20-types.md).
	if intLit, ok := expr.(*ast.IntegerLiteral); ok {
		return &ConstIntType{Value: intLit.Value}
	}

	if ident, ok := expr.(*ast.Identifier); ok {
		// Library-qualified types (c.Int32, ...) resolve before anything
		// else: type position always means the library (docs/spec/92-ffi.md).
		if libraryType, isLibrary := tc.libraryQualifiedType(ident); isLibrary {
			return libraryType
		}
		// Check if it's a primitive type
		switch ident.Value {
		case "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "f32", "f64":
			return &PrimitiveType{Name: ident.Value}
		case "int", "uint", "ptr", "uptr":
			// Platform-dependent types
			return &PrimitiveType{Name: ident.Value}
		case "byte":
			// byte is an alias for u8
			return &PrimitiveType{Name: "u8"}
		case "rune":
			// rune is the canonical refined u32 (docs/spec/70-strings.md section 9)
			return &PrimitiveType{Name: "u32"}
		case "string":
			return &StringType{}
		case "Bool":
			return &BoolType{}
		case "()":
			return &UnitType{}
		case "never":
			return &NeverType{}
		case "any":
			return &AnyType{}
		case "Atomic":
			tc.addError(ident, "Atomic requires exactly one carrier: Atomic[u8|u16|u32|u64|i8|i16|i32|i64]")
			return nil
		default:
			// Check if it's a type alias in the environment
			if aliasType, ok := tc.env.GetType(ident.Value); ok {
				return aliasType
			}
			// Assume it's an ADT type
			return &ADTType{Name: ident.Value}
		}
	}

	if fnExpr, ok := expr.(*ast.FunctionTypeExpression); ok {
		params := make([]Type, 0, len(fnExpr.Parameters))
		for _, param := range fnExpr.Parameters {
			paramType := tc.parseTypeExpression(param)
			if paramType == nil {
				return nil
			}
			params = append(params, paramType)
		}
		var returnType Type = &UnitType{}
		if fnExpr.Return != nil {
			returnType = tc.parseTypeExpression(fnExpr.Return)
			if returnType == nil {
				return nil
			}
		}
		return &FunctionType{Parameters: params, ReturnType: returnType}
	}

	// Handle array types: [N]T or []T
	if indexExpr, ok := expr.(*ast.IndexExpression); ok {
		// Phantom-encoded strings: Str[Utf8] etc. (docs/spec/70-strings.md).
		if strType := tc.parseStrEncodingType(indexExpr); strType != nil {
			return strType
		}
		// Check if left side is an array literal syntax or identifier
		// For [N]T, the parser represents it as IndexExpression with IntegerLiteral in Index
		// For []T, it's represented as IndexExpression with empty Identifier in Index
		elementType := tc.parseTypeExpression(indexExpr.Left)
		if elementType == nil {
			return nil
		}

		if intLit, ok := indexExpr.Index.(*ast.IntegerLiteral); ok {
			// Fixed-size array: [N]T
			return &ArrayType{
				Length:      intLit.Value,
				IsSlice:     false,
				IsSpan:      false,
				ElementType: elementType,
			}
		} else if ident, ok := indexExpr.Index.(*ast.Identifier); ok {
			if ident.Value == "*" {
				// Span type: [*]T
				return &ArrayType{
					Length:      -1,
					IsSlice:     false,
					IsSpan:      true,
					ElementType: elementType,
				}
			} else if ident.Value == "" {
				// Slice type: []T (empty identifier means slice)
				return &ArrayType{
					Length:      -1,
					IsSlice:     true,
					IsSpan:      false,
					ElementType: elementType,
				}
			}
		} else if indexExpr.Left == nil {
			// Legacy: Slice type: []T (represented as IndexExpression with nil left, index is the element type)
			elementType := tc.parseTypeExpression(indexExpr.Index)
			if elementType == nil {
				return nil
			}
			return &ArrayType{
				Length:      -1,
				IsSlice:     true,
				IsSpan:      false,
				ElementType: elementType,
			}
		}
	}

	// Handle record types: { field: Type, ... }
	if recordLit, ok := expr.(*ast.RecordLiteral); ok {
		fields := make(map[string]Type)
		for name, fieldExpr := range recordLit.Fields {
			// In a type annotation, fieldExpr should be a type expression
			fieldType := tc.parseTypeExpression(fieldExpr)
			if fieldType == nil {
				return nil
			}
			fields[name] = fieldType
		}
		row := ""
		if recordLit.Extension != nil {
			row = recordLit.Extension.Value
		}
		return &RecordType{Fields: fields, Open: recordLit.Extension != nil, Row: row}
	}

	// Handle function types: fn(Type1, Type2) -> Type3
	// This would require the parser to represent function types as FunctionLiteral
	// For now, function types in annotations are not fully supported

	return nil
}

// collectIntersectionTypes recursively collects all types in an intersection expression
// This is a helper that avoids infinite recursion by not calling parseTypeExpression
// for intersection expressions - it only calls it for non-intersection base types
func (tc *TypeChecker) collectIntersectionTypes(expr ast.Expression, types *[]Type) {
	if infixExpr, ok := expr.(*ast.InfixExpression); ok && infixExpr.Operator == "&" {
		// Recursively collect from left and right
		tc.collectIntersectionTypes(infixExpr.Left, types)
		tc.collectIntersectionTypes(infixExpr.Right, types)
	} else {
		// Base case: parse the type (this won't recurse into intersections since
		// we've already handled the & operator case in parseTypeExpression)
		typ := tc.parseTypeExpressionNonIntersection(expr)
		if typ != nil {
			*types = append(*types, typ)
		}
	}
}

// parseTypeExpressionNonIntersection parses a type expression but stops at intersections
// This is used by collectIntersectionTypes to avoid infinite recursion
func (tc *TypeChecker) parseTypeExpressionNonIntersection(expr ast.Expression) Type {
	// Don't handle intersections here - that's done by the caller
	if infix, ok := expr.(*ast.InfixExpression); ok && infix.Operator == "&" {
		// This shouldn't happen if called correctly, but handle gracefully
		return nil
	}

	// Record-template applications (Ring[u8, 16]): typechecker/mono.go.
	if indexExpr, ok := expr.(*ast.IndexExpression); ok {
		if instantiated, isTemplate := tc.resolveRecordTemplateApplication(indexExpr); isTemplate {
			return instantiated
		}
	}

	// Handle all other type expressions (same as parseTypeExpression but without intersection handling)
	// Library-qualified types (c.Int32, ...): docs/spec/92-ffi.md.
	if ident, ok := expr.(*ast.Identifier); ok {
		if libraryType, isLibrary := tc.libraryQualifiedType(ident); isLibrary {
			return libraryType
		}
		// Check if it's a primitive type
		switch ident.Value {
		case "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "f32", "f64":
			return &PrimitiveType{Name: ident.Value}
		case "int", "uint", "ptr", "uptr":
			// Platform-dependent types
			return &PrimitiveType{Name: ident.Value}
		case "byte":
			return &PrimitiveType{Name: "u8"}
		case "rune":
			// rune is the canonical refined u32 (docs/spec/70-strings.md section 9)
			return &PrimitiveType{Name: "u32"}
		case "string":
			return &StringType{}
		case "Bool":
			return &BoolType{}
		case "()":
			return &UnitType{}
		case "never":
			return &NeverType{}
		case "any":
			return &AnyType{}
		case "Atomic":
			tc.addError(ident, "Atomic requires exactly one carrier: Atomic[u8|u16|u32|u64|i8|i16|i32|i64]")
			return nil
		default:
			// Check if it's a type alias in the environment
			if aliasType, ok := tc.env.GetType(ident.Value); ok {
				return aliasType
			}
			// Assume it's an ADT type
			return &ADTType{Name: ident.Value}
		}
	}

	if fnExpr, ok := expr.(*ast.FunctionTypeExpression); ok {
		params := make([]Type, 0, len(fnExpr.Parameters))
		for _, param := range fnExpr.Parameters {
			paramType := tc.parseTypeExpressionNonIntersection(param)
			if paramType == nil {
				return nil
			}
			params = append(params, paramType)
		}
		var returnType Type = &UnitType{}
		if fnExpr.Return != nil {
			returnType = tc.parseTypeExpressionNonIntersection(fnExpr.Return)
			if returnType == nil {
				return nil
			}
		}
		return &FunctionType{Parameters: params, ReturnType: returnType}
	}

	// Handle array types: [N]T or []T
	if indexExpr, ok := expr.(*ast.IndexExpression); ok {
		// Phantom-encoded strings: Str[Utf8] etc. (docs/spec/70-strings.md).
		if strType := tc.parseStrEncodingType(indexExpr); strType != nil {
			return strType
		}
		elementType := tc.parseTypeExpressionNonIntersection(indexExpr.Left)
		if elementType == nil {
			return nil
		}

		if intLit, ok := indexExpr.Index.(*ast.IntegerLiteral); ok {
			// Fixed-size array: [N]T
			return &ArrayType{
				Length:      intLit.Value,
				IsSlice:     false,
				IsSpan:      false,
				ElementType: elementType,
			}
		} else if ident, ok := indexExpr.Index.(*ast.Identifier); ok {
			if ident.Value == "*" {
				// Span type: [*]T
				return &ArrayType{
					Length:      -1,
					IsSlice:     false,
					IsSpan:      true,
					ElementType: elementType,
				}
			} else if ident.Value == "" {
				// Slice type: []T
				return &ArrayType{
					Length:      -1,
					IsSlice:     true,
					IsSpan:      false,
					ElementType: elementType,
				}
			}
		} else if indexExpr.Left == nil {
			// Legacy: Slice type: []T
			elementType := tc.parseTypeExpressionNonIntersection(indexExpr.Index)
			if elementType == nil {
				return nil
			}
			return &ArrayType{
				Length:      -1,
				IsSlice:     true,
				IsSpan:      false,
				ElementType: elementType,
			}
		}
	}

	// Handle record types: { field: Type, ... }
	if recordLit, ok := expr.(*ast.RecordLiteral); ok {
		fields := make(map[string]Type)
		for name, fieldExpr := range recordLit.Fields {
			fieldType := tc.parseTypeExpressionNonIntersection(fieldExpr)
			if fieldType == nil {
				return nil
			}
			fields[name] = fieldType
		}
		row := ""
		if recordLit.Extension != nil {
			row = recordLit.Extension.Value
		}
		return &RecordType{Fields: fields, Open: recordLit.Extension != nil, Row: row}
	}

	return nil
}

// implementsIntersection checks if a type implements all interfaces in an intersection type
// This is used when checking intersection constraints: T: A & B & C
func (tc *TypeChecker) implementsIntersection(concreteType Type, intersection *IntersectionType) bool {
	for _, requiredType := range intersection.Types {
		if !tc.implementsInterface(concreteType, requiredType) {
			return false
		}
	}
	return true
}

// normalizeIntersectionToRecord normalizes an IntersectionType to a single RecordType
// by merging all record types in the intersection
func (tc *TypeChecker) normalizeIntersectionToRecord(intersection *IntersectionType) *RecordType {
	mergedFields := make(map[string]Type)

	for _, typ := range intersection.Types {
		// If it's a record type, merge its fields
		if recordType, ok := typ.(*RecordType); ok {
			for fieldName, fieldType := range recordType.Fields {
				// Check for conflicts
				if existingType, exists := mergedFields[fieldName]; exists {
					if !existingType.Equals(fieldType) {
						tc.addError(nil, "intersection type: field %s has conflicting types %s and %s", fieldName, existingType, fieldType)
						return nil
					}
				} else {
					mergedFields[fieldName] = fieldType
				}
			}
		} else if adtType, ok := typ.(*ADTType); ok {
			// If it's an ADT type, try to get its record type from the environment
			// Look up the type in the environment - it should be stored as a RecordType
			if namedType, ok := tc.env.GetType(adtType.Name); ok {
				if recordType, ok := namedType.(*RecordType); ok {
					for fieldName, fieldType := range recordType.Fields {
						if existingType, exists := mergedFields[fieldName]; exists {
							if !existingType.Equals(fieldType) {
								tc.addError(nil, "intersection type: field %s has conflicting types %s and %s", fieldName, existingType, fieldType)
								return nil
							}
						} else {
							mergedFields[fieldName] = fieldType
						}
					}
				}
			}
		} else {
			// Non-record type in intersection - this is an error for type definitions
			tc.addError(nil, "intersection type contains non-record type %s", typ)
			return nil
		}
	}

	return &RecordType{Fields: mergedFields}
}

// checkIntersectionConstraint checks if a type satisfies an intersection constraint
// Used when checking qualified types with intersection constraints
func (tc *TypeChecker) checkIntersectionConstraint(concreteType Type, constraintExpr ast.Expression) bool {
	// Parse the constraint expression to get intersection type
	constraintType := tc.parseTypeExpression(constraintExpr)
	if constraintType == nil {
		return false
	}

	// If it's an intersection, check all components
	if intersection, ok := constraintType.(*IntersectionType); ok {
		return tc.implementsIntersection(concreteType, intersection)
	}

	// Single interface constraint
	return tc.implementsInterface(concreteType, constraintType)
}

// implementsInterface checks if a concrete type implements an interface
// This is a structural check: the type must have methods matching the interface
func (tc *TypeChecker) implementsInterface(concreteType Type, interfaceType Type) bool {
	// If it's the same type, return true
	if concreteType.Equals(interfaceType) {
		return true
	}

	// Semantic record shapes are static field requirements. Candidate order,
	// extra fields, and runtime representation are intentionally irrelevant.
	if requiredRecord, ok := interfaceType.(*RecordType); ok {
		candidateRecord, ok := tc.asRecordType(concreteType)
		return ok && recordSatisfiesShape(candidateRecord, requiredRecord)
	}

	// Otherwise this is the existing method-interface relation.
	iface, ok := interfaceType.(*InterfaceType)
	if !ok {
		// Not an interface type - can't implement it
		return false
	}

	// Get the concrete type name for method lookup
	var concreteTypeName string
	switch t := concreteType.(type) {
	case *ADTType:
		concreteTypeName = t.Name
	case *PrimitiveType:
		// Primitive types don't have methods
		return false
	case *RecordType:
		// Record types don't have methods (yet)
		return false
	default:
		// Unknown type - can't implement interface
		return false
	}

	// Check that the concrete type has all methods required by the interface
	for methodName, requiredMethodType := range iface.Methods {
		// Look up method on concrete type: TypeName::methodName
		methodKey := fmt.Sprintf("%s::%s", concreteTypeName, methodName)
		methodScheme, ok := tc.env.Get(methodKey)
		if !ok {
			// Method not found - type doesn't implement interface
			return false
		}

		// Instantiate the method scheme to get the actual method type
		unifier := NewUnifier()
		methodType := Instantiate(methodScheme, unifier)
		concreteMethodType, ok := methodType.(*FunctionType)
		if !ok {
			// Method is not a function type - invalid
			return false
		}

		// Check that return types match
		if !concreteMethodType.ReturnType.Equals(requiredMethodType.ReturnType) {
			// Return type mismatch
			return false
		}

		// Check parameter types match
		if len(concreteMethodType.Parameters) != len(requiredMethodType.Parameters) {
			// Parameter count mismatch
			return false
		}
		for i, requiredParam := range requiredMethodType.Parameters {
			concreteParam := concreteMethodType.Parameters[i]
			// Parameters must match exactly (no subtyping for parameters)
			if !concreteParam.Equals(requiredParam) {
				return false
			}
		}
	}

	// All required methods are present with matching signatures
	return true
}

// checkFunctionConstraints checks that inferred type arguments satisfy function constraints
// This is called after type checking a function call to ensure constraints are satisfied
//
// Note: Full constraint checking in HM-style inference requires:
// 1. Unifying parameter types with argument types to get type variable bindings
// 2. Tracking which fresh type vars map to which original type var names
// 3. Checking that bound type variables satisfy their constraints
//
// For now, we do a simplified check: if we can directly match parameter types (that are type vars)
// with argument types, we check constraints. This works for simple cases but may miss
// constraints on type vars that appear only in return types or are inferred indirectly.
func (tc *TypeChecker) checkFunctionConstraints(scheme *TypeScheme, fnType *FunctionType, argTypes []Type, expr ast.Node) {
	if len(scheme.Constraints) == 0 {
		return // No constraints to check
	}

	// Try to infer type variable bindings from parameter-argument pairs
	// This is a simplified approach - full HM inference would use unification
	typeVarBindings := make(map[string]Type)
	unifier := NewUnifier()

	for i, paramType := range fnType.Parameters {
		if i >= len(argTypes) {
			continue
		}
		argType := argTypes[i]
		if argType == nil {
			continue
		}

		// Try to unify parameter type with argument type
		// This will give us bindings for type variables
		sub := unifier.Unify(paramType, argType)
		if sub != nil {
			// Apply substitution to see what type variables got bound
			// For now, we'll check if paramType is directly a TypeVar
			if typeVar, ok := paramType.(*TypeVar); ok {
				// Check if this type variable name has constraints
				for _, constraint := range scheme.Constraints {
					if constraint.Var == typeVar.Name {
						// Check that the argument type satisfies the constraint
						if !tc.SatisfiesConstraint(argType, constraint) {
							tc.addError(expr, "function call: type argument %s (inferred as %s) does not satisfy constraint: %s",
								typeVar.Name, argType, constraint)
						}
					}
				}
				typeVarBindings[typeVar.Name] = argType
			}
		}
	}

	// Check all constraints that we can verify with direct bindings
	for _, constraint := range scheme.Constraints {
		if concreteType, ok := typeVarBindings[constraint.Var]; ok {
			if !tc.SatisfiesConstraint(concreteType, constraint) {
				tc.addError(expr, "function call: type argument %s (inferred as %s) does not satisfy constraint: %s",
					constraint.Var, concreteType, constraint)
			}
		}
		// Note: Constraints on type variables that appear only in return types or are inferred
		// indirectly through unification are not checked here. Full constraint checking would
		// require tracking the full substitution mapping from instantiation through unification.
	}
}

// SatisfiesConstraint checks if a concrete type satisfies an interface constraint
// This is used when instantiating a polymorphic function with interface constraints
func (tc *TypeChecker) SatisfiesConstraint(concreteType Type, constraint Constraint) bool {
	// For each required interface, check if the concrete type implements it
	for _, ifaceName := range constraint.Interfaces {
		// Look up the interface type
		ifaceType, ok := tc.env.GetType(ifaceName)
		if !ok {
			// Interface not found - this is a type error
			tc.addError(nil, "constraint requirement %s not found", ifaceName)
			return false
		}

		// Check if concreteType implements the interface
		if !tc.implementsInterface(concreteType, ifaceType) {
			return false
		}
	}

	return true
}

// extractInterfacesFromConstraint extracts interface names from a constraint expression
// Handles both single interfaces (Identifier) and intersections (InfixExpression with &)
// This flattens intersection constraints into a list of interface names for storage in Constraint
func (tc *TypeChecker) extractInterfacesFromConstraint(expr ast.Expression) []string {
	interfaces := []string{}

	// Handle single interface: Reader
	if ident, ok := expr.(*ast.Identifier); ok {
		interfaces = append(interfaces, ident.Value)
		return interfaces
	}

	// Handle intersection: Reader & Writer & Closer
	if infix, ok := expr.(*ast.InfixExpression); ok && infix.Operator == "&" {
		// Recursively extract from left and right
		leftInterfaces := tc.extractInterfacesFromConstraint(infix.Left)
		rightInterfaces := tc.extractInterfacesFromConstraint(infix.Right)
		interfaces = append(interfaces, leftInterfaces...)
		interfaces = append(interfaces, rightInterfaces...)
		return interfaces
	}

	// Unknown constraint expression
	if node, ok := expr.(ast.Node); ok {
		tc.addError(node, "invalid constraint expression: %s", expr.String())
	} else {
		tc.addError(nil, "invalid constraint expression: %s", expr.String())
	}
	return interfaces
}

// SatisfiesIntersectionConstraint checks if a concrete type satisfies an intersection constraint
// This is used when checking constraints like T: Reader & Writer & Closer
func (tc *TypeChecker) SatisfiesIntersectionConstraint(concreteType Type, interfaces []string) bool {
	// For each required interface, check if the concrete type implements it
	for _, ifaceName := range interfaces {
		// Look up the interface type
		ifaceType, ok := tc.env.GetType(ifaceName)
		if !ok {
			// Interface not found - this is a type error
			tc.addError(nil, "constraint requirement %s not found", ifaceName)
			return false
		}

		// Check if concreteType implements the interface
		if !tc.implementsInterface(concreteType, ifaceType) {
			return false
		}
	}

	return true
}

// getLiteralType extracts the type of a literal object
func (tc *TypeChecker) getLiteralType(literal object.Object) Type {
	switch lit := literal.(type) {
	case *object.Integer:
		// Infer integer type from value
		// For now, default to i32, but could be more sophisticated
		return &PrimitiveType{Name: "i32"}
	case *object.String:
		return &StringType{}
	case *object.Boolean:
		return &BoolType{}
	case *object.Record:
		// For record literals, construct a RecordType
		fields := make(map[string]Type)
		for name, fieldObj := range lit.Fields {
			fields[name] = tc.getLiteralType(fieldObj)
		}
		return &RecordType{Fields: fields}
	default:
		return nil
	}
}

// checkInterfaceType type checks an interface definition
func (tc *TypeChecker) checkInterfaceType(stmt *ast.InterfaceType) {
	// Extract type parameters
	typeVars := []string{}
	if stmt.TypeParams != nil {
		for _, tp := range stmt.TypeParams {
			typeVars = append(typeVars, tp.Name.Value)
		}
	}

	// Parse method signatures into FunctionTypes
	methods := make(map[string]*FunctionType)
	for _, method := range stmt.Methods {
		// Parse return type
		returnType := tc.parseTypeExpression(method.ReturnType)
		if returnType == nil {
			returnType = &UnitType{}
		}

		// Parse parameters
		paramTypes := []Type{}
		for _, param := range method.Parameters {
			paramType := tc.parseTypeExpression(param.Type)
			if paramType == nil {
				paramType = &UnitType{}
			}
			paramTypes = append(paramTypes, paramType)
		}

		// Create function type with full signature
		methods[method.Name.Value] = &FunctionType{
			Parameters: paramTypes,
			ReturnType: returnType,
		}
	}

	// Create interface type
	interfaceType := &InterfaceType{
		Name:    stmt.Name.Value,
		Methods: methods,
	}

	// Store in environment
	tc.env.SetType(stmt.Name.Value, interfaceType)
}

// parseRecordComposition parses record composition and flattens it into a single record type
// Example: point3: type = point2 & { z: u8 }
// Example: point3_node: type = point3 & intrusive_dlist_node[point3]
func (tc *TypeChecker) parseRecordComposition(typeName string, expr ast.Expression) *RecordType {
	// Collect all record types from the composition chain
	fields := make(map[string]Type)

	// Recursively flatten the composition
	tc.flattenRecordComposition(expr, &fields)

	return &RecordType{Fields: fields}
}

// flattenRecordComposition recursively flattens a record composition expression
// into a single set of fields, checking for duplicate field names
func (tc *TypeChecker) flattenRecordComposition(expr ast.Expression, fields *map[string]Type) {
	if infix, ok := expr.(*ast.InfixExpression); ok && infix.Operator == "&" {
		// Recursively flatten left and right
		tc.flattenRecordComposition(infix.Left, fields)
		tc.flattenRecordComposition(infix.Right, fields)
		return
	}

	// Base case: either a record literal or a type name
	if recordLit, ok := expr.(*ast.RecordLiteral); ok {
		// Parse record literal fields
		for fieldName, fieldExpr := range recordLit.Fields {
			fieldType := tc.parseTypeExpression(fieldExpr)
			if fieldType == nil {
				if node, ok := fieldExpr.(ast.Node); ok {
					tc.addError(node, "invalid field type in record composition: %s", fieldName)
				} else {
					tc.addError(recordLit, "invalid field type in record composition: %s", fieldName)
				}
				continue
			}

			// Check for duplicate field names
			if existingType, exists := (*fields)[fieldName]; exists {
				if !existingType.Equals(fieldType) {
					if node, ok := fieldExpr.(ast.Node); ok {
						tc.addError(node, "duplicate field %s in record composition with conflicting types: %s vs %s",
							fieldName, existingType, fieldType)
					} else {
						tc.addError(recordLit, "duplicate field %s in record composition with conflicting types: %s vs %s",
							fieldName, existingType, fieldType)
					}
				}
			} else {
				(*fields)[fieldName] = fieldType
			}
		}
	} else if ident, ok := expr.(*ast.Identifier); ok {
		// Look up the type name and flatten its fields
		// This should be a record type
		typeScheme, ok := tc.env.Get(ident.Value)
		if !ok {
			tc.addError(ident, "type %s not found in record composition", ident.Value)
			return
		}

		// Instantiate the type scheme
		unifier := NewUnifier()
		typ := Instantiate(typeScheme, unifier)

		// Check if it's a record type
		if recordType, ok := typ.(*RecordType); ok {
			// Merge fields from the record type
			for fieldName, fieldType := range recordType.Fields {
				// Check for duplicate field names
				if existingType, exists := (*fields)[fieldName]; exists {
					if !existingType.Equals(fieldType) {
						tc.addError(ident, "duplicate field %s in record composition with conflicting types: %s vs %s",
							fieldName, existingType, fieldType)
					}
				} else {
					(*fields)[fieldName] = fieldType
				}
			}
		} else {
			tc.addError(ident, "type %s in record composition is not a record type, got %T", ident.Value, typ)
		}
	} else {
		if node, ok := expr.(ast.Node); ok {
			tc.addError(node, "invalid expression in record composition: %T", expr)
		} else {
			tc.addError(nil, "invalid expression in record composition: %T", expr)
		}
	}
}
