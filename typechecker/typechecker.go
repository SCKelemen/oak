package typechecker

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/object"
)

// Type represents a type in the Oak type system
type Type interface {
	String() string
	Equals(other Type) bool
}

// PrimitiveType represents primitive integer types
type PrimitiveType struct {
	Name string // "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64"
}

func (t *PrimitiveType) String() string {
	return t.Name
}

func (t *PrimitiveType) Equals(other Type) bool {
	if otherPrim, ok := other.(*PrimitiveType); ok {
		return t.Name == otherPrim.Name
	}
	return false
}

// StringType represents the string type
type StringType struct{}

func (t *StringType) String() string {
	return "string"
}

func (t *StringType) Equals(other Type) bool {
	_, ok := other.(*StringType)
	return ok
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
	_, ok := other.(*UnitType)
	return ok
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
	return false
}

// NarrowedADTVariantType represents a narrowed ADT variant type
// Used for type narrowing in pattern matching (TypeScript-style)
type NarrowedADTVariantType struct {
	ADTName     string
	VariantName string
}

func (t *NarrowedADTVariantType) String() string {
	return fmt.Sprintf("%s::%s", t.ADTName, t.VariantName)
}

func (t *NarrowedADTVariantType) Equals(other Type) bool {
	if otherNarrowed, ok := other.(*NarrowedADTVariantType); ok {
		return t.ADTName == otherNarrowed.ADTName && t.VariantName == otherNarrowed.VariantName
	}
	// A narrowed variant is compatible with its parent ADT type
	if otherADT, ok := other.(*ADTType); ok {
		return t.ADTName == otherADT.Name
	}
	return false
}

// RecordType represents a record/struct type
type RecordType struct {
	Fields map[string]Type // field name -> type
}

func (t *RecordType) String() string {
	var out string
	out += "{"
	first := true
	for name, typ := range t.Fields {
		if !first {
			out += ", "
		}
		out += fmt.Sprintf("%s: %s", name, typ.String())
		first = false
	}
	out += "}"
	return out
}

func (t *RecordType) Equals(other Type) bool {
	if otherRecord, ok := other.(*RecordType); ok {
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
		typeSet := make(map[string]bool)
		for _, typ := range t.Types {
			typeSet[typ.String()] = true
		}
		for _, typ := range otherIntersection.Types {
			if !typeSet[typ.String()] {
				return false
			}
		}
		return true
	}
	return false
}

// FunctionType represents a function type
type FunctionType struct {
	Parameters []Type
	ReturnType Type
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
	errors   []string
	env      *TypeEnvironment
	adtTypes map[string]*object.ADTType // ADT type definitions
}

// TypeEnvironment stores type information for variables
// In HM-style inference, we store TypeSchemes (polymorphic types) for let-bound variables
type TypeEnvironment struct {
	store map[string]*TypeScheme // Store schemes, not monomorphic types
	outer *TypeEnvironment
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
	tc := &TypeChecker{
		errors:   []string{},
		env:      NewTypeEnvironment(),
		adtTypes: env.GetAllADTTypes(),
	}
	// Add builtin type aliases
	tc.addBuiltinTypeAliases()
	return tc
}

// addBuiltinTypeAliases adds builtin type aliases to the type environment
func (tc *TypeChecker) addBuiltinTypeAliases() {
	// byte is an alias for u8
	tc.env.SetType("byte", &PrimitiveType{Name: "u8"})
}

func (tc *TypeChecker) Errors() []string {
	return tc.errors
}

func (tc *TypeChecker) ClearErrors() {
	tc.errors = []string{}
}

func (tc *TypeChecker) addError(format string, args ...interface{}) {
	tc.errors = append(tc.errors, fmt.Sprintf("[type error] "+format, args...))
}

// CheckProgram type checks a program
func (tc *TypeChecker) CheckProgram(program *ast.Program) {
	for _, stmt := range program.Statements {
		tc.checkStatement(stmt)
	}
}

// CheckExpression type checks a single expression and returns its type
// This is useful for REPL inspection commands like :typeof()
func (tc *TypeChecker) CheckExpression(expr ast.Expression) Type {
	return tc.checkExpression(expr)
}

// checkStatement type checks a statement
func (tc *TypeChecker) checkStatement(stmt ast.Statement) {
	switch s := stmt.(type) {
	case *ast.VariableDeclaration:
		tc.checkVariableDeclaration(s)
	case *ast.AssignmentStatement:
		tc.checkAssignmentStatement(s)
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
		// Expression statements don't need type checking beyond checking the expression
		tc.checkExpression(s.Expression)
	case *ast.WhileStatement:
		tc.checkWhileStatement(s)
	case *ast.UnsafeBlock:
		tc.checkUnsafeBlock(s)
	case *ast.PackageStatement:
		// Package statements don't need type checking
		// They're just metadata
	case *ast.ImportStatement:
		// Import statements don't need type checking
		// They're just metadata
	case *ast.BlockStatement:
		// Block statements are checked as part of function bodies, while loops, etc.
		tc.checkBlockStatement(s)
	default:
		tc.addError("unknown statement type: %T", stmt)
	}
}

// checkExpression type checks an expression and returns its type
// expectedType is optional - if provided, it's used for context-based type inference (e.g., for literals)
func (tc *TypeChecker) checkExpression(expr ast.Expression, expectedType ...Type) Type {
	var expected Type
	if len(expectedType) > 0 {
		expected = expectedType[0]
	}

	switch e := expr.(type) {
	case *ast.IntegerLiteral:
		// Integer literals: use context-based inference if expected type is provided
		if expected != nil {
			if primType, ok := expected.(*PrimitiveType); ok {
				// Check if literal fits in the expected primitive type
				if tc.literalFitsInType(e.Value, primType.Name) {
					return primType
				}
				// Literal doesn't fit - fall through to default inference
			}
		}
		// No context: infer the smallest type that fits the literal
		// Prefer unsigned types for non-negative values
		if e.Value >= 0 {
			if e.Value <= 255 {
				return &PrimitiveType{Name: "u8"}
			} else if e.Value <= 65535 {
				return &PrimitiveType{Name: "u16"}
			} else if e.Value <= 4294967295 {
				return &PrimitiveType{Name: "u32"}
			} else {
				return &PrimitiveType{Name: "u64"}
			}
		} else {
			// Negative values: use signed types
			if e.Value >= -128 && e.Value <= 127 {
				return &PrimitiveType{Name: "i8"}
			} else if e.Value >= -32768 && e.Value <= 32767 {
				return &PrimitiveType{Name: "i16"}
			} else if e.Value >= -2147483648 && e.Value <= 2147483647 {
				return &PrimitiveType{Name: "i32"}
			} else {
				return &PrimitiveType{Name: "i64"}
			}
		}
	case *ast.StringLiteral:
		return &StringType{}
	case *ast.Boolean:
		return &BoolType{}
	case *ast.Identifier:
		return tc.checkIdentifier(e)
	case *ast.PrefixExpression:
		return tc.checkPrefixExpression(e)
	case *ast.InfixExpression:
		return tc.checkInfixExpression(e, expected)
	case *ast.FunctionLiteral:
		return tc.checkFunctionLiteral(e)
	case *ast.InvocationExpression:
		return tc.checkInvocationExpression(e)
	case *ast.MatchExpression:
		return tc.checkMatchExpression(e)
	case *ast.VariantExpression:
		return tc.checkVariantExpression(e)
	case *ast.RecordLiteral:
		return tc.checkRecordLiteral(e, expected)
	case *ast.IndexExpression:
		return tc.checkIndexExpression(e)
	case *ast.ArrayLiteral:
		return tc.checkArrayLiteral(e)
	case nil:
		// Nil expression - likely a parser error, but don't crash
		tc.addError("nil expression encountered (parser error)")
		return nil
	default:
		tc.addError("unknown expression type: %T", expr)
		return nil
	}
}

// Helper functions for type checking specific expression types
func (tc *TypeChecker) checkIdentifier(ident *ast.Identifier) Type {
	scheme, ok := tc.env.Get(ident.Value)
	if !ok {
		tc.addError("undefined variable: %s", ident.Value)
		return nil
	}
	// Instantiate the scheme to get a fresh type
	unifier := NewUnifier()
	return Instantiate(scheme, unifier)
}

func (tc *TypeChecker) checkPrefixExpression(expr *ast.PrefixExpression) Type {
	rightType := tc.checkExpression(expr.Right)
	if rightType == nil {
		return nil
	}

	switch expr.Operator {
	case "!":
		if !rightType.Equals(&BoolType{}) {
			tc.addError("operator ! requires bool, got %s", rightType)
			return nil
		}
		return &BoolType{}
	case "-":
		// Negation: promote unsigned to signed, or keep signed
		if prim, ok := rightType.(*PrimitiveType); ok {
			if prim.Name[0] == 'i' { // signed integer
				return rightType
			} else if prim.Name[0] == 'u' {
				// Unsigned: promote to corresponding signed type
				// u8 -> i8, u16 -> i16, u32 -> i32, u64 -> i64
				signedName := "i" + prim.Name[1:]
				return &PrimitiveType{Name: signedName}
			}
		}
		tc.addError("operator - requires integer type, got %s", rightType)
		return nil
	default:
		tc.addError("unknown prefix operator: %s", expr.Operator)
		return nil
	}
}

func (tc *TypeChecker) checkInfixExpression(expr *ast.InfixExpression, expectedType ...Type) Type {
	var expected Type
	if len(expectedType) > 0 {
		expected = expectedType[0]
	}

	leftType := tc.checkExpression(expr.Left)
	// For right side, if expected type is numeric and we're doing arithmetic,
	// use it for context-based inference of literals
	var rightExpected Type
	if expected != nil {
		if prim, ok := expected.(*PrimitiveType); ok {
			if tc.isNumericType(prim) {
				rightExpected = expected
			}
		}
	}
	rightType := tc.checkExpression(expr.Right, rightExpected)
	if leftType == nil || rightType == nil {
		return nil
	}

	switch expr.Operator {
	case "+":
		// Addition: numeric + numeric, or string + string
		if leftType.Equals(&StringType{}) && rightType.Equals(&StringType{}) {
			return &StringType{}
		}
		if tc.isNumericType(leftType) && tc.isNumericType(rightType) {
			return tc.promoteNumericTypes(leftType, rightType)
		}
		tc.addError("operator + requires numeric types or strings, got %s and %s", leftType, rightType)
		return nil
	case "-", "*", "/":
		// Arithmetic operators require numeric types
		if !tc.isNumericType(leftType) || !tc.isNumericType(rightType) {
			tc.addError("operator %s requires numeric types, got %s and %s", expr.Operator, leftType, rightType)
			return nil
		}
		return tc.promoteNumericTypes(leftType, rightType)
	case "==", "!=":
		// Equality operators work on compatible types
		if !tc.areCompatibleTypes(leftType, rightType) {
			tc.addError("operator %s requires compatible types, got %s and %s", expr.Operator, leftType, rightType)
			return nil
		}
		return &BoolType{}
	case "<", ">", "<=", ">=":
		// Comparison operators require numeric types
		if !tc.isNumericType(leftType) || !tc.isNumericType(rightType) {
			tc.addError("operator %s requires numeric types, got %s and %s", expr.Operator, leftType, rightType)
			return nil
		}
		return &BoolType{}
	default:
		tc.addError("unknown infix operator: %s", expr.Operator)
		return nil
	}
}

func (tc *TypeChecker) isNumericType(typ Type) bool {
	if prim, ok := typ.(*PrimitiveType); ok {
		return prim.Name[0] == 'i' || prim.Name[0] == 'u'
	}
	return false
}

// promoteNumericTypes returns the wider of two numeric types
// Implements widening conversions: u8 -> u16 -> u32 -> u64, i8 -> i16 -> i32 -> i64
// No implicit conversion between signed and unsigned
func (tc *TypeChecker) promoteNumericTypes(left, right Type) Type {
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
		tc.addError("cannot mix signed and unsigned types: %s and %s", left, right)
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

	// Numeric types can be compared (with coercion)
	if tc.isNumericType(left) && tc.isNumericType(right) {
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

func (tc *TypeChecker) checkFunctionLiteral(fn *ast.FunctionLiteral) Type {
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

func (tc *TypeChecker) checkInvocationExpression(expr *ast.InvocationExpression) Type {
	// Check if this is a primitive type constructor: u32(x), u64(y), etc.
	if ident, ok := expr.Function.(*ast.Identifier); ok {
		if constructorType := tc.checkPrimitiveConstructor(ident.Value, expr.Arguments); constructorType != nil {
			return constructorType
		}
		// Check if this is a narrowing function: u8_trunc_u32(x), u8_checked_u32(x), etc.
		if narrowingType := tc.checkNarrowingFunction(ident.Value, expr.Arguments); narrowingType != nil {
			return narrowingType
		}
		// Check if this is a Castable constructor: string(x), byte(x), etc.
		if castableType := tc.checkCastableConstructor(ident.Value, expr.Arguments); castableType != nil {
			return castableType
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
	funcType := tc.checkExpression(expr.Function)
	if funcType == nil {
		return nil
	}

	fnType, ok := funcType.(*FunctionType)
	if !ok {
		tc.addError("attempting to call non-function type: %s", funcType)
		return nil
	}

	// Check argument count
	if len(expr.Arguments) != len(fnType.Parameters) {
		tc.addError("function expects %d arguments, got %d", len(fnType.Parameters), len(expr.Arguments))
		return nil
	}

	// Check argument types (with coercion)
	// Pass expected type for context-based inference (e.g., for integer literals)
	for i, arg := range expr.Arguments {
		expectedType := fnType.Parameters[i]
		argType := tc.checkExpression(arg, expectedType)
		if argType == nil {
			continue
		}
		if !tc.isAssignable(argType, expectedType) {
			tc.addError("argument %d: expected %s, got %s", i+1, expectedType, argType)
		}
	}

	return fnType.ReturnType
}

// checkPrimitiveConstructor checks if an invocation is a primitive type constructor
// (e.g., u32(x), u64(y)) and returns the target type if valid
func (tc *TypeChecker) checkPrimitiveConstructor(typeName string, args []ast.Expression) Type {
	// Check if it's a primitive type name
	primitiveTypes := map[string]bool{
		"u8": true, "u16": true, "u32": true, "u64": true,
		"i8": true, "i16": true, "i32": true, "i64": true,
	}
	if !primitiveTypes[typeName] {
		return nil // Not a primitive constructor
	}

	// Constructors take exactly one argument
	if len(args) != 1 {
		tc.addError("primitive constructor %s expects 1 argument, got %d", typeName, len(args))
		return nil
	}

	// Check if argument is an integer literal (untyped)
	if intLit, ok := args[0].(*ast.IntegerLiteral); ok {
		// Check if literal fits in target type
		if !tc.literalFitsInType(intLit.Value, typeName) {
			tc.addError("literal %d does not fit in type %s", intLit.Value, typeName)
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

	// Check if argument is a primitive type
	argPrim, ok := argType.(*PrimitiveType)
	if !ok {
		tc.addError("primitive constructor %s requires a primitive integer argument, got %s", typeName, argType)
		return nil
	}

	// Check if widening is valid (same signedness, source is narrower or equal)
	if !tc.isValidWidening(argPrim.Name, typeName) {
		tc.addError("cannot widen %s to %s (must be same signedness and source must be narrower or equal)", argPrim.Name, typeName)
		return nil
	}

	// Return the target type
	return &PrimitiveType{Name: typeName}
}

// literalFitsInType checks if an integer literal value fits in the given primitive type
func (tc *TypeChecker) literalFitsInType(value int64, typeName string) bool {
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
	default:
		return false
	}
}

// isValidWidening checks if widening from sourceType to targetType is valid
// Widening is valid if:
// - Both types have the same signedness (both signed or both unsigned)
// - Source type is narrower than or equal to target type
func (tc *TypeChecker) isValidWidening(sourceType, targetType string) bool {
	// Check signedness
	sourceSigned := sourceType[0] == 'i'
	targetSigned := targetType[0] == 'i'
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
func (tc *TypeChecker) getTypeWidth(typeName string) int {
	switch typeName {
	case "u8", "i8":
		return 8
	case "u16", "i16":
		return 16
	case "u32", "i32":
		return 32
	case "u64", "i64":
		return 64
	default:
		return 0
	}
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
	if !primitiveTypes[targetType] || !primitiveTypes[sourceType] {
		return nil
	}

	// Validate operation
	validOperations := map[string]bool{
		"trunc":      true,
		"checked":    true,
		"saturating": true,
	}
	if !validOperations[operation] {
		return nil
	}

	// Narrowing functions take exactly one argument
	if len(args) != 1 {
		tc.addError("narrowing function %s expects 1 argument, got %d", funcName, len(args))
		return nil
	}

	// Check that narrowing is valid (source must be wider than target, same signedness)
	if !tc.isValidNarrowing(sourceType, targetType) {
		tc.addError("invalid narrowing: cannot narrow %s to %s (must be same signedness and source must be wider)", sourceType, targetType)
		return nil
	}

	// Check argument type matches source type
	argType := tc.checkExpression(args[0])
	if argType == nil {
		return nil
	}

	argPrim, ok := argType.(*PrimitiveType)
	if !ok || argPrim.Name != sourceType {
		tc.addError("narrowing function %s expects argument of type %s, got %s", funcName, sourceType, argType)
		return nil
	}

	// Return type depends on operation
	if operation == "checked" {
		// Checked operations return Result[target, Overflow]
		// Create target type
		targetPrimType := &PrimitiveType{Name: targetType}

		// Create Overflow error type (ADT type)
		overflowType := &ADTType{Name: "Overflow"}

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
		tc.addError("Castable constructor %s expects 1 argument, got %d", typeName, len(args))
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
		tc.addError("type %s does not implement Castable[%s] (missing into() method)", argType, typeName)
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
		tc.addError("method calls only supported for ADT types, got %s", recvType)
		return nil
	}

	// Look up method: TypeName::methodName
	methodKey := fmt.Sprintf("%s::%s", receiverTypeName, methodName)
	methodScheme, ok := tc.env.Get(methodKey)
	if !ok {
		tc.addError("method %s not found for type %s", methodName, receiverTypeName)
		return nil
	}

	// Instantiate the method scheme
	unifier := NewUnifier()
	methodType := Instantiate(methodScheme, unifier)
	fnType, ok := methodType.(*FunctionType)
	if !ok {
		tc.addError("method %s is not a function type", methodName)
		return nil
	}

	// Check argument count (method has receiver as first parameter, so args should match parameters)
	if len(args) != len(fnType.Parameters) {
		tc.addError("method %s expects %d arguments, got %d", methodName, len(fnType.Parameters), len(args))
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
			tc.addError("method %s argument %d: expected %s, got %s", methodName, i+1, expectedType, argType)
		}
	}

	return fnType.ReturnType
}

func (tc *TypeChecker) checkMatchExpression(expr *ast.MatchExpression) Type {
	scrutineeType := tc.checkExpression(expr.Scrutinee)
	if scrutineeType == nil {
		return nil
	}

	// Check that match expression has at least one arm
	if len(expr.Arms) == 0 {
		tc.addError("match expression must have at least one arm")
		return nil
	}

	// Type check each arm and collect types for lattice join
	armTypes := []Type{}
	for _, arm := range expr.Arms {
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

		// Type check arm body expression with narrowed type context
		armType := tc.checkExpression(arm.Body)
		if armType == nil {
			// Unreachable or error - use never type
			armType = &NeverType{}
		}
		armTypes = append(armTypes, armType)

		// Restore environment
		tc.env = oldEnv
	}

	// Compute join of all arm types (lattice-based)
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
			tc.addError("match expression has branches with incompatible types. Use explicit 'any' return type if intentional.")
		}
	}

	// Check exhaustiveness for ADT types
	if adtType, ok := scrutineeType.(*ADTType); ok {
		tc.checkExhaustiveness(expr.Arms, adtType)
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
		// Bind the variable in the environment
		tc.env.SetType(p.Name.Value, expectedType)
		return expectedType
	case *ast.LiteralPattern:
		// Check that literal matches expected type
		litType := tc.checkExpression(p.Value)
		if litType == nil {
			return nil
		}
		if !litType.Equals(expectedType) {
			tc.addError("pattern literal type %s does not match expected type %s", litType, expectedType)
			return nil
		}
		return expectedType
	case *ast.VariantPattern:
		// Check that variant belongs to expected ADT type
		if adtType, ok := expectedType.(*ADTType); ok {
			// Verify variant exists in ADT
			if adtDef, ok := tc.adtTypes[adtType.Name]; ok {
				variantName := p.Variant.Value
				found := false
				for _, variant := range adtDef.Variants {
					if variant.Name == variantName {
						found = true
						// Check payload type if variant has one
						if p.Payload != nil {
							if variant.Payload == "" {
								tc.addError("variant %s of ADT %s does not accept a payload", variantName, adtType.Name)
								return nil
							}
							// Check payload type matches variant's expected payload type
							expectedPayloadType := tc.parseTypeExpression(&ast.Identifier{Value: variant.Payload})
							if expectedPayloadType == nil {
								return nil
							}
							// For variant patterns, payload is a pattern, so we check it matches the expected type
							payloadType := tc.checkPattern(p.Payload, expectedPayloadType)
							if payloadType == nil {
								return nil
							}
						} else if variant.Payload != "" {
							tc.addError("variant %s of ADT %s requires a payload of type %s", variantName, adtType.Name, variant.Payload)
							return nil
						}
						// Return narrowed variant type for type narrowing
						return &NarrowedADTVariantType{
							ADTName:     adtType.Name,
							VariantName: variantName,
						}
					}
				}
				if !found {
					tc.addError("variant %s not found in ADT %s", variantName, adtType.Name)
					return nil
				}
			}
			return expectedType
		}
		// Handle matching on primitive types with ADT literal tags (type narrowing)
		// If matching a primitive literal against an ADT with literal tags, narrow to the variant
		if tc.isNumericType(expectedType) || expectedType.Equals(&StringType{}) {
			// Check if any ADT has a variant with a matching literal tag
			variantName := p.Variant.Value
			for adtName, adtDef := range tc.adtTypes {
				for _, variant := range adtDef.Variants {
					if variant.Name == variantName && variant.Literal != nil {
						// Check if literal type matches expected type
						litType := tc.getLiteralType(variant.Literal)
						if litType != nil && litType.Equals(expectedType) {
							// This is a valid narrowing: primitive -> ADT variant
							return &NarrowedADTVariantType{
								ADTName:     adtName,
								VariantName: variantName,
							}
						}
					}
				}
			}
		}
		tc.addError("variant pattern used on non-ADT type: %s", expectedType)
		return nil
	default:
		tc.addError("unknown pattern type: %T", pattern)
		return nil
	}
}

func (tc *TypeChecker) checkVariantExpression(expr *ast.VariantExpression) Type {
	var adtTypeName string

	if expr.TypeName != nil {
		// Type::Variant form
		adtTypeName = expr.TypeName.Value
	} else {
		// Bare variant (.Variant) - need to infer from context
		// For now, we'll need to search for ADT types that contain this variant
		// This is a limitation - we'd need better type inference
		variantName := expr.Variant.Value
		for name, adtDef := range tc.adtTypes {
			for _, variant := range adtDef.Variants {
				if variant.Name == variantName {
					adtTypeName = name
					break
				}
			}
			if adtTypeName != "" {
				break
			}
		}
		if adtTypeName == "" {
			tc.addError("cannot infer ADT type for variant .%s", variantName)
			return nil
		}
	}

	// Verify variant exists in ADT
	if adtDef, ok := tc.adtTypes[adtTypeName]; ok {
		variantName := expr.Variant.Value
		found := false
		for _, variant := range adtDef.Variants {
			if variant.Name == variantName {
				found = true
				// Check payload if provided
				if expr.Payload != nil {
					if variant.Payload == "" {
						tc.addError("variant %s of ADT %s does not accept a payload", variantName, adtTypeName)
						return nil
					}
					expectedPayloadType := tc.parseTypeExpression(&ast.Identifier{Value: variant.Payload})
					actualPayloadType := tc.checkExpression(expr.Payload)
					if actualPayloadType == nil {
						return nil
					}
					if !actualPayloadType.Equals(expectedPayloadType) {
						tc.addError("variant %s payload: expected %s, got %s", variantName, expectedPayloadType, actualPayloadType)
						return nil
					}
				} else if variant.Payload != "" {
					tc.addError("variant %s of ADT %s requires a payload of type %s", variantName, adtTypeName, variant.Payload)
					return nil
				}
				break
			}
		}
		if !found {
			tc.addError("variant %s not found in ADT %s", variantName, adtTypeName)
			return nil
		}
		return &ADTType{Name: adtTypeName}
	}

	tc.addError("ADT type %s not found", adtTypeName)
	return nil
}

func (tc *TypeChecker) checkRecordLiteral(expr *ast.RecordLiteral, expectedType ...Type) Type {
	// If expected type is a RecordType, use it for context-based inference
	var expectedRecord *RecordType
	if len(expectedType) > 0 {
		if recType, ok := expectedType[0].(*RecordType); ok {
			expectedRecord = recType
		}
	}

	fields := make(map[string]Type)
	for name, fieldExpr := range expr.Fields {
		// Use expected field type for context-based inference
		var expectedFieldType Type
		if expectedRecord != nil {
			if fieldType, ok := expectedRecord.Fields[name]; ok {
				expectedFieldType = fieldType
			}
		}
		fieldType := tc.checkExpression(fieldExpr, expectedFieldType)
		if fieldType == nil {
			continue
		}
		// Check for duplicate field names
		if _, exists := fields[name]; exists {
			tc.addError("record literal: duplicate field name %s", name)
			continue
		}
		fields[name] = fieldType
	}
	return &RecordType{Fields: fields}
}

func (tc *TypeChecker) checkIndexExpression(expr *ast.IndexExpression) Type {
	leftType := tc.checkExpression(expr.Left)
	if leftType == nil {
		return nil
	}

	// Handle record field access: record.field
	if recordType, ok := leftType.(*RecordType); ok {
		if ident, ok := expr.Index.(*ast.Identifier); ok {
			fieldName := ident.Value
			if fieldType, ok := recordType.Fields[fieldName]; ok {
				return fieldType
			}
			tc.addError("field %s not found in record type %s", fieldName, recordType)
			return nil
		}
		tc.addError("record field access requires identifier, got %T", expr.Index)
		return nil
	}

	// Handle array indexing: array[index]
	if arrayType, ok := leftType.(*ArrayType); ok {
		indexType := tc.checkExpression(expr.Index)
		if indexType == nil {
			return nil
		}
		// Index must be an integer type
		if !tc.isNumericType(indexType) {
			tc.addError("array index must be numeric type, got %s", indexType)
			return nil
		}
		// Index should ideally be unsigned, but we allow any numeric for now
		// In the future, we could require u32 specifically for array indices
		return arrayType.ElementType
	}

	tc.addError("index expression not supported for type: %s", leftType)
	return nil
}

func (tc *TypeChecker) checkVariableDeclaration(stmt *ast.VariableDeclaration) {
	// Check if variable already exists
	varScheme, exists := tc.env.Get(stmt.Name.Value)
	if exists {
		// Variable already exists - this is actually an assignment, not a declaration
		// Only allow assignment if there's a value (x = value), not just declaration (x: type)
		if stmt.Value == nil {
			// This is a redeclaration without assignment - error
			tc.addError("variable %s already declared", stmt.Name.Value)
			return
		}
		// This is an assignment to an existing variable
		// Instantiate the scheme to get the actual type
		unifier := NewUnifier()
		varType := Instantiate(varScheme, unifier)
		// Check that assigned value matches variable type
		valueType := tc.checkExpression(stmt.Value, varType)
		if valueType != nil {
			if !tc.isAssignable(valueType, varType) {
				tc.addError("assignment: variable %s has type %s, cannot assign %s", stmt.Name.Value, varType, valueType)
			}
		}
		return
	}

	// Variable doesn't exist - check if this is a declaration without type annotation
	// If it has no type and no value, that's an error
	if stmt.Type == nil && stmt.Value == nil {
		tc.addError("variable %s: no type annotation and no initializer", stmt.Name.Value)
		return
	}

	// Variable doesn't exist - this is a declaration
	// HM-style: let-bound variables get generalized types
	if stmt.Type != nil {
		// Explicit type annotation: parse and use it
		varType := tc.parseTypeExpression(stmt.Type)
		if varType == nil {
			tc.addError("variable %s: invalid type annotation", stmt.Name.Value)
			return
		}

		// If there's an initializer, check that it matches the type (with coercion)
		// Pass expected type for context-based inference (e.g., for integer literals)
		if stmt.Value != nil {
			valueType := tc.checkExpression(stmt.Value, varType)
			if valueType != nil {
				// Use unification to check compatibility
				unifier := NewUnifier()
				sub := unifier.Unify(valueType, varType)
				if sub == nil {
					// Try assignability check as fallback
					if !tc.isAssignable(valueType, varType) {
						tc.addError("variable %s: expected type %s, got %s", stmt.Name.Value, varType, valueType)
					}
				} else {
					// Apply substitution to get the unified type
					varType = sub.Apply(varType)
				}
			}
		}

		// Generalize the type (quantify over free type variables)
		scheme := Generalize(varType, tc.env)
		tc.env.Set(stmt.Name.Value, scheme)
	} else {
		// Type inference from initializer (HM-style)
		if stmt.Value != nil {
			inferredType := tc.checkExpression(stmt.Value)
			if inferredType != nil {
				// Generalize: convert to a type scheme
				scheme := Generalize(inferredType, tc.env)
				tc.env.Set(stmt.Name.Value, scheme)
			}
		} else {
			tc.addError("variable %s: no type annotation and no initializer", stmt.Name.Value)
		}
	}
}

// isAssignable checks if a value type can be assigned to a variable type
// Allows widening conversions (u8 -> u16, etc.) but not narrowing or sign changes
func (tc *TypeChecker) isAssignable(valueType, varType Type) bool {
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
	// Assignment: x = expr
	// Rule: x must already be bound in the current scope, otherwise it's a compile-time error
	// This prevents accidental "silent declaration by typo" (e.g., cont = 1 vs count = 1)
	varScheme, ok := tc.env.Get(stmt.Name.Value)
	if !ok {
		tc.addError("undefined variable: %s", stmt.Name.Value)
		return
	}

	// Variable exists - this is a real assignment
	// Instantiate the scheme to get the actual type
	unifier := NewUnifier()
	varType := Instantiate(varScheme, unifier)

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
							tc.addError("assignment: variable %s has type %s, cannot assign %s (use %s_trunc_%s(...) or %s_checked_%s(...) for narrowing)",
								stmt.Name.Value, varType, valueType, varPrim.Name, valuePrim.Name, varPrim.Name, valuePrim.Name)
							return
						}
					}
				}
			}
			tc.addError("assignment: variable %s has type %s, cannot assign %s", stmt.Name.Value, varType, valueType)
		}
	}
}

func (tc *TypeChecker) checkFunctionStatement(stmt *ast.FunctionStatement) {
	// Extract type parameters and constraints
	typeVars := []string{}
	constraints := []Constraint{}

	if stmt.TypeParams != nil {
		for _, tp := range stmt.TypeParams {
			typeVars = append(typeVars, tp.Name.Value)

			// Extract constraint if present
			// Constraints can be single interfaces or intersections (A & B & C)
			if tp.Constraint != nil {
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

	// Create new environment for function parameters
	funcEnv := NewEnclosedTypeEnvironment(tc.env)

	// If this is a method, add receiver to the environment
	if stmt.Receiver != nil {
		receiverType := tc.parseTypeExpression(stmt.Receiver.Type)
		if receiverType == nil {
			tc.addError("method %s: invalid receiver type", stmt.Name.Value)
			return
		}
		funcEnv.SetType(stmt.Receiver.Name.Value, receiverType)
	}

	// Parse parameter types from function signature
	paramTypes := []Type{}
	for _, param := range stmt.Parameters {
		paramType := tc.parseTypeExpression(param.Type)
		if paramType == nil {
			// Default to i32 if type parsing fails
			paramType = &PrimitiveType{Name: "i32"}
		}
		paramTypes = append(paramTypes, paramType)
		funcEnv.SetType(param.Name.Value, paramType)
	}

	// Parse return type
	returnType := tc.parseTypeExpression(stmt.ReturnType)
	if returnType == nil {
		returnType = &UnitType{}
	}

	// Save current environment and switch to function environment
	oldEnv := tc.env
	tc.env = funcEnv

	// Type check function body
	bodyType := tc.checkExpression(stmt.Body)
	if bodyType == nil {
		bodyType = &UnitType{}
	}

	// Check that body type matches return type
	if !bodyType.Equals(returnType) {
		tc.addError("function %s: expected return type %s, got %s", stmt.Name.Value, returnType, bodyType)
	}

	// Restore environment
	tc.env = oldEnv

	// Store function type in environment
	funcType := &FunctionType{
		Parameters: paramTypes,
		ReturnType: returnType,
	}

	// Generalize function type to a scheme with constraints
	funcScheme := Generalize(funcType, tc.env)

	// Add type parameters and constraints to the scheme
	if len(typeVars) > 0 || len(constraints) > 0 {
		funcScheme = &TypeScheme{
			TypeVars:    typeVars,
			Constraints: constraints,
			Type:        funcScheme.Type,
		}
	}

	tc.env.Set(stmt.Name.Value, funcScheme)

	// If this is a method, also store it with TypeName::methodName key
	if stmt.Receiver != nil {
		receiverType := tc.parseTypeExpression(stmt.Receiver.Type)
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
				// This is a record type definition
				tc.checkRecordTypeDefinition(stmt.Name.Value, recordLit)
				// Store the record type in the environment
				recordType := tc.parseRecordTypeFromLiteral(recordLit)
				if recordType != nil {
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

	// ADT types are already registered in the environment
	// Verify they're well-formed
	variantNames := make(map[string]bool)

	for _, variant := range stmt.Variants {
		variantName := variant.Name.Value

		// Check for duplicate variants
		if variantNames[variantName] {
			tc.addError("ADT %s: duplicate variant %s", stmt.Name.Value, variantName)
			continue
		}
		variantNames[variantName] = true

		// Check payload type if present
		if variant.Payload != nil {
			payloadType := tc.parseTypeExpression(variant.Payload)
			if payloadType == nil {
				tc.addError("ADT %s variant %s: invalid payload type", stmt.Name.Value, variantName)
			}
		}

		// Check literal tag if present
		if variant.Literal != nil {
			literalType := tc.checkExpression(variant.Literal)
			if literalType == nil {
				tc.addError("ADT %s variant %s: invalid literal tag", stmt.Name.Value, variantName)
			} else {
				// Verify literal tag type consistency across variants
				tc.checkADTVariantLiteralTag(stmt.Name.Value, variantName, variant.Literal, literalType)
			}
		}
	}

	// Check that ADT has at least one variant
	if len(stmt.Variants) == 0 {
		tc.addError("ADT %s: must have at least one variant", stmt.Name.Value)
	}
}

// checkRecordTypeDefinition type checks a record type definition
func (tc *TypeChecker) checkRecordTypeDefinition(typeName string, recordLit *ast.RecordLiteral) {
	// Check that all fields have valid type annotations
	fieldNames := make(map[string]bool)
	for fieldName, fieldExpr := range recordLit.Fields {
		// Check for duplicate field names
		if fieldNames[fieldName] {
			tc.addError("record type %s: duplicate field name %s", typeName, fieldName)
			continue
		}
		fieldNames[fieldName] = true

		// Parse field type from the expression
		// In a record type definition, fieldExpr should be a type expression (identifier)
		fieldType := tc.parseTypeExpression(fieldExpr)
		if fieldType == nil {
			tc.addError("record type %s field %s: invalid type", typeName, fieldName)
		}
	}
}

// parseRecordTypeFromLiteral parses a RecordType from a record literal used in a type definition
func (tc *TypeChecker) parseRecordTypeFromLiteral(recordLit *ast.RecordLiteral) *RecordType {
	fields := make(map[string]Type)
	for fieldName, fieldExpr := range recordLit.Fields {
		fieldType := tc.parseTypeExpression(fieldExpr)
		if fieldType == nil {
			return nil
		}
		fields[fieldName] = fieldType
	}
	return &RecordType{Fields: fields}
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
					tc.addError("ADT %s: variant %s literal tag type %s does not match expected type %s",
						adtName, variantName, literalType, expectedLiteralType)
					return
				}
			}
		}
	}
}

func (tc *TypeChecker) checkWhileStatement(stmt *ast.WhileStatement) {
	conditionType := tc.checkExpression(stmt.Condition)
	if conditionType != nil && !conditionType.Equals(&BoolType{}) {
		tc.addError("while condition must be bool, got %s", conditionType)
	}

	// Type check body
	tc.checkBlockStatement(stmt.Body)
}

func (tc *TypeChecker) checkBlockStatement(block *ast.BlockStatement) {
	// Type check all statements in the block
	for _, stmt := range block.Statements {
		tc.checkStatement(stmt)
	}
}

// checkBlockExpression type checks a block expression and returns the type of the last expression
func (tc *TypeChecker) checkBlockExpression(block *ast.BlockStatement) Type {
	if len(block.Statements) == 0 {
		return &UnitType{}
	}

	// Type check all statements except the last
	for i := 0; i < len(block.Statements)-1; i++ {
		tc.checkStatement(block.Statements[i])
	}

	// The last statement should be an expression statement
	lastStmt := block.Statements[len(block.Statements)-1]
	if exprStmt, ok := lastStmt.(*ast.ExpressionStatement); ok {
		return tc.checkExpression(exprStmt.Expression)
	}

	// If the last statement is not an expression, return unit
	tc.checkStatement(lastStmt)
	return &UnitType{}
}

func (tc *TypeChecker) checkUnsafeBlock(stmt *ast.UnsafeBlock) {
	// Type check body (same as regular block)
	// Unsafe blocks don't change type checking rules, they just bypass borrow checking
	tc.checkBlockStatement(stmt.Body)
}

func (tc *TypeChecker) checkArrayLiteral(expr *ast.ArrayLiteral) Type {
	// Check if this is a typed array literal: [N]Type{ ... }
	if expr.Type != nil {
		// Parse the array type from the Type field (which is an IndexExpression)
		expectedArrayType := tc.parseTypeExpression(expr.Type)
		if expectedArrayType == nil {
			return nil
		}

		expectedArray, ok := expectedArrayType.(*ArrayType)
		if !ok {
			tc.addError("expected array type in typed array literal, got %s", expectedArrayType)
			return nil
		}

		// Check that the number of elements matches the array size
		if !expectedArray.IsSlice && int64(len(expr.Elements)) != expectedArray.Length {
			tc.addError("array literal has %d elements, expected %d", len(expr.Elements), expectedArray.Length)
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
				tc.addError("array element %d: expected type %s, got %s", i, expectedArray.ElementType, elemType)
			}
		}

		return expectedArray
	}

	// Untyped array literal: [ expr1, expr2, ... ]
	// Infer element type from first element
	if len(expr.Elements) == 0 {
		// Empty array - default to []i32 for now
		return &ArrayType{
			ElementType: &PrimitiveType{Name: "i32"},
			IsSlice:     true,
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
				commonType = tc.promoteNumericTypes(commonType, elemType)
				if commonType == nil {
					tc.addError("array element %d: incompatible types %s and %s", i+1, firstType, elemType)
					commonType = firstType // Fallback
				}
			} else {
				tc.addError("array element %d: expected type %s, got %s", i+1, commonType, elemType)
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
	// Handle intersection types: A & B & C
	if infix, ok := expr.(*ast.InfixExpression); ok && infix.Operator == "&" {
		// Parse left and right sides recursively
		leftType := tc.parseTypeExpression(infix.Left)
		rightType := tc.parseTypeExpression(infix.Right)

		if leftType == nil || rightType == nil {
			return nil
		}

		// Build intersection type
		types := []Type{leftType, rightType}

		// If left or right is already an intersection, flatten it
		if leftIntersection, ok := leftType.(*IntersectionType); ok {
			types = append(leftIntersection.Types, rightType)
		}
		if rightIntersection, ok := rightType.(*IntersectionType); ok {
			if leftIntersection, ok := leftType.(*IntersectionType); ok {
				// Both are intersections - merge them
				types = append(leftIntersection.Types, rightIntersection.Types...)
			} else {
				types = []Type{leftType}
				types = append(types, rightIntersection.Types...)
			}
		}

		return &IntersectionType{Types: types}
	}

	if ident, ok := expr.(*ast.Identifier); ok {
		// Check if it's a primitive type
		switch ident.Value {
		case "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64":
			return &PrimitiveType{Name: ident.Value}
		case "byte":
			// byte is an alias for u8
			return &PrimitiveType{Name: "u8"}
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
		default:
			// Check if it's a type alias in the environment
			if aliasType, ok := tc.env.GetType(ident.Value); ok {
				return aliasType
			}
			// Assume it's an ADT type
			return &ADTType{Name: ident.Value}
		}
	}

	// Handle array types: [N]T or []T
	if indexExpr, ok := expr.(*ast.IndexExpression); ok {
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
		return &RecordType{Fields: fields}
	}

	// Handle function types: fn(Type1, Type2) -> Type3
	// This would require the parser to represent function types as FunctionLiteral
	// For now, function types in annotations are not fully supported

	// Handle intersection types: A & B & C
	// The parser would need to represent this as an InfixExpression with AMP operators
	// For now, we'll check if it's a chain of & operations
	if infixExpr, ok := expr.(*ast.InfixExpression); ok && infixExpr.Operator == "&" {
		// Parse intersection type: left & right
		leftType := tc.parseTypeExpression(infixExpr.Left)
		rightType := tc.parseTypeExpression(infixExpr.Right)
		if leftType == nil || rightType == nil {
			return nil
		}
		// Collect all types in the intersection
		types := []Type{}
		tc.collectIntersectionTypes(infixExpr, &types)
		return &IntersectionType{Types: types}
	}

	return nil
}

// collectIntersectionTypes recursively collects all types in an intersection expression
func (tc *TypeChecker) collectIntersectionTypes(expr ast.Expression, types *[]Type) {
	if infixExpr, ok := expr.(*ast.InfixExpression); ok && infixExpr.Operator == "&" {
		// Recursively collect from left and right
		tc.collectIntersectionTypes(infixExpr.Left, types)
		tc.collectIntersectionTypes(infixExpr.Right, types)
	} else {
		// Base case: parse the type
		typ := tc.parseTypeExpression(expr)
		if typ != nil {
			*types = append(*types, typ)
		}
	}
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

	// Check if interfaceType is an InterfaceType
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

// SatisfiesConstraint checks if a concrete type satisfies an interface constraint
// This is used when instantiating a polymorphic function with interface constraints
func (tc *TypeChecker) SatisfiesConstraint(concreteType Type, constraint Constraint) bool {
	// For each required interface, check if the concrete type implements it
	for _, ifaceName := range constraint.Interfaces {
		// Look up the interface type
		ifaceType, ok := tc.env.GetType(ifaceName)
		if !ok {
			// Interface not found - this is a type error
			tc.addError("interface %s not found in constraint", ifaceName)
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
	tc.addError("invalid constraint expression: %s", expr.String())
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
			tc.addError("interface %s not found in constraint", ifaceName)
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
				tc.addError("invalid field type in record composition: %s", fieldName)
				continue
			}

			// Check for duplicate field names
			if existingType, exists := (*fields)[fieldName]; exists {
				if !existingType.Equals(fieldType) {
					tc.addError("duplicate field %s in record composition with conflicting types: %s vs %s",
						fieldName, existingType, fieldType)
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
			tc.addError("type %s not found in record composition", ident.Value)
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
						tc.addError("duplicate field %s in record composition with conflicting types: %s vs %s",
							fieldName, existingType, fieldType)
					}
				} else {
					(*fields)[fieldName] = fieldType
				}
			}
		} else {
			tc.addError("type %s in record composition is not a record type, got %T", ident.Value, typ)
		}
	} else {
		tc.addError("invalid expression in record composition: %T", expr)
	}
}

// checkExhaustiveness verifies that a match expression covers all variants of an ADT
func (tc *TypeChecker) checkExhaustiveness(arms []*ast.MatchArm, adtType *ADTType) {
	if adtDef, ok := tc.adtTypes[adtType.Name]; ok {
		coveredVariants := make(map[string]bool)
		hasWildcard := false

		// Check which variants are covered
		for _, arm := range arms {
			switch p := arm.Pattern.(type) {
			case *ast.WildcardPattern:
				hasWildcard = true
			case *ast.VariantPattern:
				variantName := p.Variant.Value
				coveredVariants[variantName] = true
			}
		}

		// If there's a wildcard, all variants are covered
		if hasWildcard {
			return
		}

		// Check that all variants are covered
		for _, variant := range adtDef.Variants {
			if !coveredVariants[variant.Name] {
				tc.addError("match expression is not exhaustive: missing variant %s of ADT %s", variant.Name, adtType.Name)
			}
		}
	}
}
