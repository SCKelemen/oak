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
type TypeEnvironment struct {
	store map[string]Type
	outer *TypeEnvironment
}

func NewTypeEnvironment() *TypeEnvironment {
	return &TypeEnvironment{
		store: make(map[string]Type),
		outer: nil,
	}
}

func NewEnclosedTypeEnvironment(outer *TypeEnvironment) *TypeEnvironment {
	env := NewTypeEnvironment()
	env.outer = outer
	return env
}

func (e *TypeEnvironment) Get(name string) (Type, bool) {
	typ, ok := e.store[name]
	if !ok && e.outer != nil {
		typ, ok = e.outer.Get(name)
	}
	return typ, ok
}

func (e *TypeEnvironment) Set(name string, typ Type) {
	e.store[name] = typ
}

func New(env *object.Environment) *TypeChecker {
	return &TypeChecker{
		errors:   []string{},
		env:      NewTypeEnvironment(),
		adtTypes: env.GetAllADTTypes(),
	}
}

func (tc *TypeChecker) Errors() []string {
	return tc.errors
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
func (tc *TypeChecker) checkExpression(expr ast.Expression) Type {
	switch e := expr.(type) {
	case *ast.IntegerLiteral:
		// Integer literals are inferred as i32 by default
		// In the future, we could infer based on literal size or context
		// For now, i32 is a reasonable default
		return &PrimitiveType{Name: "i32"}
	case *ast.StringLiteral:
		return &StringType{}
	case *ast.Boolean:
		return &BoolType{}
	case *ast.Identifier:
		return tc.checkIdentifier(e)
	case *ast.PrefixExpression:
		return tc.checkPrefixExpression(e)
	case *ast.InfixExpression:
		return tc.checkInfixExpression(e)
	case *ast.FunctionLiteral:
		return tc.checkFunctionLiteral(e)
	case *ast.InvocationExpression:
		return tc.checkInvocationExpression(e)
	case *ast.MatchExpression:
		return tc.checkMatchExpression(e)
	case *ast.VariantExpression:
		return tc.checkVariantExpression(e)
	case *ast.RecordLiteral:
		return tc.checkRecordLiteral(e)
	case *ast.IndexExpression:
		return tc.checkIndexExpression(e)
	case *ast.ArrayLiteral:
		return tc.checkArrayLiteral(e)
	default:
		tc.addError("unknown expression type: %T", expr)
		return nil
	}
}

// Helper functions for type checking specific expression types
func (tc *TypeChecker) checkIdentifier(ident *ast.Identifier) Type {
	typ, ok := tc.env.Get(ident.Value)
	if !ok {
		tc.addError("undefined variable: %s", ident.Value)
		return nil
	}
	return typ
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
		// Negation works on signed integers
		if prim, ok := rightType.(*PrimitiveType); ok {
			if prim.Name[0] == 'i' { // signed integer
				return rightType
			}
		}
		tc.addError("operator - requires signed integer, got %s", rightType)
		return nil
	default:
		tc.addError("unknown prefix operator: %s", expr.Operator)
		return nil
	}
}

func (tc *TypeChecker) checkInfixExpression(expr *ast.InfixExpression) Type {
	leftType := tc.checkExpression(expr.Left)
	rightType := tc.checkExpression(expr.Right)
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
		funcEnv.Set(param.Value, paramType)
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
	for i, arg := range expr.Arguments {
		argType := tc.checkExpression(arg)
		if argType == nil {
			continue
		}
		expectedType := fnType.Parameters[i]
		if !tc.isAssignable(argType, expectedType) {
			tc.addError("argument %d: expected %s, got %s", i+1, expectedType, argType)
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

	// Check that all arms return the same type
	var returnType Type
	for i, arm := range expr.Arms {
		// Type check pattern
		patternType := tc.checkPattern(arm.Pattern, scrutineeType)
		if patternType == nil {
			continue
		}

		// Type check arm body expression
		armType := tc.checkExpression(arm.Body)
		if armType == nil {
			continue
		}

		if returnType == nil {
			returnType = armType
		} else if !armType.Equals(returnType) {
			tc.addError("match arm %d: expected return type %s, got %s", i+1, returnType, armType)
		}
	}

	// Check exhaustiveness for ADT types
	if adtType, ok := scrutineeType.(*ADTType); ok {
		tc.checkExhaustiveness(expr.Arms, adtType)
	}

	if returnType == nil {
		return &UnitType{}
	}
	return returnType
}

func (tc *TypeChecker) checkPattern(pattern ast.Pattern, expectedType Type) Type {
	switch p := pattern.(type) {
	case *ast.WildcardPattern:
		return expectedType
	case *ast.BindingPattern:
		// Bind the variable in the environment
		tc.env.Set(p.Name.Value, expectedType)
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
						break
					}
				}
				if !found {
					tc.addError("variant %s not found in ADT %s", variantName, adtType.Name)
					return nil
				}
			}
			return expectedType
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

func (tc *TypeChecker) checkRecordLiteral(expr *ast.RecordLiteral) Type {
	fields := make(map[string]Type)
	for name, fieldExpr := range expr.Fields {
		fieldType := tc.checkExpression(fieldExpr)
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
	// Check if type annotation exists
	if stmt.Type != nil {
		// Parse type from annotation
		varType := tc.parseTypeExpression(stmt.Type)
		if varType == nil {
			tc.addError("variable %s: invalid type annotation", stmt.Name.Value)
			return
		}

		tc.env.Set(stmt.Name.Value, varType)

		// If there's an initializer, check that it matches the type (with coercion)
		if stmt.Value != nil {
			valueType := tc.checkExpression(stmt.Value)
			if valueType != nil {
				if !tc.isAssignable(valueType, varType) {
					tc.addError("variable %s: expected type %s, got %s", stmt.Name.Value, varType, valueType)
				}
			}
		}
	} else {
		// Type inference from initializer
		if stmt.Value != nil {
			inferredType := tc.checkExpression(stmt.Value)
			if inferredType != nil {
				tc.env.Set(stmt.Name.Value, inferredType)
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
	// Check that variable exists
	varType, ok := tc.env.Get(stmt.Name.Value)
	if !ok {
		tc.addError("undefined variable: %s", stmt.Name.Value)
		return
	}

	// Check that assigned value matches variable type (with coercion)
	valueType := tc.checkExpression(stmt.Value)
	if valueType != nil {
		if !tc.isAssignable(valueType, varType) {
			tc.addError("assignment: variable %s has type %s, cannot assign %s", stmt.Name.Value, varType, valueType)
		}
	}
}

func (tc *TypeChecker) checkFunctionStatement(stmt *ast.FunctionStatement) {
	// Create new environment for function parameters
	funcEnv := NewEnclosedTypeEnvironment(tc.env)

	// Parse parameter types from function signature
	paramTypes := []Type{}
	for _, param := range stmt.Parameters {
		paramType := tc.parseTypeExpression(param.Type)
		if paramType == nil {
			// Default to i32 if type parsing fails
			paramType = &PrimitiveType{Name: "i32"}
		}
		paramTypes = append(paramTypes, paramType)
		funcEnv.Set(param.Name.Value, paramType)
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
	tc.env.Set(stmt.Name.Value, funcType)
}

func (tc *TypeChecker) checkADTType(stmt *ast.ADTType) {
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
			}
		}
	}

	// Check that ADT has at least one variant
	if len(stmt.Variants) == 0 {
		tc.addError("ADT %s: must have at least one variant", stmt.Name.Value)
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
	// For now, infer element type from first element
	// Note: Typed arrays [N]T are not yet supported in the parser
	// For now, all array literals create slices []T
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
	Length      int64 // -1 for slices, >= 0 for arrays
	IsSlice     bool  // true for []T, false for [N]T
}

func (t *ArrayType) String() string {
	if t.IsSlice {
		return fmt.Sprintf("[]%s", t.ElementType.String())
	}
	return fmt.Sprintf("[%d]%s", t.Length, t.ElementType.String())
}

func (t *ArrayType) Equals(other Type) bool {
	if otherArray, ok := other.(*ArrayType); ok {
		return t.ElementType.Equals(otherArray.ElementType) &&
			t.Length == otherArray.Length &&
			t.IsSlice == otherArray.IsSlice
	}
	return false
}

// parseTypeExpression parses a type from an AST expression
func (tc *TypeChecker) parseTypeExpression(expr ast.Expression) Type {
	if ident, ok := expr.(*ast.Identifier); ok {
		// Check if it's a primitive type
		switch ident.Value {
		case "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64":
			return &PrimitiveType{Name: ident.Value}
		case "string":
			return &StringType{}
		case "Bool":
			return &BoolType{}
		case "()":
			return &UnitType{}
		default:
			// Assume it's an ADT type
			return &ADTType{Name: ident.Value}
		}
	}
	// Handle array types: []T or [N]T
	// Handle record types: { field: Type, ... }
	// Handle function types: fn(Type1, Type2) -> Type3
	// For now, these require explicit type annotations in variable declarations
	// TODO: Implement full type expression parsing for complex types
	return nil
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
