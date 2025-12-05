package codegen

import (
	"fmt"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
	"github.com/SCKelemen/oak/typechecker"
)

// CodeGenerator generates C code from Oak AST
type CodeGenerator struct {
	packageName string
	sourceFile   string // Source file path for source location comments
	output      strings.Builder
	indentLevel int
	types       map[string]bool // Track emitted types to avoid duplicates
	typeChecker *typechecker.TypeChecker
	typeEnv     map[string]typechecker.Type // Type environment for lookups
}

// New creates a new code generator
func New(packageName string, tc *typechecker.TypeChecker) *CodeGenerator {
	return &CodeGenerator{
		packageName: packageName,
		sourceFile:   "unknown.oak", // Default, can be set via SetSourceFile
		types:       make(map[string]bool),
		typeChecker: tc,
		typeEnv:     make(map[string]typechecker.Type),
	}
}

// SetSourceFile sets the source file path for source location comments
func (cg *CodeGenerator) SetSourceFile(file string) {
	cg.sourceFile = file
}

// Generate generates C code from an Oak program
func (cg *CodeGenerator) Generate(program *ast.Program, tc *typechecker.TypeChecker) (string, error) {
	cg.output.Reset()
	cg.types = make(map[string]bool)

	// Extract package name from program
	for _, stmt := range program.Statements {
		if pkgStmt, ok := stmt.(*ast.PackageStatement); ok {
			cg.packageName = pkgStmt.Name.Value
			break
		}
	}

	// Emit header includes and type aliases
	cg.emitHeader()

	// Emit standard library ADTs first
	cg.emitBoolADT()
	cg.emitComparisonADT()

	// Emit type definitions (ADTs, records)
	for _, stmt := range program.Statements {
		switch s := stmt.(type) {
		case *ast.ADTType:
			cg.emitADTType(s, tc)
		case *ast.FunctionStatement:
			// Functions will be emitted separately
		}
	}

	// Emit function definitions
	for _, stmt := range program.Statements {
		switch s := stmt.(type) {
		case *ast.FunctionStatement:
			cg.emitFunction(s, tc)
		}
	}

	return cg.output.String(), nil
}

// emitHeader emits the standard header with includes and type aliases
func (cg *CodeGenerator) emitHeader() {
	cg.write("/* Generated C code from Oak */\n")
	cg.write("#include <stdint.h>\n")
	cg.write("#include <stddef.h>\n")
	cg.write("\n")

	// Emit primitive type aliases
	cg.write("typedef uint8_t  u8;\n")
	cg.write("typedef uint16_t u16;\n")
	cg.write("typedef uint32_t u32;\n")
	cg.write("typedef uint64_t u64;\n")
	cg.write("\n")
	cg.write("typedef int8_t   i8;\n")
	cg.write("typedef int16_t i16;\n")
	cg.write("typedef int32_t i32;\n")
	cg.write("typedef int64_t i64;\n")
	cg.write("\n")
	cg.write("typedef u8  byte;\n")
	cg.write("typedef i32 rune;\n")
	cg.write("\n")

	// Emit string type
	cg.write("typedef struct oak_string {\n")
	cg.indentLevel++
	cg.write("  u8* data;  /* UTF-8 bytes, not necessarily null-terminated */\n")
	cg.write("  u32 len;   /* number of bytes */\n")
	cg.indentLevel--
	cg.write("} string;\n")
	cg.write("\n")
}

// write writes a string to the output with proper indentation
// Follows C style rules: spaces inside parentheses, braces on same line
func (cg *CodeGenerator) write(s string) {
	lines := strings.Split(s, "\n")
	for i, line := range lines {
		if i > 0 {
			cg.output.WriteString("\n")
		}
		if line != "" {
			for j := 0; j < cg.indentLevel; j++ {
				cg.output.WriteString("  ")
			}
		}
		cg.output.WriteString(line)
	}
}

// writeRaw writes a string without indentation (for multi-line constructs)
func (cg *CodeGenerator) writeRaw(s string) {
	cg.output.WriteString(s)
}

// emitADTType emits C code for an ADT type definition
func (cg *CodeGenerator) emitADTType(adt *ast.ADTType, tc *typechecker.TypeChecker) {
	typeName := adt.Name.Value
	cName := cg.cTypeName(typeName)

	// Check if already emitted
	if cg.types[cName] {
		return
	}

	// Emit source location comment
	cg.emitSourceLocationComment(adt.Token, fmt.Sprintf("ADT type %s", typeName))

	// Check if this is a record type definition: Name: type = { field: Type, ... }
	// Record type definitions are parsed as ADTType with a single variant that has a record literal
	if len(adt.Variants) == 1 {
		variant := adt.Variants[0]
		if variant.Literal != nil {
			if recordLit, ok := variant.Literal.(*ast.RecordLiteral); ok {
				// This is a record type definition
				cg.emitRecordType(typeName, recordLit, tc)
				return
			}
		}
	}

	cg.types[cName] = true

	// Emit tag enum (with proper C style spacing)
	tagEnumName := fmt.Sprintf("%s_tag", cName)
	cg.write(fmt.Sprintf("typedef enum %s {\n", tagEnumName))
	cg.indentLevel++

	for i, variant := range adt.Variants {
		variantName := variant.Name.Value
		tagName := fmt.Sprintf("%s_tag_%s", cName, variantName)
		cg.write(fmt.Sprintf("  %s", tagName))
		if i < len(adt.Variants)-1 {
			cg.write(",")
		}
		cg.write("\n")
	}

	cg.indentLevel--
	cg.write(fmt.Sprintf("} %s;\n", tagEnumName))
	cg.write("\n")

	// Check if any variant has a payload
	hasPayload := false
	for _, variant := range adt.Variants {
		if variant.Payload != nil {
			hasPayload = true
			break
		}
	}

	// Emit struct
	cg.write(fmt.Sprintf("typedef struct %s {\n", cName))
	cg.indentLevel++
	cg.write(fmt.Sprintf("  %s tag;\n", tagEnumName))

	if hasPayload {
		cg.write("  union {\n")
		cg.indentLevel++
		for _, variant := range adt.Variants {
			if variant.Payload != nil {
				// Parse payload type
				payloadType := cg.parsePayloadType(variant.Payload)
				cg.write(fmt.Sprintf("    %s %s;\n", payloadType, variant.Name.Value))
			}
		}
		cg.indentLevel--
		cg.write("  } payload;\n")
	}

	cg.indentLevel--
	cg.write(fmt.Sprintf("} %s;\n", cName))
	cg.write("\n")

	// Emit constructors
	for _, variant := range adt.Variants {
		cg.emitADTConstructor(cName, variant)
	}
}

// emitADTConstructor emits a constructor function for an ADT variant
func (cg *CodeGenerator) emitADTConstructor(typeName string, variant *ast.ADTVariant) {
	// Emit source location comment for constructor
	cg.emitSourceLocationComment(variant.Token, fmt.Sprintf("ADT constructor %s::%s", typeName, variant.Name.Value))
	
	variantName := variant.Name.Value
	funcName := fmt.Sprintf("%s_%s", typeName, variantName)

	// C style: space inside parentheses
	cg.write(fmt.Sprintf("static inline %s %s( ", typeName, funcName))
	if variant.Payload != nil {
		payloadType := cg.parsePayloadType(variant.Payload)
		cg.write(fmt.Sprintf("%s value", payloadType))
	}
	cg.write(" ) {\n")
	cg.indentLevel++

	cg.write(fmt.Sprintf("  %s res;\n", typeName))
	cg.write(fmt.Sprintf("  res.tag = %s_tag_%s;\n", typeName, variantName))
	if variant.Payload != nil {
		cg.write(fmt.Sprintf("  res.payload.%s = value;\n", variantName))
	}
	cg.write("  return res;\n")

	cg.indentLevel--
	cg.write("}\n")
	cg.write("\n")
}

// emitFunction emits C code for a function or method
func (cg *CodeGenerator) emitFunction(fn *ast.FunctionStatement, tc *typechecker.TypeChecker) {
	// Emit source location comment
	funcName := fn.Name.Value
	cg.emitSourceLocationComment(fn.Token, fmt.Sprintf("function %s", funcName))
	
	cFuncName := cg.cFunctionName(funcName)

	// Determine return type
	returnType := "void"
	if fn.ReturnType != nil {
		returnType = cg.parseTypeExpression(fn.ReturnType)
	}

	// Emit function signature (C style: space inside parentheses)
	cg.write(fmt.Sprintf("%s %s( ", returnType, cFuncName))

	// If method, add receiver as first parameter
	if fn.Receiver != nil {
		receiverType := cg.parseTypeExpression(fn.Receiver.Type)
		receiverName := fn.Receiver.Name.Value
		cg.write(fmt.Sprintf("%s %s", receiverType, receiverName))
		if len(fn.Parameters) > 0 {
			cg.write(", ")
		}
	}

	// Emit parameters
	for i, param := range fn.Parameters {
		paramType := cg.parseTypeExpression(param.Type)
		paramName := param.Name.Value
		cg.write(fmt.Sprintf("%s %s", paramType, paramName))
		if i < len(fn.Parameters)-1 {
			cg.write(", ")
		}
	}

	cg.write(" ) {\n")
	cg.indentLevel++

	// Emit function body (can be expression or block)
	cg.emitFunctionBody(fn.Body, tc)

	cg.indentLevel--
	cg.write("}\n")
	cg.write("\n")
}

// emitFunctionBody emits the body of a function (expression or block)
func (cg *CodeGenerator) emitFunctionBody(body ast.Expression, tc *typechecker.TypeChecker) {
	// Single expression - emit as return
	cg.emitExpression(body, tc)
}

// emitExpression emits C code for an expression (as a return statement)
func (cg *CodeGenerator) emitExpression(expr ast.Expression, tc *typechecker.TypeChecker) {
	cg.write("  return ")
	cg.emitExpressionFragment(expr, tc)
	cg.write(";\n")
}

// emitStatementExpression emits C code for an expression used as a statement
func (cg *CodeGenerator) emitStatementExpression(expr ast.Expression, tc *typechecker.TypeChecker) {
	cg.emitExpressionFragment(expr, tc)
	cg.write(";\n")
}

// emitInfixExpression emits C code for an infix expression (as fragment)
func (cg *CodeGenerator) emitInfixExpression(expr *ast.InfixExpression, tc *typechecker.TypeChecker) {
	// C style: space around operators, parentheses for grouping
	cg.output.WriteString("( ")
	cg.emitExpressionFragment(expr.Left, tc)
	cg.output.WriteString(fmt.Sprintf(" %s ", expr.Operator))
	cg.emitExpressionFragment(expr.Right, tc)
	cg.output.WriteString(" )")
}

// emitExpressionFragment emits a fragment of an expression (no return statement)
func (cg *CodeGenerator) emitExpressionFragment(expr ast.Expression, tc *typechecker.TypeChecker) {
	switch e := expr.(type) {
	case *ast.IntegerLiteral:
		cg.output.WriteString(fmt.Sprintf("%d", e.Value))
	case *ast.StringLiteral:
		// TODO: Properly handle string literals (create string struct)
		cg.output.WriteString(fmt.Sprintf("/* string: %s */", e.Value))
	case *ast.Boolean:
		if e.Value {
			cg.output.WriteString("oak_Bool_True")
		} else {
			cg.output.WriteString("oak_Bool_False")
		}
	case *ast.Identifier:
		cg.output.WriteString(e.Value)
	case *ast.InfixExpression:
		cg.emitInfixExpression(e, tc)
	case *ast.PrefixExpression:
		cg.output.WriteString(fmt.Sprintf("%s", e.Operator))
		cg.output.WriteString("( ")
		cg.emitExpressionFragment(e.Right, tc)
		cg.output.WriteString(" )")
	case *ast.IndexExpression:
		// Field access or array indexing
		cg.emitExpressionFragment(e.Left, tc)
		if ident, ok := e.Index.(*ast.Identifier); ok {
			// Field access: record.field
			cg.output.WriteString(fmt.Sprintf(".%s", ident.Value))
		} else {
			// Array indexing: array[index]
			cg.output.WriteString("[ ")
			cg.emitExpressionFragment(e.Index, tc)
			cg.output.WriteString(" ]")
		}
	case *ast.VariantExpression:
		// ADT variant construction: .Ok or Status::Ok
		if e.TypeName != nil {
			typeName := cg.cTypeName(e.TypeName.Value)
			variantName := e.Variant.Value
			constructorName := fmt.Sprintf("%s_%s", typeName, variantName)
			cg.output.WriteString(fmt.Sprintf("%s(", constructorName))
			if e.Payload != nil {
				cg.emitExpressionFragment(e.Payload, tc)
			}
			cg.output.WriteString(")")
		} else {
			// Bare variant - need type context
			variantName := e.Variant.Value
			cg.output.WriteString(fmt.Sprintf("/* .%s */", variantName))
		}
	case *ast.InvocationExpression:
		// Function or method call
		cg.emitExpressionFragment(e.Function, tc)
		cg.output.WriteString("( ")
		for i, arg := range e.Arguments {
			cg.emitExpressionFragment(arg, tc)
			if i < len(e.Arguments)-1 {
				cg.output.WriteString(", ")
			}
		}
		cg.output.WriteString(" )")
	case *ast.MatchExpression:
		// Pattern matching - this is complex, emit as a block
		cg.emitMatchExpressionInline(e, tc)
	case *ast.ArrayLiteral:
		cg.emitArrayLiteral(e, tc)
	case *ast.RecordLiteral:
		cg.emitRecordLiteral(e, tc)
	case *ast.FunctionLiteral:
		// Function literal (closure) - emit as function pointer
		cg.emitFunctionLiteral(e, tc)
	default:
		cg.output.WriteString(fmt.Sprintf("/* TODO: emit expression type %T */", e))
	}
}

// emitMatchExpression emits C code for a pattern matching expression
func (cg *CodeGenerator) emitMatchExpression(expr *ast.MatchExpression, tc *typechecker.TypeChecker) {
	// Try to determine scrutinee type from type environment
	// For now, we'll infer from the pattern or use a simple heuristic
	// In a full implementation, we'd use the type checker's environment

	// Check if first pattern is a variant pattern (indicates ADT match)
	if len(expr.Arms) > 0 {
		if _, ok := expr.Arms[0].Pattern.(*ast.VariantPattern); ok {
			// This is likely an ADT match - we need to infer the type
			// For now, use a placeholder
			cg.emitADTMatch(expr, nil, tc)
			return
		}
	}

	// Scalar match
	cg.emitScalarMatch(expr, tc)
}

// emitADTMatch emits C code for ADT pattern matching
func (cg *CodeGenerator) emitADTMatch(expr *ast.MatchExpression, adtType *typechecker.ADTType, tc *typechecker.TypeChecker) {
	// Infer ADT type name from first variant pattern
	typeName := "Unknown"
	if len(expr.Arms) > 0 {
		if _, ok := expr.Arms[0].Pattern.(*ast.VariantPattern); ok {
			// Try to extract type name from variant expression
			// For now, use a placeholder - in full implementation, we'd look up the type
			typeName = "ADT" // Placeholder
		}
	}
	if adtType != nil {
		typeName = cg.cTypeName(adtType.Name)
	} else {
		typeName = cg.cTypeName(typeName)
	}
	// C style: space inside parentheses
	cg.write(fmt.Sprintf("  %s scrutinee = ", typeName))
	cg.emitExpressionFragment(expr.Scrutinee, tc)
	cg.write(";\n")
	cg.write("\n")
	cg.write("  switch ( scrutinee.tag ) {\n")
	cg.indentLevel++

	for _, arm := range expr.Arms {
		if variantPattern, ok := arm.Pattern.(*ast.VariantPattern); ok {
			variantName := variantPattern.Variant.Value
			tagName := fmt.Sprintf("%s_tag_%s", typeName, variantName)
			cg.write(fmt.Sprintf("    case %s: {\n", tagName))
			cg.indentLevel++

			// Extract payload if present
			if variantPattern.Payload != nil {
				// Check if payload is a binding pattern
				if bindingPattern, ok := variantPattern.Payload.(*ast.BindingPattern); ok {
					payloadName := bindingPattern.Name.Value
					// Try to determine payload type from ADT definition
					payloadType := "/* TODO: infer type */"
					// For now, use a placeholder - in full implementation, we'd look up the ADT variant
					cg.write(fmt.Sprintf("      %s %s = scrutinee.payload.%s;\n", payloadType, payloadName, variantName))
				} else {
					// Payload is not a binding - this shouldn't happen in valid code
					cg.write(fmt.Sprintf("      /* payload extraction */\n"))
				}
			}

			// Emit body
			cg.emitExpression(arm.Body, tc)

			cg.indentLevel--
			cg.write("    } break;\n")
		}
	}

	cg.indentLevel--
	cg.write("  }\n")
}

// emitScalarMatch emits C code for scalar pattern matching
func (cg *CodeGenerator) emitScalarMatch(expr *ast.MatchExpression, tc *typechecker.TypeChecker) {
	// Emit if/else if chain (C style: space inside parentheses)
	for i, arm := range expr.Arms {
		if i == 0 {
			cg.write("  if ( ")
		} else {
			cg.write("  } else if ( ")
		}

		// Emit pattern condition
		if literalPattern, ok := arm.Pattern.(*ast.LiteralPattern); ok {
			cg.emitExpressionFragment(expr.Scrutinee, tc)
			cg.write(" == ")
			cg.emitExpressionFragment(literalPattern.Value, tc)
		} else if _, ok := arm.Pattern.(*ast.BindingPattern); ok {
			// Binding pattern - matches anything, binds to variable
			cg.write("1")
			// In full implementation, we'd need to handle the binding
			// For now, we'll assume the variable is available in the body
		} else if _, ok := arm.Pattern.(*ast.WildcardPattern); ok {
			// Wildcard - this should be the last arm
			cg.write("1")
		}

		cg.write(" ) {\n")
		cg.indentLevel++

		// Emit body
		cg.emitExpression(arm.Body, tc)

		cg.indentLevel--
	}

	cg.write("  }\n")
}

// emitMatchExpressionInline emits pattern matching as an inline expression
// This is used when a match expression is part of a larger expression
func (cg *CodeGenerator) emitMatchExpressionInline(expr *ast.MatchExpression, tc *typechecker.TypeChecker) {
	// For inline matches, we need to create a temporary variable
	// This is a simplified version - full implementation would be more sophisticated
	cg.output.WriteString("( ")

	// Determine if ADT or scalar match
	isADT := false
	if len(expr.Arms) > 0 {
		if _, ok := expr.Arms[0].Pattern.(*ast.VariantPattern); ok {
			isADT = true
		}
	}

	if isADT {
		// ADT match - emit switch inline (simplified)
		cg.output.WriteString("/* match expression */")
	} else {
		// Scalar match - emit ternary-like chain
		for i, arm := range expr.Arms {
			if i > 0 {
				cg.output.WriteString(" : ")
			}
			cg.output.WriteString("( ")
			// Condition
			if literalPattern, ok := arm.Pattern.(*ast.LiteralPattern); ok {
				cg.emitExpressionFragment(expr.Scrutinee, tc)
				cg.output.WriteString(" == ")
				cg.emitExpressionFragment(literalPattern.Value, tc)
			} else {
				cg.output.WriteString("1") // wildcard
			}
			cg.output.WriteString(" ) ? ")
			cg.emitExpressionFragment(arm.Body, tc)
		}
	}

	cg.output.WriteString(" )")
}

// Helper functions for name mangling and type parsing

func (cg *CodeGenerator) cTypeName(oakName string) string {
	if cg.packageName != "" && cg.packageName != "main" {
		return fmt.Sprintf("oak_%s_%s", cg.packageName, oakName)
	}
	return fmt.Sprintf("oak_%s", oakName)
}

func (cg *CodeGenerator) cFunctionName(oakName string) string {
	if cg.packageName != "" && cg.packageName != "main" {
		return fmt.Sprintf("oak_%s_%s", cg.packageName, oakName)
	}
	return fmt.Sprintf("oak_%s", oakName)
}

func (cg *CodeGenerator) parseTypeExpression(expr ast.Expression) string {
	if ident, ok := expr.(*ast.Identifier); ok {
		switch ident.Value {
		case "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64":
			return ident.Value
		case "string":
			return "string"
		case "Bool":
			return "Bool"
		default:
			// Assume it's a type name
			return cg.cTypeName(ident.Value)
		}
	}

	// Handle array types: [N]T or []T
	// The parser represents array types as IndexExpression
	if indexExpr, ok := expr.(*ast.IndexExpression); ok {
		// Check if this is an array type annotation
		if intLit, ok := indexExpr.Index.(*ast.IntegerLiteral); ok {
			// Fixed-size array: [N]T
			elementType := cg.parseTypeExpression(indexExpr.Left)
			return fmt.Sprintf("%s[ %d ]", elementType, intLit.Value)
		} else if indexExpr.Left == nil {
			// Slice type: []T (represented as IndexExpression with nil left)
			elementType := cg.parseTypeExpression(indexExpr.Index)
			// Emit view type for []T
			return cg.emitViewType(elementType)
		}
	}

	// Handle record types: { field: Type, ... }
	if _, ok := expr.(*ast.RecordLiteral); ok {
		// This is a record type definition
		// We'll need to generate a struct type name
		// For now, return a placeholder
		return "/* record type */"
	}

	return "void"
}

// emitViewType emits a view type struct and returns the type name
func (cg *CodeGenerator) emitViewType(elementType string) string {
	viewTypeName := fmt.Sprintf("oak_view_%s", elementType)

	// Check if already emitted
	if cg.types[viewTypeName] {
		return viewTypeName
	}
	cg.types[viewTypeName] = true

	// Emit view struct (read-only slice)
	cg.write(fmt.Sprintf("typedef struct %s {\n", viewTypeName))
	cg.indentLevel++
	cg.write(fmt.Sprintf("  const %s* base;\n", elementType))
	cg.write("  u32       len;\n")
	cg.indentLevel--
	cg.write(fmt.Sprintf("} %s;\n", viewTypeName))
	cg.write("\n")

	return viewTypeName
}

// emitSpanType emits a span type struct and returns the type name
func (cg *CodeGenerator) emitSpanType(elementType string) string {
	spanTypeName := fmt.Sprintf("oak_span_%s", elementType)

	// Check if already emitted
	if cg.types[spanTypeName] {
		return spanTypeName
	}
	cg.types[spanTypeName] = true

	// Emit span struct (mutable slice)
	cg.write(fmt.Sprintf("typedef struct %s {\n", spanTypeName))
	cg.indentLevel++
	cg.write(fmt.Sprintf("  %s* base;\n", elementType))
	cg.write("  u32 len;\n")
	cg.indentLevel--
	cg.write(fmt.Sprintf("} %s;\n", spanTypeName))
	cg.write("\n")

	return spanTypeName
}

// SourceLocation represents a location in the source code
type SourceLocation struct {
	File   string
	Line   int
	Column int
	Package string
}

// emitSourceLocationComment emits a C comment with source location information
func (cg *CodeGenerator) emitSourceLocationComment(tok token.Token, description string) {
	// Format: /* Generated from: package file.oak:line:col - description */
	// For now, we'll use a simple format since Token doesn't have line/col info
	// In a full implementation, we'd track line/column numbers during parsing
	// TODO: Extract line/column from token when available
	loc := cg.getSourceLocation(tok)
	cg.write(fmt.Sprintf("/* Generated from: %s %s:%d:%d - %s */\n", 
		loc.Package, loc.File, loc.Line, loc.Column, description))
}

// getSourceLocation extracts source location from a token
// TODO: Enhance when Token struct includes line/column information
func (cg *CodeGenerator) getSourceLocation(tok token.Token) SourceLocation {
	return SourceLocation{
		File:    cg.sourceFile,
		Line:    0, // TODO: Extract from token when available
		Column:  0, // TODO: Extract from token when available
		Package: cg.packageName,
	}
}

// emitBlockStatement emits a block statement
func (cg *CodeGenerator) emitBlockStatement(block *ast.BlockStatement, tc *typechecker.TypeChecker, isFunctionBody bool) {
	for i, stmt := range block.Statements {
		cg.emitStatement(stmt, tc, isFunctionBody && i == len(block.Statements)-1)
	}
}

// emitBlockExpression emits a block as an expression (last statement is the value)
func (cg *CodeGenerator) emitBlockExpression(block *ast.BlockStatement, tc *typechecker.TypeChecker) {
	// For block expressions, we need to handle statements and return the last expression
	// This is simplified - in full implementation, we'd need proper scoping
	cg.output.WriteString("( ")
	
	for i, stmt := range block.Statements {
		if i < len(block.Statements)-1 {
			// Not the last statement - emit as statement
			cg.emitStatement(stmt, tc, false)
		} else {
			// Last statement - emit as expression
			if exprStmt, ok := stmt.(*ast.ExpressionStatement); ok {
				cg.emitExpressionFragment(exprStmt.Expression, tc)
			} else {
				cg.output.WriteString("/* block expression */")
			}
		}
	}
	
	cg.output.WriteString(" )")
}

// emitStatement emits a statement
func (cg *CodeGenerator) emitStatement(stmt ast.Statement, tc *typechecker.TypeChecker, isLastInFunction bool) {
	switch s := stmt.(type) {
	case *ast.VariableDeclaration:
		cg.emitVariableDeclaration(s, tc)
	case *ast.AssignmentStatement:
		cg.emitAssignmentStatement(s, tc)
	case *ast.ExpressionStatement:
		if isLastInFunction {
			// Last statement in function - emit as return
			cg.emitExpression(s.Expression, tc)
		} else {
			// Regular statement - emit without return
			cg.emitStatementExpression(s.Expression, tc)
		}
	case *ast.WhileStatement:
		cg.emitWhileStatement(s, tc)
	case *ast.BlockStatement:
		cg.write("  {\n")
		cg.indentLevel++
		cg.emitBlockStatement(s, tc, false)
		cg.indentLevel--
		cg.write("  }\n")
	default:
		cg.write(fmt.Sprintf("  /* TODO: emit statement type %T */\n", s))
	}
}

// emitVariableDeclaration emits a variable declaration
func (cg *CodeGenerator) emitVariableDeclaration(stmt *ast.VariableDeclaration, tc *typechecker.TypeChecker) {
	varName := stmt.Name.Value
	
	// Determine type
	var varType string
	if stmt.Type != nil {
		varType = cg.parseTypeExpression(stmt.Type)
	} else {
		// Type inference - try to infer from value
		// For now, default to i32
		varType = "i32"
	}
	
	// C style: type name;
	cg.write(fmt.Sprintf("  %s %s", varType, varName))
	
	if stmt.Value != nil {
		cg.write(" = ")
		cg.emitExpressionFragment(stmt.Value, tc)
	}
	
	cg.write(";\n")
}

// emitAssignmentStatement emits an assignment statement
func (cg *CodeGenerator) emitAssignmentStatement(stmt *ast.AssignmentStatement, tc *typechecker.TypeChecker) {
	cg.write("  ")
	cg.emitExpressionFragment(stmt.Name, tc)
	cg.write(" = ")
	cg.emitExpressionFragment(stmt.Value, tc)
	cg.write(";\n")
}

// emitWhileStatement emits a while loop
func (cg *CodeGenerator) emitWhileStatement(stmt *ast.WhileStatement, tc *typechecker.TypeChecker) {
	cg.write("  while ( ")
	cg.emitExpressionFragment(stmt.Condition, tc)
	cg.write(" ) {\n")
	cg.indentLevel++
	
	// Emit body (while body is always a BlockStatement)
	cg.emitBlockStatement(stmt.Body, tc, false)
	
	cg.indentLevel--
	cg.write("  }\n")
}

// emitArrayLiteral emits an array literal
func (cg *CodeGenerator) emitArrayLiteral(expr *ast.ArrayLiteral, tc *typechecker.TypeChecker) {
	// For now, emit as array initializer
	// In full implementation, we'd need to determine the element type and size
	cg.output.WriteString("{ ")
	for i, elem := range expr.Elements {
		if i > 0 {
			cg.output.WriteString(", ")
		}
		cg.emitExpressionFragment(elem, tc)
	}
	cg.output.WriteString(" }")
}

// emitRecordLiteral emits a record literal
func (cg *CodeGenerator) emitRecordLiteral(expr *ast.RecordLiteral, tc *typechecker.TypeChecker) {
	// C99 designated initializers
	cg.output.WriteString("{ ")
	first := true
	for fieldName, fieldExpr := range expr.Fields {
		if !first {
			cg.output.WriteString(", ")
		}
		cg.output.WriteString(fmt.Sprintf(".%s = ", fieldName))
		cg.emitExpressionFragment(fieldExpr, tc)
		first = false
	}
	cg.output.WriteString(" }")
}

// emitFunctionLiteral emits a function literal (closure)
func (cg *CodeGenerator) emitFunctionLiteral(expr *ast.FunctionLiteral, tc *typechecker.TypeChecker) {
	// For now, function literals are not fully supported in C
	// In full implementation, we'd need to emit a function pointer or struct
	cg.output.WriteString("/* function literal */")
}

func (cg *CodeGenerator) parsePayloadType(expr ast.Expression) string {
	return cg.parseTypeExpression(expr)
}

// emitBoolADT emits the standard Bool ADT
func (cg *CodeGenerator) emitBoolADT() {
	if cg.types["Bool"] {
		return
	}
	cg.types["Bool"] = true

	cg.write("typedef enum oak_Bool {\n")
	cg.indentLevel++
	cg.write("  oak_Bool_False = 0,\n")
	cg.write("  oak_Bool_True  = 1\n")
	cg.indentLevel--
	cg.write("} Bool;\n")
	cg.write("\n")
}

// emitComparisonADT emits the standard Comparison ADT
func (cg *CodeGenerator) emitComparisonADT() {
	if cg.types["Comparison"] {
		return
	}
	cg.types["Comparison"] = true

	cg.write("typedef enum oak_Comparison {\n")
	cg.indentLevel++
	cg.write("  oak_Comparison_Less,\n")
	cg.write("  oak_Comparison_Equal,\n")
	cg.write("  oak_Comparison_Greater\n")
	cg.indentLevel--
	cg.write("} Comparison;\n")
	cg.write("\n")
}

// emitRecordType emits C code for a record type definition
func (cg *CodeGenerator) emitRecordType(typeName string, recordLit *ast.RecordLiteral, tc *typechecker.TypeChecker) {
	cName := cg.cTypeName(typeName)

	// Check if already emitted
	if cg.types[cName] {
		return
	}
	cg.types[cName] = true

	// Emit source location comment
	cg.emitSourceLocationComment(recordLit.Token, fmt.Sprintf("record type %s", typeName))

	// Emit struct definition (C style: opening brace on same line)
	cg.write(fmt.Sprintf("typedef struct %s {\n", cName))
	cg.indentLevel++

	// Emit fields in declaration order
	// Note: Go maps don't preserve order, so we'll iterate in the order they appear
	// For now, we'll use the map order (which may vary)
	for fieldName, fieldExpr := range recordLit.Fields {
		// Parse field type
		fieldType := cg.parseTypeExpression(fieldExpr)
		// C style: pointer asterisk with type (u8* ptr)
		cg.write(fmt.Sprintf("  %s %s;\n", fieldType, fieldName))
	}

	cg.indentLevel--
	cg.write(fmt.Sprintf("} %s;\n", cName))
	cg.write("\n")
}
