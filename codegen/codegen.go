package codegen

import (
	"fmt"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// CodeGenerator generates C code from Oak AST
type CodeGenerator struct {
	packageName string
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
		types:       make(map[string]bool),
		typeChecker: tc,
		typeEnv:     make(map[string]typechecker.Type),
	}
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
	funcName := fn.Name.Value
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

	// Emit function body
	cg.emitExpression(fn.Body, tc)

	cg.indentLevel--
	cg.write("}\n")
	cg.write("\n")
}

// emitExpression emits C code for an expression
func (cg *CodeGenerator) emitExpression(expr ast.Expression, tc *typechecker.TypeChecker) {
	switch e := expr.(type) {
	case *ast.IntegerLiteral:
		cg.write(fmt.Sprintf("  return %d;\n", e.Value))
	case *ast.StringLiteral:
		// TODO: Handle string literals properly
		cg.write("  /* string literal */\n")
	case *ast.InfixExpression:
		cg.emitInfixExpression(e, tc)
	case *ast.MatchExpression:
		cg.emitMatchExpression(e, tc)
	default:
		cg.write("  /* TODO: emit expression */\n")
	}
}

// emitInfixExpression emits C code for an infix expression
func (cg *CodeGenerator) emitInfixExpression(expr *ast.InfixExpression, tc *typechecker.TypeChecker) {
	// For now, simple arithmetic
	cg.write("  return ")
	cg.emitExpressionFragment(expr.Left, tc)
	cg.write(fmt.Sprintf(" %s ", expr.Operator))
	cg.emitExpressionFragment(expr.Right, tc)
	cg.write(";\n")
}

// emitExpressionFragment emits a fragment of an expression (no return statement)
func (cg *CodeGenerator) emitExpressionFragment(expr ast.Expression, tc *typechecker.TypeChecker) {
	switch e := expr.(type) {
	case *ast.IntegerLiteral:
		cg.output.WriteString(fmt.Sprintf("%d", e.Value))
	case *ast.Identifier:
		cg.output.WriteString(e.Value)
	case *ast.InfixExpression:
		cg.output.WriteString("(")
		cg.emitExpressionFragment(e.Left, tc)
		cg.output.WriteString(fmt.Sprintf(" %s ", e.Operator))
		cg.emitExpressionFragment(e.Right, tc)
		cg.output.WriteString(")")
	default:
		cg.output.WriteString("/* TODO */")
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
				payloadName := "value" // TODO: get from binding pattern
				cg.write(fmt.Sprintf("      %s %s = scrutinee.payload.%s;\n", "/* TODO: type */", payloadName, variantName))
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
	return "void"
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

