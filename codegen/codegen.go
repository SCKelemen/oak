package codegen

import (
	"fmt"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/discipline"
	"github.com/SCKelemen/oak/lsp"
	"github.com/SCKelemen/oak/token"
	"github.com/SCKelemen/oak/typechecker"
)

// CodeGenerator generates C code from Oak AST
type CodeGenerator struct {
	packageName      string
	sourceFile       string // Source file path for source location comments
	sourceText       string // Full source text for UTF-8 to UTF-16 conversion
	output           strings.Builder
	indentLevel      int
	types            map[string]bool // Track emitted types to avoid duplicates
	typeChecker      *typechecker.TypeChecker
	typeEnv          map[string]typechecker.Type // Type environment for lookups
	stringLiterals   []string                    // Track string literals to emit as static arrays
	stringLiteralMap map[string]int              // Map string value to index
	adtTypes         map[string]*ast.ADTType     // Map ADT name to AST definition
	// tailLoopFunction is set while emitting a loop-lowered self-tail-recursive
	// function: its tail self-call emits parameter rebinding plus continue.
	tailLoopFunction *ast.FunctionStatement
	// Trampoline lowering state (docs/spec/85-discipline.md): mutual tail
	// cycles merge into one state-machine engine so the cycle runs in one
	// frame. trampolineMember maps a member to its group key; tailGroup maps
	// members to their state tags while an engine body is being emitted.
	programFunctions  map[string]*ast.FunctionStatement
	trampolineMember  map[string]string
	trampolineGroups  map[string][]string
	trampolineEmitted map[string]bool
	tailGroup         map[string]string
	tailGroupParams   []*ast.FunctionParameter
}

// New creates a new code generator
func New(packageName string, tc *typechecker.TypeChecker) *CodeGenerator {
	return &CodeGenerator{
		packageName:      packageName,
		sourceFile:       "unknown.oak", // Default, can be set via SetSourceFile
		types:            make(map[string]bool),
		typeChecker:      tc,
		typeEnv:          make(map[string]typechecker.Type),
		stringLiterals:   []string{},
		stringLiteralMap: make(map[string]int),
		adtTypes:         make(map[string]*ast.ADTType),
	}
}

// SetSourceFile sets the source file path for source location comments
func (cg *CodeGenerator) SetSourceFile(file string) {
	cg.sourceFile = file
}

// SetSourceText sets the full source text for UTF-8 to UTF-16 conversion
func (cg *CodeGenerator) SetSourceText(text string) {
	cg.sourceText = text
}

// Generate generates C code from an Oak program
func (cg *CodeGenerator) Generate(program *ast.Program, tc *typechecker.TypeChecker) (string, error) {
	cg.output.Reset()
	cg.types = make(map[string]bool)
	cg.stringLiterals = []string{}
	cg.stringLiteralMap = make(map[string]int)

	// Extract package name from program
	for _, stmt := range program.Statements {
		if pkgStmt, ok := stmt.(*ast.PackageStatement); ok {
			cg.packageName = pkgStmt.Name.Value
			break
		}
	}

	// First pass: collect all string literals
	cg.collectStringLiterals(program)

	// Discipline analysis drives recursion lowering: self tail loops and
	// mutual tail trampolines (docs/spec/85-discipline.md).
	cg.programFunctions = make(map[string]*ast.FunctionStatement)
	for _, stmt := range program.Statements {
		if fn, ok := stmt.(*ast.FunctionStatement); ok && fn.Name != nil {
			cg.programFunctions[fn.Name.Value] = fn
		}
	}
	cg.trampolineMember = make(map[string]string)
	cg.trampolineGroups = make(map[string][]string)
	cg.trampolineEmitted = make(map[string]bool)
	for _, group := range discipline.AnalyzeProgram(program).TrampolineGroups {
		key := strings.Join(group, "_")
		cg.trampolineGroups[key] = group
		for _, member := range group {
			cg.trampolineMember[member] = key
		}
	}

	// Emit header includes and type aliases
	cg.emitHeader()

	// Emit string literal static arrays
	cg.emitStringLiterals()

	// Emit standard library ADTs first
	cg.emitBoolADT()
	cg.emitComparisonADT()

	// Emit type definitions (ADTs, records)
	// First, collect all ADT types for later lookup
	for _, stmt := range program.Statements {
		switch s := stmt.(type) {
		case *ast.ADTType:
			cg.adtTypes[s.Name.Value] = s
		}
	}

	// Now emit the type definitions
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

// collectStringLiterals collects all string literals from the program
func (cg *CodeGenerator) collectStringLiterals(program *ast.Program) {
	var collectFromExpr func(expr ast.Expression)
	var collectFromStmt func(stmt ast.Statement)

	collectFromExpr = func(expr ast.Expression) {
		switch e := expr.(type) {
		case *ast.StringLiteral:
			if _, exists := cg.stringLiteralMap[e.Value]; !exists {
				idx := len(cg.stringLiterals)
				cg.stringLiterals = append(cg.stringLiterals, e.Value)
				cg.stringLiteralMap[e.Value] = idx
			}
		case *ast.InfixExpression:
			collectFromExpr(e.Left)
			collectFromExpr(e.Right)
		case *ast.PrefixExpression:
			collectFromExpr(e.Right)
		case *ast.IndexExpression:
			collectFromExpr(e.Left)
			collectFromExpr(e.Index)
		case *ast.VariantExpression:
			if e.Payload != nil {
				collectFromExpr(e.Payload)
			}
		case *ast.InvocationExpression:
			collectFromExpr(e.Function)
			for _, arg := range e.Arguments {
				collectFromExpr(arg)
			}
		case *ast.MatchExpression:
			collectFromExpr(e.Scrutinee)
			for _, arm := range e.Arms {
				collectFromExpr(arm.Body)
			}
		case *ast.BlockExpression:
			if e.Block != nil {
				for _, st := range e.Block.Statements {
					collectFromStmt(st)
				}
			}
		case *ast.RecordLiteral:
			for _, fieldExpr := range e.Fields {
				collectFromExpr(fieldExpr)
			}
		case *ast.ArrayLiteral:
			for _, elem := range e.Elements {
				collectFromExpr(elem)
			}
		}
	}

	collectFromStmt = func(stmt ast.Statement) {
		switch s := stmt.(type) {
		case *ast.ExpressionStatement:
			collectFromExpr(s.Expression)
		case *ast.VariableDeclaration:
			if s.Value != nil {
				collectFromExpr(s.Value)
			}
		case *ast.WhileStatement:
			collectFromExpr(s.Condition)
			// Body is a BlockStatement, will be handled recursively
			for _, st := range s.Body.Statements {
				collectFromStmt(st)
			}
		case *ast.BlockStatement:
			for _, st := range s.Statements {
				collectFromStmt(st)
			}
		case *ast.AssignmentStatement:
			collectFromExpr(s.Value)
		}
	}

	// Collect from all top-level statements
	for _, stmt := range program.Statements {
		switch s := stmt.(type) {
		case *ast.FunctionStatement:
			collectFromExpr(s.Body)
		case *ast.ExpressionStatement:
			collectFromExpr(s.Expression)
		case *ast.VariableDeclaration:
			if s.Value != nil {
				collectFromExpr(s.Value)
			}
		case *ast.WhileStatement:
			collectFromExpr(s.Condition)
			for _, st := range s.Body.Statements {
				collectFromStmt(st)
			}
		case *ast.BlockStatement:
			for _, st := range s.Statements {
				collectFromStmt(st)
			}
		}
	}
}

// emitStringLiterals emits static arrays for all string literals
func (cg *CodeGenerator) emitStringLiterals() {
	if len(cg.stringLiterals) == 0 {
		return
	}
	cg.write("/* String literals */\n")
	for i, str := range cg.stringLiterals {
		// Escape the string for C
		escaped := cg.escapeCString(str)
		cg.write(fmt.Sprintf("static const u8 str_lit_%d[] = \"%s\";\n", i, escaped))
	}
	cg.write("\n")
}

// escapeCString escapes a string for use in a C string literal
// Operates on bytes to preserve UTF-8 encoding correctly
func (cg *CodeGenerator) escapeCString(s string) string {
	var result strings.Builder
	for i := 0; i < len(s); i++ {
		b := s[i]
		switch b {
		case '\n':
			result.WriteString("\\n")
		case '\r':
			result.WriteString("\\r")
		case '\t':
			result.WriteString("\\t")
		case '\\':
			result.WriteString("\\\\")
		case '"':
			result.WriteString("\\\"")
		default:
			if b < 32 || b > 126 {
				// Non-printable or non-ASCII byte – preserve exact UTF-8 byte value
				result.WriteString(fmt.Sprintf("\\x%02x", b))
			} else {
				result.WriteByte(b)
			}
		}
	}
	return result.String()
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
	cg.write("typedef u32 rune;   /* refined u32: docs/spec/70-strings.md section 9 */\n")
	cg.write("\n")
	// Emit string type definition
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
	loc := cg.getSourceLocation(adt.Token)
	// Use EndToken if available, otherwise fall back to last variant
	if adt.EndToken.Line > 0 {
		endLoc := cg.getSourceLocation(adt.EndToken)
		loc.EndLine = endLoc.Line
		loc.EndCol = endLoc.Column
		loc.ByteEnd = endLoc.ByteEnd
	} else if len(adt.Variants) > 0 {
		// Fallback: use last variant
		lastVariant := adt.Variants[len(adt.Variants)-1]
		if lastVariant.Literal != nil {
			if recordLit, ok := lastVariant.Literal.(*ast.RecordLiteral); ok {
				endLoc := cg.getSourceLocation(recordLit.EndToken)
				loc.EndLine = endLoc.Line
				loc.EndCol = endLoc.Column
				loc.ByteEnd = endLoc.ByteEnd
			} else {
				endLoc := cg.getSourceLocation(lastVariant.Name.Token)
				loc.EndLine = endLoc.Line
				loc.EndCol = endLoc.Column
				loc.ByteEnd = endLoc.ByteEnd
			}
		} else {
			endLoc := cg.getSourceLocation(lastVariant.Name.Token)
			loc.EndLine = endLoc.Line
			loc.EndCol = endLoc.Column
			loc.ByteEnd = endLoc.ByteEnd
		}
	}

	metadata := SourceMetadata{
		Source:     cg.formatSourceRange(loc),
		Package:    cg.packageName,
		Kind:       "ADT",
		Identifier: typeName,
	}
	cg.emitSourceLocationComment(metadata)

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
	variantName := variant.Name.Value
	funcName := fmt.Sprintf("%s_%s", typeName, variantName)

	// Emit source location comment for constructor
	loc := cg.getSourceLocation(variant.Token)
	metadata := SourceMetadata{
		Source:     cg.formatSourceRange(loc),
		Package:    cg.packageName,
		Kind:       "constructor",
		Identifier: fmt.Sprintf("%s::%s", typeName, variantName),
	}
	cg.emitSourceLocationComment(metadata)

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

	// Trampoline-group members are emitted once, together, as one engine
	// plus per-member wrappers.
	if key, isMember := cg.trampolineMember[funcName]; isMember {
		if !cg.trampolineEmitted[key] {
			cg.trampolineEmitted[key] = true
			cg.emitTrampolineGroup(cg.trampolineGroups[key], tc)
		}
		return
	}

	cFuncName := cg.cFunctionName(funcName)

	// Build Oak function signature
	signature := cg.buildFunctionSignature(fn)

	// Emit source location comment
	loc := cg.getSourceLocation(fn.Token)
	// Use EndToken if available
	if fn.EndToken.Line > 0 {
		endLoc := cg.getSourceLocation(fn.EndToken)
		loc.EndLine = endLoc.Line
		loc.EndCol = endLoc.Column
		loc.ByteEnd = endLoc.ByteEnd
	} else {
		// Fallback: estimate from body (shouldn't happen if parser is correct)
		loc.EndLine = loc.Line
		loc.EndCol = loc.Column
		loc.ByteEnd = loc.ByteStart
	}

	metadata := SourceMetadata{
		Source:     cg.formatSourceRange(loc),
		Package:    cg.packageName,
		Kind:       "function",
		Identifier: funcName,
		Signature:  signature,
	}
	cg.emitSourceLocationComment(metadata)

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

	// Self tail recursion compiles to a loop (docs/spec/85-discipline.md):
	// the tail self-call becomes parameter rebinding plus continue, so the
	// frame is reused and stack depth stays constant.
	lowered := discipline.SelfTailLoop(fn)
	if lowered {
		cg.tailLoopFunction = fn
		cg.write("  while (1) {\n")
	}

	// Emit function body (can be expression or block)
	cg.emitFunctionBody(fn.Body, tc)

	if lowered {
		cg.write("  }\n")
		cg.tailLoopFunction = nil
	}

	cg.indentLevel--
	cg.write("}\n")
	cg.write("\n")
}

// emitTrampolineGroup merges one mutual-tail cycle into a state-machine
// engine plus per-member wrappers (docs/spec/85-discipline.md): tail calls
// between members become state switches inside one frame, so the cycle
// consumes no stack.
func (cg *CodeGenerator) emitTrampolineGroup(members []string, tc *typechecker.TypeChecker) {
	engine := "oak_tramp_" + strings.Join(members, "_")
	stateType := engine + "_state"
	first := cg.programFunctions[members[0]]
	returnType := cg.parseTypeExpression(first.ReturnType)

	cg.write(fmt.Sprintf("/* trampoline for mutual tail recursion: %s */\n", strings.Join(members, ", ")))
	cg.write("typedef enum {\n")
	for i, member := range members {
		separator := ","
		if i == len(members)-1 {
			separator = ""
		}
		cg.write(fmt.Sprintf("    %s_%s%s\n", engine, member, separator))
	}
	cg.write(fmt.Sprintf("} %s;\n\n", stateType))

	cg.write(fmt.Sprintf("static %s %s( %s __oak_state", returnType, engine, stateType))
	for _, param := range first.Parameters {
		cg.write(fmt.Sprintf(", %s %s", cg.parseTypeExpression(param.Type), param.Name.Value))
	}
	cg.write(" ) {\n")
	cg.write("  while (1) {\n")
	cg.write("  switch (__oak_state) {\n")

	cg.tailGroup = make(map[string]string, len(members))
	for _, member := range members {
		cg.tailGroup[member] = engine + "_" + member
	}
	cg.tailGroupParams = first.Parameters
	for _, member := range members {
		fn := cg.programFunctions[member]
		cg.write(fmt.Sprintf("  case %s_%s: {\n", engine, member))
		cg.emitFunctionBody(fn.Body, tc)
		cg.write("  }\n")
	}
	cg.tailGroup = nil
	cg.tailGroupParams = nil

	cg.write("  }\n")
	cg.write("  }\n")
	cg.write("}\n\n")

	// Wrappers preserve each member's public identity.
	for _, member := range members {
		fn := cg.programFunctions[member]
		cg.write(fmt.Sprintf("%s %s( ", returnType, cg.cFunctionName(member)))
		for i, param := range fn.Parameters {
			if i > 0 {
				cg.write(", ")
			}
			cg.write(fmt.Sprintf("%s %s", cg.parseTypeExpression(param.Type), param.Name.Value))
		}
		cg.write(" ) {\n")
		cg.write(fmt.Sprintf("  return %s( %s_%s", engine, engine, member))
		for _, param := range fn.Parameters {
			cg.write(", " + param.Name.Value)
		}
		cg.write(" );\n")
		cg.write("}\n\n")
	}
}

// emitTailGroupContinue lowers a tail call between trampoline members:
// arguments are evaluated into temporaries, the shared parameters are
// rebound, the state switches to the callee, and the loop continues in the
// same frame.
func (cg *CodeGenerator) emitTailGroupContinue(call *ast.InvocationExpression, stateTag string, tc *typechecker.TypeChecker) {
	cg.write("  {\n")
	for i, param := range cg.tailGroupParams {
		if i >= len(call.Arguments) {
			break
		}
		paramType := cg.parseTypeExpression(param.Type)
		cg.write(fmt.Sprintf("    %s __oak_tail_%d = ", paramType, i))
		cg.emitExpressionFragment(call.Arguments[i], tc)
		cg.output.WriteString(";\n")
	}
	for i, param := range cg.tailGroupParams {
		if i >= len(call.Arguments) {
			break
		}
		cg.write(fmt.Sprintf("    %s = __oak_tail_%d;\n", param.Name.Value, i))
	}
	cg.write(fmt.Sprintf("    __oak_state = %s;\n", stateTag))
	cg.write("    continue;\n")
	cg.write("  }\n")
}

// emitTailLoopContinue lowers a tail self-call inside a loop-lowered function:
// arguments are evaluated into temporaries first so parameter rebinding is
// order-independent, then the loop continues in the same frame.
func (cg *CodeGenerator) emitTailLoopContinue(call *ast.InvocationExpression, tc *typechecker.TypeChecker) {
	fn := cg.tailLoopFunction
	cg.write("  {\n")
	for i, param := range fn.Parameters {
		if i >= len(call.Arguments) {
			break
		}
		paramType := cg.parseTypeExpression(param.Type)
		cg.write(fmt.Sprintf("    %s __oak_tail_%d = ", paramType, i))
		cg.emitExpressionFragment(call.Arguments[i], tc)
		cg.output.WriteString(";\n")
	}
	for i, param := range fn.Parameters {
		if i >= len(call.Arguments) {
			break
		}
		cg.write(fmt.Sprintf("    %s = __oak_tail_%d;\n", param.Name.Value, i))
	}
	cg.write("    continue;\n")
	cg.write("  }\n")
}

// emitFunctionBody emits the body of a function (expression or block)
// Note: FunctionStatement.Body is an Expression. Block bodies arrive as
// ast.BlockExpression with every statement retained; the trailing expression
// statement becomes the C return.
func (cg *CodeGenerator) emitFunctionBody(body ast.Expression, tc *typechecker.TypeChecker) {
	if block, ok := body.(*ast.BlockExpression); ok && block.Block != nil {
		cg.emitBlockStatement(block.Block, tc, true)
		return
	}
	cg.emitExpression(body, tc)
}

// emitExpression emits C code for an expression (as a return statement)
func (cg *CodeGenerator) emitExpression(expr ast.Expression, tc *typechecker.TypeChecker) {
	// In a loop-lowered function, the tail self-call in return position is
	// the loop's next iteration, not a call.
	if cg.tailLoopFunction != nil {
		if inv, ok := expr.(*ast.InvocationExpression); ok {
			if ident, ok := inv.Function.(*ast.Identifier); ok && ident.Value == cg.tailLoopFunction.Name.Value {
				cg.emitTailLoopContinue(inv, tc)
				return
			}
		}
	}
	// In a trampoline engine, a tail call to any group member is a state
	// switch inside the same frame, not a call.
	if cg.tailGroup != nil {
		if inv, ok := expr.(*ast.InvocationExpression); ok {
			if ident, ok := inv.Function.(*ast.Identifier); ok {
				if stateTag, isMember := cg.tailGroup[ident.Value]; isMember {
					cg.emitTailGroupContinue(inv, stateTag, tc)
					return
				}
			}
		}
	}
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
		// Emit string literal as a string struct
		idx, exists := cg.stringLiteralMap[e.Value]
		if !exists {
			// Should not happen if collectStringLiterals was called
			idx = len(cg.stringLiterals)
			cg.stringLiterals = append(cg.stringLiterals, e.Value)
			cg.stringLiteralMap[e.Value] = idx
		}
		// Create string struct: { .data = (u8*)str_lit_N, .len = LEN }
		cg.output.WriteString(fmt.Sprintf("( (string) { .data = (u8*)str_lit_%d, .len = %d } )", idx, len(e.Value)))
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
	case *ast.BlockExpression:
		if e.Block != nil {
			cg.emitBlockExpression(e.Block, tc)
		}
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
			// This is likely an ADT match
			cg.emitADTMatch(expr, tc)
			return
		}
	}

	// Scalar match
	cg.emitScalarMatch(expr, tc)
}

// emitADTMatch emits C code for ADT pattern matching
func (cg *CodeGenerator) emitADTMatch(expr *ast.MatchExpression, tc *typechecker.TypeChecker) {
	// Infer ADT type name from first variant pattern
	typeName := "Unknown"
	var adtDef *ast.ADTType
	if len(expr.Arms) > 0 {
		if variantPattern, ok := expr.Arms[0].Pattern.(*ast.VariantPattern); ok {
			// Try to find the ADT type by searching through known ADT types
			variantName := variantPattern.Variant.Value
			for name, adt := range cg.adtTypes {
				for _, variant := range adt.Variants {
					if variant.Name.Value == variantName {
						typeName = cg.cTypeName(name)
						adtDef = adt
						break
					}
				}
				if typeName != "Unknown" {
					break
				}
			}
		}
	}
	if typeName == "Unknown" {
		typeName = "ADT" // Fallback
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
					payloadType := cg.inferPayloadType(adtDef, variantName, tc)
					cg.write(fmt.Sprintf("      %s %s = scrutinee.payload.%s;\n", payloadType, payloadName, variantName))
				} else {
					// Payload is not a binding - this shouldn't happen in valid code
					cg.write("      /* payload extraction */\n")
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
		// Phantom-encoded strings share one representation: every Str[E]
		// lowers to the same C string struct (docs/spec/70-strings.md).
		if base, ok := indexExpr.Left.(*ast.Identifier); ok && base.Value == "Str" {
			return "string"
		}
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
	File      string
	Line      int
	Column    int
	EndLine   int // End line (LSP-style range)
	EndCol    int // End column (LSP-style range)
	ByteStart int // UTF-8 byte offset where construct starts
	ByteEnd   int // UTF-8 byte offset where construct ends
	Package   string
}

// SourceMetadata contains structured metadata for source location comments
type SourceMetadata struct {
	Source     string // file:line:col-line:col (LSP-style range)
	Package    string
	Kind       string // ADT, function, record, constructor, etc.
	Identifier string // Name of the construct
	Signature  string // Full signature (for functions)
}

// buildFunctionSignature reconstructs the Oak function signature from AST
func (cg *CodeGenerator) buildFunctionSignature(fn *ast.FunctionStatement) string {
	var sig strings.Builder

	sig.WriteString("fn")

	// Add receiver if method
	if fn.Receiver != nil {
		sig.WriteString(" (")
		sig.WriteString(fn.Receiver.Name.Value)
		sig.WriteString(": ")
		sig.WriteString(cg.typeExpressionToString(fn.Receiver.Type))
		sig.WriteString(")")
	}

	// Function name
	sig.WriteString(" ")
	sig.WriteString(fn.Name.Value)

	// Parameters
	sig.WriteString("(")
	for i, param := range fn.Parameters {
		if i > 0 {
			sig.WriteString(", ")
		}
		sig.WriteString(param.Name.Value)
		sig.WriteString(": ")
		sig.WriteString(cg.typeExpressionToString(param.Type))
	}
	sig.WriteString(")")

	// Return type
	if fn.ReturnType != nil {
		sig.WriteString(" -> ")
		sig.WriteString(cg.typeExpressionToString(fn.ReturnType))
	}

	return sig.String()
}

// typeExpressionToString converts a type expression AST node to a string
func (cg *CodeGenerator) typeExpressionToString(expr ast.Expression) string {
	if ident, ok := expr.(*ast.Identifier); ok {
		return ident.Value
	}
	// For more complex types (arrays, records, etc.), we'd need more handling
	// For now, return a placeholder
	return "/* type */"
}

// emitSourceLocationComment emits a structured C comment with source location metadata
func (cg *CodeGenerator) emitSourceLocationComment(metadata SourceMetadata) {
	cg.write("// @source: " + metadata.Source + "\n")
	cg.write("// @package: " + metadata.Package + "\n")
	cg.write("// @kind: " + metadata.Kind + "\n")
	if metadata.Identifier != "" {
		cg.write("// @identifier: " + metadata.Identifier + "\n")
	}
	if metadata.Signature != "" {
		cg.write("// @signature: " + metadata.Signature + "\n")
	}
}

// getSourceLocation extracts source location from a token
func (cg *CodeGenerator) getSourceLocation(tok token.Token) SourceLocation {
	return SourceLocation{
		File:      cg.sourceFile,
		Line:      tok.Line,
		Column:    tok.Column,
		EndLine:   tok.Line, // Default: same as start
		EndCol:    tok.Column,
		ByteStart: tok.ByteStart,
		ByteEnd:   tok.ByteEnd,
		Package:   cg.packageName,
	}
}

// formatSourceRange formats a source location as LSP-style range (file:startLine:startCol-endLine:endCol)
// Uses UTF-16 code units for character offsets (LSP standard)
func (cg *CodeGenerator) formatSourceRange(loc SourceLocation) string {
	// Convert UTF-8 positions (1-based) to UTF-16 positions (0-based for LSP)
	var startPos, endPos lsp.Position

	if cg.sourceText != "" && loc.ByteStart >= 0 && loc.ByteEnd >= 0 {
		// Use actual byte offsets from tokens for accurate conversion
		startPos = lsp.ConvertUTF8PositionToUTF16(cg.sourceText, loc.ByteStart, loc.Line)
		endPos = lsp.ConvertUTF8PositionToUTF16(cg.sourceText, loc.ByteEnd, loc.EndLine)
	} else {
		// Fallback: use column directly (assumes 1:1 mapping, which is true for ASCII)
		// This is less accurate but works when source text isn't available
		startPos = lsp.Position{
			Line:      loc.Line - 1,   // Convert to zero-based
			Character: loc.Column - 1, // Convert to zero-based
		}
		endPos = lsp.Position{
			Line:      loc.EndLine - 1, // Convert to zero-based
			Character: loc.EndCol - 1,  // Convert to zero-based
		}
	}

	if startPos.Line == endPos.Line && startPos.Character == endPos.Character {
		// Single position
		return fmt.Sprintf("%s:%d:%d", loc.File, startPos.Line, startPos.Character)
	}
	// Range
	return fmt.Sprintf("%s:%d:%d-%d:%d", loc.File, startPos.Line, startPos.Character, endPos.Line, endPos.Character)
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

// inferPayloadType infers the C type for an ADT variant's payload
func (cg *CodeGenerator) inferPayloadType(adtType *ast.ADTType, variantName string, tc *typechecker.TypeChecker) string {
	if adtType == nil {
		return "void*" // Fallback
	}

	// Find the variant in the ADT definition
	for _, variant := range adtType.Variants {
		if variant.Name.Value == variantName {
			// Check if variant has a payload type
			if variant.Payload != nil {
				return cg.parseTypeExpression(variant.Payload)
			}
			// No payload
			return "void"
		}
	}

	// Variant not found - fallback
	return "void*"
}

// findADTTypeByName finds an ADT type definition by name in the program
func (cg *CodeGenerator) findADTTypeByName(program *ast.Program, name string) *ast.ADTType {
	// This is a helper that would need access to the program
	// For now, we'll need to pass the program or maintain a map
	return nil
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

	// Comparison enum with explicit signed values
	cg.write("typedef enum oak_Comparison {\n")
	cg.indentLevel++
	cg.write("  oak_Comparison_Less    = -1,\n")
	cg.write("  oak_Comparison_Equal    = 0,\n")
	cg.write("  oak_Comparison_Greater  = 1\n")
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
	loc := cg.getSourceLocation(recordLit.Token)
	// Use EndToken if available
	if recordLit.EndToken.Line > 0 {
		endLoc := cg.getSourceLocation(recordLit.EndToken)
		loc.EndLine = endLoc.Line
		loc.EndCol = endLoc.Column
		loc.ByteEnd = endLoc.ByteEnd
	} else {
		// Fallback: use start position
		loc.EndLine = loc.Line
		loc.EndCol = loc.Column
		loc.ByteEnd = loc.ByteStart
	}

	metadata := SourceMetadata{
		Source:     cg.formatSourceRange(loc),
		Package:    cg.packageName,
		Kind:       "record",
		Identifier: typeName,
	}
	cg.emitSourceLocationComment(metadata)

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
