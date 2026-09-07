package codegen

import (
	"fmt"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/discipline"
	"github.com/SCKelemen/oak/lsp"
	"github.com/SCKelemen/oak/semir"
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
	// recordLayouts holds the resolved natural layout of each emitted
	// record type (semir.NaturalRecordLayout, the Oak.RecordLayoutRefinement
	// transliteration), for nested-record placement and layout assertions.
	recordLayouts map[string]semir.Representation
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
	// localTypes maps in-scope names to their container kind while a
	// function body is being emitted, so element access lowers to the right
	// bounds-checked form. Unknown containers fail closed.
	localTypes map[string]localContainer
}

// localContainer classifies a local binding for element-access lowering.
type localContainer struct {
	kind    containerKind
	length  int64  // ownedArray only
	element string // C element type for ownedArray/view/span
	adtName string // declared ADT name for containerADT
}

type containerKind int

const (
	containerUnknown containerKind = iota
	containerOwnedArray
	containerView
	containerSpan
	containerString
	containerADT
)

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
	cg.recordLayouts = make(map[string]semir.Representation)

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
	cg.emitAssertHelper()
	cg.emitUtf8Helper()
	cg.emitIntrinsicHelpers(program)
	cg.emitSimdSupport(program)
	cg.emitConversionHelpers(program)
	cg.emitAtomicGlobals(program)

	// Container typedefs (and their bounds-checked index helpers) must
	// precede the functions that use them: pre-emit every view/span element
	// type appearing in parameters and local declarations, and the element
	// views of variadic parameters.
	cg.preEmitContainerTypes(program)

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

	// Forward declarations: C requires declaration before use, and Oak
	// functions are order-independent.
	cg.emitFunctionPrototypes(program)

	// Emit function definitions
	for _, stmt := range program.Statements {
		switch s := stmt.(type) {
		case *ast.FunctionStatement:
			cg.emitFunction(s, tc)
		}
	}

	cg.emitEntryPoint()

	return cg.output.String(), nil
}

// emitEntryPoint emits the real C entry point when the program defines a
// top-level main: pure delegation to oak_main, nothing else. Programs
// without main stay library-style.
func (cg *CodeGenerator) emitEntryPoint() {
	mainFn, ok := cg.programFunctions["main"]
	if !ok || mainFn == nil || mainFn.Receiver != nil || len(mainFn.Parameters) != 0 {
		return
	}
	returnType := cg.parseTypeExpression(mainFn.ReturnType)
	cg.write("int main(void) {" + "\n")
	if returnType == "void" {
		cg.write(fmt.Sprintf("  %s();", cg.cFunctionName("main")) + "\n")
		cg.write("  return 0;" + "\n")
	} else {
		cg.write(fmt.Sprintf("  return (int)%s();", cg.cFunctionName("main")) + "\n")
	}
	cg.write("}" + "\n")
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
		case *ast.IfStatement:
			collectFromExpr(s.Condition)
			if s.Consequence != nil {
				collectFromStmt(s.Consequence)
			}
			if s.Alternative != nil {
				collectFromStmt(s.Alternative)
			}
		case *ast.BlockStatement:
			for _, st := range s.Statements {
				collectFromStmt(st)
			}
		case *ast.AssignmentStatement:
			collectFromExpr(s.Value)
		case *ast.IndexAssignmentStatement:
			collectFromExpr(s.Target.Left)
			collectFromExpr(s.Target.Index)
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
		case *ast.IfStatement:
			collectFromExpr(s.Condition)
			if s.Consequence != nil {
				collectFromStmt(s.Consequence)
			}
			if s.Alternative != nil {
				collectFromStmt(s.Alternative)
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

	// A record type declaration (one record-literal variant) is a struct,
	// not a tagged union (docs/spec/40-records.md).
	if recordLit, isRecord := recordDefinitionShape(adt); isRecord {
		cg.types[cName] = true
		cg.emitRecordTypeDef(typeName, recordLit)
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
	// Extern bindings have no Oak body; their foreign declaration was
	// emitted with the prototypes (docs/spec/92-ffi.md section 2.3).
	if fn.ExternSymbol != "" {
		return
	}

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
		if param.Variadic {
			// The body sees a read-only view of the caller-owned argument
			// array (docs/spec/10-syntax.md, variadic parameters).
			viewType := cg.emitViewType(cg.parseTypeExpression(param.Type))
			cg.write(fmt.Sprintf("%s %s", viewType, param.Name.Value))
		} else {
			cg.write(cg.cParameter(param.Type, param.Name.Value))
		}
		if i < len(fn.Parameters)-1 {
			cg.write(", ")
		}
	}

	cg.write(" ) {\n")
	cg.indentLevel++

	cg.localTypes = cg.buildLocalTypes(fn)
	defer func() { cg.localTypes = nil }()

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

// emitMatchReturn emits a lowerable-shape match (identifier scrutinee,
// literal/wildcard patterns) in return position as guarded statements. Arm
// bodies are emitted in return position themselves, so nested matches,
// returns, and loop/trampoline tail continues all compose.
func (cg *CodeGenerator) emitMatchReturn(match *ast.MatchExpression, tc *typechecker.TypeChecker) {
	for _, arm := range match.Arms {
		switch pattern := arm.Pattern.(type) {
		case *ast.LiteralPattern:
			cg.write("  if ( ")
			cg.emitExpressionFragment(match.Scrutinee, tc)
			cg.output.WriteString(" == ")
			cg.emitExpressionFragment(pattern.Value, tc)
			cg.output.WriteString(" ) {\n")
			cg.emitExpression(arm.Body, tc)
			cg.write("  }\n")
			continue
		case *ast.VariantPattern:
			// Guard strictly on the tag; the payload union is read only
			// under the matching guard.
			info := cg.localContainerOf(match.Scrutinee)
			if info.kind != containerADT {
				cg.write("  OAK_UNSUPPORTED_MATCH_SCRUTINEE;\n")
				return
			}
			adt := cg.adtTypes[info.adtName]
			cName := cg.cTypeName(info.adtName)
			variantName := pattern.Variant.Value
			cg.write("  if ( ")
			cg.emitExpressionFragment(match.Scrutinee, tc)
			cg.output.WriteString(fmt.Sprintf(".tag == %s_tag_%s ) {\n", cName, variantName))
			if binding, ok := pattern.Payload.(*ast.BindingPattern); ok && binding.Name != nil {
				payloadType := "OAK_UNKNOWN_PAYLOAD"
				for _, variant := range adt.Variants {
					if variant.Name.Value == variantName && variant.Payload != nil {
						payloadType = cg.parsePayloadType(variant.Payload)
					}
				}
				cg.write(fmt.Sprintf("    %s %s = ", payloadType, binding.Name.Value))
				cg.emitExpressionFragment(match.Scrutinee, tc)
				cg.output.WriteString(fmt.Sprintf(".payload.%s;\n", variantName))
			}
			cg.emitExpression(arm.Body, tc)
			cg.write("  }\n")
			continue
		}
		// Wildcard: unconditional; later arms are unreachable by
		// exhaustiveness analysis.
		cg.emitExpression(arm.Body, tc)
		return
	}
}

// preEmitContainerTypes emits the view/span typedefs and their index helpers
// for every container type expression in the program, so later per-function
// emission never writes a typedef mid-function.
func (cg *CodeGenerator) preEmitContainerTypes(program *ast.Program) {
	emit := func(typeExpr ast.Expression) {
		info := cg.classifyContainer(typeExpr)
		switch info.kind {
		case containerView:
			cg.emitViewType(info.element)
		case containerSpan:
			cg.emitSpanType(info.element)
		}
	}
	var walkStmt func(stmt ast.Statement)
	walkStmt = func(stmt ast.Statement) {
		switch s := stmt.(type) {
		case *ast.VariableDeclaration:
			if s.Type != nil {
				emit(s.Type)
			}
		case *ast.FunctionStatement:
			for _, param := range s.Parameters {
				if param.Variadic {
					cg.emitViewType(cg.parseTypeExpression(param.Type))
				} else if param.Type != nil {
					emit(param.Type)
				}
			}
			if block, ok := s.Body.(*ast.BlockExpression); ok && block.Block != nil {
				for _, inner := range block.Block.Statements {
					walkStmt(inner)
				}
			}
		case *ast.WhileStatement:
			if s.Body != nil {
				for _, inner := range s.Body.Statements {
					walkStmt(inner)
				}
			}
		case *ast.IfStatement:
			if s.Consequence != nil {
				walkStmt(s.Consequence)
			}
			if s.Alternative != nil {
				walkStmt(s.Alternative)
			}
		case *ast.BlockStatement:
			for _, inner := range s.Statements {
				walkStmt(inner)
			}
		case *ast.UnsafeBlock:
			if s.Body != nil {
				for _, inner := range s.Body.Statements {
					walkStmt(inner)
				}
			}
		}
	}
	for _, stmt := range program.Statements {
		walkStmt(stmt)
	}
}

// classifyContainer analyzes a type expression for element-access lowering.
func (cg *CodeGenerator) classifyContainer(typeExpr ast.Expression) localContainer {
	switch t := typeExpr.(type) {
	case *ast.Identifier:
		if t.Value == "string" {
			return localContainer{kind: containerString}
		}
		if _, isADT := cg.adtTypes[t.Value]; isADT {
			return localContainer{kind: containerADT, adtName: t.Value}
		}
	case *ast.IndexExpression:
		if base, ok := t.Left.(*ast.Identifier); ok && base.Value == "Str" {
			return localContainer{kind: containerString}
		}
		switch index := t.Index.(type) {
		case *ast.IntegerLiteral:
			return localContainer{
				kind:    containerOwnedArray,
				length:  index.Value,
				element: cg.parseTypeExpression(t.Left),
			}
		case *ast.Identifier:
			if index.Value == "" {
				return localContainer{kind: containerView, element: cg.parseTypeExpression(t.Left)}
			}
			if index.Value == "*" {
				return localContainer{kind: containerSpan, element: cg.parseTypeExpression(t.Left)}
			}
		}
	}
	return localContainer{kind: containerUnknown}
}

// buildLocalTypes indexes a function's parameters and local declarations for
// element-access lowering.
func (cg *CodeGenerator) buildLocalTypes(fn *ast.FunctionStatement) map[string]localContainer {
	table := make(map[string]localContainer)
	for _, param := range fn.Parameters {
		if param.Name == nil {
			continue
		}
		if param.Variadic {
			table[param.Name.Value] = localContainer{
				kind:    containerView,
				element: cg.parseTypeExpression(param.Type),
			}
			continue
		}
		table[param.Name.Value] = cg.classifyContainer(param.Type)
	}
	var walkStmt func(stmt ast.Statement)
	var walkExpr func(expr ast.Expression)
	walkStmt = func(stmt ast.Statement) {
		switch s := stmt.(type) {
		case *ast.VariableDeclaration:
			if s.Name != nil && s.Type != nil {
				table[s.Name.Value] = cg.classifyContainer(s.Type)
			}
		case *ast.WhileStatement:
			if s.Body != nil {
				for _, inner := range s.Body.Statements {
					walkStmt(inner)
				}
			}
		case *ast.BlockStatement:
			for _, inner := range s.Statements {
				walkStmt(inner)
			}
		case *ast.UnsafeBlock:
			if s.Body != nil {
				for _, inner := range s.Body.Statements {
					walkStmt(inner)
				}
			}
		case *ast.ExpressionStatement:
			walkExpr(s.Expression)
		}
	}
	walkExpr = func(expr ast.Expression) {
		if block, ok := expr.(*ast.BlockExpression); ok && block.Block != nil {
			for _, inner := range block.Block.Statements {
				walkStmt(inner)
			}
		}
	}
	if fn.Body != nil {
		walkExpr(fn.Body)
		if inv, ok := fn.Body.(*ast.InvocationExpression); ok {
			_ = inv
		}
	}
	return table
}

// localContainerOf resolves an expression's container classification; only
// identifiers are classified — everything else fails closed.
func (cg *CodeGenerator) localContainerOf(expr ast.Expression) localContainer {
	ident, ok := expr.(*ast.Identifier)
	if !ok || cg.localTypes == nil {
		return localContainer{kind: containerUnknown}
	}
	return cg.localTypes[ident.Value]
}

// primitiveCasts maps primitive constructor names to their C cast targets.
var primitiveCasts = map[string]string{
	"u8": "u8", "u16": "u16", "u32": "u32", "u64": "u64",
	"i8": "i8", "i16": "i16", "i32": "i32", "i64": "i64",
	"byte": "u8", "rune": "u32",
}

// emitCoreIndex lowers core_index(seq, i) to the bounds-checked access for
// the container kind (docs/spec/50-borrowing.md: out-of-range access is
// never undefined behavior). Unknown containers fail closed with a marker
// the C compiler rejects.
func (cg *CodeGenerator) emitCoreIndex(call *ast.InvocationExpression, tc *typechecker.TypeChecker) {
	seq, index := call.Arguments[0], call.Arguments[1]
	info := cg.localContainerOf(seq)
	switch info.kind {
	case containerView:
		cg.output.WriteString(fmt.Sprintf("oak_view_index_%s( ", info.element))
		cg.emitExpressionFragment(seq, tc)
		cg.output.WriteString(", (u64)( ")
		cg.emitExpressionFragment(index, tc)
		cg.output.WriteString(" ) )")
	case containerSpan:
		cg.output.WriteString(fmt.Sprintf("oak_span_index_%s( ", info.element))
		cg.emitExpressionFragment(seq, tc)
		cg.output.WriteString(", (u64)( ")
		cg.emitExpressionFragment(index, tc)
		cg.output.WriteString(" ) )")
	case containerOwnedArray:
		cg.output.WriteString("oak_index( ")
		cg.emitExpressionFragment(seq, tc)
		cg.output.WriteString(fmt.Sprintf(", %d, (u64)( ", info.length))
		cg.emitExpressionFragment(index, tc)
		cg.output.WriteString(" ) )")
	default:
		cg.output.WriteString("OAK_UNSUPPORTED_INDEX_TARGET")
	}
}

// emitBorrowConstruction lowers view(&owner) / span(&owner) to a struct
// literal over the owned array's storage with its static length. Unknown
// owners fail closed.
func (cg *CodeGenerator) emitBorrowConstruction(kind string, call *ast.InvocationExpression, tc *typechecker.TypeChecker) {
	prefix, ok := call.Arguments[0].(*ast.PrefixExpression)
	if !ok || prefix.Operator != "&" {
		cg.output.WriteString("OAK_UNSUPPORTED_BORROW_SOURCE")
		return
	}
	info := cg.localContainerOf(prefix.Right)
	if info.kind != containerOwnedArray {
		cg.output.WriteString("OAK_UNSUPPORTED_BORROW_SOURCE")
		return
	}
	structName := ""
	if kind == "view" {
		structName = cg.emitViewType(info.element)
	} else {
		structName = cg.emitSpanType(info.element)
	}
	cg.output.WriteString(fmt.Sprintf("(%s){ ", structName))
	cg.emitExpressionFragment(prefix.Right, tc)
	cg.output.WriteString(fmt.Sprintf(", %d }", info.length))
}

// emitLen lowers len(x): static length for owned arrays, the len field for
// views, spans, and strings.
func (cg *CodeGenerator) emitLen(call *ast.InvocationExpression, tc *typechecker.TypeChecker) {
	seq := call.Arguments[0]
	info := cg.localContainerOf(seq)
	switch info.kind {
	case containerOwnedArray:
		cg.output.WriteString(fmt.Sprintf("%d", info.length))
	case containerView, containerSpan, containerString:
		cg.output.WriteString("((u32)( ")
		cg.emitExpressionFragment(seq, tc)
		cg.output.WriteString(" ).len)")
	default:
		cg.output.WriteString("OAK_UNSUPPORTED_LEN_TARGET")
	}
}

// emitFunctionPrototypes forward-declares every top-level function so calls
// are order-independent in the emitted C.
func (cg *CodeGenerator) emitFunctionPrototypes(program *ast.Program) {
	emitted := false
	for _, stmt := range program.Statements {
		fn, ok := stmt.(*ast.FunctionStatement)
		if !ok || fn.Name == nil || fn.Receiver != nil {
			continue
		}
		if !emitted {
			cg.write("/* forward declarations */\n")
			emitted = true
		}
		// An extern binding declares the foreign symbol it asserts
		// (docs/spec/92-ffi.md section 2.3) instead of an Oak prototype.
		if fn.ExternSymbol != "" {
			cg.emitExternPrototype(fn)
			continue
		}
		returnType := cg.parseTypeExpression(fn.ReturnType)
		cg.write(fmt.Sprintf("%s %s( ", returnType, cg.cFunctionName(fn.Name.Value)))
		if len(fn.Parameters) == 0 {
			cg.write("void")
		}
		for i, param := range fn.Parameters {
			if param.Variadic {
				viewType := cg.emitViewType(cg.parseTypeExpression(param.Type))
				cg.write(fmt.Sprintf("%s %s", viewType, param.Name.Value))
			} else {
				cg.write(cg.cParameter(param.Type, param.Name.Value))
			}
			if i < len(fn.Parameters)-1 {
				cg.write(", ")
			}
		}
		cg.write(" );\n")
	}
	if emitted {
		cg.write("\n")
	}
}

// variadicCallee reports whether name is a known variadic function.
func (cg *CodeGenerator) variadicCallee(name string) (*ast.FunctionStatement, bool) {
	fn, ok := cg.programFunctions[name]
	if !ok || fn == nil || len(fn.Parameters) == 0 {
		return nil, false
	}
	last := fn.Parameters[len(fn.Parameters)-1]
	if last == nil || !last.Variadic {
		return nil, false
	}
	return fn, true
}

// emitVariadicCall lowers a call to a variadic function: fixed arguments
// pass through; the trailing arguments are materialized as a caller-owned
// stack array (a C99 compound literal, whose lifetime is the full
// expression) passed as a read-only view. No hidden allocation.
func (cg *CodeGenerator) emitVariadicCall(fn *ast.FunctionStatement, call *ast.InvocationExpression, tc *typechecker.TypeChecker) {
	fixed := len(fn.Parameters) - 1
	lastParam := fn.Parameters[fixed]
	elementType := cg.parseTypeExpression(lastParam.Type)
	viewType := cg.emitViewType(elementType)

	cg.output.WriteString(cg.cFunctionName(fn.Name.Value))
	cg.output.WriteString("( ")
	for i := 0; i < fixed && i < len(call.Arguments); i++ {
		if i > 0 {
			cg.output.WriteString(", ")
		}
		cg.emitExpressionFragment(call.Arguments[i], tc)
	}
	if fixed > 0 {
		cg.output.WriteString(", ")
	}

	trailing := call.Arguments[min(fixed, len(call.Arguments)):]
	if len(trailing) == 0 {
		cg.output.WriteString(fmt.Sprintf("(%s){ 0, 0 }", viewType))
	} else {
		cg.output.WriteString(fmt.Sprintf("(%s){ (%s[]){ ", viewType, elementType))
		for i, arg := range trailing {
			if i > 0 {
				cg.output.WriteString(", ")
			}
			cg.emitExpressionFragment(arg, tc)
		}
		cg.output.WriteString(fmt.Sprintf(" }, %d }", len(trailing)))
	}
	cg.output.WriteString(" )")
}

// cParameter renders one C parameter declaration, using C's inside-out
// declarator syntax for owned array parameters ([N]T). In C such parameters
// decay to pointers; the explicit-cost copy semantics of 50-borrowing
// section 8 for owned aggregates is tracked as backend debt.
func (cg *CodeGenerator) cParameter(typeExpr ast.Expression, name string) string {
	if indexExpr, ok := typeExpr.(*ast.IndexExpression); ok {
		if intLit, ok := indexExpr.Index.(*ast.IntegerLiteral); ok {
			element := cg.parseTypeExpression(indexExpr.Left)
			return fmt.Sprintf("%s %s[%d]", element, name, intLit.Value)
		}
	}
	return fmt.Sprintf("%s %s", cg.parseTypeExpression(typeExpr), name)
}

// runtimeBuiltins maps Oak builtins to the C runtime helpers emitted with
// every compilation unit.
var runtimeBuiltins = map[string]string{
	"assert":        "oak_assert",        // 85-discipline section 5: never elided
	"is_valid_utf8": "oak_is_valid_utf8", // 70-strings: Oak.Utf8Validity brackets
}

// emitUtf8Helper emits the zero-allocation UTF-8 validator: a C
// transliteration of the well-formed sequences proven in Oak.Utf8Validity
// (the third projection of one fact, after the Lean model and the Go
// ingestion validator). Bounds checks use u64 arithmetic so no view length
// can wrap them; the helper reads only v.len bytes and fails closed.
func (cg *CodeGenerator) emitUtf8Helper() {
	viewType := cg.emitViewType("u8")
	cg.write("/* core_slice: view construction as a brace initializer (declaration\n   position); field order matches the view/span structs {base, len} */\n#define core_slice(arr, lo, hi) { (arr) + (lo), (u32)((hi) - (lo)) }\n\n/* bounds-checked owned-array indexing: out-of-range traps, never UB */\nstatic inline u64 oak_bounds_trap(void) { __builtin_trap(); return 0; }\n#define oak_index(base, len, i) ((u64)(i) < (u64)(len) ? (base)[(i)] : (base)[oak_bounds_trap()])\n#define oak_store(base, len, i, v) do { if ((u64)(i) >= (u64)(len)) { __builtin_trap(); } (base)[(i)] = (v); } while (0)\n\n/* is_valid_utf8: Unicode Table 3-7, transliterated from Oak.Utf8Validity */\n")
	cg.write(fmt.Sprintf("static Bool oak_is_valid_utf8(%s v) {\n", viewType))
	cg.write("  u64 i = 0;\n")
	cg.write("  u64 n = (u64)v.len;\n")
	cg.write("  while (i < n) {\n")
	cg.write("    u8 b0 = v.base[i];\n")
	cg.write("    if (b0 <= 0x7F) { i += 1; continue; }\n")
	cg.write("    if (0xC2 <= b0 && b0 <= 0xDF) {\n")
	cg.write("      if (i + 1 >= n || v.base[i+1] < 0x80 || v.base[i+1] > 0xBF) { return oak_Bool_False; }\n")
	cg.write("      i += 2; continue;\n")
	cg.write("    }\n")
	cg.write("    if (b0 == 0xE0) {\n")
	cg.write("      if (i + 2 >= n || v.base[i+1] < 0xA0 || v.base[i+1] > 0xBF ||\n")
	cg.write("          v.base[i+2] < 0x80 || v.base[i+2] > 0xBF) { return oak_Bool_False; }\n")
	cg.write("      i += 3; continue;\n")
	cg.write("    }\n")
	cg.write("    if (0xE1 <= b0 && b0 <= 0xEC) {\n")
	cg.write("      if (i + 2 >= n || v.base[i+1] < 0x80 || v.base[i+1] > 0xBF ||\n")
	cg.write("          v.base[i+2] < 0x80 || v.base[i+2] > 0xBF) { return oak_Bool_False; }\n")
	cg.write("      i += 3; continue;\n")
	cg.write("    }\n")
	cg.write("    if (b0 == 0xED) {\n")
	cg.write("      if (i + 2 >= n || v.base[i+1] < 0x80 || v.base[i+1] > 0x9F ||\n")
	cg.write("          v.base[i+2] < 0x80 || v.base[i+2] > 0xBF) { return oak_Bool_False; }\n")
	cg.write("      i += 3; continue;\n")
	cg.write("    }\n")
	cg.write("    if (0xEE <= b0 && b0 <= 0xEF) {\n")
	cg.write("      if (i + 2 >= n || v.base[i+1] < 0x80 || v.base[i+1] > 0xBF ||\n")
	cg.write("          v.base[i+2] < 0x80 || v.base[i+2] > 0xBF) { return oak_Bool_False; }\n")
	cg.write("      i += 3; continue;\n")
	cg.write("    }\n")
	cg.write("    if (b0 == 0xF0) {\n")
	cg.write("      if (i + 3 >= n || v.base[i+1] < 0x90 || v.base[i+1] > 0xBF ||\n")
	cg.write("          v.base[i+2] < 0x80 || v.base[i+2] > 0xBF ||\n")
	cg.write("          v.base[i+3] < 0x80 || v.base[i+3] > 0xBF) { return oak_Bool_False; }\n")
	cg.write("      i += 4; continue;\n")
	cg.write("    }\n")
	cg.write("    if (0xF1 <= b0 && b0 <= 0xF3) {\n")
	cg.write("      if (i + 3 >= n || v.base[i+1] < 0x80 || v.base[i+1] > 0xBF ||\n")
	cg.write("          v.base[i+2] < 0x80 || v.base[i+2] > 0xBF ||\n")
	cg.write("          v.base[i+3] < 0x80 || v.base[i+3] > 0xBF) { return oak_Bool_False; }\n")
	cg.write("      i += 4; continue;\n")
	cg.write("    }\n")
	cg.write("    if (b0 == 0xF4) {\n")
	cg.write("      if (i + 3 >= n || v.base[i+1] < 0x80 || v.base[i+1] > 0x8F ||\n")
	cg.write("          v.base[i+2] < 0x80 || v.base[i+2] > 0xBF ||\n")
	cg.write("          v.base[i+3] < 0x80 || v.base[i+3] > 0xBF) { return oak_Bool_False; }\n")
	cg.write("      i += 4; continue;\n")
	cg.write("    }\n")
	cg.write("    return oak_Bool_False;\n")
	cg.write("  }\n")
	cg.write("  return oak_Bool_True;\n")
	cg.write("}\n\n")
}

// emitAssertHelper emits the always-on assertion primitive: TigerStyle
// assertions are compiled into every build mode, never elided
// (docs/spec/85-discipline.md section 5).
func (cg *CodeGenerator) emitAssertHelper() {
	cg.write("/* assert: always compiled in (docs/spec/85-discipline.md section 5) */\n")
	cg.write("static inline void oak_assert(Bool cond) {\n")
	cg.write("  if (!cond) {\n")
	cg.write("    __builtin_trap();\n")
	cg.write("  }\n")
	cg.write("}\n\n")
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
		cg.write(", " + cg.cParameter(param.Type, param.Name.Value))
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
		cg.localTypes = cg.buildLocalTypes(fn)
		cg.write(fmt.Sprintf("  case %s_%s: {\n", engine, member))
		cg.emitFunctionBody(fn.Body, tc)
		cg.write("  }\n")
		cg.localTypes = nil
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
			cg.write(cg.cParameter(param.Type, param.Name.Value))
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
	// A lowerable-shape match in return position emits as guarded statements
	// so arm bodies stay in return position: value arms return, tail calls
	// inside arms lower to loop/trampoline continues. The shape decision is
	// discipline.LowerableMatchShape — the same procedure the analyzer uses.
	if match, ok := expr.(*ast.MatchExpression); ok && discipline.LowerableMatchShape(match) {
		cg.emitMatchReturn(match, tc)
		return
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
			// Bare variant: resolve the ADT by unique variant name across
			// the program's declarations; ambiguity fails closed.
			adtName := ""
			for name, adt := range cg.adtTypes {
				for _, variant := range adt.Variants {
					if variant.Name.Value == e.Variant.Value {
						if adtName != "" && adtName != name {
							adtName = ""
							break
						}
						adtName = name
					}
				}
			}
			if adtName == "" {
				cg.output.WriteString("OAK_UNRESOLVED_VARIANT")
				return
			}
			constructorName := fmt.Sprintf("%s_%s", cg.cTypeName(adtName), e.Variant.Value)
			cg.output.WriteString(fmt.Sprintf("%s(", constructorName))
			if e.Payload != nil {
				cg.emitExpressionFragment(e.Payload, tc)
			}
			cg.output.WriteString(")")
		}
	case *ast.InvocationExpression:
		if cg.emitAtomicInvocation(e, tc) {
			return
		}
		// Function or method call. Runtime builtins lower to their always-on
		// helpers; calls to variadic functions bundle the trailing arguments
		// into a caller-owned stack array passed as a view.
		// Compiler-known library calls first: c conversions become explicit
		// casts, arm64 instruction functions become their helpers.
		if cg.emitLibraryCall(e, tc) {
			return
		}
		// Explicit integer conversions ({target}_{op}_{source}) lower to
		// their total two's-complement helpers.
		if cg.emitConversionCall(e, tc) {
			return
		}
		if ident, ok := e.Function.(*ast.Identifier); ok {
			if fn, isVariadicCallee := cg.variadicCallee(ident.Value); isVariadicCallee {
				cg.emitVariadicCall(fn, e, tc)
				return
			}
		}
		if ident, ok := e.Function.(*ast.Identifier); ok {
			if ident.Value == "core_index" && len(e.Arguments) == 2 {
				cg.emitCoreIndex(e, tc)
				return
			}
			if ident.Value == "len" && len(e.Arguments) == 1 {
				cg.emitLen(e, tc)
				return
			}
			if (ident.Value == "view" || ident.Value == "span") && len(e.Arguments) == 1 {
				cg.emitBorrowConstruction(ident.Value, e, tc)
				return
			}
			if target, isCast := primitiveCasts[ident.Value]; isCast && len(e.Arguments) == 1 {
				cg.output.WriteString(fmt.Sprintf("((%s)( ", target))
				cg.emitExpressionFragment(e.Arguments[0], tc)
				cg.output.WriteString(" ))")
				return
			}
		}
		if ident, ok := e.Function.(*ast.Identifier); ok && runtimeBuiltins[ident.Value] != "" {
			cg.output.WriteString(runtimeBuiltins[ident.Value])
		} else if ident, ok := e.Function.(*ast.Identifier); ok && cg.programFunctions[ident.Value] != nil {
			// Calls to program functions use the mangled C name; calls to
			// extern bindings use the validated foreign symbol raw
			// (docs/spec/92-ffi.md section 2.3).
			if target := cg.programFunctions[ident.Value]; target.ExternSymbol != "" {
				if typechecker.ValidCSymbol(target.ExternSymbol) {
					cg.output.WriteString(target.ExternSymbol)
				} else {
					cg.output.WriteString("OAK_INVALID_EXTERN_SYMBOL")
				}
			} else {
				cg.output.WriteString(cg.cFunctionName(ident.Value))
			}
		} else {
			cg.emitExpressionFragment(e.Function, tc)
		}
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
		case "()":
			return "void"
		default:
			// c-library boundary types carry their C spellings
			// (docs/spec/92-ffi.md section 2.1).
			if spelling, isCType := cQualifiedTypeSpelling(ident.Value); isCType {
				return spelling
			}
			// simd vector types lower to their struct typedefs
			// (docs/spec/93-simd.md section 1.4).
			if spelling, isSimd := simdQualifiedTypeSpelling(ident.Value); isSimd {
				return spelling
			}
			// Assume it's a type name
			return cg.cTypeName(ident.Value)
		}
	}

	// Handle array types: [N]T or []T
	// The parser represents array types as IndexExpression
	if indexExpr, ok := expr.(*ast.IndexExpression); ok {
		if cType, atomic := atomicTypeC(indexExpr); atomic {
			return cType
		}
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
		} else if marker, ok := indexExpr.Index.(*ast.Identifier); ok {
			// The parser represents []T as IndexExpression{Left: T, Index: ""}
			// and [*]T as IndexExpression{Left: T, Index: "*"}.
			elementType := cg.parseTypeExpression(indexExpr.Left)
			if marker.Value == "" {
				return cg.emitViewType(elementType)
			}
			if marker.Value == "*" {
				return cg.emitSpanType(elementType)
			}
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

	// Bounds-checked element access: out-of-range is a trap, never UB
	// (docs/spec/50-borrowing.md).
	cg.write(fmt.Sprintf("static inline %s oak_view_index_%s(%s v, u64 i) {\n", elementType, elementType, viewTypeName))
	cg.write("  if (i >= (u64)v.len) { __builtin_trap(); }\n")
	cg.write("  return v.base[i];\n")
	cg.write("}\n\n")

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

	// Bounds-checked element access: out-of-range is a trap, never UB
	// (docs/spec/50-borrowing.md).
	cg.write(fmt.Sprintf("static inline %s oak_span_index_%s(%s v, u64 i) {\n", elementType, elementType, spanTypeName))
	cg.write("  if (i >= (u64)v.len) { __builtin_trap(); }\n")
	cg.write("  return v.base[i];\n")
	cg.write("}\n\n")

	// Bounds-checked element store, symmetric with the load.
	cg.write(fmt.Sprintf("static inline void oak_span_store_%s(%s v, u64 i, %s value) {\n", elementType, spanTypeName, elementType))
	cg.write("  if (i >= (u64)v.len) { __builtin_trap(); }\n")
	cg.write("  v.base[i] = value;\n")
	cg.write("}\n\n")

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
	case *ast.IndexAssignmentStatement:
		cg.emitIndexAssignment(s, tc)
	case *ast.WhileStatement:
		cg.emitWhileStatement(s, tc)
	case *ast.IfStatement:
		cg.emitIfStatement(s, tc)
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

// emitIndexAssignment emits a bounds-checked element store: spans go through
// the trapping helper, owned arrays through the static-length store guard;
// unknown targets fail closed.
func (cg *CodeGenerator) emitIndexAssignment(stmt *ast.IndexAssignmentStatement, tc *typechecker.TypeChecker) {
	info := cg.localContainerOf(stmt.Target.Left)
	switch info.kind {
	case containerSpan:
		cg.write(fmt.Sprintf("  oak_span_store_%s( ", info.element))
		cg.emitExpressionFragment(stmt.Target.Left, tc)
		cg.output.WriteString(", (u64)( ")
		cg.emitExpressionFragment(stmt.Target.Index, tc)
		cg.output.WriteString(" ), ")
		cg.emitExpressionFragment(stmt.Value, tc)
		cg.output.WriteString(" );\n")
	case containerOwnedArray:
		cg.write("  oak_store( ")
		cg.emitExpressionFragment(stmt.Target.Left, tc)
		cg.output.WriteString(fmt.Sprintf(", %d, (u64)( ", info.length))
		cg.emitExpressionFragment(stmt.Target.Index, tc)
		cg.output.WriteString(" ), ")
		cg.emitExpressionFragment(stmt.Value, tc)
		cg.output.WriteString(" );\n")
	default:
		cg.write("  OAK_UNSUPPORTED_STORE_TARGET;\n")
	}
}

// emitVariableDeclaration emits a variable declaration
func (cg *CodeGenerator) emitVariableDeclaration(stmt *ast.VariableDeclaration, tc *typechecker.TypeChecker) {
	varName := stmt.Name.Value

	if stmt.Type != nil {
		if cType, atomic := atomicTypeC(stmt.Type); atomic {
			if stmt.Value != nil {
				cg.write("  OAK_ATOMIC_INITIALIZER_MUST_BE_ZERO_INIT;\n")
				return
			}
			cg.write(fmt.Sprintf("  %s %s = 0;\n", cType, varName))
			return
		}
	}

	// Owned arrays use C declarator syntax; value-less arrays are
	// zero-filled (definite-initialization semantics pending — the backend
	// never leaves storage uninitialized).
	if stmt.Type != nil {
		if info := cg.classifyContainer(stmt.Type); info.kind == containerOwnedArray {
			cg.write(fmt.Sprintf("  %s %s[%d]", info.element, varName, info.length))
			if stmt.Value == nil {
				cg.output.WriteString(" = {0}")
			} else {
				cg.output.WriteString(" = ")
				cg.emitExpressionFragment(stmt.Value, tc)
			}
			cg.output.WriteString(";\n")
			return
		}
	}

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

// emitIfStatement emits the statement-position conditional as C if/else
// (docs/spec/10-syntax.md).
func (cg *CodeGenerator) emitIfStatement(stmt *ast.IfStatement, tc *typechecker.TypeChecker) {
	cg.write("  if ( ")
	cg.emitExpressionFragment(stmt.Condition, tc)
	cg.write(" ) {\n")
	cg.indentLevel++
	if stmt.Consequence != nil {
		cg.emitBlockStatement(stmt.Consequence, tc, false)
	}
	cg.indentLevel--
	switch alternative := stmt.Alternative.(type) {
	case *ast.IfStatement:
		cg.write("  } else {\n")
		cg.indentLevel++
		cg.emitIfStatement(alternative, tc)
		cg.indentLevel--
		cg.write("  }\n")
	case *ast.BlockStatement:
		cg.write("  } else {\n")
		cg.indentLevel++
		cg.emitBlockStatement(alternative, tc, false)
		cg.indentLevel--
		cg.write("  }\n")
	default:
		cg.write("  }\n")
	}
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
	// C99 designated initializers in declaration order (deterministic
	// output; layout-significant order is the struct's own).
	if expr.TypeName != nil {
		// Typed construction is a compound literal usable in any
		// expression position: ((oak_Point){ .x = ..., .y = ... }).
		cg.output.WriteString(fmt.Sprintf("((%s)", cg.cTypeName(expr.TypeName.Value)))
	}
	cg.output.WriteString("{ ")
	first := true
	for _, field := range expr.FieldOrder {
		if !first {
			cg.output.WriteString(", ")
		}
		cg.output.WriteString(fmt.Sprintf(".%s = ", field.Name))
		cg.emitExpressionFragment(field.Value, tc)
		first = false
	}
	cg.output.WriteString(" }")
	if expr.TypeName != nil {
		cg.output.WriteString(")")
	}
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
