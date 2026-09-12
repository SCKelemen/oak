package codegen

import (
	"fmt"
	"github.com/SCKelemen/oak/asm"
	"path/filepath"
	"sort"
	"strconv"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/discipline"
	"github.com/SCKelemen/oak/lsp"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/semir"
	"github.com/SCKelemen/oak/token"
	"github.com/SCKelemen/oak/typechecker"
)

// CodeGenerator generates C code from Oak AST
type CodeGenerator struct {
	// refinementName resolves an application of a generic refinement to
	// literals (IrqId[4]) in a re-substituted template field to its
	// specialization's name (typechecker.RefinementApplicationName).
	refinementName func(ast.Expression) (string, bool)
	// equalityTypes caches the aggregates whose equality functions the
	// program needs (typechecker.EqualityTypes); nil until first asked.
	equalityTypes map[string]bool
	// atomicCarriers records every Atomic[T] carrier the program declares
	// storage for, so the lock-free admission block asserts exactly those
	// (docs/spec/65-machine-memory.md §6); atomicsIncluded says whether
	// <stdatomic.h> was emitted, which the block's macros need.
	atomicCarriers  map[string]bool
	atomicsIncluded bool
	// strictAdmission drops the OAK_ATOMIC_ACCEPT_LOCKED opt-out from the
	// lock-free admission block: a strict-profile build never accepts a
	// locked atomic fallback (docs/spec/85-discipline.md §7).
	strictAdmission bool
	// usesHostWrite records that the program binds the host package's
	// write shim, so the hosted definition of oak_host_write and the shim
	// are emitted (pay-for-use; every other program's C is unchanged).
	usesHostWrite bool
	// constantContext is set while emitting C integer constant expressions
	// (file-scope initializers, static_assert), where arithmetic must stay
	// a plain operator rather than a helper call.
	constantContext bool
	// inlineHelpers names the functions emitted as forced-inline helpers
	// (OAK_INLINE): private, leaf, loop-free, and short.
	inlineHelpers   map[string]bool
	asmFunctions    []*asm.Function
	nativeAsm       bool // asm units go to a companion object, not inline __asm__
	packageName     string
	sourceFile      string // Source file path for source location comments
	sourceText      string // Full source text for UTF-8 to UTF-16 conversion
	abstractAliases map[string]string
	sourceIndex     *lsp.PositionIndex
	output          strings.Builder
	bareCondition   bool // the next infix emitted is a statement condition (emitCondition)
	// launchCounter numbers the recorded test launches of a program, so
	// their temporaries never collide (codegen/launch.go).
	launchCounter int
	// mutatedGlobals names the top-level bindings some statement writes,
	// borrows, or addresses; the others may be C constants (globals.go).
	mutatedGlobals   map[string]bool
	indentLevel      int
	types            map[string]bool // Track emitted types to avoid duplicates
	typeChecker      *typechecker.TypeChecker
	typeEnv          map[string]typechecker.Type // Type environment for lookups
	stringLiterals   []string                    // Track string literals to emit as static arrays
	stringLiteralMap map[string]int              // Map string value to index
	adtTypes         map[string]*ast.ADTType     // Map ADT name to AST definition
	// fieldAccessors are context-specialized .field values. Each becomes a
	// static inline C function for one concrete record layout.
	fieldAccessors map[string]*ast.FieldAccessorExpression
	// scrutineeCounter names hoisted match-scrutinee temporaries.
	scrutineeCounter int
	// globalTypes classifies top-level bindings (static globals) the same
	// way localTypes classifies function locals.
	globalTypes map[string]localContainer
	// targetConstants are the program's `c.const` bindings and
	// foreignHeaders the distinct headers they name, sorted; a program with
	// any declares its extern bindings through asm labels so the headers'
	// own prototypes cannot conflict (docs/spec/92-ffi.md section 2.11).
	targetConstants map[string]*typechecker.TargetConstant
	foreignHeaders  []string
	// globalErrors collects top-level initializers the backend could not
	// place in static storage; Generate reports the first (OAK-T0501 as an
	// error at emission, ml finding F19).
	globalErrors []error
	// foldEnv holds the values of the constant globals emitted so far, so a
	// later constant initializer may read them (codegen/globals.go).
	foldEnv *object.Environment
	// constantGlobals names the globals emitted so far with constant
	// initializers; foldTypeHint is the annotated type of the global whose
	// initializer is being emitted.
	constantGlobals map[string]bool
	foldTypeHint    string
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
	// inCustodyWrap marks the inner emission of a custody transition call.
	inCustodyWrap bool
	sliceHelpers  map[string]string
	// foreignFnLocals maps the `c.Fn[...]` locals of the function being
	// emitted to their annotated signatures (docs/spec/92-ffi.md section
	// 2.10), so a call through one is cast to exactly that signature;
	// usesMessageSend gates the objc_msgSend declaration and the arm64
	// target guard on programs that send Objective-C messages
	// (docs/spec/92-ffi.md section 2.12).
	usesMessageSend bool
	// usesForeignFunctionAt gates the oak_fn_at helper on programs that
	// name a foreign function.
	foreignFnLocals       map[string]*ast.FunctionTypeExpression
	usesForeignFunctionAt bool
	// liftedLiterals is the C text of every typed function literal lifted
	// to a top-level function (emitFunctionLiteral); liftedCount names them
	// in emission order; liftedOffset is where the text is spliced — after
	// the prototypes, before the first definition that refers to one.
	liftedLiterals strings.Builder
	liftedCount    int
	liftedOffset   int
	// protocolTables records which protocols' transition tables (or
	// shift rows) have been emitted, so the three step functions share one.
	protocolTables map[string]bool
	// lineDirectives enables #line directives before every function and
	// statement (docs/spec/90-backend.md section 10), so C diagnostics and
	// debuggers attribute generated code to the Oak source line.
	lineDirectives bool
	// emittingBodies is set once function definitions begin: a type that
	// first appears there cannot receive a file-scope typedef any more
	// (codegen/arrays.go fails closed instead).
	emittingBodies bool
}

// localContainer classifies a local binding for element-access lowering.
type localContainer struct {
	kind    containerKind
	length  int64  // ownedArray only
	element string // C element type for ownedArray/view/span
	adtName string // declared ADT name for containerADT
	// elementType is the element's type expression for ownedArray, view,
	// and span, so an element that is itself a container (a row of a
	// [N][M]T grid) classifies through the same path.
	elementType ast.Expression
}

type containerKind int

const (
	containerUnknown containerKind = iota
	// containerBuffer is an owned foreign buffer Buffer[T]
	// (docs/spec/92-ffi.md section 2.8): the span struct {base, len}.
	containerBuffer
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
		fieldAccessors:   make(map[string]*ast.FieldAccessorExpression),
	}
}

// SetSourceFile sets the source file path for source location comments
func (cg *CodeGenerator) SetSourceFile(file string) {
	cg.sourceFile = file
}

// SetSourceText sets the full source text for UTF-8 to UTF-16 conversion
func (cg *CodeGenerator) SetSourceText(text string) {
	cg.sourceText = text
	cg.sourceIndex = nil
}

// Generate generates C code from an Oak program
func (cg *CodeGenerator) Generate(program *ast.Program, tc *typechecker.TypeChecker) (string, error) {
	if tc != nil {
		cg.refinementName = tc.RefinementApplicationName
	}
	cg.output.Reset()
	cg.sliceHelpers = make(map[string]string)
	cg.types = make(map[string]bool)
	cg.stringLiterals = []string{}
	cg.stringLiteralMap = make(map[string]int)
	cg.recordLayouts = make(map[string]semir.Representation)
	cg.fieldAccessors = make(map[string]*ast.FieldAccessorExpression)
	cg.globalErrors = nil

	// Extract package name from program
	for _, stmt := range program.Statements {
		if pkgStmt, ok := stmt.(*ast.PackageStatement); ok {
			cg.packageName = pkgStmt.Name.Value
			break
		}
	}

	// Target constants and the foreign headers they need (docs/spec/92-ffi.md
	// section 2.11), before the header is emitted.
	cg.targetConstants = make(map[string]*typechecker.TargetConstant)
	cg.foreignHeaders = nil
	if tc != nil {
		seen := map[string]bool{}
		for _, constant := range tc.TargetConstants() {
			cg.targetConstants[constant.Name] = constant
			if !seen[constant.Header] {
				seen[constant.Header] = true
				cg.foreignHeaders = append(cg.foreignHeaders, constant.Header)
			}
		}
		sort.Strings(cg.foreignHeaders)
	}

	// First pass: collect all string literals
	cg.collectStringLiterals(program)
	// Programs that name a foreign function at a pointer (docs/spec/92-ffi.md
	// section 2.10) get the oak_fn_at helper; no other program's C changes.
	cg.usesForeignFunctionAt = false
	cg.usesMessageSend = false
	scanCalls(program, func(library, member string) {
		if library == "c" && member == "fn_at" {
			cg.usesForeignFunctionAt = true
		}
		if library == "c" && member == "msg_send" {
			cg.usesMessageSend = true
		}
	})

	// Discipline analysis drives recursion lowering: self tail loops and
	// mutual tail trampolines (docs/spec/85-discipline.md).
	cg.programFunctions = make(map[string]*ast.FunctionStatement)
	for _, stmt := range program.Statements {
		if fn, ok := stmt.(*ast.FunctionStatement); ok && fn.Name != nil {
			if fn.Receiver == nil {
				cg.programFunctions[fn.Name.Value] = fn
			} else if identity, isMethod := methodIdentity(fn); isMethod {
				// Methods are known by the checker's Type::method identity
				// so they never shadow a function of the same bare name.
				cg.programFunctions[identity] = fn
			}
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
	cg.emitHeader(program)

	// Emit string literal static arrays
	cg.emitStringLiterals()

	// Emit standard library ADTs first
	cg.emitBoolADT()
	cg.emitStringEquality(tc)
	cg.emitComparisonADT()
	cg.emitAssertHelper()
	cg.emitUtf8Helper(program)
	cg.emitIntrinsicHelpers(program)
	cg.emitArgvHelper(program)
	cg.emitSimdSupport(program)
	cg.emitAtomicGlobals(program)

	// Container typedefs (and their bounds-checked index helpers) must
	// precede the functions that use them: pre-emit every view/span element
	// type appearing in parameters and local declarations, and the element
	// views of variadic parameters.

	// Emit type definitions (ADTs, records)
	// First, collect all ADT types for later lookup
	for _, stmt := range program.Statements {
		switch s := stmt.(type) {
		case *ast.ADTType:
			cg.adtTypes[s.Name.Value] = s
		}
	}

	// Now emit the type definitions in dependency order (codegen/mono.go):
	// records and record-template instantiations may reference each other
	// as field types (Thread holding an Idx[Thread] link, Ring[Thread, 8]
	// holding [8]Thread), so emission runs to a fixpoint — a type emits
	// once every field it needs is already placed. Generic templates are
	// never emitted; tagged-union ADTs follow the records they may carry
	// as payloads.
	cg.emitTypesInDependencyOrder(program, tc)
	cg.preEmitContainerTypes(program)
	cg.emitFieldAccessorHelpers()

	// Static globals come after type emission (record/ADT globals need
	// their typedefs) and before functions.
	cg.emitGlobals(program, tc)

	// Conversion helpers come after ADT emission: checked narrowing returns
	// a monomorphized Result (docs/spec/20-types.md §11.1).
	cg.emitConversionHelpers(program)
	cg.emitArithmeticHelpers(program)

	// Forward declarations: C requires declaration before use, and Oak
	// functions are order-independent.
	sliceHelperOffset := cg.output.Len()
	// Every type a body can name has a typedef by now; a wrapper typedef
	// requested past this point would land inside a function.
	cg.emittingBodies = true
	cg.emitFunctionPrototypes(program)
	cg.emitStaticAsserts(program, tc)
	cg.emitAsmUnits()
	cg.liftedOffset = cg.output.Len()

	// Emit function definitions
	for _, stmt := range program.Statements {
		switch s := stmt.(type) {
		case *ast.FunctionStatement:
			cg.emitFunction(s, tc)
		}
	}
	cg.emitExportWrappers(program)

	cg.emitEntryPoint()
	cg.emitAtomicAdmission()

	output := cg.output.String()
	if cg.liftedLiterals.Len() != 0 {
		output = output[:cg.liftedOffset] + "/* function literals lifted to plain functions: a literal is a code\n   pointer, never an environment (docs/spec/10-syntax.md section 3c) */\n" + cg.liftedLiterals.String() + output[cg.liftedOffset:]
	}
	if len(cg.sliceHelpers) != 0 {
		names := make([]string, 0, len(cg.sliceHelpers))
		for name := range cg.sliceHelpers {
			names = append(names, name)
		}
		sort.Strings(names)
		var helpers strings.Builder
		for _, name := range names {
			helpers.WriteString(cg.sliceHelpers[name])
		}
		output = output[:sliceHelperOffset] + helpers.String() + output[sliceHelperOffset:]
	}
	if len(cg.globalErrors) > 0 {
		return "", cg.globalErrors[0]
	}
	return output, nil
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
		case *ast.FieldAccessorExpression:
			if e.ResolvedRecord != "" {
				cg.fieldAccessors[e.ResolvedRecord+"\x00"+e.Field.Value] = e
			}
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
		case *ast.UnsafeBlock:
			// Literals inside an unsafe block (a `c.cstr("...\0")` at a
			// call through a foreign function pointer) are interned like
			// every other.
			if s.Body != nil {
				for _, st := range s.Body.Statements {
					collectFromStmt(st)
				}
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
func (cg *CodeGenerator) emitHeader(program *ast.Program) {
	cg.write("/* Generated C code from Oak */\n")
	cg.emitForeignHeaders()
	cg.write("#include <stdint.h>\n")
	cg.write("#include <stddef.h>\n")
	cg.usesHostWrite = programBindsExtern(program, "oak_host_write_call")
	cg.emitHostBoundary()
	// <math.h> and the float helpers only when the program uses floating
	// point, so every other program stays freestanding.
	usesFloats := programUsesFloats(program)
	if usesFloats {
		// <math.h> is a hosted header; the emitted float code needs only
		// signbit from it (the transcendental functions are Oak code in the
		// standard library), so a freestanding build (docs/spec/90-backend.md
		// §2a) takes the compiler's builtin and stays free of libm.
		cg.write("#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)\n#include <math.h>\n#else\n#ifndef signbit\n#define signbit(x) __builtin_signbit(x)\n#endif\n#ifndef isnan\n#define isnan(x) __builtin_isnan(x)\n#endif\n#ifndef isinf\n#define isinf(x) __builtin_isinf(x)\n#endif\n#ifndef isfinite\n#define isfinite(x) __builtin_isfinite(x)\n#endif\n#endif\n")
		cg.write("#include <float.h>\n")
		// Every operation rounds to its own type: no excess intermediate
		// precision (docs/spec/20-types.md section 11.3.3). A target that
		// evaluates in wider registers (x87) fails the build instead of
		// silently changing results.
		cg.write("#if FLT_EVAL_METHOD != 0\n#error \"Oak floating point requires FLT_EVAL_METHOD == 0: every operation rounds to its own type\"\n#endif\n")
		// Floating-point semantics are part of Oak's semantics, not of the
		// C compiler's optimization level: no contraction of a * b + c into
		// an fma, ever (docs/spec/20-types.md section 11.3.3, 90-backend.md
		// 7a). Clang honors the standard pragma; gcc does not implement it
		// (and warns under -Wunknown-pragmas), but never contracts in strict
		// ISO mode, and the drivers pass -ffp-contract=off besides.
		cg.write("#if defined(__clang__)\n#pragma STDC FP_CONTRACT OFF\n#endif\n")
	}
	cg.write("\n")

	// Emit primitive type aliases
	cg.write("/* the test host's launch recorder (docs/spec/110-testing.md, \"Launch targets\"): defined by the oak test harness */\n")
	cg.write("extern void oak_test_host_launch_begin(const char *kernel, uint32_t grid);\n")
	cg.write("extern void oak_test_host_launch_arg(const char *name, const char *kind, const char *element, const void *base, uint32_t bytes);\n")
	cg.write("extern void oak_test_host_launch_out(const char *name, const void *base, uint32_t bytes);\n")
	cg.write("extern void oak_test_host_launch_end(void);\n")
	cg.write("typedef uint8_t  u8;\n")
	if programReturnsNever(program) {
		// The uninhabited bottom carrier, emitted once and only when some
		// function (Oak-bodied or asm-backed) is declared never to return.
		cg.write("typedef u8 oak_never; /* uninhabited Oak bottom carrier */\n")
	}
	cg.write("typedef uint16_t u16;\n")
	cg.write("typedef uint32_t u32;\n")
	cg.write("typedef uint64_t u64;\n")
	// u128 is the compiler's 128-bit unsigned integer (docs/spec/20-types.md
	// section 11): 16 bytes at 16-byte alignment on every LP64 ABI. A C
	// compiler without one leaves the name undefined, so a program that
	// uses u128 fails to compile there rather than narrowing.
	cg.write("#if defined(__SIZEOF_INT128__)\ntypedef unsigned __int128 u128;\n#endif\n")
	cg.write("\n")
	cg.write("typedef int8_t   i8;\n")
	cg.write("typedef int16_t i16;\n")
	cg.write("typedef int32_t i32;\n")
	cg.write("typedef int64_t i64;\n")
	cg.write("\n")
	cg.write("typedef u8  byte;\n")
	cg.write("typedef u32 rune;   /* refined u32: docs/spec/70-strings.md section 9 */\n")
	cg.write("\n")
	cg.write("typedef float  f32; /* IEEE 754 binary32: docs/spec/20-types.md section 11.3 */\n")
	cg.write("typedef double f64; /* IEEE 754 binary64 */\n")
	cg.write("typedef uint16_t f16;  /* binary16 storage: load, store, widen, round only */\n")
	cg.write("typedef uint16_t bf16; /* bfloat16 storage */\n")
	cg.write("typedef uint8_t f8e4m3; /* OCP FP8 E4M3 storage: no infinities, NaN is S.1111.111 */\n")
	cg.write("typedef uint8_t f8e5m2; /* OCP FP8 E5M2 storage: IEEE-like */\n")
	cg.write("\n")
	if usesFloats {
		cg.writeRaw(floatPreamble)
	}
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

	// Generic templates have no representation of their own; their
	// instantiations are emitted by instantiateGenericADTs.
	if len(adt.TypeParams) > 0 {
		return
	}

	// A refinement declaration is a typedef of its base and a guard
	// (typechecker/refinements.go, docs/spec/20-types.md section 12).
	if adt.Refinement != nil {
		cg.types[cName] = true
		cg.emitRefinement(adt, cName, tc)
		return
	}
	// A record type declaration (one record-literal variant) is a struct,
	// not a tagged union (docs/spec/40-records.md).
	if recordLit, isRecord := recordDefinitionShape(adt); isRecord {
		cg.types[cName] = true
		cg.emitRecordTypeDef(typeName, recordLit)
		cg.emitRecordEquality(typeName, cName, tc)
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

	// Payload types resolve before the enum opens, so a payload that is an
	// owned array places its wrapper typedef at file scope
	// (codegen/arrays.go) rather than inside the union.
	for _, variant := range adt.Variants {
		if variant.Payload != nil {
			cg.parsePayloadType(variant.Payload)
		}
	}

	// Emit tag enum (with proper C style spacing)
	tagEnumName := fmt.Sprintf("%s_tag", cName)
	cg.write(fmt.Sprintf("typedef enum %s {\n", tagEnumName))
	cg.indentLevel++

	for i, variant := range adt.Variants {
		variantName := variant.Name.Value
		tagName := fmt.Sprintf("%s_tag_%s", cName, variantName)
		cg.write(fmt.Sprintf("  %s", tagName))
		if i < len(adt.TagValues) {
			// A representation choice recorded on the declaration (a
			// shift-DFA state type: tags are field offsets 6*i).
			cg.write(fmt.Sprintf(" = %d", adt.TagValues[i]))
		}
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

	// Emit struct. The tag is a fixed-width u32 holding the variant's
	// declaration index (the enum above names the values), so the union
	// has one shape on both sides of the C boundary (docs/spec/92-ffi.md
	// section 2.6); a C enum's width is implementation-defined.
	cg.write(fmt.Sprintf("typedef struct %s {\n", cName))
	cg.indentLevel++
	cg.write("  u32 tag;\n")

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
	cg.emitUnionLayout(typeName, cName, adt)

	// Emit constructors
	for _, variant := range adt.Variants {
		cg.emitADTConstructor(cName, variant)
	}
	cg.emitADTEquality(typeName, cName, tc)
}

// emitRefinement emits a refinement type: the base's typedef, so values
// carry the base representation everywhere, and the construction guard
// `oak_refine_Name`, which traps on a value outside the predicate. The
// predicate is emitted by the ordinary expression emitter over `value`.
func (cg *CodeGenerator) emitRefinement(adt *ast.ADTType, cName string, tc *typechecker.TypeChecker) {
	base := cg.parsePayloadType(adt.Variants[0].Payload)
	cg.write(fmt.Sprintf("typedef %s %s;\n", base, cName))
	saved := cg.output
	cg.output = strings.Builder{}
	cg.emitExpressionFragment(adt.Refinement, tc)
	predicate := cg.output.String()
	cg.output = saved
	cg.write(fmt.Sprintf("static inline %s oak_refine_%s( %s value ) { if ( !( %s ) ) { __builtin_trap(); } return value; }\n\n",
		cName, cName, base, predicate))
}

// equalityTerm is the C expression comparing two values of typ held in l
// and r: the operator for scalars, the generated function for aggregates
// (typechecker/equality.go states which types have one).
func (cg *CodeGenerator) equalityTerm(typ typechecker.Type, l, r string) string {
	switch t := typ.(type) {
	case *typechecker.UnitType:
		return "oak_Bool_True"
	case *typechecker.ADTType:
		return fmt.Sprintf("oak_eq_%s( %s, %s )", cg.cTypeName(t.Name), l, r)
	case *typechecker.NarrowedADTVariantType:
		return fmt.Sprintf("oak_eq_%s( %s, %s )", cg.cTypeName(t.ADTName), l, r)
	case *typechecker.RecordType:
		if t.Name != "" {
			return fmt.Sprintf("oak_eq_%s( %s, %s )", cg.cTypeName(t.Name), l, r)
		}
	case *typechecker.StringType:
		return fmt.Sprintf("oak_eq_string( %s, %s )", l, r)
	case *typechecker.ArrayType:
		if !t.IsSlice && !t.IsSpan {
			element := cg.parseTypeExpression(typeExpressionOf(t.ElementType))
			return fmt.Sprintf("%s( %s, %s )", cg.arrayEqualityName(element, t.Length), l, r)
		}
	}
	return fmt.Sprintf("( %s == %s )", l, r)
}

// typeExpressionOf spells a checked scalar type as the AST the C type
// mapping reads; the equality functions need it for array elements only.
func typeExpressionOf(typ typechecker.Type) ast.Expression {
	return &ast.Identifier{Value: typ.String()}
}

// equalityNeeded is the set of aggregates the program compares, closed
// under nesting; only those get an equality function, so a type the
// checker refused to compare never references a helper that does not
// exist.
func (cg *CodeGenerator) equalityNeeded(tc *typechecker.TypeChecker) map[string]bool {
	if cg.equalityTypes == nil {
		cg.equalityTypes = tc.EqualityTypes()
	}
	return cg.equalityTypes
}

// emitADTEquality emits the equality function of a concrete sum type:
// tags first, then the payload of the shared variant.
func (cg *CodeGenerator) emitADTEquality(typeName, cName string, tc *typechecker.TypeChecker) {
	if tc == nil || !cg.equalityNeeded(tc)[typeName] {
		return
	}
	variants, ok := tc.ADTVariants(typeName)
	if !ok {
		return
	}
	cg.write(fmt.Sprintf("static inline Bool oak_eq_%s( %s a, %s b ) {\n", cName, cName, cName))
	cg.write("  if ( a.tag != b.tag ) { return oak_Bool_False; }\n")
	cg.write("  switch ( a.tag ) {\n")
	for _, variant := range variants {
		if variant.Payload == nil {
			continue
		}
		if _, isUnit := variant.Payload.(*typechecker.UnitType); isUnit {
			continue
		}
		cg.write(fmt.Sprintf("    case %s_tag_%s: return %s;\n", cName, variant.Name,
			cg.equalityTerm(variant.Payload, "a.payload."+variant.Name, "b.payload."+variant.Name)))
	}
	cg.write("    default: return oak_Bool_True;\n")
	cg.write("  }\n")
	cg.write("}\n\n")
}

// emitStringEquality emits the string equality the program compares
// with, when it compares strings at all (typechecker/equality.go records
// the comparison): the lengths first, then the bytes, never a read past
// the shorter operand (docs/spec/70-strings.md).
func (cg *CodeGenerator) emitStringEquality(tc *typechecker.TypeChecker) {
	if tc == nil || !cg.equalityNeeded(tc)["string"] {
		return
	}
	cg.write("static inline Bool oak_eq_string( string a, string b ) {\n")
	cg.write("  if ( a.len != b.len ) { return oak_Bool_False; }\n")
	cg.write("  for ( u32 i = 0; i < a.len; i++ ) { if ( a.data[i] != b.data[i] ) { return oak_Bool_False; } }\n")
	cg.write("  return oak_Bool_True;\n")
	cg.write("}\n\n")
}

// emitRecordEquality emits the equality function of a declared record:
// every field in declaration order.
func (cg *CodeGenerator) emitRecordEquality(typeName, cName string, tc *typechecker.TypeChecker) {
	if tc == nil || !cg.equalityNeeded(tc)[typeName] {
		return
	}
	order, fields, ok := tc.RecordFields(typeName)
	if !ok {
		return
	}
	cg.write(fmt.Sprintf("static inline Bool oak_eq_%s( %s a, %s b ) {\n", cName, cName, cName))
	for _, field := range order {
		cg.write(fmt.Sprintf("  if ( !%s ) { return oak_Bool_False; }\n", cg.equalityTerm(fields[field], "a."+field, "b."+field)))
	}
	cg.write("  return oak_Bool_True;\n")
	cg.write("}\n\n")
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
	// Asm-backed declarations have their body emitted as an assembly
	// block beside the prototypes (docs/spec/94-assembler.md).
	if fn.ExternSymbol != "" || fn.Body == nil {
		return
	}
	if fn.AsmBacked || fn.NativeBacked {
		// The Oak fallback body realizes the signature where the asm unit
		// (or the natively lowered body) does not apply: another
		// architecture than the unit's lane, or the portable lowering.
		arch := fn.AsmArch
		if arch == "" {
			arch = asm.ArchArm64 // native bodies are AArch64
		}
		cg.write(fmt.Sprintf("#if !(%s) || defined(OAK_PORTABLE_INTRINSICS)\n", asm.ArchCondition(arch)))
		defer cg.write("#endif\n")
	}

	funcName := fn.Name.Value
	cFuncName := cg.cFunctionName(funcName)
	if fn.Receiver != nil {
		// A method is emitted under its Type::method identity with the
		// receiver as its first C parameter; the name is mangled
		// injectively so two types' methods, or a method and a function
		// of a similar spelling, never share a C symbol.
		identity, isMethod := methodIdentity(fn)
		if !isMethod {
			cg.write("OAK_UNSUPPORTED_RECEIVER_TYPE;\n")
			return
		}
		funcName = identity
		typeName, method, _ := strings.Cut(identity, "::")
		cFuncName = cg.cMethodName(typeName, method)
	}

	// Trampoline-group members are emitted once, together, as one engine
	// plus per-member wrappers.
	if key, isMember := cg.trampolineMember[funcName]; isMember {
		if !cg.trampolineEmitted[key] {
			cg.trampolineEmitted[key] = true
			cg.emitTrampolineGroup(cg.trampolineGroups[key], tc)
		}
		return
	}

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
	cg.emitLineDirective(fn.Token)
	cg.write(fmt.Sprintf("%s%s %s( ", cg.linkage(funcName), returnType, cFuncName))

	// If method, add receiver as first parameter
	if fn.Receiver != nil {
		receiverType := cg.parseTypeExpression(fn.Receiver.Type)
		receiverName := fn.Receiver.Name.Value
		cg.write(fmt.Sprintf("%s %s", receiverType, receiverName))
		if len(fn.Parameters) > 0 {
			cg.write(", ")
		}
	}

	// Emit parameters. An owned-array parameter is a wrapper-struct value
	// (codegen/arrays.go): C's by-value passing is the copy the language
	// specifies, so a store in the callee never reaches the caller.
	for i, param := range fn.Parameters {
		if param.Variadic {
			// The body sees a read-only view of the caller-owned argument
			// array (docs/spec/10-syntax.md, variadic parameters).
			viewType := cg.emitViewType(cg.parseTypeExpression(param.Type))
			cg.write(fmt.Sprintf("%s %s", viewType, cIdent(param.Name.Value)))
		} else {
			cg.write(cg.cParameter(param.Type, param.Name.Value))
		}
		if i < len(fn.Parameters)-1 {
			cg.write(", ")
		}
	}

	cg.write(" ) {\n")
	cg.indentLevel++

	cg.foreignFnLocals = nil
	cg.localTypes = cg.buildLocalTypes(fn)
	defer func() { cg.localTypes = nil; cg.foreignFnLocals = nil }()

	// A projected protocol step function has a compiler-known lowering
	// (docs/spec/90-backend.md section 14): the table or shift-DFA body
	// replaces the Oak body, which remains the meaning for the interpreter
	// and the Lean extraction.
	if fn.Lowering != nil {
		cg.emitProtocolLoweringBody(fn)
		cg.indentLevel--
		cg.write("}\n")
		cg.write("\n")
		return
	}

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

// boolMatchBranches recognizes a Bool condition match: two arms whose
// patterns are the true/false literals (a trailing wildcard covers the
// remaining case). Returns the branch bodies.
func boolMatchBranches(match *ast.MatchExpression) (trueBody, falseBody ast.Expression, ok bool) {
	if match.Scrutinee == nil || len(match.Arms) != 2 {
		return nil, nil, false
	}
	for i, arm := range match.Arms {
		switch pattern := arm.Pattern.(type) {
		case *ast.LiteralPattern:
			boolLit, isBool := pattern.Value.(*ast.Boolean)
			if !isBool {
				return nil, nil, false
			}
			if boolLit.Value {
				trueBody = arm.Body
			} else {
				falseBody = arm.Body
			}
		case *ast.WildcardPattern:
			if i != 1 {
				return nil, nil, false
			}
			if trueBody == nil {
				trueBody = arm.Body
			} else {
				falseBody = arm.Body
			}
		default:
			return nil, nil, false
		}
	}
	if trueBody == nil || falseBody == nil {
		return nil, nil, false
	}
	return trueBody, falseBody, true
}

// emitBoolMatchReturn emits a Bool condition match in return position as C
// if/else with both branches in return position.
func (cg *CodeGenerator) emitBoolMatchReturn(condition, trueBody, falseBody ast.Expression, tc *typechecker.TypeChecker) {
	cg.write("  if ( ")
	cg.emitCondition(condition, tc)
	cg.output.WriteString(" ) {\n")
	cg.indentLevel++
	cg.emitFunctionBody(trueBody, tc)
	cg.indentLevel--
	cg.write("  } else {\n")
	cg.indentLevel++
	cg.emitFunctionBody(falseBody, tc)
	cg.indentLevel--
	cg.write("  }\n")
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
			cg.emitMatchArmReturn(arm.Body, tc)
			cg.write("  }\n")
			continue
		case *ast.VariantPattern:
			// Guard strictly on the tag; the payload union is read only
			// under the matching guard.
			info := cg.localContainerOf(match.Scrutinee)
			if info.kind != containerADT {
				// The type checker's recorded instantiation covers
				// scrutinees the local-type table cannot classify
				// (typechecker/mono.go).
				if mangled, resolved := tc.MatchResolution(match); resolved {
					info = localContainer{kind: containerADT, adtName: mangled}
				} else {
					cg.write("  OAK_UNSUPPORTED_MATCH_SCRUTINEE;\n")
					return
				}
			}
			adt := cg.adtTypes[info.adtName]
			cName := cg.cTypeName(info.adtName)
			variantName := pattern.Variant.Value
			cg.write("  if ( ")
			cg.emitExpressionFragment(match.Scrutinee, tc)
			cg.output.WriteString(fmt.Sprintf(".tag == %s_tag_%s ) {\n", cName, variantName))
			restorePayload := func() {}
			if binding, ok := pattern.Payload.(*ast.BindingPattern); ok && binding.Name != nil {
				payloadType := "OAK_UNKNOWN_PAYLOAD"
				for _, variant := range adt.Variants {
					if variant.Name.Value == variantName && variant.Payload != nil {
						payloadType = cg.parsePayloadType(variant.Payload)
						restorePayload = cg.bindMatchContainer(binding.Name.Value, variant.Payload)
					}
				}
				cg.write(fmt.Sprintf("    %s %s = ", payloadType, cIdent(binding.Name.Value)))
				cg.emitExpressionFragment(match.Scrutinee, tc)
				cg.output.WriteString(fmt.Sprintf(".payload.%s;\n", variantName))
			}
			cg.emitMatchArmReturn(arm.Body, tc)
			restorePayload()
			cg.write("  }\n")
			continue
		}
		// Wildcard: unconditional; later arms are unreachable by
		// exhaustiveness analysis.
		cg.emitMatchArmReturn(arm.Body, tc)
		return
	}
	// Exhaustiveness is checked upstream; if control ever falls through the
	// guards, that impossibility is a fail-stop, never undefined behavior.
	cg.write("  __builtin_trap(); /* unreachable: exhaustive match */\n")
}

// Keep simple value arms in their existing expression form. A compound arm
// or a nested match needs statements; C99 has no block-valued expression.
func (cg *CodeGenerator) emitMatchArmReturn(body ast.Expression, tc *typechecker.TypeChecker) {
	if block, ok := body.(*ast.BlockExpression); ok && block.Block != nil {
		statements := block.Block.Statements
		compound := len(statements) != 1
		if len(statements) == 1 {
			if expr, ok := statements[0].(*ast.ExpressionStatement); ok {
				_, compound = expr.Expression.(*ast.MatchExpression)
			} else {
				compound = true
			}
		}
		if compound {
			cg.emitFunctionBody(body, tc)
			return
		}
	}
	cg.emitExpression(body, tc)
}

// emitMatchStatement emits a statement-position match (side-effecting
// arms) as tag-guarded statement blocks — the same structure as
// emitMatchReturn with bodies in statement position. Produced by the
// lowering hoist for value matches and by statement-position ADT matches.
func (cg *CodeGenerator) emitMatchStatement(match *ast.MatchExpression, tc *typechecker.TypeChecker) {
	emitBody := func(body ast.Expression) {
		if block, ok := body.(*ast.BlockExpression); ok && block.Block != nil {
			cg.emitBlockStatement(block.Block, tc, false)
		} else {
			cg.emitStatementExpression(body, tc)
		}
	}
	// Nested statement matches can reach codegen without IfStatement lowering.
	// Evaluate a Boolean condition once, before either arm can mutate its inputs.
	if trueBody, falseBody, isBool := boolMatchBranches(match); isBool {
		cg.write("  if ( ")
		cg.emitCondition(match.Scrutinee, tc)
		cg.output.WriteString(" ) {\n")
		cg.indentLevel++
		emitBody(trueBody)
		cg.indentLevel--
		cg.write("  } else {\n")
		cg.indentLevel++
		emitBody(falseBody)
		cg.indentLevel--
		cg.write("  }\n")
		return
	}
	// A non-identifier scrutinee (matching on a call result) evaluates
	// exactly once: hoist it into a temporary, then guard on the
	// temporary — never re-evaluate per arm.
	if _, isIdent := match.Scrutinee.(*ast.Identifier); !isIdent {
		if mangled, resolved := tc.MatchResolution(match); resolved {
			if _, known := cg.adtTypes[mangled]; known {
				tmp := fmt.Sprintf("oak__scrutinee_%d", cg.scrutineeCounter)
				cg.scrutineeCounter++
				// The temporary is used through the identifier path, so its
				// declaration must carry the same C spelling.
				cg.write(fmt.Sprintf("  %s %s = ", cg.cTypeName(mangled), cIdent(tmp)))
				cg.emitExpressionFragment(match.Scrutinee, tc)
				cg.output.WriteString(";\n")
				if cg.localTypes == nil {
					cg.localTypes = map[string]localContainer{}
				}
				cg.localTypes[tmp] = localContainer{kind: containerADT, adtName: mangled}
				match = &ast.MatchExpression{
					BaseNode:  match.BaseNode,
					Token:     match.Token, // same position: resolution carries over
					Scrutinee: &ast.Identifier{Token: match.Token, Value: tmp},
					Arms:      match.Arms,
				}
			}
		}
	}
	guarded := false
	emitGuard := func() {
		if guarded {
			cg.write("  else if ( ")
		} else {
			cg.write("  if ( ")
		}
		guarded = true
	}
	for _, arm := range match.Arms {
		switch pattern := arm.Pattern.(type) {
		case *ast.LiteralPattern:
			emitGuard()
			cg.emitExpressionFragment(match.Scrutinee, tc)
			cg.output.WriteString(" == ")
			cg.emitExpressionFragment(pattern.Value, tc)
			cg.output.WriteString(" ) {\n")
			cg.indentLevel++
			emitBody(arm.Body)
			cg.indentLevel--
			cg.write("  }\n")
			continue
		case *ast.VariantPattern:
			info := cg.localContainerOf(match.Scrutinee)
			if info.kind != containerADT {
				if mangled, resolved := tc.MatchResolution(match); resolved {
					info = localContainer{kind: containerADT, adtName: mangled}
				} else {
					cg.write("  OAK_UNSUPPORTED_MATCH_SCRUTINEE;\n")
					return
				}
			}
			adt := cg.adtTypes[info.adtName]
			cName := cg.cTypeName(info.adtName)
			variantName := pattern.Variant.Value
			emitGuard()
			cg.emitExpressionFragment(match.Scrutinee, tc)
			cg.output.WriteString(fmt.Sprintf(".tag == %s_tag_%s ) {\n", cName, variantName))
			restorePayload := func() {}
			if binding, ok := pattern.Payload.(*ast.BindingPattern); ok && binding.Name != nil {
				payloadType := "OAK_UNKNOWN_PAYLOAD"
				for _, variant := range adt.Variants {
					if variant.Name.Value == variantName && variant.Payload != nil {
						payloadType = cg.parsePayloadType(variant.Payload)
						restorePayload = cg.bindMatchContainer(binding.Name.Value, variant.Payload)
					}
				}
				cg.write(fmt.Sprintf("    %s %s = ", payloadType, cIdent(binding.Name.Value)))
				cg.emitExpressionFragment(match.Scrutinee, tc)
				cg.output.WriteString(fmt.Sprintf(".payload.%s;\n", variantName))
			}
			cg.indentLevel++
			emitBody(arm.Body)
			cg.indentLevel--
			restorePayload()
			cg.write("  }\n")
			continue
		}
		// A fallback executes only when no preceding arm matched.
		if guarded {
			cg.write("  else {\n")
			cg.indentLevel++
		}
		emitBody(arm.Body)
		if guarded {
			cg.indentLevel--
			cg.write("  }\n")
		}
		return
	}
	// Every arm was guarded and none was a fallback. Exhaustiveness is
	// checked upstream, so the trailing branch is unreachable; emitting it
	// makes the C data flow total (a binding assigned in every arm is
	// assigned on every path the C compiler can see, so -Wall stays clean)
	// and turns the impossible fallthrough into a fail-stop, never UB.
	if guarded {
		cg.write("  else { __builtin_trap(); /* unreachable: exhaustive match */ }\n")
	}
}

// isLocalName reports whether name is a local (parameter or binding) of the
// function being emitted, which shadows a root function of the same name.
func (cg *CodeGenerator) isLocalName(name string) bool {
	_, isLocal := cg.localTypes[name]
	return isLocal
}

// Match payloads are scoped locals too. Preserve their declared container
// shape so record array fields keep bounds-checked indexing in each arm.
func (cg *CodeGenerator) bindMatchContainer(name string, typ ast.Expression) func() {
	if cg.localTypes == nil {
		cg.localTypes = make(map[string]localContainer)
	}
	previous, existed := cg.localTypes[name]
	cg.localTypes[name] = cg.classifyContainer(typ)
	return func() {
		if existed {
			cg.localTypes[name] = previous
		} else {
			delete(cg.localTypes, name)
		}
	}
}

// preEmitContainerTypes emits the view/span typedefs and their index helpers
// for every container type expression in the program, so later per-function
// emission never writes a typedef mid-function.
func (cg *CodeGenerator) preEmitContainerTypes(program *ast.Program) {
	var emit func(typeExpr ast.Expression)
	emit = func(typeExpr ast.Expression) {
		switch t := typeExpr.(type) {
		case *ast.FunctionTypeExpression:
			for _, parameter := range t.Parameters {
				emit(parameter)
			}
			emit(t.Return)
		case *ast.IndexExpression:
			info := cg.classifyContainer(t)
			switch info.kind {
			case containerView:
				cg.emitViewType(info.element)
			case containerSpan, containerBuffer:
				cg.emitSpanType(info.element)
			case containerOwnedArray:
				// Resolving the spelling places the wrapper typedef (and
				// the typedefs of nested element arrays) at file scope; an
				// inline view(&owner) or span(&owner) of the array — the
				// source of a view_as — needs the element's view and span
				// structs at file scope too.
				cg.parseTypeExpression(t)
				if strings.HasPrefix(info.element, "oak_") {
					// Record elements only: a scalar's structs are placed
					// where the program first names the view or span.
					cg.emitViewType(info.element)
					cg.emitSpanType(info.element)
				}
			}
		}
	}
	walkTypePositions(program, emit)
	for _, stmt := range program.Statements {
		fn, isFunction := stmt.(*ast.FunctionStatement)
		if !isFunction {
			continue
		}
		for _, param := range fn.Parameters {
			if param.Variadic {
				cg.emitViewType(cg.parseTypeExpression(param.Type))
			}
		}
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
		if element, isBuffer := bufferElementSyntax(t); isBuffer {
			return localContainer{kind: containerBuffer, element: cg.parseTypeExpression(element), elementType: element}
		}
		if mangled, isGeneric := cg.genericAnnotationName(t); isGeneric {
			return localContainer{kind: containerADT, adtName: mangled}
		}
		switch index := t.Index.(type) {
		case *ast.IntegerLiteral:
			return localContainer{
				kind:        containerOwnedArray,
				length:      index.Value,
				element:     cg.parseTypeExpression(t.Left),
				elementType: t.Left,
			}
		case *ast.Identifier:
			if index.Value == "" {
				return localContainer{kind: containerView, element: cg.parseTypeExpression(t.Left), elementType: t.Left}
			}
			if index.Value == "*" {
				return localContainer{kind: containerSpan, element: cg.parseTypeExpression(t.Left), elementType: t.Left}
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
				// A `c.Fn[...]` local names a foreign function pointer
				// (docs/spec/92-ffi.md section 2.10); calls through it are
				// lowered as a cast to the annotated signature. Names are
				// unique within a function (no redeclaration), so the
				// annotation is looked up by name at the call.
				if fnExpr, isCFn := typechecker.CFnTypeExpression(s.Type); isCFn {
					if cg.foreignFnLocals == nil {
						cg.foreignFnLocals = make(map[string]*ast.FunctionTypeExpression)
					}
					cg.foreignFnLocals[s.Name.Value] = fnExpr
				}
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
	if call, ok := expr.(*ast.InvocationExpression); ok {
		if id, ok := call.Function.(*ast.Identifier); ok {
			switch id.Value {
			case "str_from_utf8":
				return localContainer{kind: containerString}
			case "str_bytes":
				return localContainer{kind: containerView, element: "u8"}
			}
		}
		// An inline borrow construction (`view(&x)`, `span(&x)`) classifies as
		// the view or span of x's element type, so slicing or measuring it in
		// expression position lowers through the same checked helpers a named
		// view uses (F20: the `core_slice` macro cannot take a compound literal).
		if id, ok := call.Function.(*ast.Identifier); ok && (id.Value == "view" || id.Value == "span") && len(call.Arguments) == 1 {
			if prefix, ok := call.Arguments[0].(*ast.PrefixExpression); ok && prefix.Operator == "&" {
				inner := cg.localContainerOf(prefix.Right)
				if inner.kind == containerOwnedArray || inner.kind == containerBuffer {
					kind := containerView
					if id.Value == "span" {
						kind = containerSpan
					}
					return localContainer{kind: kind, element: inner.element, elementType: inner.elementType}
				}
			}
		}
		if id, ok := call.Function.(*ast.Identifier); ok && id.Value == "core_slice" && len(call.Arguments) == 3 {
			info := cg.localContainerOf(call.Arguments[0])
			if info.kind == containerView || info.kind == containerSpan {
				return info
			}
		}
		if id, ok := call.Function.(*ast.Identifier); ok && id.Value == "core_index" && len(call.Arguments) == 2 {
			return cg.localContainerOf(&ast.IndexExpression{Left: call.Arguments[0], Index: call.Arguments[1]})
		}
		// A call to a program function classifies by its declared return
		// type: a region-indexed function returning a view
		// (docs/spec/50-borrowing.md section 8c) is indexed like the view.
		if id, ok := call.Function.(*ast.Identifier); ok && cg.programFunctions != nil {
			if fn, declared := cg.programFunctions[id.Value]; declared && fn.ReturnType != nil {
				if info := cg.classifyContainer(fn.ReturnType); info.kind != containerUnknown {
					return info
				}
			}
		}
	}
	if index, ok := expr.(*ast.IndexExpression); ok && !index.Dot {
		base := cg.localContainerOf(index.Left)
		if base.kind == containerOwnedArray || base.kind == containerView || base.kind == containerSpan {
			// An element that is itself a container (a row of a [N][M]T
			// grid, a view of arrays) classifies by its declared type.
			if base.elementType != nil {
				if element := cg.classifyContainer(base.elementType); element.kind != containerUnknown {
					return element
				}
			}
			name := strings.TrimPrefix(base.element, "oak_")
			if _, exists := cg.adtTypes[name]; exists {
				return localContainer{kind: containerADT, adtName: name}
			}
		}
	}
	// Record-field access paths resolve through the record's declared
	// field type: ring.buffer classifies as the [N]T it was declared as.
	if access, isAccess := expr.(*ast.IndexExpression); isAccess && access.Dot {
		base := cg.localContainerOf(access.Left)
		fieldIdent, isIdent := access.Index.(*ast.Identifier)
		if base.kind == containerADT && isIdent {
			if recordDecl, known := cg.adtTypes[base.adtName]; known {
				if recordLit, isRecord := recordDefinitionShape(recordDecl); isRecord {
					if fieldType, declared := recordLit.Fields[fieldIdent.Value]; declared {
						return cg.classifyContainer(fieldType)
					}
				}
			}
		}
		return localContainer{kind: containerUnknown}
	}
	ident, ok := expr.(*ast.Identifier)
	if !ok {
		return localContainer{kind: containerUnknown}
	}
	if cg.localTypes != nil {
		if info, isLocal := cg.localTypes[ident.Value]; isLocal && info.kind != containerUnknown {
			return info
		}
	}
	// Static globals: no-shadowing makes the fallback unambiguous.
	if info, isGlobal := cg.globalTypes[ident.Value]; isGlobal {
		return info
	}
	return localContainer{kind: containerUnknown}
}

// primitiveCasts maps primitive constructor names to their C cast targets.
var primitiveCasts = map[string]string{
	"u8": "u8", "u16": "u16", "u32": "u32", "u64": "u64", "u128": "u128",
	"i8": "i8", "i16": "i16", "i32": "i32", "i64": "i64",
	"byte": "u8", "rune": "u32",
	// f64(x: f32) is the one implicit floating-point move, an exact
	// widening; f32(literal) types the literal (docs/spec/20-types.md 11.3.4).
	"f32": "f32", "f64": "f64",
}

// emitCoreIndex lowers core_index(seq, i) to the bounds-checked access for
// the container kind (docs/spec/50-borrowing.md: out-of-range access is
// never undefined behavior). Unknown containers fail closed with a marker
// the C compiler rejects.
func (cg *CodeGenerator) emitCoreIndex(call *ast.InvocationExpression, tc *typechecker.TypeChecker) {
	seq, index := call.Arguments[0], call.Arguments[1]
	info := cg.localContainerOf(seq)
	// A proven access (typechecker/extents.go) needs no runtime check: the
	// fact that bounds it dominates this position.
	if tc.IndexProven(call.Token) {
		switch info.kind {
		case containerView, containerSpan:
			cg.output.WriteString("( ")
			cg.emitExpressionFragment(seq, tc)
			cg.output.WriteString(" ).base[ ")
			cg.emitExpressionFragment(index, tc)
			cg.output.WriteString(" ]")
			return
		case containerOwnedArray:
			cg.emitExpressionFragment(seq, tc)
			cg.output.WriteString(".v[ ")
			cg.emitExpressionFragment(index, tc)
			cg.output.WriteString(" ]")
			return
		}
	}
	if (info.kind == containerView || info.kind == containerSpan) && strings.HasPrefix(info.element, "oak_") {
		// A record element is read in place — the checked index selects
		// the element, and the field read that follows reads through it —
		// never returned by value from a helper: a 400 KiB state record
		// behind a span is one live instance, not a copy per read (the OS
		// pilot's R1; docs/spec/50-borrowing.md section 8e).
		cg.output.WriteString("( ")
		cg.emitExpressionFragment(seq, tc)
		cg.output.WriteString(" ).base[ oak_lv_idx( (u64)( ")
		cg.emitExpressionFragment(index, tc)
		cg.output.WriteString(" ), (u64)( ( ")
		cg.emitExpressionFragment(seq, tc)
		cg.output.WriteString(" ).len ) ) ]")
		return
	}
	switch info.kind {
	case containerView:
		cg.output.WriteString(fmt.Sprintf("oak_view_index_%s( ", elementIdent(info.element)))
		cg.emitExpressionFragment(seq, tc)
		cg.output.WriteString(", (u64)( ")
		cg.emitExpressionFragment(index, tc)
		cg.output.WriteString(" ) )")
	case containerSpan:
		cg.output.WriteString(fmt.Sprintf("oak_span_index_%s( ", elementIdent(info.element)))
		cg.emitExpressionFragment(seq, tc)
		cg.output.WriteString(", (u64)( ")
		cg.emitExpressionFragment(index, tc)
		cg.output.WriteString(" ) )")
	case containerOwnedArray:
		cg.output.WriteString("oak_index( ")
		cg.emitExpressionFragment(seq, tc)
		cg.output.WriteString(fmt.Sprintf(".v, %d, (u64)( ", info.length))
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
	if info.kind != containerOwnedArray && info.kind != containerBuffer {
		cg.output.WriteString("OAK_UNSUPPORTED_BORROW_SOURCE")
		return
	}
	structName := ""
	if kind == "view" {
		structName = cg.emitViewType(info.element)
	} else {
		structName = cg.emitSpanType(info.element)
	}
	if info.kind == containerBuffer {
		// A buffer is already a {base, len} pair (docs/spec/92-ffi.md
		// section 2.8): the borrow copies the pointer and the count.
		cg.output.WriteString(fmt.Sprintf("(%s){ ( ", structName))
		cg.emitExpressionFragment(prefix.Right, tc)
		cg.output.WriteString(" ).base, ( ")
		cg.emitExpressionFragment(prefix.Right, tc)
		cg.output.WriteString(" ).len }")
		return
	}
	cg.output.WriteString(fmt.Sprintf("(%s){ ", structName))
	cg.emitExpressionFragment(prefix.Right, tc)
	cg.output.WriteString(fmt.Sprintf(".v, %d }", info.length))
}

// emitLen lowers len(x): static length for owned arrays, the len field for
// views, spans, and strings.
func (cg *CodeGenerator) emitLen(call *ast.InvocationExpression, tc *typechecker.TypeChecker) {
	seq := call.Arguments[0]
	info := cg.localContainerOf(seq)
	switch info.kind {
	case containerOwnedArray:
		cg.output.WriteString(fmt.Sprintf("%d", info.length))
	case containerView, containerSpan, containerString, containerBuffer:
		cg.output.WriteString("((u32)( ")
		cg.emitExpressionFragment(seq, tc)
		cg.output.WriteString(" ).len)")
	default:
		cg.output.WriteString("OAK_UNSUPPORTED_LEN_TARGET")
	}
}

// programReturnsNever reports whether any function declares the never
// result — the pay-for-use condition for the bottom carrier typedef.
func programReturnsNever(program *ast.Program) bool {
	for _, stmt := range program.Statements {
		if fn, ok := stmt.(*ast.FunctionStatement); ok && fn.ReturnType != nil && fn.ReturnType.String() == "never" {
			return true
		}
	}
	return false
}

// emitLayoutBuiltin emits size_of/align_of/offset_of over the real emitted
// type, address_of as the code symbol's address, and static_assert as a
// compile-time check (a negative array size in a sizeof type is a C
// constraint violation, so a false condition fails the build). Reports
// whether the invocation was one of these.
func (cg *CodeGenerator) emitLayoutBuiltin(ident *ast.Identifier, e *ast.InvocationExpression, tc *typechecker.TypeChecker) bool {
	switch ident.Value {
	case "address_of":
		if len(e.Arguments) != 1 {
			return false
		}
		target, ok := e.Arguments[0].(*ast.Identifier)
		if !ok {
			return false
		}
		cg.output.WriteString(fmt.Sprintf("((u64)(uintptr_t)&%s)", cg.cFunctionName(target.Value)))
		return true
	case "static_assert":
		if len(e.Arguments) != 1 {
			return false
		}
		cg.output.WriteString("((void)sizeof(char[ (")
		cg.emitConstantExpression(e.Arguments[0], tc)
		cg.output.WriteString(") ? 1 : -1 ]))")
		return true
	case "size_of", "align_of", "offset_of":
		query, ok := tc.LayoutQueryAt(ident.Token)
		if !ok {
			cg.output.WriteString("OAK_UNRESOLVED_LAYOUT_QUERY")
			return true
		}
		typeName := query.TypeName
		if query.Record {
			typeName = cg.cTypeName(query.TypeName)
		}
		switch query.Kind {
		case "size_of":
			cg.output.WriteString(fmt.Sprintf("((u32)sizeof(%s))", typeName))
		case "align_of":
			cg.output.WriteString(fmt.Sprintf("((u32)_Alignof(%s))", typeName))
		case "offset_of":
			cg.output.WriteString(fmt.Sprintf("((u32)offsetof(%s, %s))", typeName, cIdent(query.Field)))
		}
		return true
	}
	return false
}

// emitConstantExpression emits an expression that C must accept as an
// integer constant expression: arithmetic stays a plain operator there.
func (cg *CodeGenerator) emitConstantExpression(expr ast.Expression, tc *typechecker.TypeChecker) {
	previous := cg.constantContext
	cg.constantContext = true
	cg.emitExpressionFragment(expr, tc)
	cg.constantContext = previous
}

// emitStaticAsserts emits top-level static_assert statements as typedef
// assertions once every type and global they may mention exists.
func (cg *CodeGenerator) emitStaticAsserts(program *ast.Program, tc *typechecker.TypeChecker) {
	count := 0
	for _, stmt := range program.Statements {
		exprStmt, ok := stmt.(*ast.ExpressionStatement)
		if !ok {
			continue
		}
		call, ok := exprStmt.Expression.(*ast.InvocationExpression)
		if !ok || len(call.Arguments) != 1 {
			continue
		}
		if ident, isIdent := call.Function.(*ast.Identifier); !isIdent || ident.Value != "static_assert" {
			continue
		}
		if count == 0 {
			cg.write("/* static_assert: the C compiler ratifies each layout claim */\n")
		}
		cg.write(fmt.Sprintf("typedef char oak_static_assert_%d[ (", count))
		cg.emitConstantExpression(call.Arguments[0], tc)
		cg.write(") ? 1 : -1 ];\n")
		count++
	}
	if count > 0 {
		cg.write("\n")
	}
}

// SetAsmFunctions supplies the checked asm-unit functions to emit.
func (cg *CodeGenerator) SetAsmFunctions(functions []*asm.Function) {
	cg.asmFunctions = functions
}

// SetNativeAsm selects the native realization of asm units: the Oak
// assembler encodes them into a companion object and the C keeps only
// their prototypes (docs/spec/94-assembler.md §9).
// SetStrictAdmission makes the lock-free admission block unconditional: the
// strict profile's zero-warning posture extends to the C build, which then
// cannot accept a locked atomic fallback with OAK_ATOMIC_ACCEPT_LOCKED
// (docs/spec/65-machine-memory.md §6, 85-discipline.md §7).
func (cg *CodeGenerator) SetStrictAdmission(strict bool) {
	cg.strictAdmission = strict
}

func (cg *CodeGenerator) SetNativeAsm(native bool) {
	cg.nativeAsm = native
}

// CFunctionName is the C symbol of an Oak function in this package — the
// name the companion object defines and its relocations reference.
func (cg *CodeGenerator) CFunctionName(oakName string) string {
	return cg.cFunctionName(oakName)
}

// emitAsmUnits emits every asm-unit function as a top-level assembly block
// under the C symbol its Oak prototype declared (docs/spec/94-assembler.md).
func (cg *CodeGenerator) emitAsmUnits() {
	if len(cg.asmFunctions) == 0 {
		return
	}
	if cg.nativeAsm {
		for _, fn := range cg.asmFunctions {
			cg.write(asm.EmitCExtern(fn, cg.cFunctionName(fn.Name)))
		}
		return
	}
	cg.write(asm.CPrelude)
	cg.write("\n")
	for _, fn := range cg.asmFunctions {
		cg.write(asm.EmitC(fn, cg.cFunctionName(fn.Name), cg.cFunctionName))
	}
}

// emitFunctionPrototypes forward-declares every top-level function so calls
// are order-independent in the emitted C.
// inlineHelperLines bounds the source span of a forced-inline helper.
const inlineHelperLines = 12

// computeInlineHelpers decides which functions are emitted as forced-inline
// helpers (docs/spec/90-backend.md section 9): private (not pub), named,
// non-generic, non-method, with an Oak body, calling no user function,
// containing no loop, and at most inlineHelperLines long. Exported and
// extern/asm-backed functions keep external linkage.
func (cg *CodeGenerator) computeInlineHelpers(program *ast.Program) {
	cg.inlineHelpers = make(map[string]bool)
	functions := make(map[string]*ast.FunctionStatement)
	for _, stmt := range program.Statements {
		if fn, ok := stmt.(*ast.FunctionStatement); ok && fn.Name != nil && fn.Receiver == nil {
			functions[fn.Name.Value] = fn
		}
	}
	for name, fn := range functions {
		if fn.Receiver != nil || fn.ExternSymbol != "" || fn.AsmBacked || fn.NativeBacked || fn.Body == nil ||
			fn.Exported || len(fn.TypeParams) > 0 || name == "main" {
			continue
		}
		if fn.EndToken.Line <= 0 || fn.EndToken.Line-fn.Token.Line > inlineHelperLines {
			continue
		}
		if _, isMember := cg.trampolineMember[name]; isMember {
			continue
		}
		if discipline.InlineHelperShape(fn, functions) {
			cg.inlineHelpers[name] = true
		}
	}
	// The derived JSON readers' hot helpers (compiler/codec_decode.go) are
	// forced inline wherever they are compiled in: the integer scanner and
	// its word arithmetic, whitespace skipping, the value boundary test,
	// and the decoded-key comparison sit inside every derived record
	// reader's loop, and a call there costs more than their bodies
	// (docs/spec/71-codecs.md section 19). They are exported and some
	// contain loops, so the shape rule above would not pick them.
	for _, name := range codecHotHelpers {
		fn := functions[name]
		if fn == nil || fn.Body == nil || fn.Receiver != nil || fn.ExternSymbol != "" || fn.AsmBacked ||
			fn.NativeBacked || len(fn.TypeParams) > 0 {
			continue
		}
		if _, isMember := cg.trampolineMember[name]; isMember {
			continue
		}
		cg.inlineHelpers[name] = true
	}
}

// codecHotHelpers are the standard library functions the derived JSON
// record readers call on their hot path (stdlib/json.oak).
var codecHotHelpers = []string{
	"json_scan_integer", "json_non_digit_mask", "json_word_value", "json_non_digit_mask32", "json_word_value32",
	"json_skip_space", "json_value_boundary", "json_key_decoded_equal",
}

// linkage returns the storage-class prefix for a function's prototype and
// definition. Forced-inline helpers are C99 `extern inline` with the
// always-inline attribute: every call inlines at every optimization level
// and the external definition is still emitted, so the symbol stays
// available to linkers and to assembly inspection.
func (cg *CodeGenerator) linkage(name string) string {
	if cg.inlineHelpers[name] {
		return "OAK_INLINE "
	}
	return ""
}

func (cg *CodeGenerator) emitFunctionPrototypes(program *ast.Program) {
	cg.computeInlineHelpers(program)
	emitted := false
	for _, stmt := range program.Statements {
		fn, ok := stmt.(*ast.FunctionStatement)
		if !ok || fn.Name == nil {
			continue
		}
		cName := cg.cFunctionName(fn.Name.Value)
		if fn.Receiver != nil {
			identity, isMethod := methodIdentity(fn)
			if !isMethod {
				continue
			}
			typeName, method, _ := strings.Cut(identity, "::")
			cName = cg.cMethodName(typeName, method)
		}
		if !emitted {
			cg.write("/* forward declarations; OAK_INLINE marks private leaf helpers the C\n   compiler must inline at every optimization level (the external\n   definition is still emitted: C99 extern inline) */\n")
			cg.write("#define OAK_INLINE extern inline __attribute__((always_inline))\n")
			emitted = true
		}
		// An extern binding declares the foreign symbol it asserts
		// (docs/spec/92-ffi.md section 2.3) instead of an Oak prototype.
		if fn.ExternSymbol != "" {
			cg.emitExternPrototype(fn)
			continue
		}
		returnType := cg.parseTypeExpression(fn.ReturnType)
		cg.write(fmt.Sprintf("%s%s %s( ", cg.linkage(fn.Name.Value), returnType, cName))
		if fn.Receiver != nil {
			cg.write(cg.cParameter(fn.Receiver.Type, fn.Receiver.Name.Value))
			if len(fn.Parameters) > 0 {
				cg.write(", ")
			}
		} else if len(fn.Parameters) == 0 {
			cg.write("void")
		}
		for i, param := range fn.Parameters {
			if param.Variadic {
				viewType := cg.emitViewType(cg.parseTypeExpression(param.Type))
				cg.write(fmt.Sprintf("%s %s", viewType, cIdent(param.Name.Value)))
			} else {
				cg.write(cg.cParameter(param.Type, param.Name.Value))
			}
			if i < len(fn.Parameters)-1 {
				cg.write(", ")
			}
		}
		cg.write(" );\n")
		// An explicit C ABI export is a second entry point with the
		// declared symbol (docs/spec/92-ffi.md section 2.9).
		if fn.ExportSymbol != "" {
			cg.write(fmt.Sprintf("%s %s( %s );\n", returnType, fn.ExportSymbol, cg.cParameterList(fn)))
		}
	}
	if emitted {
		cg.write("\n")
	}
}

// cParameterList spells a free function's parameters as a C parameter list
// (`void` when there are none), the way the prototype and definition do:
// owned arrays as wrapper structs, a variadic tail as a read-only view.
func (cg *CodeGenerator) cParameterList(fn *ast.FunctionStatement) string {
	if len(fn.Parameters) == 0 {
		return "void"
	}
	parts := make([]string, 0, len(fn.Parameters))
	for _, param := range fn.Parameters {
		if param.Variadic {
			viewType := cg.emitViewType(cg.parseTypeExpression(param.Type))
			parts = append(parts, fmt.Sprintf("%s %s", viewType, cIdent(param.Name.Value)))
		} else {
			parts = append(parts, cg.cParameter(param.Type, param.Name.Value))
		}
	}
	return strings.Join(parts, ", ")
}

// emitExportWrappers defines every explicit C ABI export
// (docs/spec/92-ffi.md section 2.9) as a forwarding function under its
// declared symbol: the Oak-internal definition keeps the elaborator's name
// for Oak callers, and the wrapper, one call the C compiler inlines, is the
// stable symbol a C consumer links. The type checker has already rejected
// symbols that are not C identifiers or that collide (OAK-F0108/F0109); the
// backend re-checks the grammar before emitting.
func (cg *CodeGenerator) emitExportWrappers(program *ast.Program) {
	emitted := false
	for _, stmt := range program.Statements {
		fn, ok := stmt.(*ast.FunctionStatement)
		if !ok || fn.Name == nil || fn.ExportSymbol == "" || fn.Receiver != nil || fn.ExternSymbol != "" || len(fn.TypeParams) != 0 {
			continue
		}
		if !typechecker.ValidCSymbol(fn.ExportSymbol) {
			cg.write(fmt.Sprintf("OAK_UNSUPPORTED_EXPORT_SYMBOL /* %q */\n", fn.ExportSymbol))
			continue
		}
		if !emitted {
			cg.write("/* C ABI exports (docs/spec/92-ffi.md section 2.9): stable symbols forwarding to the Oak definitions */\n")
			emitted = true
		}
		returnType := "void"
		if fn.ReturnType != nil {
			returnType = cg.parseTypeExpression(fn.ReturnType)
		}
		args := make([]string, 0, len(fn.Parameters))
		for _, param := range fn.Parameters {
			args = append(args, cIdent(param.Name.Value))
		}
		cg.write(fmt.Sprintf("%s %s( %s ) {\n", returnType, fn.ExportSymbol, cg.cParameterList(fn)))
		if returnType == "void" {
			cg.write(fmt.Sprintf("  %s( %s );\n}\n", cg.cFunctionName(fn.Name.Value), strings.Join(args, ", ")))
		} else {
			cg.write(fmt.Sprintf("  return %s( %s );\n}\n", cg.cFunctionName(fn.Name.Value), strings.Join(args, ", ")))
		}
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
	name = cIdent(name)
	if fn, ok := typeExpr.(*ast.FunctionTypeExpression); ok {
		return cg.cFunctionPointer(fn, name)
	}
	// An owned array is a wrapper-struct value (codegen/arrays.go): the
	// parameter is the callee's own copy, mutable like any local.
	return fmt.Sprintf("%s %s", cg.parseTypeExpression(typeExpr), name)
}

// ownedArrayParameter recognizes a fixed-length owned array type [N]T.
func ownedArrayParameter(typeExpr ast.Expression, cg *CodeGenerator) (element string, length int64, ok bool) {
	indexExpr, isIndex := typeExpr.(*ast.IndexExpression)
	if !isIndex {
		return "", 0, false
	}
	// A generic application (Ring[u8, 8]) is a record, not an array whose
	// element type happens to be indexed.
	if _, isGeneric := cg.genericAnnotationName(typeExpr); isGeneric {
		return "", 0, false
	}
	intLit, isLit := indexExpr.Index.(*ast.IntegerLiteral)
	if !isLit {
		return "", 0, false
	}
	return cg.parseTypeExpression(indexExpr.Left), intLit.Value, true
}

// cFunctionPointer renders a named C declarator for an Oak function type.
// Field accessors use ordinary function pointers: no closure environment,
// boxing, dispatch table, or allocation is introduced.
func (cg *CodeGenerator) cFunctionPointer(fn *ast.FunctionTypeExpression, name string) string {
	parameters := make([]string, 0, len(fn.Parameters))
	for _, parameter := range fn.Parameters {
		parameters = append(parameters, cg.parseTypeExpression(parameter))
	}
	if len(parameters) == 0 {
		parameters = append(parameters, "void")
	}
	return fmt.Sprintf("%s (*%s)(%s)", cg.parseTypeExpression(fn.Return), name, strings.Join(parameters, ", "))
}

func (cg *CodeGenerator) fieldAccessorCName(record, field string) string {
	return fmt.Sprintf("oak_field_%s_%s", cg.cTypeName(record), field)
}

// emitFieldAccessorHelpers materializes each context-specialized accessor
// as a tiny typed function. Sorting keeps generated C deterministic.
func (cg *CodeGenerator) emitFieldAccessorHelpers() {
	keys := make([]string, 0, len(cg.fieldAccessors))
	for key := range cg.fieldAccessors {
		keys = append(keys, key)
	}
	sort.Strings(keys)
	if len(keys) == 0 {
		return
	}
	cg.write("/* context-specialized Elm field accessors */\n")
	for _, key := range keys {
		accessor := cg.fieldAccessors[key]
		recordDecl := cg.adtTypes[accessor.ResolvedRecord]
		record, ok := recordDefinitionShape(recordDecl)
		if !ok {
			cg.write("OAK_UNRESOLVED_FIELD_ACCESSOR_RECORD;\n")
			continue
		}
		fieldType, found := record.Fields[accessor.Field.Value]
		if !found {
			cg.write("OAK_UNRESOLVED_FIELD_ACCESSOR_FIELD;\n")
			continue
		}
		cg.write(fmt.Sprintf("static inline %s %s(%s value) { return value.%s; }\n",
			cg.parseTypeExpression(fieldType),
			cg.fieldAccessorCName(accessor.ResolvedRecord, accessor.Field.Value),
			cg.cTypeName(accessor.ResolvedRecord),
			accessor.Field.Value))
	}
	cg.write("\n")
}

// programDefinesFunction reports whether the merged program declares a
// function under the given (package-internal) name.
func programDefinesFunction(program *ast.Program, name string) bool {
	if program == nil {
		return false
	}
	for _, stmt := range program.Statements {
		if fn, isFn := stmt.(*ast.FunctionStatement); isFn && fn.Name != nil && fn.Name.Value == name {
			return true
		}
	}
	return false
}

// runtimeBuiltins maps Oak builtins to the C runtime helpers emitted with
// every compilation unit.
var runtimeBuiltins = map[string]string{
	"assert":        "oak_assert",        // 85-discipline section 5: never elided
	"is_valid_utf8": "oak_is_valid_utf8", // 70-strings: Oak.Utf8Validity brackets
}

// emitUtf8Helper emits the zero-allocation UTF-8 validator behind
// is_valid_utf8 and str_from_utf8. In a module build the loader has pulled
// in the standard library's utf8 package whenever the program reaches
// either (compiler/modules.go reachesUtf8Builtin), and the helper is a call
// to the compiled utf8.valid — the vector program Oak.Utf8Blocks.program_valid
// proves decides Oak.Utf8Validity.Valid (docs/spec/70-strings.md section 8,
// 93-simd.md section 1.5). A bare source build has no packages, so it keeps
// the C transliteration of the well-formed sequences of Oak.Utf8Validity (the
// third projection of one fact, after the Lean model and the Go ingestion
// validator). Bounds checks use u64 arithmetic so no view length can wrap
// them; the helper reads only v.len bytes and fails closed.
func (cg *CodeGenerator) emitUtf8Helper(program *ast.Program) {
	viewType := cg.emitViewType("u8")
	cg.write("/* core_slice: view construction as a brace initializer (declaration\n   position); field order matches the view/span structs {base, len} */\n#define core_slice(arr, lo, hi) { (arr) + (lo), (u32)((hi) - (lo)) }\n\n/* bounds-checked owned-array indexing: out-of-range traps, never UB */\nstatic inline u64 oak_bounds_trap(void) { __builtin_trap(); return 0; }\n#define oak_index(base, len, i) ((u64)(i) < (u64)(len) ? (base)[(i)] : (base)[oak_bounds_trap()])\n/* checked index in lvalue position: pool[ oak_lv_idx(i, len) ].field = v */\nstatic inline u64 oak_lv_idx(u64 i, u64 len) { if (i >= len) { __builtin_trap(); } return i; }\n\n/* checked shifts: a count reaching the operand width traps, never UB\n   (docs/spec/10-syntax.md section 3b); constant counts fold the check away */\n#define OAK_SHIFT_HELPERS(T, W) \\\n  static inline T oak_shl_##T(T v, T n) { if (n >= W) { __builtin_trap(); } return (T)(v << n); } \\\n  static inline T oak_shr_##T(T v, T n) { if (n >= W) { __builtin_trap(); } return (T)(v >> n); }\nOAK_SHIFT_HELPERS(u8, 8u) OAK_SHIFT_HELPERS(u16, 16u) OAK_SHIFT_HELPERS(u32, 32u) OAK_SHIFT_HELPERS(u64, 64u)\n\n/* total fixed-width arithmetic (docs/spec/20-types.md section 11.1, 90-backend.md\n   section 7): results wrap mod 2^N, computed in unsigned space so no C\n   promotion overflows; signed results come back through a union pun (defined\n   since C99 TC3). Division by zero traps; MIN / -1 wraps. Never UB. */\n#define OAK_ARITH_U(T) \\\n  static inline T oak_add_##T(T a, T b) { return (T)((u64)a + (u64)b); } \\\n  static inline T oak_sub_##T(T a, T b) { return (T)((u64)a - (u64)b); } \\\n  static inline T oak_neg_##T(T a) { return (T)(0u - (u64)a); } \\\n  static inline T oak_mul_##T(T a, T b) { return (T)((u64)a * (u64)b); } \\\n  static inline T oak_div_##T(T a, T b) { if (b == 0) { __builtin_trap(); } return (T)(a / b); } \\\n  static inline T oak_rem_##T(T a, T b) { if (b == 0) { __builtin_trap(); } return (T)(a % b); }\n#define OAK_ARITH_I(T, U, MIN) \\\n  static inline T oak_pun_##T(U bits) { union { U from; T to; } pun; pun.from = bits; return pun.to; } \\\n  static inline T oak_add_##T(T a, T b) { return oak_pun_##T((U)((u64)(U)a + (u64)(U)b)); } \\\n  static inline T oak_sub_##T(T a, T b) { return oak_pun_##T((U)((u64)(U)a - (u64)(U)b)); } \\\n  static inline T oak_neg_##T(T a) { return oak_pun_##T((U)(0u - (u64)(U)a)); } \\\n  static inline T oak_mul_##T(T a, T b) { return oak_pun_##T((U)((u64)(U)a * (u64)(U)b)); } \\\n  static inline T oak_div_##T(T a, T b) { if (b == 0) { __builtin_trap(); } if (a == MIN && b == -1) { return a; } return (T)(a / b); } \\\n  static inline T oak_rem_##T(T a, T b) { if (b == 0) { __builtin_trap(); } if (b == -1) { return 0; } return (T)(a % b); }\nOAK_ARITH_U(u8) OAK_ARITH_U(u16) OAK_ARITH_U(u32) OAK_ARITH_U(u64)\nOAK_ARITH_I(i8, u8, INT8_MIN) OAK_ARITH_I(i16, u16, INT16_MIN) OAK_ARITH_I(i32, u32, INT32_MIN) OAK_ARITH_I(i64, u64, INT64_MIN)\n#if defined(__SIZEOF_INT128__)\n/* u128: unsigned __int128 arithmetic is defined mod 2^128 by C itself; the\n   helpers keep the one shape (division by zero traps, shifts checked) */\nOAK_SHIFT_HELPERS(u128, 128u)\nstatic inline u128 oak_add_u128(u128 a, u128 b) { return a + b; }\nstatic inline u128 oak_sub_u128(u128 a, u128 b) { return a - b; }\nstatic inline u128 oak_neg_u128(u128 a) { return (u128)0 - a; }\nstatic inline u128 oak_mul_u128(u128 a, u128 b) { return a * b; }\nstatic inline u128 oak_div_u128(u128 a, u128 b) { if (b == 0) { __builtin_trap(); } return a / b; }\nstatic inline u128 oak_rem_u128(u128 a, u128 b) { if (b == 0) { __builtin_trap(); } return a % b; }\n#endif\n#define oak_store(base, len, i, v) do { if ((u64)(i) >= (u64)(len)) { __builtin_trap(); } (base)[(i)] = (v); } while (0)\n\n/* is_valid_utf8: Unicode Table 3-7, transliterated from Oak.Utf8Validity */\n")
	if programDefinesFunction(program, "utf8__valid") {
		cg.write("/* is_valid_utf8: lowered to the standard library's vector validator utf8.valid\n   (stdlib/utf8.oak), which Oak.Utf8Blocks.program_valid proves decides Oak.Utf8Validity.Valid */\n")
		cg.write(fmt.Sprintf("Bool %s( %s bytes );\n", cg.cFunctionName("utf8__valid"), viewType))
		cg.write(fmt.Sprintf("static inline Bool oak_is_valid_utf8(%s v) { return %s( v ); }\n\n", viewType, cg.cFunctionName("utf8__valid")))
		return
	}
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
	// A failed assertion names its Oak source position before trapping
	// (docs/spec/85-discipline.md section 5). Hosted builds print it to
	// stderr; freestanding builds (-ffreestanding, or -DOAK_FREESTANDING)
	// keep the bare trap and no libc dependency.
	cg.write("#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)\n")
	cg.write("#include <stdio.h>\n")
	cg.write("static inline void oak_assert(Bool cond, const char *file, u32 line) {\n")
	cg.write("  if (!cond) {\n")
	cg.write("    fprintf(stderr, \"oak: assertion failed at %s:%u\\n\", file, (unsigned)line);\n")
	cg.write("    __builtin_trap();\n")
	cg.write("  }\n")
	cg.write("}\n")
	cg.write("#else\n")
	cg.write("static inline void oak_assert(Bool cond, const char *file, u32 line) {\n")
	cg.write("  if (!cond) {\n")
	cg.write("    oak_report(\"assertion failed\", file, line);\n")
	cg.write("    __builtin_trap();\n")
	cg.write("  }\n")
	cg.write("}\n")
	if cg.usesForeignFunctionAt {
		// c.fn_at(p) (docs/spec/92-ffi.md section 2.10): the one check the
		// backend can make on a foreign function pointer is that it is not
		// NULL, so a call through it never dereferences NULL; the trap
		// names the Oak source position as an assertion does. Emitted only
		// for programs that use the form, so every other program's C is
		// unchanged.
		cg.write("#endif\n")
		cg.write("#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)\n")
		cg.write("static inline void *oak_fn_at(void *p, const char *file, u32 line) {\n")
		cg.write("  if (p == 0) {\n")
		cg.write("    fprintf(stderr, \"oak: c.fn_at of a NULL pointer at %s:%u\\n\", file, (unsigned)line);\n")
		cg.write("    __builtin_trap();\n")
		cg.write("  }\n")
		cg.write("  return p;\n")
		cg.write("}\n")
		cg.write("#else\n")
		cg.write("static inline void *oak_fn_at(void *p, const char *file, u32 line) {\n")
		cg.write("  if (p == 0) { oak_report(\"c.fn_at of a NULL pointer\", file, line); __builtin_trap(); }\n")
		cg.write("  return p;\n")
		cg.write("}\n")
	}
	cg.write("#endif\n\n")
	if cg.usesMessageSend {
		// c.msg_send (docs/spec/92-ffi.md section 2.12): the Objective-C
		// runtime's one dispatch entry point, declared with no prototype so
		// each call casts it to the signature the program asserts. On arm64
		// every message goes through objc_msgSend itself; other targets
		// split struct and float returns into _stret/_fpret variants the
		// form does not select, so the build fails closed there. Emitted
		// only for programs that send messages.
		cg.write("#if !defined(__aarch64__) && !defined(__arm64__)\n")
		cg.write("#error \"c.msg_send is arm64-only in this increment: other targets route struct and float returns through objc_msgSend_stret/_fpret (docs/spec/92-ffi.md section 2.12)\"\n")
		cg.write("#endif\n")
		cg.write("extern void objc_msgSend(void);\n\n")
	}
	cg.emitAssertValueHelpers()
}

// emitHostBoundary emits the freestanding host boundary (docs/spec/90-backend.md
// §2a): one weak hook, oak_host_write, that a kernel or firmware may
// define; a diagnostic that a hosted build prints to stderr reaches the
// hook as one bounded line (fd 2) and then traps as before. Without the
// hook the diagnostic path is the bare trap. The text is assembled from
// compile-time literals and the Oak source position — no format strings,
// no libc — so the block is exactly what the object can promise: the
// hook is the only foreign symbol it introduces.
func (cg *CodeGenerator) emitHostBoundary() {
	// The hook's one prototype, in both build modes: the `host` package
	// binds it with c.extern (stdlib/host.oak), and emitExternPrototype
	// defers to this declaration so the two never disagree on the
	// signature. Hosted builds define it — weak, so a harness may still
	// supply its own — over the C library: fd 2 is stderr, anything else
	// stdout, flushed per call so a trap that follows loses nothing.
	// Pay-for-use: a program that never imports `host` gets exactly the
	// freestanding block it always got, and no hosted definition.
	if cg.usesHostWrite {
		cg.write("/* host boundary (docs/spec/90-backend.md section 2a): the one write hook */\n")
		cg.write("#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)\n")
		cg.write("#include <stdio.h>\n")
		cg.write("int64_t oak_host_write(int64_t fd, const uint8_t *buf, size_t len) __attribute__((weak));\n")
		cg.write("int64_t oak_host_write(int64_t fd, const uint8_t *buf, size_t len) {\n")
		cg.write("  FILE *out = fd == 2 ? stderr : stdout;\n")
		cg.write("  size_t n = fwrite(buf, 1, len, out);\n")
		cg.write("  fflush(out);\n")
		cg.write("  return (int64_t)n;\n")
		cg.write("}\n")
		cg.write("static inline int64_t oak_host_write_call(int64_t fd, const uint8_t *buf, size_t len) { return oak_host_write(fd, buf, len); }\n")
		cg.write("#else\n")
	} else {
		cg.write("#if !__STDC_HOSTED__ || defined(OAK_FREESTANDING)\n")
	}
	cg.write("/* freestanding host boundary (docs/spec/90-backend.md section 2a): a weak\n   hook the kernel or firmware may define; diagnostics reach it, then trap */\n")
	cg.write("extern int64_t oak_host_write(int64_t fd, const uint8_t *buf, size_t len) __attribute__((weak));\n")
	cg.write("static void oak_report(const char *what, const char *file, uint32_t line) {\n")
	cg.write("  if (&oak_host_write == 0) { return; }\n")
	cg.write("  uint8_t buf[192]; size_t n = 0;\n")
	cg.write("  const char *parts[4] = { \"oak: \", what, \" at \", file };\n")
	cg.write("  for (int p = 0; p < 4; p++) { for (const char *c = parts[p]; *c != 0 && n < sizeof buf - 16; c++) { buf[n++] = (uint8_t)*c; } }\n")
	cg.write("  buf[n++] = ':';\n")
	cg.write("  uint8_t digits[10]; int d = 0;\n")
	cg.write("  do { digits[d++] = (uint8_t)('0' + line % 10u); line /= 10u; } while (line != 0u);\n")
	cg.write("  while (d > 0) { buf[n++] = digits[--d]; }\n")
	cg.write("  buf[n++] = '\\n';\n")
	cg.write("  (void)oak_host_write(2, buf, n);\n")
	cg.write("}\n")
	if cg.usesHostWrite {
		cg.write("/* the host package's entry: a host that defined no hook takes nothing */\n")
		cg.write("static inline int64_t oak_host_write_call(int64_t fd, const uint8_t *buf, size_t len) {\n")
		cg.write("  if (&oak_host_write == 0) { return 0; }\n")
		cg.write("  return oak_host_write(fd, buf, len);\n")
		cg.write("}\n")
	}
	cg.write("#endif\n")
}

// programBindsExtern reports whether any extern binding in the program
// names the C symbol — the `host` package's `oak_host_write_call`, whose
// hosted definition and shim are emitted only for programs that import it.
func programBindsExtern(program *ast.Program, symbol string) bool {
	for _, stmt := range program.Statements {
		if fn, ok := stmt.(*ast.FunctionStatement); ok && fn.ExternSymbol == symbol {
			return true
		}
	}
	return false
}

// assertValueFormats spells each comparable operand type for the failure
// message of assert_eq/assert_ne: the C type, the printf conversion, and the
// cast that makes the conversion exact. Floats print with enough digits to
// round-trip (nine for binary32, seventeen for binary64), so the message
// identifies the exact value rather than a rounded reading of it.
var assertValueFormats = []struct{ name, ctype, format, cast string }{
	{"u8", "u8", "%llu", "(unsigned long long)"},
	{"u16", "u16", "%llu", "(unsigned long long)"},
	{"u32", "u32", "%llu", "(unsigned long long)"},
	{"u64", "u64", "%llu", "(unsigned long long)"},
	{"i8", "i8", "%lld", "(long long)"},
	{"i16", "i16", "%lld", "(long long)"},
	{"i32", "i32", "%lld", "(long long)"},
	{"i64", "i64", "%lld", "(long long)"},
	{"f32", "f32", "%.9g", "(double)"},
	{"f64", "f64", "%.17g", "(double)"},
}

// emitAssertValueHelpers emits oak_assert_eq_T / oak_assert_ne_T for every
// comparable type: the same always-on trap as oak_assert, whose hosted
// message names both values (docs/spec/85-discipline.md section 5).
func (cg *CodeGenerator) emitAssertValueHelpers() {
	cg.write("/* assert_eq / assert_ne: the failure names both values (85-discipline section 5) */\n")
	for _, f := range assertValueFormats {
		cg.write(fmt.Sprintf("static inline void oak_assert_eq_%s(%s got, %s want, const char *file, u32 line) {\n", f.name, f.ctype, f.ctype))
		cg.write("  if (!(got == want)) {\n")
		cg.write("#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)\n")
		cg.write(fmt.Sprintf("    fprintf(stderr, \"oak: assertion failed at %%s:%%u: got %s, want %s\\n\", file, (unsigned)line, %sgot, %swant);\n", f.format, f.format, f.cast, f.cast))
		cg.write("#else\n    oak_report(\"assertion failed (assert_eq; values need a hosted build)\", file, line);\n#endif\n")
		cg.write("    __builtin_trap();\n  }\n}\n")
		cg.write(fmt.Sprintf("static inline void oak_assert_ne_%s(%s got, %s want, const char *file, u32 line) {\n", f.name, f.ctype, f.ctype))
		cg.write("  if (got == want) {\n")
		cg.write("#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)\n")
		cg.write(fmt.Sprintf("    fprintf(stderr, \"oak: assertion failed at %%s:%%u: got %s, want anything but %s\\n\", file, (unsigned)line, %sgot, %swant);\n", f.format, f.format, f.cast, f.cast))
		cg.write("#else\n    oak_report(\"assertion failed (assert_ne; values need a hosted build)\", file, line);\n#endif\n")
		cg.write("    __builtin_trap();\n  }\n}\n")
	}
	// u128 has no printf conversion: the message spells both values as
	// two 64-bit hexadecimal halves.
	cg.write("#if defined(__SIZEOF_INT128__)\n")
	cg.write("static inline void oak_assert_eq_u128(u128 got, u128 want, const char *file, u32 line) {\n")
	cg.write("  if (!(got == want)) {\n")
	cg.write("#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)\n")
	cg.write("    fprintf(stderr, \"oak: assertion failed at %s:%u: got 0x%016llx%016llx, want 0x%016llx%016llx\\n\", file, (unsigned)line, (unsigned long long)(got >> 64), (unsigned long long)got, (unsigned long long)(want >> 64), (unsigned long long)want);\n")
	cg.write("#else\n    oak_report(\"assertion failed (assert_eq; values need a hosted build)\", file, line);\n#endif\n")
	cg.write("    __builtin_trap();\n  }\n}\n")
	cg.write("static inline void oak_assert_ne_u128(u128 got, u128 want, const char *file, u32 line) {\n")
	cg.write("  if (got == want) {\n")
	cg.write("#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)\n")
	cg.write("    fprintf(stderr, \"oak: assertion failed at %s:%u: got 0x%016llx%016llx, want anything but 0x%016llx%016llx\\n\", file, (unsigned)line, (unsigned long long)(got >> 64), (unsigned long long)got, (unsigned long long)(want >> 64), (unsigned long long)want);\n")
	cg.write("#else\n    oak_report(\"assertion failed (assert_ne; values need a hosted build)\", file, line);\n#endif\n")
	cg.write("    __builtin_trap();\n  }\n}\n")
	cg.write("#endif\n")
	cg.write("static inline void oak_assert_eq_Bool(Bool got, Bool want, const char *file, u32 line) {\n")
	cg.write("  if (!(got == want)) {\n")
	cg.write("#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)\n")
	cg.write("    fprintf(stderr, \"oak: assertion failed at %s:%u: got %s, want %s\\n\", file, (unsigned)line, got ? \"true\" : \"false\", want ? \"true\" : \"false\");\n")
	cg.write("#else\n    oak_report(got ? \"assertion failed: got true, want false\" : \"assertion failed: got false, want true\", file, line);\n#endif\n")
	cg.write("    __builtin_trap();\n  }\n}\n")
	cg.write("static inline void oak_assert_ne_Bool(Bool got, Bool want, const char *file, u32 line) {\n")
	cg.write("  if (got == want) {\n")
	cg.write("#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)\n")
	cg.write("    fprintf(stderr, \"oak: assertion failed at %s:%u: got %s, want anything but %s\\n\", file, (unsigned)line, got ? \"true\" : \"false\", want ? \"true\" : \"false\");\n")
	cg.write("#else\n    oak_report(got ? \"assertion failed: got true, want anything but true\" : \"assertion failed: got false, want anything but false\", file, line);\n#endif\n")
	cg.write("    __builtin_trap();\n  }\n}\n\n")
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
			cg.write(", " + cIdent(param.Name.Value))
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
		cg.write(fmt.Sprintf("    %s = __oak_tail_%d;\n", cIdent(param.Name.Value), i))
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
		cg.write(fmt.Sprintf("    %s = __oak_tail_%d;\n", cIdent(param.Name.Value), i))
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
	// A Bool condition match in return position emits as plain C if/else —
	// the condition evaluates exactly once, and arm bodies stay in return
	// position (blocks return their trailing value; tail calls lower to
	// loop/trampoline continues). The surface is one match form; the
	// lowering is what a C author would write (docs/spec/10-syntax.md §3a).
	if match, ok := expr.(*ast.MatchExpression); ok {
		if trueBody, falseBody, isBool := boolMatchBranches(match); isBool {
			cg.emitBoolMatchReturn(match.Scrutinee, trueBody, falseBody, tc)
			return
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
	// An ADT match on a non-identifier scrutinee (matching directly on a
	// call result) hoists the scrutinee into a temporary — evaluated once —
	// then emits the guarded returns against the temporary. The type
	// checker's recorded resolution names the monomorphized type.
	if match, ok := expr.(*ast.MatchExpression); ok {
		if _, isIdent := match.Scrutinee.(*ast.Identifier); !isIdent {
			if mangled, resolved := tc.MatchResolution(match); resolved {
				if _, known := cg.adtTypes[mangled]; known {
					tmp := fmt.Sprintf("oak__scrutinee_%d", cg.scrutineeCounter)
					cg.scrutineeCounter++
					cg.write(fmt.Sprintf("  %s %s = ", cg.cTypeName(mangled), cIdent(tmp)))
					cg.emitExpressionFragment(match.Scrutinee, tc)
					cg.output.WriteString(";\n")
					if cg.localTypes == nil {
						cg.localTypes = map[string]localContainer{}
					}
					cg.localTypes[tmp] = localContainer{kind: containerADT, adtName: mangled}
					hoisted := &ast.MatchExpression{
						BaseNode:  match.BaseNode,
						Token:     match.Token, // same position: resolution carries over
						Scrutinee: &ast.Identifier{Token: match.Token, Value: tmp},
						Arms:      match.Arms,
					}
					cg.emitMatchReturn(hoisted, tc)
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
	if match, ok := expr.(*ast.MatchExpression); ok {
		cg.emitMatchStatement(match, tc)
		return
	}
	cg.emitExpressionFragment(expr, tc)
	cg.write(";\n")
}

// arithmeticHelpers names the prelude helper family for each total operator.
var arithmeticHelpers = map[string]string{
	"+": "oak_add", "-": "oak_sub", "*": "oak_mul", "/": "oak_div", "%": "oak_rem",
}

// emitInfixExpression emits C code for an infix expression (as fragment)
func (cg *CodeGenerator) emitInfixExpression(expr *ast.InfixExpression, tc *typechecker.TypeChecker) {
	// A statement condition (emitCondition) drops the grouping parentheses
	// of its top-level infix: `if ( a == b )`, not `if ( ( a == b ) )`,
	// which clang reports as -Wparentheses-equality. Operands group as usual.
	bare := cg.bareCondition
	cg.bareCondition = false
	if cg.emitBytePack(expr, tc) {
		return
	}
	// Equality on sum types and records calls the type's generated
	// equality function (typechecker/equality.go records the type).
	if expr.Operator == "==" || expr.Operator == "!=" {
		if name, isAggregate := tc.EqualityType(expr.Token); isAggregate {
			if expr.Operator == "!=" {
				cg.output.WriteString("!")
			}
			helper := "oak_eq_" + cg.cTypeName(name)
			if name == "string" {
				helper = "oak_eq_string"
			}
			cg.output.WriteString(helper + "( ")
			cg.emitExpressionFragment(expr.Left, tc)
			cg.output.WriteString(", ")
			cg.emitExpressionFragment(expr.Right, tc)
			cg.output.WriteString(" )")
			return
		}
	}
	// Shifts route through the checked helpers (oak_shl_u32 and friends):
	// the operand width was recorded by the checker; without a record the
	// emission fails closed rather than guessing a width.
	if expr.Operator == "<<" || expr.Operator == ">>" {
		width, known := tc.ShiftWidth(expr.Token)
		if !known {
			cg.output.WriteString("OAK_UNSUPPORTED_SHIFT")
			return
		}
		if cg.constantContext {
			// A constant context (a global initializer) needs a C integer
			// constant expression: the shift is the plain operator at the
			// checked width, which the checker has already bounded.
			cg.output.WriteString(fmt.Sprintf("((u%d)( ", width))
			cg.emitExpressionFragment(expr.Left, tc)
			cg.output.WriteString(fmt.Sprintf(" ) %s ", expr.Operator))
			cg.emitExpressionFragment(expr.Right, tc)
			cg.output.WriteString(" )")
			return
		}
		helper := "oak_shl_u"
		if expr.Operator == ">>" {
			helper = "oak_shr_u"
		}
		cg.output.WriteString(fmt.Sprintf("%s%d( ", helper, width))
		cg.emitExpressionFragment(expr.Left, tc)
		cg.output.WriteString(", ")
		cg.emitExpressionFragment(expr.Right, tc)
		cg.output.WriteString(" )")
		return
	}
	// Fixed-width arithmetic routes through the total helpers (oak_add_u8
	// and friends): the checker recorded the result width. Constant contexts
	// and literal-only operands keep the plain operator so C integer constant
	// expressions stay constant; an unrecorded expression also stays plain.
	if helper, isArithmetic := arithmeticHelpers[expr.Operator]; isArithmetic && !cg.constantContext &&
		!(typechecker.IsLiteralOnlyExpression(expr.Left) && typechecker.IsLiteralOnlyExpression(expr.Right)) {
		// Floats keep the plain C operator: their rounding is fixed by the
		// FP_CONTRACT pragma and the absence of fast-math, not by a helper.
		if width, known := tc.ArithmeticType(expr.Token); known && !typechecker.IsFloatName(width) {
			cg.output.WriteString(fmt.Sprintf("%s_%s( ", helper, width))
			cg.emitExpressionFragment(expr.Left, tc)
			cg.output.WriteString(", ")
			cg.emitExpressionFragment(expr.Right, tc)
			cg.output.WriteString(" )")
			return
		}
	}
	// C style: space around operators, parentheses for grouping
	if !bare {
		cg.output.WriteString("( ")
	}
	cg.emitExpressionFragment(expr.Left, tc)
	cg.output.WriteString(fmt.Sprintf(" %s ", expr.Operator))
	cg.emitExpressionFragment(expr.Right, tc)
	if !bare {
		cg.output.WriteString(" )")
	}
}

// emitCondition emits the condition of an if or while: an infix at the
// top level is written without its grouping parentheses, since the
// statement's own parentheses already hold it.
func (cg *CodeGenerator) emitCondition(expr ast.Expression, tc *typechecker.TypeChecker) {
	if _, isInfix := expr.(*ast.InfixExpression); isInfix {
		cg.bareCondition = true
	}
	cg.emitExpressionFragment(expr, tc)
	cg.bareCondition = false
}

// emitExpressionFragment emits a fragment of an expression (no return statement)
func (cg *CodeGenerator) emitExpressionFragment(expr ast.Expression, tc *typechecker.TypeChecker) {
	switch e := expr.(type) {
	case *ast.IntegerLiteral:
		if e.Wide {
			cg.output.WriteString(fmt.Sprintf("%dULL", e.Magnitude()))
		} else {
			cg.output.WriteString(fmt.Sprintf("%d", e.Value))
		}
	case *ast.FloatLiteral:
		cg.emitFloatLiteral(e, tc)
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
		// A program function named as a value (passed to a higher-order
		// function, stored in a function-typed binding) is its C symbol. A
		// local of the same name — scope is per package, so an imported
		// package's local may share a root function's name — stays a local.
		_, isLocal := cg.localTypes[e.Value]
		if target := cg.programFunctions[e.Value]; target != nil && target.Receiver == nil && !isLocal {
			if target.ExternSymbol != "" && typechecker.ValidCSymbol(target.ExternSymbol) {
				cg.output.WriteString(cg.externCallee(target.ExternSymbol))
			} else {
				cg.output.WriteString(cg.cFunctionName(e.Value))
			}
			return
		}
		if _, isTargetConstant := cg.targetConstants[e.Value]; isTargetConstant && !isLocal {
			// A target constant's static carries a prefixed C name
			// (codegen/globals.go, docs/spec/92-ffi.md section 2.11).
			cg.output.WriteString(targetConstantCName(e.Value))
			return
		}
		cg.output.WriteString(cIdent(e.Value))
	case *ast.InfixExpression:
		cg.emitInfixExpression(e, tc)
	case *ast.PrefixExpression:
		operator := e.Operator
		// Unary minus on a machine integer is total in its width: route
		// through oak_neg_<type> (the checker recorded the width) except in
		// constant contexts and on literal-only operands.
		if operator == "-" && !cg.constantContext && !typechecker.IsLiteralOnlyExpression(e.Right) {
			if width, known := tc.ArithmeticType(e.Token); known {
				cg.output.WriteString(fmt.Sprintf("oak_neg_%s( ", width))
				cg.emitExpressionFragment(e.Right, tc)
				cg.output.WriteString(" )")
				return
			}
		}
		// Oak's unary ^ (bitwise complement, Go-style) is C's ~; C's
		// unary ^ does not exist.
		if operator == "^" {
			operator = "~"
		}
		cg.output.WriteString(operator)
		cg.output.WriteString("( ")
		cg.emitExpressionFragment(e.Right, tc)
		cg.output.WriteString(" )")
	case *ast.IndexExpression:
		// Field access (the Dot mark) or array indexing — never guessed
		// from the index's shape.
		if e.Dot {
			cg.emitExpressionFragment(e.Left, tc)
			if ident, ok := e.Index.(*ast.Identifier); ok {
				cg.output.WriteString(fmt.Sprintf(".%s", cIdent(ident.Value)))
			} else {
				cg.output.WriteString(".OAK_UNSUPPORTED_FIELD")
			}
		} else {
			// Bracket indexing that reaches the fragment emitter unlowered
			// goes through the checked-lvalue helper when the container is
			// known, so element access is never unchecked.
			info := cg.localContainerOf(e.Left)
			if info.kind == containerOwnedArray {
				cg.emitExpressionFragment(e.Left, tc)
				cg.output.WriteString(".v[ oak_lv_idx( (u64)( ")
				cg.emitExpressionFragment(e.Index, tc)
				cg.output.WriteString(fmt.Sprintf(" ), %d ) ]", info.length))
			} else {
				cg.emitExpressionFragment(e.Left, tc)
				cg.output.WriteString("[ ")
				cg.emitExpressionFragment(e.Index, tc)
				cg.output.WriteString(" ]")
			}
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
			// Bare variant: the type checker's recorded resolution is the
			// authority (typechecker/mono.go) — it knows which
			// instantiation this constructor was checked against. The
			// unique-name search over concrete declarations is the
			// fallback; generic templates never participate; ambiguity
			// fails closed.
			adtName := ""
			if mangled, resolved := tc.VariantResolution(e); resolved {
				adtName = mangled
			}
			if adtName == "" {
				for name, adt := range cg.adtTypes {
					if len(adt.TypeParams) > 0 {
						continue
					}
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
		// A custody transition (docs/spec/92-ffi.md section 2.8.5) hands the
		// buffer over as pointer and count and yields the same buffer under
		// its new type: the foreign call is sequenced before the copy.
		if operand := cg.custodyTransitionOperand(e); operand != nil && !cg.inCustodyWrap {
			cg.inCustodyWrap = true
			cg.output.WriteString("( ")
			cg.emitExpressionFragment(e, tc)
			cg.inCustodyWrap = false
			cg.output.WriteString(", (")
			cg.output.WriteString(cg.parseTypeExpression(cg.programFunctions[e.Function.(*ast.Identifier).Value].ReturnType))
			cg.output.WriteString("){ ( ")
			cg.emitExpressionFragment(operand, tc)
			cg.output.WriteString(" ).base, ( ")
			cg.emitExpressionFragment(operand, tc)
			cg.output.WriteString(" ).len } )")
			return
		}
		// An inbound buffer borrow (docs/spec/92-ffi.md section 2.7) is
		// spelled as an index over a library member, so it comes before the
		// generic index-call paths.
		if member, element, isForeign := typechecker.ForeignBorrowCall(e); isForeign && (len(e.Arguments) == 2 || (member == "borrow_string" && len(e.Arguments) == 1)) {
			cg.emitForeignBorrow(member, element, e, tc)
			return
		}
		// A foreign function pointer named by c.fn_at(p) (docs/spec/92-ffi.md
		// section 2.10): the pointer, NULL-checked at the conversion.
		if typechecker.ForeignFunctionAtCall(e) && len(e.Arguments) == 1 {
			cg.emitForeignFunctionAt(e, tc)
			return
		}
		// A refinement's construction: the base value through its guard
		// (typechecker/refinements.go).
		if name, isRefinement := tc.RefinedConstruction(e.Token); isRefinement && len(e.Arguments) == 1 {
			if tc.RefinementDischarged(e.Token) {
				// The facts in scope proved the predicate: no guard.
				cg.output.WriteString(fmt.Sprintf("((%s)( ", cg.cTypeName(name)))
				cg.emitExpressionFragment(e.Arguments[0], tc)
				cg.output.WriteString(" ))")
				return
			}
			cg.output.WriteString(fmt.Sprintf("oak_refine_%s( ", cg.cTypeName(name)))
			cg.emitExpressionFragment(e.Arguments[0], tc)
			cg.output.WriteString(" )")
			return
		}
		// Sealed-boundary coercions are identities: the fresh abstract type is
		// a typedef alias of its underlying type (docs/spec/83-modules.md
		// section 6.3).
		if callee, ok := e.Function.(*ast.Identifier); ok && len(e.Arguments) == 1 &&
			(strings.HasPrefix(callee.Value, "__abstract_") || strings.HasPrefix(callee.Value, "__concrete_")) {
			cg.emitExpressionFragment(e.Arguments[0], tc)
			return
		}
		if accessor, ok := e.Function.(*ast.FieldAccessorExpression); ok && len(e.Arguments) == 1 {
			cg.output.WriteString("( ")
			cg.emitExpressionFragment(e.Arguments[0], tc)
			cg.output.WriteString(" ).")
			cg.output.WriteString(accessor.Field.Value)
			return
		}
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
		// Checked and saturating arithmetic (docs/spec/20-types.md
		// section 11.1a) lower to their overflow-detecting helpers.
		if cg.emitArithmeticCall(e, tc) {
			return
		}
		// Floating-point intrinsics lower to their correctly rounded C99
		// realizations (docs/spec/20-types.md section 11.3.8).
		if cg.emitFloatIntrinsicCall(e, tc) {
			return
		}
		if ident, ok := e.Function.(*ast.Identifier); ok {
			if fn, isVariadicCallee := cg.variadicCallee(ident.Value); isVariadicCallee {
				cg.emitVariadicCall(fn, e, tc)
				return
			}
		}
		if ident, ok := e.Function.(*ast.Identifier); ok {
			// assert_eq / assert_ne name both values on failure; the checker
			// recorded the operand type by position, which selects the
			// printing helper (docs/spec/85-discipline.md section 5).
			if (ident.Value == "assert_eq" || ident.Value == "assert_ne") && len(e.Arguments) == 2 {
				name, known := tc.ArithmeticType(ident.Token)
				if !known {
					name = "u64"
				}
				cg.output.WriteString(fmt.Sprintf("oak_%s_%s( ", ident.Value, name))
				cg.emitExpressionFragment(e.Arguments[0], tc)
				cg.output.WriteString(", ")
				cg.emitExpressionFragment(e.Arguments[1], tc)
				cg.output.WriteString(fmt.Sprintf(", %q, %d )", cg.tokenSourceFile(ident.Token), ident.Token.Line))
				return
			}
			if cg.emitStringViewCall(e, tc) {
				return
			}
			if ident.Value == "core_slice" && len(e.Arguments) == 3 && cg.emitBorrowedSlice(e, tc) {
				return
			}
			if ident.Value == "core_index" && len(e.Arguments) == 2 {
				cg.emitCoreIndex(e, tc)
				return
			}
			if (ident.Value == "len" || ident.Value == "core_len") && len(e.Arguments) == 1 {
				cg.emitLen(e, tc)
				return
			}
			if (ident.Value == "view" || ident.Value == "span") && len(e.Arguments) == 1 {
				cg.emitBorrowConstruction(ident.Value, e, tc)
				return
			}
			if (ident.Value == "view_as" || ident.Value == "span_as") && len(e.Arguments) == 1 {
				// view_as[U](v) / span_as[U](s) (docs/spec/50-borrowing.md
				// section 8d): the same storage as a view of U with the
				// record's scalar count times as many elements; the
				// checker proved the record's layout contiguous U.
				reinterpretation, known := tc.ReinterpretationAt(e.Token)
				if !known {
					cg.output.WriteString("OAK_UNSUPPORTED_REINTERPRET")
					return
				}
				factor := reinterpretation.Factor
				element := cg.parseTypeExpression(&ast.Identifier{Value: reinterpretation.Element})
				if ident.Value == "view_as" {
					cg.output.WriteString(fmt.Sprintf("(%s){ (const %s *)( ", cg.emitViewType(element), element))
				} else {
					cg.output.WriteString(fmt.Sprintf("(%s){ (%s *)( ", cg.emitSpanType(element), element))
				}
				cg.emitExpressionFragment(e.Arguments[0], tc)
				cg.output.WriteString(" ).base, (u32)(( ")
				cg.emitExpressionFragment(e.Arguments[0], tc)
				cg.output.WriteString(fmt.Sprintf(" ).len * %du) }", factor))
				return
			}
			if ident.Value == "subslice" && len(e.Arguments) == 3 {
				// subslice(v, start, n) derives a view/span of the same kind
				// (docs/spec/50-borrowing.md); the helper traps past the end.
				info := cg.localContainerOf(e.Arguments[0])
				helper := ""
				switch info.kind {
				case containerView:
					helper = fmt.Sprintf("oak_view_subslice_%s", elementIdent(info.element))
				case containerSpan:
					helper = fmt.Sprintf("oak_span_subslice_%s", elementIdent(info.element))
				}
				if helper == "" {
					cg.output.WriteString("OAK_UNSUPPORTED_SUBSLICE_SOURCE")
					return
				}
				cg.output.WriteString(helper + "( ")
				cg.emitExpressionFragment(e.Arguments[0], tc)
				cg.output.WriteString(", (u64)( ")
				cg.emitExpressionFragment(e.Arguments[1], tc)
				cg.output.WriteString(" ), (u64)( ")
				cg.emitExpressionFragment(e.Arguments[2], tc)
				cg.output.WriteString(" ) )")
				return
			}
			if target, isCast := primitiveCasts[ident.Value]; isCast && len(e.Arguments) == 1 {
				// f32(x) over a storage format is an exact widening through
				// its helper, never a C cast of the uint16_t carrier
				// (docs/spec/20-types.md section 11.3.1).
				if source, recorded := tc.ArithmeticType(e.Token); recorded && strings.HasPrefix(source, "widen_") {
					cg.output.WriteString(fmt.Sprintf("oak_%s( ", source))
					cg.emitExpressionFragment(e.Arguments[0], tc)
					cg.output.WriteString(" )")
					return
				}
				cg.output.WriteString(fmt.Sprintf("((%s)( ", target))
				cg.emitExpressionFragment(e.Arguments[0], tc)
				cg.output.WriteString(" ))")
				return
			}
			if cg.emitLayoutBuiltin(ident, e, tc) {
				return
			}
		}
		if access, isDot := e.Function.(*ast.IndexExpression); isDot && access.Dot && e.ResolvedMethod != "" {
			// An ADT method call (docs/spec/90-backend.md): a direct call to
			// the method's C function with the receiver as the first
			// argument. No dispatch, no thunk, no allocation.
			typeName, method, _ := strings.Cut(e.ResolvedMethod, "::")
			cg.output.WriteString(cg.cMethodName(typeName, method))
			cg.output.WriteString("( ")
			cg.emitExpressionFragment(access.Left, tc)
			for _, arg := range e.Arguments {
				cg.output.WriteString(", ")
				cg.emitExpressionFragment(arg, tc)
			}
			cg.output.WriteString(" )")
			return
		}
		if signature, isSend := typechecker.MessageSendCallee(e.Function); isSend {
			// An Objective-C message send (docs/spec/92-ffi.md section
			// 2.12): objc_msgSend cast to the receiver, the selector, and
			// the bracketed signature, spelled from the extern prototype
			// table exactly as a c.Fn call is.
			cg.emitMessageSendCallee(signature)
		} else if ident, ok := e.Function.(*ast.Identifier); ok && cg.foreignFnLocals[ident.Value] != nil {
			// A call through a foreign function pointer (docs/spec/92-ffi.md
			// section 2.10): the opaque pointer cast to the annotated
			// signature, spelled from the extern prototype table.
			cg.emitForeignFunctionCallee(cg.foreignFnLocals[ident.Value], e.Function, tc)
		} else if ident, ok := e.Function.(*ast.Identifier); ok && runtimeBuiltins[ident.Value] != "" {
			cg.output.WriteString(runtimeBuiltins[ident.Value])
		} else if ident, ok := e.Function.(*ast.Identifier); ok && cg.programFunctions[ident.Value] != nil && !cg.isLocalName(ident.Value) {
			// Calls to program functions use the mangled C name; calls to
			// extern bindings use the validated foreign symbol raw
			// (docs/spec/92-ffi.md section 2.3). A local of the same name — a
			// function-typed parameter `step` in a package whose caller also
			// declares a root function `step` — is a call through the local.
			if target := cg.programFunctions[ident.Value]; target.ExternSymbol != "" {
				if typechecker.ValidCSymbol(target.ExternSymbol) {
					cg.output.WriteString(cg.externCallee(target.ExternSymbol))
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
			if cg.localContainerOf(arg).kind == containerBuffer && cg.isExternCallee(e.Function) {
				// A Buffer parameter of an extern binding is the pointer and
				// the element count (section 2.8.5).
				cg.output.WriteString("( ")
				cg.emitExpressionFragment(arg, tc)
				cg.output.WriteString(" ).base, (size_t)( ")
				cg.emitExpressionFragment(arg, tc)
				cg.output.WriteString(" ).len")
			} else if operand, isSpan := boundarySpanArgument(arg); isSpan {
				// A boundary span lowers to the pointer and the element
				// count of the view or span, for this call only
				// (docs/spec/92-ffi.md section 2.5.4). No copy, no thunk.
				cg.output.WriteString("(void *)( ")
				cg.emitExpressionFragment(operand, tc)
				cg.output.WriteString(" ).base, (size_t)( ")
				cg.emitExpressionFragment(operand, tc)
				cg.output.WriteString(" ).len")
			} else if operand, isCString := cStringArgument(arg); isCString {
				cg.emitCStringArgument(operand, arg, tc)
			} else if bytes, slots, isArgv := argvArgument(arg); isArgv {
				cg.emitArgvArgument(bytes, slots, arg, tc)
			} else if operand, isOut := outArgument(arg); isOut {
				cg.emitOutArgument(operand, tc)
			} else {
				cg.emitExpressionFragment(arg, tc)
			}
			if i < len(e.Arguments)-1 {
				cg.output.WriteString(", ")
			}
		}
		// assert carries its source position so a trap can be attributed.
		if ident, ok := e.Function.(*ast.Identifier); ok && ident.Value == "assert" && len(e.Arguments) == 1 {
			cg.output.WriteString(fmt.Sprintf(", %q, %d", cg.tokenSourceFile(ident.Token), ident.Token.Line))
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
	case *ast.FieldAccessorExpression:
		if e.ResolvedRecord == "" {
			cg.output.WriteString("OAK_CONTEXTUAL_FIELD_ACCESSOR")
		} else {
			cg.output.WriteString(cg.fieldAccessorCName(e.ResolvedRecord, e.Field.Value))
		}
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
	// The type checker's recorded scrutinee instantiation is the authority
	// (typechecker/mono.go); the variant-name scan is the fallback and
	// never considers generic templates.
	if mangled, resolved := tc.MatchResolution(expr); resolved {
		if adt, registered := cg.adtTypes[mangled]; registered {
			typeName = cg.cTypeName(mangled)
			adtDef = adt
		}
	}
	if adtDef == nil && len(expr.Arms) > 0 {
		if variantPattern, ok := expr.Arms[0].Pattern.(*ast.VariantPattern); ok {
			// Try to find the ADT type by searching through known ADT types
			variantName := variantPattern.Variant.Value
			for name, adt := range cg.adtTypes {
				if len(adt.TypeParams) > 0 {
					continue
				}
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
					payloadName := cIdent(bindingPattern.Name.Value)
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
	} else if trueBody, falseBody, isBool := boolMatchBranches(expr); isBool {
		// Bool condition match: a plain C ternary, condition evaluated once.
		cg.output.WriteString("( ")
		cg.emitExpressionFragment(expr.Scrutinee, tc)
		cg.output.WriteString(" ) ? ")
		cg.emitExpressionFragment(trueBody, tc)
		cg.output.WriteString(" : ")
		cg.emitExpressionFragment(falseBody, tc)
	} else {
		// Scalar match - a guarded ternary chain; the final arm is the
		// unconditional else (exhaustiveness is checked upstream, so a
		// match reaching codegen always has a last arm to fall to).
		for i, arm := range expr.Arms {
			last := i == len(expr.Arms)-1
			if last {
				cg.emitExpressionFragment(arm.Body, tc)
				break
			}
			cg.output.WriteString("( ")
			if literalPattern, ok := arm.Pattern.(*ast.LiteralPattern); ok {
				cg.emitExpressionFragment(expr.Scrutinee, tc)
				cg.output.WriteString(" == ")
				cg.emitExpressionFragment(literalPattern.Value, tc)
			} else {
				cg.output.WriteString("1") // wildcard
			}
			cg.output.WriteString(" ) ? ")
			cg.emitExpressionFragment(arm.Body, tc)
			cg.output.WriteString(" : ")
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

// cMethodName mangles a method Type::method into a C symbol that no
// function's mangled name and no other method's can equal: the receiver
// type's length in decimal, the type, an underscore, the method
// (docs/spec/90-backend.md). The length prefix begins with a digit, which
// no Oak identifier can, so it cannot be a function's name; and it fixes
// where the type ends, so `A_b::c` and `A::b_c` differ. Oak.MethodMangling
// (spec/lean/Oak/MethodMangling.lean) proves the injectivity.
func (cg *CodeGenerator) cMethodName(typeName, method string) string {
	return cg.cFunctionName(fmt.Sprintf("%d%s_%s", len(typeName), typeName, method))
}

// methodIdentity is the checker's Type::method identity of a method whose
// receiver type is a plain nominal type.
func methodIdentity(fn *ast.FunctionStatement) (string, bool) {
	if fn == nil || fn.Receiver == nil || fn.Name == nil {
		return "", false
	}
	receiver, isIdent := fn.Receiver.Type.(*ast.Identifier)
	if !isIdent {
		return "", false
	}
	return receiver.Value + "::" + fn.Name.Value, true
}

func (cg *CodeGenerator) parseTypeExpression(expr ast.Expression) string {
	if ident, ok := expr.(*ast.Identifier); ok {
		switch ident.Value {
		case "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "u128", "f32", "f64", "f16", "bf16", "f8e4m3", "f8e5m2":
			return ident.Value
		case "string":
			return "string"
		case "Bool":
			return "Bool"
		case "()":
			return "void"
		case "never":
			return "oak_never"
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
	// A foreign function pointer (docs/spec/92-ffi.md section 2.10) is
	// stored as an opaque pointer and cast to its signature at each call.
	if _, isCFn := typechecker.CFnTypeExpression(expr); isCFn {
		return "void *"
	}
	// The parser represents array types as IndexExpression
	if indexExpr, ok := expr.(*ast.IndexExpression); ok {
		if cType, atomic := atomicTypeC(indexExpr); atomic {
			cg.noteAtomicCarrier(indexExpr)
			return cType
		}
		// Phantom-encoded strings share one representation: every Str[E]
		// lowers to the same C string struct (docs/spec/70-strings.md).
		if base, ok := indexExpr.Left.(*ast.Identifier); ok && base.Value == "Str" {
			return "string"
		}
		// An owned foreign buffer is the span struct over its element type
		// (docs/spec/92-ffi.md section 2.8).
		if element, isBuffer := bufferElementSyntax(indexExpr); isBuffer {
			return cg.emitSpanType(cg.parseTypeExpression(element))
		}
		// Atomic cells embed as C11 _Atomic members (docs/spec/65).
		if atomicC, isAtomic := atomicTypeC(indexExpr); isAtomic {
			return atomicC
		}
		// Concrete generic-ADT annotations lower to their monomorphized
		// typedefs: Option[i32] -> oak_Option_i32 (codegen/mono.go).
		if mangled, isGeneric := cg.genericAnnotationName(indexExpr); isGeneric {
			return cg.cTypeName(mangled)
		}
		// Check if this is an array type annotation
		if intLit, ok := indexExpr.Index.(*ast.IntegerLiteral); ok {
			// Fixed-size array: [N]T is a wrapper-struct value
			// (codegen/arrays.go), never a raw C array.
			elementType := cg.parseTypeExpression(indexExpr.Left)
			return cg.arrayTypeName(elementType, intLit.Value)
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
	viewTypeName := fmt.Sprintf("oak_view_%s", elementIdent(elementType))

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
	cg.write(fmt.Sprintf("static inline %s oak_view_index_%s(%s v, u64 i) {\n", elementType, elementIdent(elementType), viewTypeName))
	cg.write("  if (i >= (u64)v.len) { __builtin_trap(); }\n")
	cg.write("  return v.base[i];\n")
	cg.write("}\n\n")

	if elementType == "u8" {
		// c.cstr(v) (docs/spec/92-ffi.md section 2.5.3): the view's base
		// pointer is a C string only when its last byte is NUL; the check
		// runs at the foreign call and names the Oak source position before
		// trapping, as an assertion does.
		cg.write("#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)\n#include <stdio.h>\n")
		cg.write(fmt.Sprintf("static inline const char *oak_cstr_u8(%s v, const char *file, u32 line) {\n", viewTypeName))
		cg.write("  if (v.len == 0u || v.base[v.len - 1u] != 0u) {\n")
		cg.write("    fprintf(stderr, \"oak: c.cstr view is not NUL-terminated at %s:%u\\n\", file, (unsigned)line);\n")
		cg.write("    __builtin_trap();\n  }\n  return (const char *)v.base;\n}\n#else\n")
		cg.write(fmt.Sprintf("static inline const char *oak_cstr_u8(%s v, const char *file, u32 line) {\n", viewTypeName))
		cg.write("  if (v.len == 0u || v.base[v.len - 1u] != 0u) { oak_report(\"c.cstr view is not NUL-terminated\", file, line); __builtin_trap(); }\n  return (const char *)v.base;\n}\n#endif\n\n")
		// c.borrow_string(p) (section 2.7.1): the terminator's offset,
		// counted without libc so freestanding builds stay free of it; a
		// NULL pointer is the empty string, and a length past u32 traps.
		cg.write("static inline u32 oak_cstr_len(const void *p) {\n")
		cg.write("  const unsigned char *s = (const unsigned char *)p;\n  u64 n = 0;\n  if (s == 0) { return 0u; }\n")
		cg.write("  while (s[n] != 0u) { n++; if (n > 0xFFFFFFFFull) { __builtin_trap(); } }\n  return (u32)n;\n}\n\n")
	}

	// subslice(v, start, n): the derived view is exactly n elements starting
	// at start, admitted only when start + n <= len (no overflow: both
	// comparisons stay within u64 without adding).
	cg.write(fmt.Sprintf("static inline %s oak_view_subslice_%s(%s v, u64 start, u64 n) {\n", viewTypeName, elementIdent(elementType), viewTypeName))
	cg.write("  if (start > (u64)v.len || n > (u64)v.len - start) { __builtin_trap(); }\n")
	cg.write(fmt.Sprintf("  return (%s){ v.base + start, (u32)n };\n", viewTypeName))
	cg.write("}\n\n")

	return viewTypeName
}

// emitSpanType emits a span type struct and returns the type name
func (cg *CodeGenerator) emitSpanType(elementType string) string {
	spanTypeName := fmt.Sprintf("oak_span_%s", elementIdent(elementType))

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
	cg.write(fmt.Sprintf("static inline %s oak_span_index_%s(%s v, u64 i) {\n", elementType, elementIdent(elementType), spanTypeName))
	cg.write("  if (i >= (u64)v.len) { __builtin_trap(); }\n")
	cg.write("  return v.base[i];\n")
	cg.write("}\n\n")

	// Bounds-checked element store, symmetric with the load.
	cg.write(fmt.Sprintf("static inline void oak_span_store_%s(%s v, u64 i, %s value) {\n", elementIdent(elementType), spanTypeName, elementType))
	cg.write("  if (i >= (u64)v.len) { __builtin_trap(); }\n")
	cg.write("  v.base[i] = value;\n")
	cg.write("}\n\n")

	cg.write(fmt.Sprintf("static inline %s oak_span_subslice_%s(%s v, u64 start, u64 n) {\n", spanTypeName, elementIdent(elementType), spanTypeName))
	cg.write("  if (start > (u64)v.len || n > (u64)v.len - start) { __builtin_trap(); }\n")
	cg.write(fmt.Sprintf("  return (%s){ v.base + start, (u32)n };\n", spanTypeName))
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

// SetLineDirectives enables or disables #line directives in the output.
func (cg *CodeGenerator) SetLineDirectives(enabled bool) {
	cg.lineDirectives = enabled
}

// emitLineDirective writes `#line N "file"` for a token of the compiled
// source, when directives are enabled. Spliced standard-library syntax
// (SemanticContext "std") is not from that file and is left unattributed;
// a specialization's tokens are the template's and map to it.
func (cg *CodeGenerator) emitLineDirective(tok token.Token) {
	if !cg.lineDirectives || tok.Line <= 0 || tok.SemanticContext == "std" {
		return
	}
	cg.output.WriteString(fmt.Sprintf("#line %d %s\n", tok.Line, strconv.Quote(cg.tokenSourceFile(tok))))
}

// tokenSourceFile is the file a token came from, for assertion traps and
// #line directives. The module loader stamps every token `package#file`
// (docs/spec/83-modules.md section 7), so a multi-package program names the
// assertion's own file rather than the root package's directory (F21); the
// file is spelled relative to the compiled package directory when it lies
// inside it. A token without a stamp (a single-source compilation) keeps
// the compilation's source name.
func (cg *CodeGenerator) tokenSourceFile(tok token.Token) string {
	context := tok.SemanticContext
	hash := strings.LastIndex(context, "#")
	if hash < 0 || hash == len(context)-1 {
		return cg.sourceFile
	}
	file := context[hash+1:]
	if filepath.IsAbs(file) && cg.sourceFile != "" {
		if rel, err := filepath.Rel(cg.sourceFile, file); err == nil && rel != ".." && !strings.HasPrefix(rel, ".."+string(filepath.Separator)) {
			return rel
		}
	}
	return file
}

// statementToken is the token that opens a statement, for source mapping.
func statementToken(stmt ast.Statement) token.Token {
	switch s := stmt.(type) {
	case *ast.VariableDeclaration:
		return s.Token
	case *ast.AssignmentStatement:
		return s.Token
	case *ast.IndexAssignmentStatement:
		return s.Token
	case *ast.ExpressionStatement:
		return s.Token
	case *ast.WhileStatement:
		return s.Token
	case *ast.IfStatement:
		return s.Token
	case *ast.BlockStatement:
		return s.Token
	case *ast.UnsafeBlock:
		return s.Token
	}
	return token.Token{}
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
		if cg.sourceIndex == nil {
			cg.sourceIndex = lsp.NewPositionIndex(cg.sourceText)
		}
		startPos = cg.sourceIndex.Position(loc.ByteStart, loc.Line)
		endPos = cg.sourceIndex.Position(loc.ByteEnd, loc.EndLine)
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
	// Container metadata follows lexical scopes, including sibling blocks
	// that reuse a name with different array lengths.
	outer := cg.localTypes
	cg.localTypes = make(map[string]localContainer, len(outer))
	for name, info := range outer {
		cg.localTypes[name] = info
	}
	defer func() { cg.localTypes = outer }()
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
	cg.emitLineDirective(statementToken(stmt))
	switch s := stmt.(type) {
	case *ast.VariableDeclaration:
		cg.emitVariableDeclaration(s, tc)
	case *ast.AssignmentStatement:
		cg.emitAssignmentStatement(s, tc)
	case *ast.BreakStatement:
		// Statement-position conditionals lower to if/else and loops to
		// while, so C's break leaves exactly the Oak loop.
		cg.write("  break;\n")
	case *ast.ExpressionStatement:
		if call, isCall := s.Expression.(*ast.InvocationExpression); isCall {
			if callee, isIdent := call.Function.(*ast.Identifier); isIdent && callee.Value == "test_launch" {
				// A recorded kernel launch (docs/spec/110-testing.md,
				// "Launch targets"): never a result, always a statement.
				cg.emitTestLaunch(call, tc)
				break
			}
		}
		if isLastInFunction && !s.Discard {
			// Last statement in function - emit as return. A trailing
			// discard (`_ = expr`) is a statement, never the result.
			cg.emitExpression(s.Expression, tc)
		} else if match, isMatch := s.Expression.(*ast.MatchExpression); isMatch {
			// Statement-position match with side-effecting arms
			// (docs/spec/30-adts): tag-guarded statement blocks.
			cg.emitMatchStatement(match, tc)
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
	case *ast.UnsafeBlock:
		// An unsafe block is a scope like any other in C; what it admits is
		// decided by the checkers (Oak.Unsafe), and the comment keeps the
		// boundary visible in the emitted text. Before this case existed
		// the body was dropped with a TODO comment, a silent miscompile the
		// inbound-buffer tests exposed (docs/spec/92-ffi.md section 2.7).
		if s.Body != nil {
			cg.write("  { /* unsafe */\n")
			cg.indentLevel++
			cg.emitBlockStatement(s.Body, tc, false)
			cg.indentLevel--
			cg.write("  }\n")
		}
	default:
		cg.write(fmt.Sprintf("  /* TODO: emit statement type %T */\n", s))
	}
}

// emitLvaluePath emits an assignable access path: identifiers, field
// accesses, and bounds-checked owned-array/span element accesses (views are
// rejected upstream as read-only). Unknown shapes fail closed.
func (cg *CodeGenerator) emitLvaluePath(expr ast.Expression, tc *typechecker.TypeChecker) {
	switch e := expr.(type) {
	case *ast.Identifier:
		cg.output.WriteString(cIdent(e.Value))
	case *ast.IndexExpression:
		if e.Dot {
			cg.emitLvaluePath(e.Left, tc)
			if ident, ok := e.Index.(*ast.Identifier); ok {
				cg.output.WriteString(fmt.Sprintf(".%s", cIdent(ident.Value)))
			} else {
				cg.output.WriteString(".OAK_UNSUPPORTED_FIELD")
			}
			return
		}
		info := cg.localContainerOf(e.Left)
		switch info.kind {
		case containerOwnedArray:
			cg.emitLvaluePath(e.Left, tc)
			cg.output.WriteString(".v[ oak_lv_idx( (u64)( ")
			cg.emitExpressionFragment(e.Index, tc)
			cg.output.WriteString(fmt.Sprintf(" ), %d ) ]", info.length))
		case containerSpan:
			cg.emitLvaluePath(e.Left, tc)
			cg.output.WriteString(".base[ oak_lv_idx( (u64)( ")
			cg.emitExpressionFragment(e.Index, tc)
			cg.output.WriteString(" ), (u64)(")
			cg.emitLvaluePath(e.Left, tc)
			cg.output.WriteString(".len) ) ]")
		default:
			cg.output.WriteString("OAK_UNSUPPORTED_LVALUE")
		}
	case *ast.InvocationExpression:
		// A lowered core_index over a known container re-emits as a checked
		// lvalue access.
		if ident, ok := e.Function.(*ast.Identifier); ok && ident.Value == "core_index" && len(e.Arguments) == 2 {
			cg.emitLvaluePath(&ast.IndexExpression{Left: e.Arguments[0], Index: e.Arguments[1]}, tc)
			return
		}
		cg.output.WriteString("OAK_UNSUPPORTED_LVALUE")
	default:
		cg.output.WriteString("OAK_UNSUPPORTED_LVALUE")
	}
}

// emitIndexAssignment emits a bounds-checked element store: spans go through
// the trapping helper, owned arrays through the static-length store guard;
// unknown targets fail closed.
func (cg *CodeGenerator) emitIndexAssignment(stmt *ast.IndexAssignmentStatement, tc *typechecker.TypeChecker) {
	// Record field assignment: p.x = value, pool[i].next = value —
	// the target's path emits in lvalue position with checked indices
	// (docs/spec/40-records.md, docs/spec/50-borrowing.md).
	if stmt.Target.Dot {
		cg.write("  ")
		cg.emitLvaluePath(stmt.Target.Left, tc)
		if fieldIdent, isIdent := stmt.Target.Index.(*ast.Identifier); isIdent {
			cg.output.WriteString(fmt.Sprintf(".%s = ", cIdent(fieldIdent.Value)))
		} else {
			cg.output.WriteString(".OAK_UNSUPPORTED_FIELD = ")
		}
		cg.emitExpressionFragment(stmt.Value, tc)
		cg.output.WriteString(";\n")
		return
	}

	info := cg.localContainerOf(stmt.Target.Left)
	if tc.IndexProven(stmt.Target.Token) && (info.kind == containerSpan || info.kind == containerOwnedArray) {
		// Proven store (typechecker/extents.go): direct element assignment.
		cg.write("  ")
		if info.kind == containerSpan {
			cg.output.WriteString("( ")
			cg.emitExpressionFragment(stmt.Target.Left, tc)
			cg.output.WriteString(" ).base")
		} else {
			cg.emitLvaluePath(stmt.Target.Left, tc)
			cg.output.WriteString(".v")
		}
		cg.output.WriteString("[ ")
		cg.emitExpressionFragment(stmt.Target.Index, tc)
		cg.output.WriteString(" ] = ")
		cg.emitExpressionFragment(stmt.Value, tc)
		cg.output.WriteString(";\n")
		return
	}
	switch info.kind {
	case containerSpan:
		cg.write(fmt.Sprintf("  oak_span_store_%s( ", elementIdent(info.element)))
		cg.emitExpressionFragment(stmt.Target.Left, tc)
		cg.output.WriteString(", (u64)( ")
		cg.emitExpressionFragment(stmt.Target.Index, tc)
		cg.output.WriteString(" ), ")
		cg.emitExpressionFragment(stmt.Value, tc)
		cg.output.WriteString(" );\n")
	case containerOwnedArray:
		cg.write("  oak_store( ")
		// Preserve the owning storage through nested record/span paths.
		// Rvalue indexing returns a record copy, so projecting its array
		// here would silently store into a temporary.
		cg.emitLvaluePath(stmt.Target.Left, tc)
		cg.output.WriteString(fmt.Sprintf(".v, %d, (u64)( ", info.length))
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
		if cg.localTypes == nil {
			cg.localTypes = make(map[string]localContainer)
		}
		cg.localTypes[varName] = cg.classifyContainer(stmt.Type)
	}

	if stmt.Type != nil {
		if cType, atomic := atomicTypeC(stmt.Type); atomic {
			cg.noteAtomicCarrier(stmt.Type)
			if stmt.Value != nil {
				cg.write("  OAK_ATOMIC_INITIALIZER_MUST_BE_ZERO_INIT;\n")
				return
			}
			cg.write(fmt.Sprintf("  %s %s = 0;\n", cType, cIdent(varName)))
			return
		}
	}

	if fn, ok := stmt.Type.(*ast.FunctionTypeExpression); ok {
		cg.write("  " + cg.cFunctionPointer(fn, cIdent(varName)))
		if stmt.Value != nil {
			cg.write(" = ")
			cg.emitExpressionFragment(stmt.Value, tc)
		}
		cg.write(";\n")
		return
	}

	// Owned arrays are wrapper-struct values (codegen/arrays.go); value-less
	// arrays are zero-filled, as every value-less binding is (the zero of
	// its type; the backend never leaves storage uninitialized). A literal
	// initializer
	// is a brace initializer; any other initializer is a struct copy.
	if stmt.Type != nil {
		if info := cg.classifyContainer(stmt.Type); info.kind == containerOwnedArray {
			cg.write(fmt.Sprintf("  %s %s", cg.parseTypeExpression(stmt.Type), cIdent(varName)))
			if stmt.Value == nil {
				// A zero-length array has no element to zero: its wrapper
				// takes the empty initializer ({0} names an element).
				cg.output.WriteString(zeroArrayInitializer(info.length))
			} else if literal, isLiteral := stmt.Value.(*ast.ArrayLiteral); isLiteral {
				cg.output.WriteString(" = ")
				cg.emitArrayInitializer(literal, tc)
			} else {
				cg.output.WriteString(" = ")
				cg.emitExpressionFragment(stmt.Value, tc)
			}
			cg.output.WriteString(";\n")
			return
		}
	}

	// A binding inferred from a typed function literal is a function
	// pointer of the literal's own signature.
	if literal, isLiteral := stmt.Value.(*ast.FunctionLiteral); isLiteral && stmt.Type == nil && (len(literal.Parameters) > 0 || literal.ReturnType != nil) {
		signature := &ast.FunctionTypeExpression{Token: literal.Token, Return: literal.ReturnType}
		for _, param := range literal.Parameters {
			signature.Parameters = append(signature.Parameters, param.Type)
		}
		if signature.Return == nil {
			signature.Return = &ast.Identifier{Token: literal.Token, Value: "()"}
		}
		cg.write("  " + cg.cFunctionPointer(signature, cIdent(varName)) + " = ")
		cg.emitExpressionFragment(stmt.Value, tc)
		cg.write(";\n")
		return
	}

	// Determine type
	var varType string
	if stmt.Type != nil {
		varType = cg.parseTypeExpression(stmt.Type)
	} else if inferred, ok := cg.inferLocalType(stmt.Value); ok {
		varType = inferred
	} else if floatType, ok := cg.inferFloatLocalType(stmt.Value, tc); ok {
		// The checker recorded a float width for the initializer
		// (docs/spec/20-types.md section 11.3.2: no context means f64).
		varType = floatType
	} else {
		// Untyped scalar initializers default to i32 (integer literals and
		// arithmetic); everything the checker knows more about is handled
		// by inferLocalType, which fails closed to this default only for
		// shapes it does not recognize.
		varType = "i32"
	}

	// C style: type name;
	cg.write(fmt.Sprintf("  %s %s", varType, cIdent(varName)))

	if stmt.Value != nil {
		cg.write(" = ")
		cg.emitExpressionFragment(stmt.Value, tc)
	} else {
		// A binding declared without a value is its type's zero
		// (docs/spec/20-types.md section 12.2: the zero value must satisfy
		// every refinement it carries): a scalar is 0, a record or union
		// the all-zero aggregate. The backend never leaves storage
		// uninitialized.
		cg.write(zeroInitializerFor(varType))
	}

	cg.write(";\n")
}

// zeroInitializerFor is the C zero of a local by its C type: `= 0` for the
// scalar carriers, `= {0}` for a struct or union carrier.
func zeroInitializerFor(cType string) string {
	switch cType {
	case "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64", "f16", "f32", "f64", "bf16", "f8", "Bool", "bool", "_Bool", "size_t", "void *", "uintptr_t":
		return " = 0"
	}
	if strings.HasSuffix(cType, "*") {
		return " = 0"
	}
	return " = {0}"
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
	cg.emitCondition(stmt.Condition, tc)
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
	cg.emitCondition(stmt.Condition, tc)
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
	// A typed literal is a C99 compound literal of the wrapper struct, so it
	// is a value in any expression position (argument, return, assignment,
	// record field); an untyped literal is a bare initializer.
	if expr.Type != nil {
		if _, _, isArray := ownedArrayParameter(expr.Type, cg); isArray {
			cg.output.WriteString(fmt.Sprintf("(%s)", cg.parseTypeExpression(expr.Type)))
		} else if info := cg.classifyContainer(expr.Type); info.kind == containerView || info.kind == containerSpan {
			// A view or span literal ([]T{ ... }, or a bare literal in a
			// []T context): a view over a C99 array compound literal, whose
			// automatic storage lives to the end of the enclosing block —
			// long enough for the call or initializer it appears in
			// (docs/spec/10-syntax.md section 2c).
			viewType := fmt.Sprintf("oak_view_%s", elementIdent(info.element))
			if info.kind == containerSpan {
				viewType = fmt.Sprintf("oak_span_%s", elementIdent(info.element))
			}
			cg.output.WriteString(fmt.Sprintf("(%s){ (%s[]){ ", viewType, info.element))
			for i, elem := range expr.Elements {
				if i > 0 {
					cg.output.WriteString(", ")
				}
				cg.emitExpressionFragment(elem, tc)
			}
			cg.output.WriteString(fmt.Sprintf(" }, %d }", len(expr.Elements)))
			return
		}
	}
	cg.emitArrayInitializer(expr, tc)
}

// emitArrayInitializer emits the brace initializer of an owned array: the
// outer braces initialize the wrapper struct, the inner ones its array
// member (explicit, so no brace-elision warning is ever emitted).
func (cg *CodeGenerator) emitArrayInitializer(expr *ast.ArrayLiteral, tc *typechecker.TypeChecker) {
	cg.output.WriteString("{ { ")
	for i, elem := range expr.Elements {
		if i > 0 {
			cg.output.WriteString(", ")
		}
		cg.emitExpressionFragment(elem, tc)
	}
	cg.output.WriteString(" } }")
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
		cg.output.WriteString(fmt.Sprintf(".%s = ", cIdent(field.Name)))
		cg.emitExpressionFragment(field.Value, tc)
		first = false
	}
	cg.output.WriteString(" }")
	if expr.TypeName != nil {
		cg.output.WriteString(")")
	}
}

// emitFunctionLiteral emits a function literal. A typed literal
// (docs/spec/10-syntax.md section 3c) is lifted to a top-level C function
// and the expression is that function's name — a plain code pointer, which
// is all a captureless literal is (capturing literals are rejected by the
// checker, OAK-T0401). The lifted definition is spliced after the
// prototypes, so any function may refer to it. An untyped literal has no
// declared parameter types to lower and is left unsupported.
func (cg *CodeGenerator) emitFunctionLiteral(expr *ast.FunctionLiteral, tc *typechecker.TypeChecker) {
	if len(expr.Parameters) == 0 && expr.ReturnType == nil {
		cg.output.WriteString("OAK_UNSUPPORTED_UNTYPED_FUNCTION_LITERAL")
		return
	}
	cg.output.WriteString(cg.cFunctionName(cg.liftFunctionLiteral(expr, tc)))
}

// liftFunctionLiteral emits a typed function literal as a top-level
// function into the lifted-literal buffer and returns its Oak-side name.
// The name begins with a digit, which no Oak identifier can, so it never
// collides with a program function's mangled name. Nested literals are
// lifted while the outer body is emitted, so their definitions precede it.
func (cg *CodeGenerator) liftFunctionLiteral(expr *ast.FunctionLiteral, tc *typechecker.TypeChecker) string {
	name := fmt.Sprintf("0lit_%d", cg.liftedCount)
	cg.liftedCount++
	fn := &ast.FunctionStatement{
		Token:      expr.Token,
		Name:       &ast.Identifier{Token: expr.Token, Value: name},
		Parameters: expr.Parameters,
		ReturnType: expr.ReturnType,
		Body:       &ast.BlockExpression{Token: expr.Token, Block: expr.Body},
	}
	saved, savedIndent, savedLocals := cg.output, cg.indentLevel, cg.localTypes
	cg.output = strings.Builder{}
	cg.indentLevel = 0
	cg.localTypes = nil
	cg.emitFunction(fn, tc)
	lifted := cg.output.String()
	cg.output, cg.indentLevel, cg.localTypes = saved, savedIndent, savedLocals
	cg.liftedLiterals.WriteString(lifted)
	return name
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

// inferLocalType determines the C type of an untyped local from its
// initializer where the declaration surface makes it unambiguous: a call to
// a program function takes the callee's declared return type, a typed record
// literal its type, and a type-qualified variant its ADT. Other shapes report
// false and keep the scalar default.
func (cg *CodeGenerator) inferLocalType(value ast.Expression) (string, bool) {
	switch v := value.(type) {
	case *ast.InvocationExpression:
		callee, ok := v.Function.(*ast.Identifier)
		if !ok {
			return "", false
		}
		fn := cg.programFunctions[callee.Value]
		if fn == nil || fn.ReturnType == nil || fn.ExternSymbol != "" {
			return "", false
		}
		if _, isFnType := fn.ReturnType.(*ast.FunctionTypeExpression); isFnType {
			return "", false
		}
		cType := cg.parseTypeExpression(fn.ReturnType)
		if cType == "" || cType == "void" {
			return "", false
		}
		return cType, true
	case *ast.RecordLiteral:
		if v.TypeName != nil {
			return cg.cTypeName(v.TypeName.Value), true
		}
	case *ast.VariantExpression:
		if v.TypeName != nil {
			return cg.cTypeName(v.TypeName.Value), true
		}
	}
	return "", false
}

// SetAbstractAliases records the fresh abstract types of sealed imports
// (fresh internal name -> underlying internal name); each is emitted as a
// typedef alias of its underlying C type after the types.
func (cg *CodeGenerator) SetAbstractAliases(aliases map[string]string) {
	cg.abstractAliases = aliases
}

func (cg *CodeGenerator) emitAbstractAliases() {
	if len(cg.abstractAliases) == 0 {
		return
	}
	names := make([]string, 0, len(cg.abstractAliases))
	for fresh := range cg.abstractAliases {
		names = append(names, fresh)
	}
	sort.Strings(names)
	cg.write("/* sealed abstract types: aliases of their underlying representation */\n")
	for _, fresh := range names {
		cg.write(fmt.Sprintf("typedef %s %s;\n", cg.cTypeName(cg.abstractAliases[fresh]), cg.cTypeName(fresh)))
	}
	cg.write("\n")
}

// emitProtocolLoweringBody emits the body of a projected protocol step
// function from its compile-time transition table
// (docs/spec/112-protocols.md section 2a, 90-backend.md section 14). The
// signature, metadata, and closing brace are the ordinary function's; this
// writes only the statements between them.
//
// Dense form: `static const u8 T[States+1][Symbols]`, sentinel States;
// legal is one load and compare, next is one load, a compare on the
// sentinel that traps, and the tag. Shift form (States+1 <= 10): one u64
// row per symbol holding the next offset in the 6-bit field at the current
// state's offset, so a step is `(rows[sym] >> tag) & 63`; the state type's
// tags are the offsets (ADTType.TagValues). `run` steps a whole byte view
// with the sink absorbing, and checks once at the end
// (Oak.Protocol.runSink_correct).
func (cg *CodeGenerator) emitProtocolLoweringBody(fn *ast.FunctionStatement) {
	l := fn.Lowering
	tableName := cg.cFunctionName(snakeIdent(l.Protocol) + "_transitions")
	sink := l.States
	sinkValue := sink
	if l.Shift {
		sinkValue = 6 * sink
	}
	if cg.protocolTables == nil {
		cg.protocolTables = map[string]bool{}
	}
	if !cg.protocolTables[tableName] {
		cg.protocolTables[tableName] = true
		var table strings.Builder
		if l.Shift {
			// rows[symbol]: field s holds 6 * next(s, symbol); field sink holds 6 * sink.
			table.WriteString(fmt.Sprintf("  /* shift-DFA rows of protocol %s: field 6*s of rows[symbol] is 6*next(s, symbol) */\n", l.Protocol))
			table.WriteString(fmt.Sprintf("  static const u64 %s[%d] = {", tableName, l.Symbols))
			for t := 0; t < l.Symbols; t++ {
				var row uint64
				for s := 0; s <= sink; s++ {
					row |= uint64(6*l.Table[s*l.Symbols+t]) << (6 * uint(s))
				}
				if t > 0 {
					table.WriteString(",")
				}
				if t%4 == 0 {
					table.WriteString("\n    ")
				} else {
					table.WriteString(" ")
				}
				table.WriteString(fmt.Sprintf("0x%016xULL", row))
			}
			table.WriteString("\n  };\n")
		} else {
			table.WriteString(fmt.Sprintf("  /* transition table of protocol %s: T[state][symbol] is the next state, %d the sink */\n", l.Protocol, sink))
			table.WriteString(fmt.Sprintf("  static const u8 %s[%d][%d] = {\n", tableName, sink+1, l.Symbols))
			for s := 0; s <= sink; s++ {
				table.WriteString("    {")
				for t := 0; t < l.Symbols; t++ {
					if t > 0 {
						table.WriteString(",")
					}
					table.WriteString(fmt.Sprintf(" %d", l.Table[s*l.Symbols+t]))
				}
				table.WriteString(" },\n")
			}
			table.WriteString("  };\n")
		}
		// File scope, spliced after the prototypes with the lifted literals:
		// the three step functions and any caller share one table.
		cg.liftedLiterals.WriteString(table.String())
	}
	symbol := "step.tag"
	if l.ByteSymbol {
		symbol = fmt.Sprintf("step.payload.%s", l.StepName)
	}
	lookup := func(state, sym string) string {
		if l.Shift {
			return fmt.Sprintf("(u32)( ( %s[ %s ] >> %s ) & 63u )", tableName, sym, state)
		}
		return fmt.Sprintf("(u32)%s[ %s ][ %s ]", tableName, state, sym)
	}
	stateType := cg.cTypeName(l.Protocol + "State")
	switch l.Kind {
	case "legal":
		cg.write(fmt.Sprintf("  return %s != %du ? oak_Bool_True : oak_Bool_False;\n", lookup("state.tag", symbol), sinkValue))
	case "next":
		cg.write(fmt.Sprintf("  u32 next = %s;\n", lookup("state.tag", symbol)))
		cg.write(fmt.Sprintf("  oak_assert( next != %du ? oak_Bool_True : oak_Bool_False, \"%s\", 0 );\n", sinkValue, l.Protocol))
		cg.write(fmt.Sprintf("  %s result;\n  result.tag = next;\n  return result;\n", stateType))
	case "run":
		// The sink absorbs, so the loop carries no check; the trap fires
		// once at the end exactly when some step was illegal.
		cg.write("  u32 current = state.tag;\n")
		cg.write("  const u8 *symbols = bytes.base;\n")
		cg.write("  u64 count = (u64)bytes.len;\n")
		cg.write("  for (u64 i = 0; i < count; i++) {\n")
		cg.write(fmt.Sprintf("    current = %s;\n", lookup("current", "symbols[ i ]")))
		cg.write("  }\n")
		cg.write(fmt.Sprintf("  oak_assert( current != %du ? oak_Bool_True : oak_Bool_False, \"%s\", 0 );\n", sinkValue, l.Protocol))
		cg.write(fmt.Sprintf("  %s result;\n  result.tag = current;\n  return result;\n", stateType))
	default:
		cg.write("  OAK_UNSUPPORTED_PROTOCOL_LOWERING;\n")
	}
}

// snakeIdent spells a protocol name the way its projected functions are
// prefixed (compiler/protocols.go snakeCase), for the shared table's name.
func snakeIdent(name string) string {
	var out strings.Builder
	for i, r := range name {
		if r >= 'A' && r <= 'Z' {
			if i > 0 {
				out.WriteByte('_')
			}
			out.WriteRune(r + ('a' - 'A'))
			continue
		}
		out.WriteRune(r)
	}
	return out.String()
}
