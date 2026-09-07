package codegen

// C backend lowering for the foreign-interface libraries
// (docs/spec/92-ffi.md): extern binding prototypes and calls, c type
// spellings and conversions, and the arm64 instruction-function helpers.

import (
	"fmt"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/semir"
	"github.com/SCKelemen/oak/typechecker"
)

// cQualifiedTypeSpelling resolves a dotted c-library type name ("c.Int32")
// to its C spelling. Unknown members fail closed with a compile-breaking
// marker rather than guessing a spelling.
func cQualifiedTypeSpelling(name string) (string, bool) {
	if !strings.HasPrefix(name, "c.") {
		return "", false
	}
	spelling, known := typechecker.CTypeSpelling(strings.TrimPrefix(name, "c."))
	if !known {
		return "OAK_UNSUPPORTED_C_TYPE", true
	}
	return spelling, true
}

// libraryCallTarget destructures `library.member` invocation callees for
// the compiler-known libraries.
func libraryCallTarget(fn ast.Expression) (library, member string, ok bool) {
	access, isAccess := fn.(*ast.IndexExpression)
	if !isAccess {
		return "", "", false
	}
	base, isIdent := access.Left.(*ast.Identifier)
	if !isIdent || !typechecker.CompilerKnownLibrary(base.Value) {
		return "", "", false
	}
	memberIdent, isIdent := access.Index.(*ast.Identifier)
	if !isIdent {
		return "", "", false
	}
	return base.Value, memberIdent.Value, true
}

// emitLibraryCall lowers a compiler-known library call. The typechecker owns
// the arm64 signature catalog, so codegen queries arity rather than maintaining
// a second table. This supports both ordinary one-operand intrinsics and
// nullary architectural barriers without runtime dispatch.
func (cg *CodeGenerator) emitLibraryCall(call *ast.InvocationExpression, tc *typechecker.TypeChecker) bool {
	library, member, ok := libraryCallTarget(call.Function)
	if !ok {
		return false
	}
	switch library {
	case "c":
		if member == "extern" || len(call.Arguments) != 1 {
			cg.output.WriteString("OAK_UNSUPPORTED_C_CALL")
			return true
		}
		spelling, known := typechecker.CTypeSpelling(member)
		if !known {
			cg.output.WriteString("OAK_UNSUPPORTED_C_TYPE")
			return true
		}
		cg.output.WriteString(fmt.Sprintf("((%s)( ", spelling))
		cg.emitExpressionFragment(call.Arguments[0], tc)
		cg.output.WriteString(" ))")
		return true
	case "arm64":
		_, validVector := arm64VectorIntrinsicSources[member]
		_, validScalarOrBarrier := arm64HelperSources[member]
		arity, knownSignature := typechecker.Arm64IntrinsicArity(member)
		if (!validScalarOrBarrier && !validVector) || !knownSignature || len(call.Arguments) != arity {
			cg.output.WriteString("OAK_UNSUPPORTED_ARM64_INTRINSIC")
			return true
		}
		cg.output.WriteString(fmt.Sprintf("oak_arm64_%s( ", member))
		for i, arg := range call.Arguments {
			cg.emitExpressionFragment(arg, tc)
			if i < len(call.Arguments)-1 {
				cg.output.WriteString(", ")
			}
		}
		cg.output.WriteString(" )")
		return true
	case "simd":
		if _, _, valid := simdOpSplit(member); !valid {
			cg.output.WriteString("OAK_UNSUPPORTED_SIMD_OP")
			return true
		}
		cg.output.WriteString(fmt.Sprintf("oak_simd_%s( ", member))
		for i, arg := range call.Arguments {
			cg.emitExpressionFragment(arg, tc)
			if i < len(call.Arguments)-1 {
				cg.output.WriteString(", ")
			}
		}
		cg.output.WriteString(" )")
		return true
	}
	return false
}

// arm64IntrinsicWidths retains the original scalar-integer catalog for tests
// and documentation. Barrier membership is instead owned by the SemIR-backed
// typechecker catalog and arm64HelperSources below.
var arm64IntrinsicWidths = map[string]bool{
	"rev32": true, "rev64": true,
	"rbit32": true, "rbit64": true,
	"clz32": true, "clz64": true,
}

// collectUsedIntrinsics scans the program for scalar arm64 instruction
// functions and machine barriers. Presence in arm64HelperSources is the backend
// capability witness; the typechecker independently rejects unknown members.
func collectUsedIntrinsics(program *ast.Program) []string {
	used := map[string]bool{}
	scanCalls(program, func(library, member string) {
		if library == "arm64" && arm64HelperSources[member] != "" {
			used[member] = true
		}
	})
	names := make([]string, 0, len(used))
	for name := range used {
		names = append(names, name)
	}
	sort.Strings(names)
	return names
}

// scanCalls walks the program and reports every compiler-known library
// call target (library, member). The walk covers the same node kinds the
// emitter handles.
func scanCalls(program *ast.Program, visit func(library, member string)) {
	var scanExpr func(expr ast.Expression)
	var scanStmt func(stmt ast.Statement)

	scanExpr = func(expr ast.Expression) {
		switch e := expr.(type) {
		case *ast.InvocationExpression:
			if library, member, ok := libraryCallTarget(e.Function); ok {
				visit(library, member)
			} else if ident, isIdent := e.Function.(*ast.Identifier); isIdent {
				// Plain callees are visited with an empty library, so
				// helper collectors (conversions) can see them.
				visit("", ident.Value)
			} else {
				scanExpr(e.Function)
			}
			for _, arg := range e.Arguments {
				scanExpr(arg)
			}
		case *ast.InfixExpression:
			scanExpr(e.Left)
			scanExpr(e.Right)
		case *ast.PrefixExpression:
			scanExpr(e.Right)
		case *ast.IndexExpression:
			scanExpr(e.Left)
			scanExpr(e.Index)
		case *ast.SliceExpression:
			scanExpr(e.Seq)
			scanExpr(e.Low)
			scanExpr(e.High)
		case *ast.MatchExpression:
			scanExpr(e.Scrutinee)
			for _, arm := range e.Arms {
				scanExpr(arm.Body)
			}
		case *ast.BlockExpression:
			if e.Block != nil {
				for _, stmt := range e.Block.Statements {
					scanStmt(stmt)
				}
			}
		case *ast.VariantExpression:
			scanExpr(e.Payload)
		case *ast.ArrayLiteral:
			for _, element := range e.Elements {
				scanExpr(element)
			}
		case *ast.RecordLiteral:
			for _, field := range e.Fields {
				scanExpr(field)
			}
		case *ast.FunctionLiteral:
			if e.Body != nil {
				for _, stmt := range e.Body.Statements {
					scanStmt(stmt)
				}
			}
		}
	}

	scanStmt = func(stmt ast.Statement) {
		switch s := stmt.(type) {
		case *ast.ExpressionStatement:
			scanExpr(s.Expression)
		case *ast.VariableDeclaration:
			scanExpr(s.Value)
		case *ast.AssignmentStatement:
			scanExpr(s.Value)
		case *ast.IndexAssignmentStatement:
			scanExpr(s.Target)
			scanExpr(s.Value)
		case *ast.WhileStatement:
			scanExpr(s.Condition)
			if s.Body != nil {
				for _, inner := range s.Body.Statements {
					scanStmt(inner)
				}
			}
		case *ast.IfStatement:
			scanExpr(s.Condition)
			if s.Consequence != nil {
				scanStmt(s.Consequence)
			}
			if s.Alternative != nil {
				scanStmt(s.Alternative)
			}
		case *ast.UnsafeBlock:
			if s.Body != nil {
				for _, inner := range s.Body.Statements {
					scanStmt(inner)
				}
			}
		case *ast.BlockStatement:
			for _, inner := range s.Statements {
				scanStmt(inner)
			}
		case *ast.FunctionStatement:
			if s.ExternSymbol == "" {
				scanExpr(s.Body)
			}
		}
	}

	for _, stmt := range program.Statements {
		scanStmt(stmt)
	}
}

// emitIntrinsicHelpers emits only helpers referenced by the program. Scalar
// instruction functions keep their portable semantics. Architectural barriers
// deliberately have no portable branch: compiling one for a non-AArch64 target
// is a hard error rather than a semantic lie.
func (cg *CodeGenerator) emitIntrinsicHelpers(program *ast.Program) {
	used := collectUsedIntrinsics(program)
	if len(used) == 0 {
		return
	}
	header := "/* arm64 instruction functions */\n"
	for _, name := range used {
		if _, barrier := semir.LookupArm64Barrier(name); barrier {
			header = "/* arm64 instruction functions and barriers */\n"
			break
		}
	}
	cg.write(header)
	for _, name := range used {
		cg.writeRaw(arm64HelperSources[name])
		cg.write("\n")
	}
}

// arm64HelperSources holds one helper per scalar instruction function and
// barrier. The portable scalar branches supply total semantics where possible;
// barriers fail closed off AArch64 because DMB/DSB/ISB have architectural
// semantics the host evaluator/C backend cannot faithfully emulate.
var arm64HelperSources = map[string]string{
	"rev32": `static inline u32 oak_arm64_rev32( u32 x ) {
#if defined(__aarch64__) && !defined(OAK_PORTABLE_INTRINSICS)
  __asm__("rev %w0, %w1" : "=r"(x) : "r"(x));
  return x;
#else
  return __builtin_bswap32(x);
#endif
}
`,
	"rev64": `static inline u64 oak_arm64_rev64( u64 x ) {
#if defined(__aarch64__) && !defined(OAK_PORTABLE_INTRINSICS)
  __asm__("rev %0, %1" : "=r"(x) : "r"(x));
  return x;
#else
  return __builtin_bswap64(x);
#endif
}
`,
	"rbit32": `static inline u32 oak_arm64_rbit32( u32 x ) {
#if defined(__aarch64__) && !defined(OAK_PORTABLE_INTRINSICS)
  __asm__("rbit %w0, %w1" : "=r"(x) : "r"(x));
  return x;
#else
  x = ((x & 0x55555555u) << 1) | ((x >> 1) & 0x55555555u);
  x = ((x & 0x33333333u) << 2) | ((x >> 2) & 0x33333333u);
  x = ((x & 0x0F0F0F0Fu) << 4) | ((x >> 4) & 0x0F0F0F0Fu);
  return __builtin_bswap32(x);
#endif
}
`,
	"rbit64": `static inline u64 oak_arm64_rbit64( u64 x ) {
#if defined(__aarch64__) && !defined(OAK_PORTABLE_INTRINSICS)
  __asm__("rbit %0, %1" : "=r"(x) : "r"(x));
  return x;
#else
  x = ((x & 0x5555555555555555u) << 1) | ((x >> 1) & 0x5555555555555555u);
  x = ((x & 0x3333333333333333u) << 2) | ((x >> 2) & 0x3333333333333333u);
  x = ((x & 0x0F0F0F0F0F0F0F0Fu) << 4) | ((x >> 4) & 0x0F0F0F0F0F0F0F0Fu);
  return __builtin_bswap64(x);
#endif
}
`,
	"clz32": `static inline u32 oak_arm64_clz32( u32 x ) {
#if defined(__aarch64__) && !defined(OAK_PORTABLE_INTRINSICS)
  u32 r;
  __asm__("clz %w0, %w1" : "=r"(r) : "r"(x));
  return r;
#else
  return x == 0u ? 32u : (u32)__builtin_clz(x);
#endif
}
`,
	"clz64": `static inline u64 oak_arm64_clz64( u64 x ) {
#if defined(__aarch64__) && !defined(OAK_PORTABLE_INTRINSICS)
  u64 r;
  __asm__("clz %0, %1" : "=r"(r) : "r"(x));
  return r;
#else
  return x == 0u ? 64u : (u64)__builtin_clzll(x);
#endif
}
`,
	"dmb_ishld": `static inline void oak_arm64_dmb_ishld( void ) {
#if defined(__aarch64__) && !defined(OAK_PORTABLE_INTRINSICS)
  __asm__ volatile("dmb ishld" ::: "memory");
#else
#error "arm64.dmb_ishld requires an AArch64 target"
#endif
}
`,
	"dmb_ish": `static inline void oak_arm64_dmb_ish( void ) {
#if defined(__aarch64__) && !defined(OAK_PORTABLE_INTRINSICS)
  __asm__ volatile("dmb ish" ::: "memory");
#else
#error "arm64.dmb_ish requires an AArch64 target"
#endif
}
`,
	"dmb_sy": `static inline void oak_arm64_dmb_sy( void ) {
#if defined(__aarch64__) && !defined(OAK_PORTABLE_INTRINSICS)
  __asm__ volatile("dmb sy" ::: "memory");
#else
#error "arm64.dmb_sy requires an AArch64 target"
#endif
}
`,
	"dsb_ish": `static inline void oak_arm64_dsb_ish( void ) {
#if defined(__aarch64__) && !defined(OAK_PORTABLE_INTRINSICS)
  __asm__ volatile("dsb ish" ::: "memory");
#else
#error "arm64.dsb_ish requires an AArch64 target"
#endif
}
`,
	"dsb_sy": `static inline void oak_arm64_dsb_sy( void ) {
#if defined(__aarch64__) && !defined(OAK_PORTABLE_INTRINSICS)
  __asm__ volatile("dsb sy" ::: "memory");
#else
#error "arm64.dsb_sy requires an AArch64 target"
#endif
}
`,
	"isb": `static inline void oak_arm64_isb( void ) {
#if defined(__aarch64__) && !defined(OAK_PORTABLE_INTRINSICS)
  __asm__ volatile("isb" ::: "memory");
#else
#error "arm64.isb requires an AArch64 target"
#endif
}
`,
}

// emitExternPrototype emits the foreign declaration an extern binding
// asserts (docs/spec/92-ffi.md section 2.3). The symbol is re-validated
// against the C identifier grammar before emission (defense in depth behind
// OAK-F0102): an invalid symbol fails closed as a compile-breaking marker,
// never as interpolated C.
func (cg *CodeGenerator) emitExternPrototype(fn *ast.FunctionStatement) {
	symbol := fn.ExternSymbol
	if !typechecker.ValidCSymbol(symbol) {
		cg.write("OAK_INVALID_EXTERN_SYMBOL;\n")
		return
	}
	returnType := "void"
	if fn.ReturnType != nil {
		returnType = cg.parseTypeExpression(fn.ReturnType)
	}
	cg.write(fmt.Sprintf("extern %s %s( ", returnType, symbol))
	if len(fn.Parameters) == 0 {
		cg.write("void")
	}
	for i, param := range fn.Parameters {
		cg.write(fmt.Sprintf("%s %s", cg.parseTypeExpression(param.Type), param.Name.Value))
		if i < len(fn.Parameters)-1 {
			cg.write(", ")
		}
	}
	cg.write(" );\n")
}
