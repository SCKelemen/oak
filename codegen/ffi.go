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

// boundarySpanArgument recognizes `c.span_of(v)` / `c.span_mut_of(s)` in the
// argument list of an extern call (docs/spec/92-ffi.md section 2.5) and
// returns the view or span operand. The typechecker has already confirmed the
// callee is an extern binding and the operand a named view or span; a local
// `c` would have made this an ordinary call that never typechecks as a
// library access.
func boundarySpanArgument(arg ast.Expression) (operand ast.Expression, ok bool) {
	call, isCall := arg.(*ast.InvocationExpression)
	if !isCall || len(call.Arguments) != 1 {
		return nil, false
	}
	library, member, isLibrary := libraryCallTarget(call.Function)
	if !isLibrary || library != "c" || (member != "span_of" && member != "span_mut_of") {
		return nil, false
	}
	return call.Arguments[0], true
}

// cStringArgument recognizes `c.cstr(v)` in the argument list of an extern
// call (docs/spec/92-ffi.md section 2.5.3) and returns the operand: a named
// []u8 view or a string literal, as the typechecker confirmed.
func cStringArgument(arg ast.Expression) (operand ast.Expression, ok bool) {
	call, isCall := arg.(*ast.InvocationExpression)
	if !isCall || len(call.Arguments) != 1 {
		return nil, false
	}
	library, member, isLibrary := libraryCallTarget(call.Function)
	if !isLibrary || library != "c" || member != "cstr" {
		return nil, false
	}
	return call.Arguments[0], true
}

// argvArgument recognizes `c.argv_of(bytes, slots)` in the argument list of
// an extern call (docs/spec/92-ffi.md section 2.5.6) and returns both
// operands, as the typechecker confirmed them: a named []u8 view and a
// named [*]c.Ptr span.
func argvArgument(arg ast.Expression) (bytes, slots ast.Expression, ok bool) {
	call, isCall := arg.(*ast.InvocationExpression)
	if !isCall || len(call.Arguments) != 2 {
		return nil, nil, false
	}
	library, member, isLibrary := libraryCallTarget(call.Function)
	if !isLibrary || library != "c" || member != "argv_of" {
		return nil, nil, false
	}
	return call.Arguments[0], call.Arguments[1], true
}

// outArgument recognizes `c.out(x)` in the argument list of an extern call
// (docs/spec/92-ffi.md section 2.5.7) and returns the local binding.
func outArgument(arg ast.Expression) (operand ast.Expression, ok bool) {
	call, isCall := arg.(*ast.InvocationExpression)
	if !isCall || len(call.Arguments) != 1 {
		return nil, false
	}
	library, member, isLibrary := libraryCallTarget(call.Function)
	if !isLibrary || library != "c" || member != "out" {
		return nil, false
	}
	return call.Arguments[0], true
}

// emitArgvArgument lowers `c.argv_of(bytes, slots)` at its extern call site
// (docs/spec/92-ffi.md section 2.5.6): oak_argv_u8 walks the view, records
// each string's start in the slots, appends the trailing NULL, and returns
// the slots' base; it traps naming the source position when the view is not
// NUL-terminated or the slots are too few. No copy of the strings.
func (cg *CodeGenerator) emitArgvArgument(bytes, slots ast.Expression, arg ast.Expression, tc *typechecker.TypeChecker) {
	cg.emitViewType("u8")
	line := 0
	file := cg.sourceFile
	if call, isCall := arg.(*ast.InvocationExpression); isCall {
		file = cg.tokenSourceFile(call.Token)
		line = call.Token.Line
	}
	cg.output.WriteString("oak_argv_u8( ")
	cg.emitExpressionFragment(bytes, tc)
	cg.output.WriteString(", (void **)( ")
	cg.emitExpressionFragment(slots, tc)
	cg.output.WriteString(" ).base, (u64)( ")
	cg.emitExpressionFragment(slots, tc)
	cg.output.WriteString(fmt.Sprintf(" ).len, %q, %d )", file, line))
}

// emitOutArgument lowers `c.out(x)` at its extern call site (docs/spec/
// 92-ffi.md section 2.5.7): the address of the local, valid for the call.
func (cg *CodeGenerator) emitOutArgument(operand ast.Expression, tc *typechecker.TypeChecker) {
	cg.output.WriteString("(void *)&( ")
	cg.emitExpressionFragment(operand, tc)
	cg.output.WriteString(" )")
}

// emitForeignFunctionAt lowers `c.fn_at(p)` (docs/spec/92-ffi.md section
// 2.10): the pointer itself, after oak_fn_at has trapped on NULL naming the
// Oak source position. The binding it initializes is an opaque `void *`;
// the signature lives in the annotation and is applied at each call.
func (cg *CodeGenerator) emitForeignFunctionAt(call *ast.InvocationExpression, tc *typechecker.TypeChecker) {
	file := cg.tokenSourceFile(call.Token)
	cg.output.WriteString("oak_fn_at( (void *)( ")
	cg.emitExpressionFragment(call.Arguments[0], tc)
	cg.output.WriteString(fmt.Sprintf(" ), %q, %d )", file, call.Token.Line))
}

// emitForeignFunctionCallee lowers the callee of a call through a `c.Fn`
// binding (docs/spec/92-ffi.md section 2.10): the opaque pointer cast to
// the annotated signature, `((ret (*)(params))f)`, with every C spelling
// taken from the same table extern prototypes use, so the cast is exactly
// the prototype an extern binding of that signature would have declared.
func (cg *CodeGenerator) emitForeignFunctionCallee(signature *ast.FunctionTypeExpression, callee ast.Expression, tc *typechecker.TypeChecker) {
	returnType := "void"
	if signature.Return != nil {
		if ident, isIdent := signature.Return.(*ast.Identifier); !isIdent || ident.Value != "()" {
			returnType = cg.parseTypeExpression(signature.Return)
		}
	}
	params := make([]string, 0, len(signature.Parameters))
	for _, param := range signature.Parameters {
		params = append(params, cg.parseTypeExpression(param))
	}
	paramList := "void"
	if len(params) > 0 {
		paramList = strings.Join(params, ", ")
	}
	cg.output.WriteString(fmt.Sprintf("(( %s (*)( %s ) )( ", returnType, paramList))
	cg.emitExpressionFragment(callee, tc)
	cg.output.WriteString(" ))")
}

// emitMessageSendCallee lowers the callee of `c.msg_send[(params) -> ret]`
// (docs/spec/92-ffi.md section 2.12): objc_msgSend cast to the prototype
// `ret (*)(void *, void *, params)` — the receiver (`id`) and the selector
// (`SEL`) are opaque pointers, and the declared parameters are spelled from
// the same table extern prototypes use. On arm64 every message goes through
// this one entry point (no `_stret`/`_fpret` variants), which is why the
// form is arm64-only in this increment; the emitted `#error` guard says so.
func (cg *CodeGenerator) emitMessageSendCallee(signature *ast.FunctionTypeExpression) {
	returnType := "void"
	if signature.Return != nil {
		if ident, isIdent := signature.Return.(*ast.Identifier); !isIdent || ident.Value != "()" {
			returnType = cg.parseTypeExpression(signature.Return)
		}
	}
	params := []string{"void *", "void *"}
	for _, param := range signature.Parameters {
		params = append(params, cg.parseTypeExpression(param))
	}
	cg.output.WriteString(fmt.Sprintf("(( %s (*)( %s ) )( objc_msgSend ))", returnType, strings.Join(params, ", ")))
}

// emitCStringArgument lowers `c.cstr(v)` at its extern call site (docs/spec/
// 92-ffi.md section 2.5.3): a literal operand is the interned literal (the
// typechecker required its trailing NUL); a named view goes through
// oak_cstr_u8, which checks the trailing NUL at the call and traps naming
// the source position otherwise. No copy.
func (cg *CodeGenerator) emitCStringArgument(operand ast.Expression, arg ast.Expression, tc *typechecker.TypeChecker) {
	if literal, isLiteral := operand.(*ast.StringLiteral); isLiteral {
		idx, exists := cg.stringLiteralMap[literal.Value]
		if !exists {
			idx = len(cg.stringLiterals)
			cg.stringLiterals = append(cg.stringLiterals, literal.Value)
			cg.stringLiteralMap[literal.Value] = idx
		}
		cg.output.WriteString(fmt.Sprintf("((const char *)str_lit_%d)", idx))
		return
	}
	cg.emitViewType("u8")
	line := 0
	file := cg.sourceFile
	if call, isCall := arg.(*ast.InvocationExpression); isCall {
		file = cg.tokenSourceFile(call.Token)
		line = call.Token.Line
	}
	cg.output.WriteString("oak_cstr_u8( ")
	cg.emitExpressionFragment(operand, tc)
	cg.output.WriteString(fmt.Sprintf(", %q, %d )", file, line))
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
		if member == "null" && len(call.Arguments) == 0 {
			// c.null(): the null pointer (docs/spec/92-ffi.md section 2.1).
			cg.output.WriteString("((void *)0)")
			return true
		}
		if member == "disown" && len(call.Arguments) == 1 {
			// c.disown(b): the buffer's pointer, for the runtime to free
			// (docs/spec/92-ffi.md section 2.8).
			cg.output.WriteString("((void *)( ")
			cg.emitExpressionFragment(call.Arguments[0], tc)
			cg.output.WriteString(" ).base)")
			return true
		}
		if member == "extern" || member == "span_of" || member == "span_mut_of" || member == "cstr" || member == "argv_of" || member == "out" || len(call.Arguments) != 1 {
			// Boundary spans are expanded at their extern call site
			// (emitExpressionFragment); anywhere else they are not
			// expressions and the typechecker has already rejected them.
			cg.output.WriteString("OAK_UNSUPPORTED_C_CALL")
			return true
		}
		if member == "String" {
			// c.String("literal"): the interned literal array is a C string
			// initializer, so it carries the trailing NUL
			// (docs/spec/92-ffi.md section 2.5.3).
			literal, isLiteral := call.Arguments[0].(*ast.StringLiteral)
			if !isLiteral {
				cg.output.WriteString("OAK_UNSUPPORTED_C_CALL")
				return true
			}
			idx, exists := cg.stringLiteralMap[literal.Value]
			if !exists {
				idx = len(cg.stringLiterals)
				cg.stringLiterals = append(cg.stringLiterals, literal.Value)
				cg.stringLiteralMap[literal.Value] = idx
			}
			cg.output.WriteString(fmt.Sprintf("((const char *)str_lit_%d)", idx))
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
			} else if _, isSend := typechecker.MessageSendCallee(e.Function); isSend {
				// c.msg_send[sig](...) (docs/spec/92-ffi.md section 2.12):
				// the callee carries a type in its bracket, so it is not a
				// plain library access; visited under its member name.
				visit("c", "msg_send")
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

// emitArgvHelper emits oak_argv_u8 when the program uses c.argv_of
// (docs/spec/92-ffi.md section 2.5.6), so programs without an argument
// vector keep their C output unchanged. The view holds the strings back to
// back, each NUL-terminated; every string's start goes into a slot and a
// NULL closes the vector. The view must end in NUL and the slots must
// number at least strings + 1; both are checked at the foreign call, naming
// the Oak source position before trapping, as an assertion does.
func (cg *CodeGenerator) emitArgvHelper(program *ast.Program) {
	used := false
	scanCalls(program, func(library, member string) {
		if library == "c" && member == "argv_of" {
			used = true
		}
	})
	if !used {
		return
	}
	viewTypeName := cg.emitViewType("u8")
	cg.write("/* c.argv_of: a NUL-terminated pointer vector over Oak strings, for one call */\n")
	cg.write("#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)\n#include <stdio.h>\n")
	cg.write("#define OAK_ARGV_FAIL(msg) do { fprintf(stderr, \"oak: c.argv_of %s at %s:%u\\n\", msg, file, (unsigned)line); __builtin_trap(); } while (0)\n")
	cg.write("#else\n#define OAK_ARGV_FAIL(msg) do { (void)file; (void)line; __builtin_trap(); } while (0)\n#endif\n")
	cg.write(fmt.Sprintf("static inline void *oak_argv_u8(%s v, void **slots, u64 nslots, const char *file, u32 line) {\n", viewTypeName))
	cg.write("  u64 count = 0;\n  u64 i;\n")
	cg.write("  if (v.len != 0u && v.base[v.len - 1u] != 0u) { OAK_ARGV_FAIL(\"strings are not NUL-terminated\"); }\n")
	cg.write("  for (i = 0; i < (u64)v.len; i++) { if (v.base[i] == 0u) { count++; } }\n")
	cg.write("  if (nslots < count + 1u) { OAK_ARGV_FAIL(\"has too few pointer slots\"); }\n")
	cg.write("  count = 0;\n  for (i = 0; i < (u64)v.len; i++) {\n")
	cg.write("    if (i == 0u || v.base[i - 1u] == 0u) { slots[count++] = (void *)(v.base + i); }\n  }\n")
	cg.write("  slots[count] = 0;\n  return (void *)slots;\n}\n#undef OAK_ARGV_FAIL\n\n")
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
	cg.write(fmt.Sprintf("extern %s %s( ", returnType, cg.externCallee(symbol)))
	if len(fn.Parameters) == 0 {
		cg.write("void")
	}
	for i, param := range fn.Parameters {
		cg.write(fmt.Sprintf("%s %s", cg.parseTypeExpression(param.Type), cIdent(param.Name.Value)))
		if i < len(fn.Parameters)-1 {
			cg.write(", ")
		}
	}
	cg.write(" )")
	if len(cg.foreignHeaders) != 0 {
		// The declaration is Oak's own identifier bound to the foreign
		// symbol by an asm label, so a header the program includes for a
		// target constant may declare the same function with its own
		// prototype without a conflicting redeclaration (section 2.11).
		cg.write(fmt.Sprintf(" __asm__(OAK_ASM_SYMBOL(\"%s\"))", symbol))
	}
	cg.write(";\n")
}

// externCallee is the C identifier a call to an extern binding names: the
// foreign symbol itself, or — in a program that includes foreign headers
// for target constants — Oak's asm-labeled declaration of it (section
// 2.11). The symbol has passed ValidCSymbol at the call sites that use this.
func (cg *CodeGenerator) externCallee(symbol string) string {
	if len(cg.foreignHeaders) != 0 {
		return "oak_extern_" + symbol
	}
	return symbol
}

// emitForeignHeaders emits the includes the program's target constants
// need (docs/spec/92-ffi.md section 2.11), before any other header so a
// feature-test macro can precede them: POSIX.1-2008 visibility, which
// strict -std=c99 builds on glibc would otherwise withhold from <time.h>
// and friends. Every header spelling passed ValidCHeader at check time and
// is re-validated here; an invalid one fails the C build closed instead of
// being emitted.
func (cg *CodeGenerator) emitForeignHeaders() {
	if len(cg.foreignHeaders) == 0 {
		return
	}
	cg.write("/* target constants (docs/spec/92-ffi.md section 2.11): the headers that\n   define them, then Oak's extern declarations carry asm labels so these\n   headers' prototypes never conflict with them */\n")
	cg.write("#if !__STDC_HOSTED__ || defined(OAK_FREESTANDING)\n#error \"target constants (c.const) need the hosted C library headers\"\n#endif\n")
	cg.write("#if !defined(_POSIX_C_SOURCE) && !defined(_GNU_SOURCE) && !defined(_XOPEN_SOURCE) && !defined(_DEFAULT_SOURCE)\n#define _POSIX_C_SOURCE 200809L\n#endif\n")
	for _, header := range cg.foreignHeaders {
		if !typechecker.ValidCHeader(header) {
			cg.write("OAK_INVALID_TARGET_CONSTANT_HEADER;\n")
			continue
		}
		cg.write(fmt.Sprintf("#include %s\n", header))
	}
	cg.write("#define OAK_STRINGIFY_(x) #x\n#define OAK_STRINGIFY(x) OAK_STRINGIFY_(x)\n")
	cg.write("#define OAK_ASM_SYMBOL(name) OAK_STRINGIFY(__USER_LABEL_PREFIX__) name\n")
}

// emitForeignBorrow lowers an inbound buffer borrow (docs/spec/92-ffi.md
// section 2.7): `c.borrow[T](ptr, count)` is the view struct over the
// pointer and count, `c.borrow_mut[T](ptr, count)` the span struct. No copy,
// no allocation; every element access through the result goes through the
// bounds-checked helpers against the count the program supplied.
func (cg *CodeGenerator) emitForeignBorrow(member string, element ast.Expression, call *ast.InvocationExpression, tc *typechecker.TypeChecker) {
	if member == "borrow_string" {
		// c.borrow_string(p) (section 2.7.1): the u8 view over the bytes
		// before the terminator, whose offset oak_cstr_len reads at
		// runtime (a NULL pointer is the empty view).
		structName := cg.emitViewType("u8")
		cg.output.WriteString(fmt.Sprintf("(%s){ (const u8 *)( ", structName))
		cg.emitExpressionFragment(call.Arguments[0], tc)
		cg.output.WriteString(" ), oak_cstr_len( ")
		cg.emitExpressionFragment(call.Arguments[0], tc)
		cg.output.WriteString(" ) }")
		return
	}
	elementC := cg.parseTypeExpression(element)
	if member == "borrow" {
		structName := cg.emitViewType(elementC)
		cg.output.WriteString(fmt.Sprintf("(%s){ (const %s *)( ", structName, elementC))
	} else {
		// borrow_mut, and own: an owned buffer is the span struct too
		// (section 2.8), so its views and spans are one copy away.
		structName := cg.emitSpanType(elementC)
		cg.output.WriteString(fmt.Sprintf("(%s){ (%s *)( ", structName, elementC))
	}
	cg.emitExpressionFragment(call.Arguments[0], tc)
	cg.output.WriteString(" ), (u32)( ")
	cg.emitExpressionFragment(call.Arguments[1], tc)
	cg.output.WriteString(" ) }")
}
