package codegen

// C backend lowering for checked, saturating and trapping integer
// arithmetic (docs/spec/20-types.md section 11.1a): one static inline
// helper per used function. Overflow is detected with the type-generic
// __builtin_{add,sub,mul}_overflow, which compute the exact result and
// report whether it fits the result type without ever evaluating a signed
// overflow in C — the same baseline (gcc/clang builtins) the trapping
// helpers already require. checked_* returns the monomorphized
// Result[T, Overflow]; saturating_* clamps toward the side the exact result
// left the range on; trapping_* returns the exact result or stops at a
// located trap (oak_overflow_trap, the assertion machinery of
// 85-discipline.md section 5) whose file and line the call site supplies.

import (
	"fmt"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// arithmeticHelperName is the emitted helper for one arithmetic function.
func arithmeticHelperName(oakName string) string { return "oak_arith_" + oakName }

// collectUsedArithmetic scans for arithmetic-function calls (plain
// identifier callees matching the fixed grammar).
func collectUsedArithmetic(program *ast.Program) []string {
	used := map[string]bool{}
	scanCalls(program, func(library, member string) {
		if library != "" {
			return
		}
		if _, _, _, ok := typechecker.ArithmeticParts(member); ok {
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

// emitArithmeticHelpers emits one helper per used arithmetic function.
// Runs after ADT emission: the checked forms return a monomorphized Result.
func (cg *CodeGenerator) emitArithmeticHelpers(program *ast.Program) {
	used := collectUsedArithmetic(program)
	if len(used) == 0 {
		return
	}
	cg.write("/* checked, saturating and trapping arithmetic: exact overflow detection\n")
	cg.write("   via the type-generic overflow builtins; no signed overflow is ever\n")
	cg.write("   evaluated. A trapping overflow names its Oak source position. */\n")
	cg.write("#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)\n")
	cg.write("static inline void oak_overflow_trap(const char *file, u32 line) {\n")
	cg.write("  fprintf(stderr, \"oak: arithmetic overflow at %s:%u\\n\", file, (unsigned)line);\n")
	cg.write("  __builtin_trap();\n}\n")
	cg.write("#else\n")
	cg.write("static inline void oak_overflow_trap(const char *file, u32 line) {\n")
	cg.write("  oak_report(\"arithmetic overflow\", file, line);\n  __builtin_trap();\n}\n")
	cg.write("#endif\n")
	for _, name := range used {
		cg.writeRaw(cg.arithmeticHelperSource(name))
		cg.write("\n")
	}
}

// arithmeticHelperSource builds one helper body.
func (cg *CodeGenerator) arithmeticHelperSource(oakName string) string {
	prim, op, kind, ok := typechecker.ArithmeticParts(oakName)
	if !ok {
		return "OAK_UNSUPPORTED_ARITHMETIC\n"
	}
	builtin := "__builtin_" + kind + "_overflow"
	signed := prim[0] == 'i'
	bits := typechecker.PrimitiveBits(prim)
	var minC, maxC string
	if signed {
		max := int64(1)<<uint(bits-1) - 1
		minC = fmt.Sprintf("(%s)(-%d - 1)", prim, max)
		maxC = fmt.Sprintf("(%s)%d", prim, max)
	} else {
		minC = fmt.Sprintf("(%s)0u", prim)
		if bits == 64 {
			maxC = fmt.Sprintf("(%s)%duLL", prim, ^uint64(0))
		} else {
			maxC = fmt.Sprintf("(%s)%du", prim, (uint64(1)<<uint(bits))-1)
		}
	}

	var b strings.Builder
	if op == "trapping" {
		fmt.Fprintf(&b, "static inline %s %s( %s a, %s b, const char *file, u32 line ) {\n  %s r;\n", prim, arithmeticHelperName(oakName), prim, prim, prim)
		fmt.Fprintf(&b, "  if (%s(a, b, &r)) { oak_overflow_trap(file, line); }\n  return r;\n}\n", builtin)
		return b.String()
	}
	if op == "saturating" {
		fmt.Fprintf(&b, "static inline %s %s( %s a, %s b ) {\n  %s r;\n", prim, arithmeticHelperName(oakName), prim, prim, prim)
		fmt.Fprintf(&b, "  if (%s(a, b, &r)) {\n", builtin)
		// Which side did the exact result leave on? Unsigned add and mul
		// only overflow upward, unsigned sub only downward; signed add
		// overflows upward iff b > 0, sub iff b < 0, mul iff the operands
		// share a sign.
		var upward string
		switch {
		case !signed && kind == "sub":
			upward = "0"
		case !signed:
			upward = "1"
		case kind == "add":
			upward = "b > 0"
		case kind == "sub":
			upward = "b < 0"
		default:
			upward = "(a < 0) == (b < 0)"
		}
		fmt.Fprintf(&b, "    return (%s) ? %s : %s;\n  }\n  return r;\n}\n", upward, maxC, minC)
		return b.String()
	}

	resultC, okName, errName, overflowC, overflowCtor, shaped := cg.checkedResultShape(prim)
	if !shaped {
		return fmt.Sprintf("OAK_CHECKED_ARITHMETIC_NEEDS_RESULT_AND_OVERFLOW(%s);\n", oakName)
	}
	fmt.Fprintf(&b, "static inline %s %s( %s a, %s b ) {\n  %s r;\n", resultC, arithmeticHelperName(oakName), prim, prim, prim)
	fmt.Fprintf(&b, "  if (%s(a, b, &r)) { return %s_%s(%s_%s()); }\n", builtin, resultC, errName, overflowC, overflowCtor)
	fmt.Fprintf(&b, "  return %s_%s(r);\n}\n", resultC, okName)
	return b.String()
}

// checkedResultShape resolves the program's Result[target, Overflow]
// instantiation and Overflow declaration to the C names a checked helper
// constructs with: the Result typedef, its Ok and Err constructors (the
// variants carrying the target and Overflow payloads), and Overflow's
// payload-less constructor. Anything else is unshaped and the caller fails
// closed.
func (cg *CodeGenerator) checkedResultShape(target string) (resultC, okName, errName, overflowC, overflowCtor string, ok bool) {
	resultADT, hasResult := cg.adtTypes["Result_"+target+"_Overflow"]
	overflowADT, hasOverflow := cg.adtTypes["Overflow"]
	if !hasResult || !hasOverflow || len(overflowADT.Variants) == 0 {
		return "", "", "", "", "", false
	}
	for _, variant := range resultADT.Variants {
		if variant.Payload == nil {
			continue
		}
		payload, isIdent := variant.Payload.(*ast.Identifier)
		if !isIdent {
			continue
		}
		if payload.Value == target {
			okName = variant.Name.Value
		}
		if payload.Value == "Overflow" {
			errName = variant.Name.Value
		}
	}
	for _, variant := range overflowADT.Variants {
		if variant.Payload == nil {
			overflowCtor = variant.Name.Value
			break
		}
	}
	if okName == "" || errName == "" || overflowCtor == "" {
		return "", "", "", "", "", false
	}
	return cg.cTypeName("Result_" + target + "_Overflow"), okName, errName, cg.cTypeName("Overflow"), overflowCtor, true
}

// emitArithmeticCall routes an arithmetic-function invocation to its
// helper. Reports whether handled.
func (cg *CodeGenerator) emitArithmeticCall(call *ast.InvocationExpression, tc *typechecker.TypeChecker) bool {
	ident, isIdent := call.Function.(*ast.Identifier)
	if !isIdent || len(call.Arguments) != 2 {
		return false
	}
	prim, op, _, ok := typechecker.ArithmeticParts(ident.Value)
	if !ok {
		return false
	}
	if op == "checked" {
		if _, _, _, _, _, shaped := cg.checkedResultShape(prim); !shaped {
			cg.output.WriteString("OAK_CHECKED_ARITHMETIC_NEEDS_RESULT_AND_OVERFLOW")
			return true
		}
	}
	cg.output.WriteString(fmt.Sprintf("%s( ", arithmeticHelperName(ident.Value)))
	cg.emitExpressionFragment(call.Arguments[0], tc)
	cg.output.WriteString(", ")
	cg.emitExpressionFragment(call.Arguments[1], tc)
	if op == "trapping" {
		// Like assert: the trap names the Oak call site.
		cg.output.WriteString(fmt.Sprintf(", %q, %d", cg.sourceFile, ident.Token.Line))
	}
	cg.output.WriteString(" )")
	return true
}
