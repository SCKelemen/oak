package codegen

// C backend lowering for the explicit integer conversion family
// (docs/spec/20-types.md): {target}_{op}_{source} with op in
// trunc/saturating/bits. Every helper avoids implementation-defined C:
// unsigned conversions are modulo casts (defined), and signed-target
// results are produced by union type punning from the unsigned bit pattern
// (defined since C99 TC3) — two's complement semantics, total on every
// input. checked_* returns Result[T, Overflow] and stays fail-closed until
// generic ADTs lower.

import (
	"fmt"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// conversionHelperName is the emitted helper for one conversion function.
func conversionHelperName(oakName string) string { return "oak_conv_" + oakName }

// collectUsedConversions scans for conversion-function calls (plain
// identifier callees matching the fixed grammar).
func collectUsedConversions(program *ast.Program) []string {
	used := map[string]bool{}
	scanCalls(program, func(library, member string) {
		if library != "" {
			return
		}
		if _, _, _, ok := typechecker.ConversionParts(member); ok {
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

// emitConversionHelpers emits one static inline helper per used conversion.
func (cg *CodeGenerator) emitConversionHelpers(program *ast.Program) {
	used := collectUsedConversions(program)
	if len(used) == 0 {
		return
	}
	cg.write("/* explicit integer conversions: total, two's complement, no\n")
	cg.write("   implementation-defined C (signed results via union punning) */\n")
	for _, name := range used {
		if _, op, _, _ := typechecker.ConversionParts(name); op == "checked" {
			cg.writeRaw(cg.checkedConversionHelperSource(name))
		} else {
			cg.writeRaw(conversionHelperSource(name))
		}
		cg.write("\n")
	}
}

// checkedConversionHelperSource emits the Result-returning checked
// narrowing (docs/spec/20-types.md §11.1): usable when the program declares
// Result[T, E] with Ok/Err constructors and a payload-less Overflow ADT —
// anything else fails closed.
func (cg *CodeGenerator) checkedConversionHelperSource(oakName string) string {
	target, _, source, ok := typechecker.ConversionParts(oakName)
	if !ok {
		return "OAK_UNSUPPORTED_CONVERSION\n"
	}
	resultADT, hasResult := cg.adtTypes["Result_"+target+"_Overflow"]
	overflowADT, hasOverflow := cg.adtTypes["Overflow"]
	if !hasResult || !hasOverflow || len(overflowADT.Variants) == 0 {
		return fmt.Sprintf("OAK_CHECKED_CONVERSION_NEEDS_RESULT_AND_OVERFLOW(%s);\n", oakName)
	}
	okName, errName := "", ""
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
	overflowCtor := ""
	for _, variant := range overflowADT.Variants {
		if variant.Payload == nil {
			overflowCtor = variant.Name.Value
			break
		}
	}
	if okName == "" || errName == "" || overflowCtor == "" {
		return fmt.Sprintf("OAK_CHECKED_CONVERSION_NEEDS_RESULT_AND_OVERFLOW(%s);\n", oakName)
	}

	resultC := cg.cTypeName("Result_" + target + "_Overflow")
	overflowC := cg.cTypeName("Overflow")
	targetBits := typechecker.PrimitiveBits(target)
	var b strings.Builder
	fmt.Fprintf(&b, "static inline %s %s( %s x ) {\n", resultC, conversionHelperName(oakName), source)
	if typechecker.IsFloatName(source) {
		// Float source (docs/spec/20-types.md section 11.3.4): out of range
		// and NaN are Err(Overflow); the same exact bounds as trunc.
		low, high := floatIntegerBounds(target)
		fmt.Fprintf(&b, "  if (!(x %s && x %s)) { return %s_%s(%s_%s()); }\n", low, high, resultC, errName, overflowC, overflowCtor)
		fmt.Fprintf(&b, "  return %s_%s((%s)x);\n}\n", resultC, okName, target)
		return b.String()
	}
	if strings.HasPrefix(target, "u") {
		max := (uint64(1) << uint(targetBits)) - 1
		fmt.Fprintf(&b, "  if (x > (%s)%du) { return %s_%s(%s_%s()); }\n", source, max, resultC, errName, overflowC, overflowCtor)
	} else {
		max := int64(1)<<uint(targetBits-1) - 1
		min := -(int64(1) << uint(targetBits-1))
		fmt.Fprintf(&b, "  if (x > (%s)%d || x < (%s)(%d)) { return %s_%s(%s_%s()); }\n", source, max, source, min, resultC, errName, overflowC, overflowCtor)
	}
	fmt.Fprintf(&b, "  return %s_%s((%s)x);\n}\n", resultC, okName, target)
	return b.String()
}

// conversionHelperSource builds the helper body. Names come from the fixed
// grammar validated by typechecker.ConversionParts.
func conversionHelperSource(oakName string) string {
	target, op, source, ok := typechecker.ConversionParts(oakName)
	if !ok || op == "checked" {
		return "OAK_UNSUPPORTED_CONVERSION\n"
	}
	if typechecker.IsFloatName(target) || typechecker.IsFloatName(source) {
		return floatConversionHelperSource(oakName, target, op, source)
	}
	targetBits := typechecker.PrimitiveBits(target)
	unsignedOf := func(prim string) string { return "u" + prim[1:] }
	helper := conversionHelperName(oakName)

	var b strings.Builder
	fmt.Fprintf(&b, "static inline %s %s( %s x ) {\n", target, helper, source)
	switch op {
	case "bits":
		// Same width, opposite signedness: pure bit reinterpretation.
		fmt.Fprintf(&b, "  union { %s from; %s to; } pun;\n", source, target)
		fmt.Fprintf(&b, "  pun.from = x;\n  return pun.to;\n")
	case "trunc":
		if strings.HasPrefix(target, "u") {
			// Unsigned narrowing is modulo arithmetic: defined by C99.
			fmt.Fprintf(&b, "  return (%s)( x );\n", target)
		} else {
			// Signed target: take the low bits in unsigned space (defined),
			// then reinterpret (defined) — two's complement wraparound.
			fmt.Fprintf(&b, "  union { %s low; %s to; } pun;\n", unsignedOf(target), target)
			fmt.Fprintf(&b, "  pun.low = (%s)( (%s)x );\n", unsignedOf(target), unsignedOf(source))
			fmt.Fprintf(&b, "  return pun.to;\n")
		}
	case "saturating":
		if strings.HasPrefix(target, "u") {
			max := (uint64(1) << uint(targetBits)) - 1
			if targetBits == 64 {
				max = ^uint64(0)
			}
			fmt.Fprintf(&b, "  return x > (%s)%du ? (%s)%du : (%s)x;\n", source, max, target, max, target)
		} else {
			max := int64(1)<<uint(targetBits-1) - 1
			min := -(int64(1) << uint(targetBits-1))
			fmt.Fprintf(&b, "  if (x > (%s)%d) { return (%s)%d; }\n", source, max, target, max)
			fmt.Fprintf(&b, "  if (x < (%s)(%d)) { return (%s)(%d); }\n", source, min, target, min)
			fmt.Fprintf(&b, "  return (%s)x;\n", target)
		}
	}
	b.WriteString("}\n")
	return b.String()
}

// emitConversionCall routes a conversion-function invocation to its helper
// (checked stays fail-closed until Result lowers). Reports whether handled.
func (cg *CodeGenerator) emitConversionCall(call *ast.InvocationExpression, tc *typechecker.TypeChecker) bool {
	ident, isIdent := call.Function.(*ast.Identifier)
	if !isIdent || len(call.Arguments) != 1 {
		return false
	}
	target, op, _, ok := typechecker.ConversionParts(ident.Value)
	if !ok {
		return false
	}
	if op == "checked" {
		// Callable once the program declares Result and Overflow (the
		// helper validates the shapes); otherwise fail closed.
		if _, hasResult := cg.adtTypes["Result_"+target+"_Overflow"]; !hasResult {
			cg.output.WriteString("OAK_CHECKED_CONVERSION_NEEDS_RESULT_AND_OVERFLOW")
			return true
		}
	}
	cg.output.WriteString(fmt.Sprintf("%s( ", conversionHelperName(ident.Value)))
	cg.emitExpressionFragment(call.Arguments[0], tc)
	cg.output.WriteString(" )")
	return true
}
