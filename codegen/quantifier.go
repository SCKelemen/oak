package codegen

import (
	"fmt"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// emitQuantifierExpression realizes a bounded quantifier
// (docs/spec/10-syntax.md section 3e) as a statement expression: one loop
// per binder over its finite domain — a counted range for Bool and the
// 8- and 16-bit integers, an array of the constructors for a payload-free
// sum type — the body evaluated in the innermost loop, and the result
// decided at the first assignment that settles it, as the interpreter
// decides it: a false body under `forall`, a true one under `exists`.
func (cg *CodeGenerator) emitQuantifierExpression(expr *ast.QuantifierExpression, tc *typechecker.TypeChecker) {
	cg.quantifierCounter++
	id := cg.quantifierCounter
	result := fmt.Sprintf("_oak_q%d", id)
	initial, settled := "oak_Bool_True", "oak_Bool_False"
	if !expr.Universal {
		initial, settled = "oak_Bool_False", "oak_Bool_True"
	}
	outerNoSequence := cg.noSequence
	cg.noSequence = true
	defer func() { cg.noSequence = outerNoSequence }()

	var out strings.Builder
	out.WriteString(fmt.Sprintf("({ Bool %s = %s; ", result, initial))
	closers := 0
	for i, binder := range expr.Binders {
		cType := cg.parseTypeExpression(binder.Type)
		name := cIdent(binder.Name.Value)
		counter := fmt.Sprintf("_oak_q%d_%d", id, i)
		if lo, hi, isRange := quantifierRange(binder.Type); isRange {
			out.WriteString(fmt.Sprintf("for (int64_t %s = %d; %s <= %d && %s == %s; %s++) { %s %s = (%s)%s; ",
				counter, lo, counter, hi, result, initial, counter, cType, name, cType, counter))
			closers++
			continue
		}
		typeName := ""
		if ident, isIdent := binder.Type.(*ast.Identifier); isIdent {
			typeName = ident.Value
		}
		adt := cg.adtTypes[typeName]
		if adt == nil {
			out.WriteString(fmt.Sprintf("/* quantifier over %s: not a finite domain */ ", typeName))
			continue
		}
		values := make([]string, 0, len(adt.Variants))
		for _, variant := range adt.Variants {
			values = append(values, fmt.Sprintf("%s_%s( )", cType, variant.Name.Value))
		}
		domain := fmt.Sprintf("_oak_q%d_d%d", id, i)
		out.WriteString(fmt.Sprintf("%s %s[%d] = { %s }; for (int64_t %s = 0; %s < %d && %s == %s; %s++) { %s %s = %s[%s]; ",
			cType, domain, len(values), strings.Join(values, ", "), counter, counter, len(values), result, initial, counter, cType, name, domain, counter))
		closers++
	}
	cg.output.WriteString(out.String())
	if expr.Universal {
		cg.output.WriteString("if (!( ")
	} else {
		cg.output.WriteString("if (( ")
	}
	cg.emitExpressionFragment(expr.Body, tc)
	cg.output.WriteString(fmt.Sprintf(" )) { %s = %s; } ", result, settled))
	for ; closers > 0; closers-- {
		cg.output.WriteString("} ")
	}
	cg.output.WriteString(fmt.Sprintf("%s; })", result))
}

// quantifierRange is the counted domain of a scalar binder type.
func quantifierRange(typ ast.Expression) (lo, hi int64, ok bool) {
	ident, isIdent := typ.(*ast.Identifier)
	if !isIdent {
		return 0, 0, false
	}
	switch ident.Value {
	case "Bool":
		return 0, 1, true
	case "u8", "byte":
		return 0, 255, true
	case "i8":
		return -128, 127, true
	case "u16":
		return 0, 65535, true
	case "i16":
		return -32768, 32767, true
	}
	return 0, 0, false
}
