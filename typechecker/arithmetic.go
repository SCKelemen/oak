package typechecker

// Checked and saturating integer arithmetic (docs/spec/20-types.md
// section 11.1a): `{type}_checked_{add|sub|mul}(a, b)` returns
// `Result[type, Overflow]`, `{type}_saturating_{add|sub|mul}(a, b)` clamps
// to the type's range. The operators themselves wrap; these are the
// explicit spellings for code that must notice the wrap — offsets, lengths,
// sequence numbers — without a manual guard on every operation.

import "github.com/SCKelemen/oak/ast"

var arithmeticKinds = map[string]bool{"add": true, "sub": true, "mul": true}
var arithmeticOperations = map[string]bool{"checked": true, "saturating": true}

// ArithmeticParts parses `{type}_{op}_{kind}` with a fixed-width integer
// type, op in checked/saturating, and kind in add/sub/mul. The grammar is
// disjoint from the conversion family's `{target}_{op}_{source}`: a kind is
// never a primitive type name.
func ArithmeticParts(name string) (prim, op, kind string, ok bool) {
	parts := splitNarrowingFunctionName(name)
	if parts == nil {
		return "", "", "", false
	}
	prim, op, kind = parts[0], parts[1], parts[2]
	if _, isPrim := conversionPrimitives[prim]; !isPrim || IsFloatName(prim) || IsStorageFloatName(prim) {
		return "", "", "", false
	}
	if !arithmeticOperations[op] || !arithmeticKinds[kind] {
		return "", "", "", false
	}
	return prim, op, kind, true
}

// checkArithmeticFunction types a checked or saturating arithmetic call.
// Both operands must have the named type (untyped literals infer against
// it); the result is the type itself for saturating and
// `Result[type, Overflow]` for checked, recorded as an ADT instantiation
// like the checked conversions so the backend monomorphizes it.
func (tc *TypeChecker) checkArithmeticFunction(funcName string, args []ast.Expression, call ast.Node) Type {
	prim, op, kind, ok := ArithmeticParts(funcName)
	if !ok {
		return nil
	}
	if len(args) != 2 {
		tc.addError(call, "%s expects 2 arguments, got %d", funcName, len(args))
		return nil
	}
	primType := &PrimitiveType{Name: prim}
	for i, arg := range args {
		argType := tc.checkExpression(arg, primType)
		if argType == nil {
			return nil
		}
		argPrim, isPrim := argType.(*PrimitiveType)
		if !isPrim || normalizePrimitiveName(argPrim.Name) != prim {
			tc.addError(arg, "%s expects operand %d of type %s, got %s (convert explicitly; %s arithmetic has one width)", funcName, i+1, prim, argType, kind)
			return nil
		}
	}
	if op == "saturating" {
		return primType
	}
	overflowType := &ADTType{Name: "Overflow"}
	tc.recordADTInstantiation("Result", []Type{primType, overflowType})
	return &GenericType{Name: "Result", TypeArgs: []Type{primType, overflowType}}
}
