package typechecker

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
)

// Refinement types (docs/spec/20-types.md section 12, docs/spec/125-verification.md
// §6). `Small: type = u16 where value < u16(256)` declares a nominal type
// whose values are the base type's values satisfying the predicate. The
// predicate is a Bool expression over `value`, checked like any expression
// with `value` bound at the base type. A refined value flows to its base
// freely (the refinement is dropped, as arithmetic drops it); a base value
// becomes refined only through the checked construction `Small(v)`, which
// the backend realizes as the base value guarded by the predicate — a trap,
// never a wrong value — and the interpreter as an assertion. Inside a body,
// a parameter or binding of a refined type carries the predicate as extent
// facts, so `table[i]` with `i: Small` and a 256-element table is proven.

// CodeRefinementShape reports a refinement declaration outside the shape:
// a base that is not a machine integer, a predicate that is not Bool.
const CodeRefinementShape = "OAK-T0602"

type refinementInfo struct {
	base      *PrimitiveType
	predicate ast.Expression
}

// checkRefinementType registers `Name: type = Base where pred`.
func (tc *TypeChecker) checkRefinementType(stmt *ast.ADTType) {
	if len(stmt.TypeParams) != 0 || len(stmt.Variants) != 1 || stmt.Variants[0].Payload == nil {
		tc.addTypeDiagnostic(stmt.Name, CodeRefinementShape,
			fmt.Sprintf("refinement %s: a refinement names one base type and no type parameters", stmt.Name.Value))
		return
	}
	baseType := tc.parseTypeExpression(stmt.Variants[0].Payload)
	base, isPrim := baseType.(*PrimitiveType)
	if !isPrim || !tc.isNumericType(base) || base.Refinement != "" {
		tc.addTypeDiagnostic(stmt.Name, CodeRefinementShape,
			fmt.Sprintf("refinement %s: the base must be a machine integer type, not %s", stmt.Name.Value, stmt.Variants[0].Payload.String()))
		return
	}
	// The predicate types with `value` at the base.
	predicateEnv := NewEnclosedTypeEnvironment(tc.env)
	predicateEnv.SetType("value", &PrimitiveType{Name: base.Name})
	outer := tc.env
	tc.env = predicateEnv
	predicateType := tc.checkExpression(stmt.Refinement, &BoolType{})
	tc.env = outer
	if predicateType == nil {
		return
	}
	if !predicateType.Equals(&BoolType{}) {
		tc.addTypeDiagnostic(stmt.Refinement, CodeRefinementShape,
			fmt.Sprintf("refinement %s: the predicate is %s, not Bool", stmt.Name.Value, predicateType.String()))
		return
	}
	if tc.refinements == nil {
		tc.refinements = map[string]*refinementInfo{}
	}
	tc.refinements[stmt.Name.Value] = &refinementInfo{base: &PrimitiveType{Name: base.Name}, predicate: stmt.Refinement}
	tc.env.SetType(stmt.Name.Value, &PrimitiveType{Name: base.Name, Refinement: stmt.Name.Value})
}

// checkRefinementConstruction types `Name(v)` for a refinement Name: the
// argument at the base type, the result refined, the call recorded for
// the backend's guard. Nil when name is not a refinement.
func (tc *TypeChecker) checkRefinementConstruction(name string, call *ast.InvocationExpression) Type {
	info, isRefinement := tc.refinements[name]
	if !isRefinement {
		return nil
	}
	if len(call.Arguments) != 1 {
		tc.addError(call, "refinement %s takes one value to check, got %d", name, len(call.Arguments))
		return nil
	}
	argType := tc.checkExpression(call.Arguments[0], info.base)
	if argType == nil {
		return nil
	}
	if !tc.isAssignable(argType, info.base) {
		if prim, isPrim := argType.(*PrimitiveType); !isPrim || prim.Refinement == "" || !tc.isAssignable(&PrimitiveType{Name: prim.Name}, info.base) {
			tc.addError(call.Arguments[0], "refinement %s checks a %s, got %s", name, info.base.Name, argType.String())
			return nil
		}
	}
	if tc.refinementChecks == nil {
		tc.refinementChecks = map[string]string{}
	}
	tc.refinementChecks[positionKey(call.Token)] = name
	// Static discharge: a predicate `value < K` (or `value <= K`) with a
	// literal K holds when the facts in scope prove the argument below the
	// bound — the same laws that prove an index; the guard is then never
	// emitted (Oak.Extents, the index laws).
	if bound, ok := predicateBound(info.predicate); ok && tc.provenBelow(call.Arguments[0], bound) {
		if tc.refinementDischarged == nil {
			tc.refinementDischarged = map[string]bool{}
		}
		tc.refinementDischarged[positionKey(call.Token)] = true
	}
	return &PrimitiveType{Name: info.base.Name, Refinement: name}
}

// predicateBound reads `value < K` or `value <= K` with a literal K as the
// exclusive bound K or K + 1.
func predicateBound(predicate ast.Expression) (int64, bool) {
	infix, isInfix := predicate.(*ast.InfixExpression)
	if !isInfix {
		return 0, false
	}
	left, isIdent := infix.Left.(*ast.Identifier)
	if !isIdent || left.Value != "value" {
		return 0, false
	}
	k, isConst := constantIndex(infix.Right)
	if !isConst || k < 0 {
		return 0, false
	}
	switch infix.Operator {
	case "<":
		return k, true
	case "<=":
		return k + 1, true
	}
	return 0, false
}

// RefinementDischarged reports whether the construction at tok was proven
// by the facts in scope, so the backend emits no guard.
func (tc *TypeChecker) RefinementDischarged(tok token.Token) bool {
	return tc.refinementDischarged[positionKey(tok)]
}

// Refinement reports a declared refinement: its base type name and predicate.
func (tc *TypeChecker) Refinement(name string) (string, ast.Expression, bool) {
	info, ok := tc.refinements[name]
	if !ok {
		return "", nil, false
	}
	return info.base.Name, info.predicate, true
}

// RefinedConstruction reports the refinement a call at tok constructs.
func (tc *TypeChecker) RefinedConstruction(tok token.Token) (string, bool) {
	name, ok := tc.refinementChecks[positionKey(tok)]
	return name, ok
}

// refinementFacts are the extent facts a binding of a refined type carries:
// the predicate with `value` read as the binding, through the same reader
// the loop guards use (typechecker/extents.go).
func (tc *TypeChecker) refinementFacts(binding string, typ Type) []extentFact {
	prim, isPrim := typ.(*PrimitiveType)
	if !isPrim || prim.Refinement == "" || !tc.localBinding(binding) {
		return nil
	}
	info, ok := tc.refinements[prim.Refinement]
	if !ok {
		return nil
	}
	predicate := substituteIdentifier(info.predicate, "value", binding)
	if predicate == nil {
		return nil
	}
	return tc.factsFromCondition(predicate)
}

// substituteIdentifier copies the expression forms a predicate may use,
// renaming one identifier; anything else yields nil (no facts, never a
// wrong one).
func substituteIdentifier(expr ast.Expression, from, to string) ast.Expression {
	switch e := expr.(type) {
	case *ast.Identifier:
		if e.Value == from {
			return &ast.Identifier{Token: e.Token, Value: to}
		}
		return &ast.Identifier{Token: e.Token, Value: e.Value}
	case *ast.IntegerLiteral:
		return e
	case *ast.Boolean:
		return e
	case *ast.PrefixExpression:
		right := substituteIdentifier(e.Right, from, to)
		if right == nil {
			return nil
		}
		return &ast.PrefixExpression{Token: e.Token, Operator: e.Operator, Right: right}
	case *ast.InfixExpression:
		left := substituteIdentifier(e.Left, from, to)
		right := substituteIdentifier(e.Right, from, to)
		if left == nil || right == nil {
			return nil
		}
		return &ast.InfixExpression{Token: e.Token, Left: left, Operator: e.Operator, Right: right}
	case *ast.InvocationExpression:
		fn, isIdent := e.Function.(*ast.Identifier)
		if !isIdent {
			return nil
		}
		args := make([]ast.Expression, len(e.Arguments))
		for i, arg := range e.Arguments {
			if args[i] = substituteIdentifier(arg, from, to); args[i] == nil {
				return nil
			}
		}
		return &ast.InvocationExpression{Token: e.Token, Function: &ast.Identifier{Token: fn.Token, Value: fn.Value}, Arguments: args}
	}
	return nil
}

// refinedBelow recognizes a construction `Name(e)` of a refinement whose
// predicate is `value < K` or `value <= K`, and returns the exclusive
// bound the constructed value satisfies.
func (tc *TypeChecker) refinedBelow(expr ast.Expression) (string, int64, bool) {
	call, isCall := expr.(*ast.InvocationExpression)
	if !isCall || len(call.Arguments) != 1 {
		return "", 0, false
	}
	// The index is proven before it is typed, so the construction is
	// recognized by its spelling: a call to a declared refinement's name,
	// which the checker types as nothing else.
	fn, isIdent := call.Function.(*ast.Identifier)
	if !isIdent {
		return "", 0, false
	}
	info, ok := tc.refinements[fn.Value]
	if !ok {
		return "", 0, false
	}
	name := fn.Value
	bound, ok := predicateBound(info.predicate)
	if !ok {
		return "", 0, false
	}
	return name, bound, true
}

// recordRefinedIndexProof proves `c[e]` when e has a refined type whose
// predicate bounds it below the container's static extent: the value was
// constructed through the guard, whatever expression produced it.
func (tc *TypeChecker) recordRefinedIndexProof(expr *ast.IndexExpression, arr *ArrayType, indexType Type) {
	prim, isPrim := indexType.(*PrimitiveType)
	if !isPrim || prim.Refinement == "" || arr == nil || arr.Length < 0 || arr.IsSlice || arr.IsSpan {
		return
	}
	info, ok := tc.refinements[prim.Refinement]
	if !ok {
		return
	}
	bound, ok := predicateBound(info.predicate)
	if !ok || bound > arr.Length {
		return
	}
	if tc.provenIndices == nil {
		tc.provenIndices = make(map[string]bool)
	}
	tc.provenIndices[positionKey(expr.Token)] = true
}

// RefinementConstructions counts the constructions the program makes: the
// ones whose guard stays (a runtime check) and the ones the facts in scope
// discharged.
func (tc *TypeChecker) RefinementConstructions() (guarded, discharged int) {
	for key := range tc.refinementChecks {
		if tc.refinementDischarged[key] {
			discharged++
		} else {
			guarded++
		}
	}
	return guarded, discharged
}

