package codegen

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// adtMatch is a read-only classification, shared by the dry run and emission.
// Resolution matters even when no arm mentions a variant (a catchall match).
// A variant without resolution still enters the checked, fail-closed path.
func adtMatch(match *ast.MatchExpression, tc *typechecker.TypeChecker) bool {
	if tc != nil {
		if _, resolved := tc.MatchResolution(match); resolved {
			return true
		}
	}
	for _, arm := range match.Arms {
		if arm == nil {
			continue
		}
		if _, variant := arm.Pattern.(*ast.VariantPattern); variant {
			return true
		}
	}
	return false
}

func checkedExpressionType(expr ast.Expression, tc *typechecker.TypeChecker) typechecker.Type {
	if tc == nil {
		return nil
	}
	if tok, positioned := ast.ExpressionToken(expr); positioned {
		if checked, ok := tc.ExpressionTypeAt(tok); ok {
			return checked
		}
	}
	if tc.Env() != nil {
		return tc.Env().CheckedExpressionType(expr)
	}
	return nil
}

// A temporary needs a value carrier, not void. Function values need a full C
// declarator, which the existing callable binding conversion already supplies.
func sequenceTypeExpression(checked typechecker.Type) (ast.Expression, bool) {
	if !supportedSequenceCarrier(checked, false) {
		return nil, false
	}
	return callableTypeExpression(checked)
}

// C declarators support a top-level function value, including a void return.
// The aggregate emitters use an element type prefix, so arrays/views/spans of
// functions or Unit are not representable by that storage path.
func supportedSequenceCarrier(checked typechecker.Type, allowUnit bool) bool {
	if _, ok := callableTypeExpression(checked); !ok {
		return false
	}
	switch typ := checked.(type) {
	case *typechecker.UnitType:
		return allowUnit
	case *typechecker.ArrayType:
		if _, callable := typ.ElementType.(*typechecker.FunctionType); callable {
			return false
		}
		return supportedSequenceCarrier(typ.ElementType, false)
	case *typechecker.FunctionType:
		if !supportedSequenceCarrier(typ.ReturnType, true) {
			return false
		}
		for _, parameter := range typ.Parameters {
			if !supportedSequenceCarrier(parameter, false) {
				return false
			}
		}
	}
	return true
}

func unsupportedPayloadStorage(typ ast.Expression) bool {
	switch typ := typ.(type) {
	case *ast.FunctionTypeExpression:
		return true
	case *ast.Identifier:
		return typ.Value == "()"
	case *ast.IndexExpression:
		return unsupportedPayloadStorage(typ.Left) || unsupportedPayloadStorage(typ.Index)
	}
	return false
}

// validateADTValueMatch checks only the flat patterns the existing guarded
// emitter implements. In particular it must not silently drop nested payload
// constraints. Type checking remains the authority for types and exhaustiveness;
// this check also makes missing backend metadata an error, not malformed C.
func (cg *CodeGenerator) validateADTValueMatch(match *ast.MatchExpression, tc *typechecker.TypeChecker) (string, error) {
	if tc == nil {
		return "", fmt.Errorf("codegen: ADT value match has no checked resolution")
	}
	name, resolved := tc.MatchResolution(match)
	adt := cg.adtTypes[name]
	if !resolved || adt == nil || len(match.Arms) == 0 {
		return "", fmt.Errorf("codegen: ADT value match has no registered checked resolution")
	}
	variants := make(map[string]*ast.ADTVariant, len(adt.Variants))
	for _, variant := range adt.Variants {
		// ADT storage and the shared payload emitter currently use a type
		// prefix, which cannot declare a function-pointer payload. Result
		// temporaries do support functions; payload storage is separate.
		if unsupportedPayloadStorage(variant.Payload) {
			return "", fmt.Errorf("codegen: callable or Unit ADT payload storage is unsupported in value matches")
		}
		variants[variant.Name.Value] = variant
	}
	covered := map[string]bool{}
	fallback := false
	for _, arm := range match.Arms {
		if arm == nil || arm.Body == nil {
			return "", fmt.Errorf("codegen: ADT value match has an empty arm")
		}
		switch pattern := arm.Pattern.(type) {
		case *ast.VariantPattern:
			if pattern.Variant == nil || variants[pattern.Variant.Value] == nil {
				return "", fmt.Errorf("codegen: ADT value match has an unknown variant")
			}
			variant := variants[pattern.Variant.Value]
			if pattern.Payload != nil && variant.Payload == nil {
				return "", fmt.Errorf("codegen: ADT value match binds a variant without a payload")
			}
			switch payload := pattern.Payload.(type) {
			case nil, *ast.WildcardPattern:
			case *ast.BindingPattern:
				if payload.Name == nil {
					return "", fmt.Errorf("codegen: ADT value match has an unnamed payload binding")
				}
			default:
				return "", fmt.Errorf("codegen: nested ADT value-match payload patterns are unsupported")
			}
			covered[pattern.Variant.Value] = true
		case *ast.WildcardPattern:
			fallback = true
		case *ast.BindingPattern:
			if pattern.Name == nil {
				return "", fmt.Errorf("codegen: ADT value match has an unnamed catchall binding")
			}
			fallback = true
		default:
			return "", fmt.Errorf("codegen: unsupported ADT value-match pattern")
		}
	}
	if !fallback && len(covered) != len(variants) {
		return "", fmt.Errorf("codegen: non-exhaustive ADT value match")
	}
	return name, nil
}

func (cg *CodeGenerator) hoistADTMatch(match *ast.MatchExpression, tc *typechecker.TypeChecker) ast.Expression {
	if _, err := cg.validateADTValueMatch(match, tc); err != nil {
		cg.globalErrors = append(cg.globalErrors, err)
		return &ast.Identifier{Token: match.Token, Value: "oak__invalid_match"}
	}
	if _, ok := sequenceTypeExpression(checkedExpressionType(match, tc)); !ok {
		cg.globalErrors = append(cg.globalErrors, fmt.Errorf("codegen: ADT value match has no supported checked C result carrier"))
		return &ast.Identifier{Token: match.Token, Value: "oak__invalid_match"}
	}
	// Validation above rules out the legacy typeof fallback for this path.
	return cg.hoistStatementForm(match, match, tc)
}

func (cg *CodeGenerator) assignADTMatch(result string, match *ast.MatchExpression, tc *typechecker.TypeChecker) {
	name, err := cg.validateADTValueMatch(match, tc)
	if err != nil {
		cg.globalErrors = append(cg.globalErrors, err)
		return
	}
	// Snapshot even a plain identifier: a catchall must evaluate its subject,
	// and a selected arm may mutate the original after binding its payload.
	subject := cg.sequence(match.Scrutinee, tc)
	tmp := fmt.Sprintf("oak__scrutinee_%d", cg.scrutineeCounter)
	cg.scrutineeCounter++
	typ := &ast.Identifier{Value: name}
	cg.write(fmt.Sprintf("  %s = ", cg.cParameter(typ, tmp)))
	cg.emitExpressionFragment(subject, tc)
	cg.output.WriteString(";\n")
	restore := cg.bindMatchContainer(tmp, typ)
	defer restore()
	copy := *match
	copy.Scrutinee = &ast.Identifier{Token: match.Token, Value: tmp}
	copy.Arms = make([]*ast.MatchArm, len(match.Arms))
	for i, arm := range match.Arms {
		cloned := *arm
		copy.Arms[i] = &cloned
		if binding, ok := arm.Pattern.(*ast.BindingPattern); ok && binding.Name.Value != "_" {
			// Introduce a whole-subject catchall binding inside this arm only.
			cloned.Body = &ast.BlockExpression{Block: &ast.BlockStatement{Statements: []ast.Statement{
				&ast.VariableDeclaration{Name: binding.Name, Type: typ, Value: copy.Scrutinee},
				&ast.ExpressionStatement{Expression: arm.Body},
			}}}
		}
		if pattern, ok := arm.Pattern.(*ast.VariantPattern); ok {
			if binding, ok := pattern.Payload.(*ast.BindingPattern); ok && binding.Name.Value == "_" {
				clonedPattern := *pattern
				clonedPattern.Payload = &ast.WildcardPattern{}
				cloned.Pattern = &clonedPattern
			}
		}
	}
	cg.emitMatchStatementBody(&copy, tc, func(body ast.Expression) { cg.assignTo(result, body, tc) })
}

// assignmentValueOperands copies only AST access paths. Owning storage remains
// in place; indices and borrowed span descriptors are values evaluated to reach
// it. Their slots precede the RHS in the same sequencing group.
func (cg *CodeGenerator) assignmentValueOperands(slot *ast.Expression, slots *[]*ast.Expression, tc *typechecker.TypeChecker) (map[*ast.Expression]func() *ast.IndexExpression, map[*ast.Expression]bool) {
	checks := map[*ast.Expression]func() *ast.IndexExpression{}
	descriptors := map[*ast.Expression]bool{}
	var path func(*ast.Expression, bool)
	path = func(slot *ast.Expression, reused bool) {
		info := cg.localContainerOf(*slot)
		if info.kind == containerUnknown {
			// A match/call may yield a borrowed descriptor before it has a
			// local name. Checked type metadata, not syntax, owns that fact.
			if typ, ok := checkedExpressionType(*slot, tc).(*typechecker.ArrayType); ok && typ.IsSpan {
				info.kind = containerSpan
			}
		}
		if info.kind == containerSpan {
			descriptors[slot] = reused
			*slots = append(*slots, slot)
			return
		}
		switch e := (*slot).(type) {
		case *ast.IndexExpression:
			copy := *e
			*slot = &copy
			path(&copy.Left, true)
			if !copy.Dot {
				*slots = append(*slots, &copy.Index)
				checks[&copy.Index] = func() *ast.IndexExpression { return &copy }
			}
		case *ast.InvocationExpression:
			if ident, ok := e.Function.(*ast.Identifier); ok && ident.Value == "core_index" && len(e.Arguments) == 2 {
				copy := *e
				copy.Arguments = append([]ast.Expression(nil), e.Arguments...)
				*slot = &copy
				path(&copy.Arguments[0], true)
				*slots = append(*slots, &copy.Arguments[1])
				checks[&copy.Arguments[1]] = func() *ast.IndexExpression {
					return &ast.IndexExpression{Token: copy.Token, Left: copy.Arguments[0], Index: copy.Arguments[1]}
				}
			}
		}
	}
	// The final element is the assignment destination, never a value copy.
	target := *(*slot).(*ast.IndexExpression)
	*slot = &target
	path(&target.Left, false)
	if !target.Dot {
		*slots = append(*slots, &target.Index)
	}
	return checks, descriptors
}

// Intermediate accesses belong to Target.Left and are evaluated before later
// address components and the RHS. The final store's own bounds check stays in
// the store emitter, after its operands, matching the evaluator's boundary.
func (cg *CodeGenerator) checkedAssignmentIndex(index *ast.IndexExpression, tc *typechecker.TypeChecker) ast.Expression {
	if tc != nil && tc.IndexProven(index.Token) {
		return index.Index
	}
	info := cg.localContainerOf(index.Left)
	if info.kind != containerOwnedArray && info.kind != containerSpan {
		cg.globalErrors = append(cg.globalErrors, fmt.Errorf("codegen: unsupported intermediate assignment address"))
		return index.Index
	}
	name := fmt.Sprintf("oak__seq_%d", cg.seqCounter)
	cg.seqCounter++
	if cg.localTypes == nil {
		cg.localTypes = map[string]localContainer{}
	}
	cg.localTypes[name] = localContainer{kind: containerUnknown}
	cg.write(fmt.Sprintf("  u64 %s = oak_lv_idx( (u64)( ", name))
	cg.emitExpressionFragment(index.Index, tc)
	cg.output.WriteString(" ), ")
	if info.kind == containerOwnedArray {
		cg.output.WriteString(fmt.Sprintf("%d", info.length))
	} else {
		cg.output.WriteString("(u64)( ")
		cg.emitExpressionFragment(index.Left, tc)
		cg.output.WriteString(" ).len")
	}
	cg.output.WriteString(" );\n")
	return &ast.Identifier{Token: tokenOf(index.Index), Value: name}
}
