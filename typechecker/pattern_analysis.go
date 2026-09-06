package typechecker

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/object"
)

// PatternRefinement is one fact learned by entering a reachable match arm.
// Today the compiler materializes constructor refinements as narrowed ADT types;
// future GADT result-index equalities plug into this same arm-fact channel.
type TypeIndexEquality struct {
	Parameter string
	Type      string
}

type PatternRefinement struct {
	Subject     string
	Constructor string
	Equalities  []TypeIndexEquality
}

type MatchArmAnalysis struct {
	Reachable   bool
	Redundant   bool
	Impossible  bool
	Reason      string
	Refinements []PatternRefinement
}

type MatchAnalysis struct {
	Arms     []MatchArmAnalysis
	Missing  []string
	Reliable bool
}

type coverageNode struct {
	typ          Type
	full         bool
	constructors map[string]*coverageNode
	literals     map[string]bool
}

func newCoverageNode(typ Type) *coverageNode {
	return &coverageNode{
		typ:          typ,
		constructors: make(map[string]*coverageNode),
		literals:     make(map[string]bool),
	}
}

func cloneCoverageNode(node *coverageNode) *coverageNode {
	if node == nil {
		return nil
	}
	clone := newCoverageNode(node.typ)
	clone.full = node.full
	for name, child := range node.constructors {
		clone.constructors[name] = cloneCoverageNode(child)
	}
	for literal, covered := range node.literals {
		clone.literals[literal] = covered
	}
	return clone
}

func (tc *TypeChecker) adtNameForCoverage(typ Type) (string, string, bool) {
	name, onlyVariant, _, ok := adtInstantiation(typ)
	return name, onlyVariant, ok
}

func (tc *TypeChecker) findADTVariant(adtName, variantName string) (*object.ADTVariantDef, bool) {
	adt, ok := tc.adtTypes[adtName]
	if !ok {
		return nil, false
	}
	for _, variant := range adt.Variants {
		if variant.Name == variantName {
			return variant, true
		}
	}
	return nil, false
}

func (tc *TypeChecker) variantPayloadType(parent Type, variant *object.ADTVariantDef) Type {
	if variant == nil || variant.Payload == "" {
		return &UnitType{}
	}
	adtName, _, args, ok := adtInstantiation(parent)
	if !ok {
		return nil
	}
	bindings, reachable := tc.variantIndexBindings(tc.adtTypes[adtName], variant, args)
	if !reachable {
		return nil
	}
	return tc.instantiateStoredType(variant.Payload, bindings)
}

func literalMatchesCoverageType(typ Type, expr ast.Expression) bool {
	switch typ.(type) {
	case *BoolType:
		_, ok := expr.(*ast.Boolean)
		return ok
	case *StringType:
		_, ok := expr.(*ast.StringLiteral)
		return ok
	case *PrimitiveType:
		_, ok := expr.(*ast.IntegerLiteral)
		return ok
	default:
		return false
	}
}

// applyCoverage applies one pattern to a cloned coverage tree.
// valid=false means ordinary pattern checking owns the diagnostic and no
// coverage conclusion should be drawn from the malformed pattern.
// possible=false means the pattern is well-formed but impossible under the
// scrutinee's current refinement.
func (tc *TypeChecker) applyCoverage(node *coverageNode, pattern ast.Pattern) (changed, possible, valid bool) {
	if node == nil || pattern == nil {
		return false, true, false
	}
	if node.full {
		return false, true, true
	}

	switch p := pattern.(type) {
	case *ast.WildcardPattern, *ast.BindingPattern:
		node.full = true
		return true, true, true

	case *ast.LiteralPattern:
		if _, _, isADT := tc.adtNameForCoverage(node.typ); isADT {
			return false, true, false
		}
		if !literalMatchesCoverageType(node.typ, p.Value) {
			return false, true, false
		}
		key, ok := patternLiteralKey(p.Value)
		if !ok {
			return false, true, false
		}
		if node.literals[key] {
			return false, true, true
		}
		node.literals[key] = true
		return true, true, true

	case *ast.VariantPattern:
		adtName, onlyVariant, ok := tc.adtNameForCoverage(node.typ)
		if !ok {
			return false, true, false
		}
		if p.TypeName != nil && p.TypeName.Value != adtName {
			return false, true, false
		}
		variant, exists := tc.findADTVariant(adtName, p.Variant.Value)
		if !exists {
			return false, true, false
		}
		if onlyVariant != "" && variant.Name != onlyVariant {
			return false, false, true
		}
		if !tc.variantReachable(node.typ, adtName, variant) {
			return false, false, true
		}

		hasPayload := variant.Payload != ""
		if hasPayload != (p.Payload != nil) {
			return false, true, false
		}

		child, exists := node.constructors[variant.Name]
		if !exists {
			payloadType := tc.variantPayloadType(node.typ, variant)
			if payloadType == nil {
				return false, true, false
			}
			child = newCoverageNode(payloadType)
			node.constructors[variant.Name] = child
		}
		if !hasPayload {
			if child.full {
				return false, true, true
			}
			child.full = true
			return true, true, true
		}
		return tc.applyCoverage(child, p.Payload)
	default:
		return false, true, false
	}
}

func patternLiteralKey(expr ast.Expression) (string, bool) {
	switch value := expr.(type) {
	case *ast.Boolean:
		if value.Value {
			return "bool:true", true
		}
		return "bool:false", true
	case *ast.IntegerLiteral:
		return fmt.Sprintf("int:%d", value.Value), true
	case *ast.StringLiteral:
		return "string:" + value.Value, true
	default:
		return "", false
	}
}

func (tc *TypeChecker) coverageComplete(node *coverageNode) bool {
	if node == nil {
		return false
	}
	if node.full {
		return true
	}
	if _, ok := node.typ.(*BoolType); ok {
		return node.literals["bool:true"] && node.literals["bool:false"]
	}

	adtName, onlyVariant, ok := tc.adtNameForCoverage(node.typ)
	if !ok {
		// Integers, strings, and other open domains require a catch-all.
		return false
	}
	adt, ok := tc.adtTypes[adtName]
	if !ok {
		return false
	}
	for _, variant := range adt.Variants {
		if onlyVariant != "" && variant.Name != onlyVariant {
			continue
		}
		if !tc.variantReachable(node.typ, adtName, variant) {
			continue
		}
		child, covered := node.constructors[variant.Name]
		if !covered || !tc.coverageComplete(child) {
			return false
		}
	}
	// No reachable constructors is the empty semantic case space. Coverage is
	// vacuously complete, which is required for impossible GADT index states.
	return true
}

func (tc *TypeChecker) coverageWitnesses(node *coverageNode, limit int) []string {
	if node == nil || limit <= 0 || tc.coverageComplete(node) {
		return nil
	}
	if _, ok := node.typ.(*BoolType); ok {
		witnesses := []string{}
		if !node.literals["bool:false"] {
			witnesses = append(witnesses, "false")
		}
		if len(witnesses) < limit && !node.literals["bool:true"] {
			witnesses = append(witnesses, "true")
		}
		return witnesses
	}

	adtName, onlyVariant, ok := tc.adtNameForCoverage(node.typ)
	if !ok {
		return []string{"_"}
	}
	adt, ok := tc.adtTypes[adtName]
	if !ok {
		return []string{"_"}
	}

	witnesses := []string{}
	for _, variant := range adt.Variants {
		if len(witnesses) >= limit {
			break
		}
		if onlyVariant != "" && variant.Name != onlyVariant {
			continue
		}
		if !tc.variantReachable(node.typ, adtName, variant) {
			continue
		}
		child, covered := node.constructors[variant.Name]
		if !covered {
			if variant.Payload == "" {
				witnesses = append(witnesses, "."+variant.Name)
			} else {
				witnesses = append(witnesses, "."+variant.Name+"(_)")
			}
			continue
		}
		if tc.coverageComplete(child) {
			continue
		}
		for _, payload := range tc.coverageWitnesses(child, limit-len(witnesses)) {
			witnesses = append(witnesses, "."+variant.Name+"("+payload+")")
			if len(witnesses) >= limit {
				break
			}
		}
	}
	return witnesses
}

func (tc *TypeChecker) constructorRefinement(subject string, pattern ast.Pattern, scrutinee Type) []PatternRefinement {
	patternVariant, ok := pattern.(*ast.VariantPattern)
	if !ok || subject == "" {
		return nil
	}
	refinement := PatternRefinement{Subject: subject, Constructor: patternVariant.Variant.Value}
	adtName, _, args, isADT := adtInstantiation(scrutinee)
	if !isADT {
		return []PatternRefinement{refinement}
	}
	adt := tc.adtTypes[adtName]
	variant, found := tc.findADTVariant(adtName, patternVariant.Variant.Value)
	if !found {
		return []PatternRefinement{refinement}
	}
	bindings, reachable := tc.variantIndexBindings(adt, variant, args)
	if !reachable {
		return []PatternRefinement{refinement}
	}
	for _, parameter := range adt.TypeParams {
		if bound, exists := bindings[parameter]; exists {
			refinement.Equalities = append(refinement.Equalities, TypeIndexEquality{
				Parameter: parameter,
				Type:      bound.String(),
			})
		}
	}
	return []PatternRefinement{refinement}
}

func (tc *TypeChecker) analyzeMatch(expr *ast.MatchExpression, scrutineeType Type) MatchAnalysis {
	analysis := MatchAnalysis{
		Arms:     make([]MatchArmAnalysis, len(expr.Arms)),
		Reliable: true,
	}
	coverage := newCoverageNode(scrutineeType)
	subject := ""
	if ident, ok := expr.Scrutinee.(*ast.Identifier); ok {
		subject = ident.Value
	}

	for i, arm := range expr.Arms {
		candidate := cloneCoverageNode(coverage)
		changed, possible, valid := tc.applyCoverage(candidate, arm.Pattern)
		state := MatchArmAnalysis{
			Reachable:   true,
			Refinements: tc.constructorRefinement(subject, arm.Pattern, scrutineeType),
		}
		switch {
		case !valid:
			// Pattern checking will report the root error. Coverage is no longer
			// reliable enough to emit a derivative non-exhaustive diagnostic.
			analysis.Reliable = false
		case !possible:
			state.Reachable = false
			state.Impossible = true
			if narrowed, ok := scrutineeType.(*NarrowedADTVariantType); ok {
				state.Reason = fmt.Sprintf("%s is already refined to .%s", narrowed.ADTName, narrowed.VariantName)
			} else {
				state.Reason = "the current refinement makes this pattern impossible"
			}
		case !changed:
			state.Reachable = false
			state.Redundant = true
			state.Reason = "earlier arms already cover every value matched by this pattern"
		default:
			coverage = candidate
		}
		analysis.Arms[i] = state
	}

	if analysis.Reliable {
		analysis.Missing = tc.coverageWitnesses(coverage, 4)
	}
	return analysis
}

func (tc *TypeChecker) emitMatchAnalysisDiagnostics(expr *ast.MatchExpression, analysis MatchAnalysis) {
	for i, state := range analysis.Arms {
		if state.Reachable || i >= len(expr.Arms) {
			continue
		}
		arm := expr.Arms[i]
		if state.Impossible {
			d := tc.addTypeWarning(arm.Pattern, CodeMatchImpossibleArm, "match arm is unreachable under the current refinement")
			d.Tags = append(d.Tags, diagnostic.TagUnnecessary)
			d.AddNote(state.Reason)
			d.AddHelp("remove the impossible arm; the compiler already knows this constructor cannot occur here")
			continue
		}
		if state.Redundant {
			d := tc.addTypeWarning(arm.Pattern, CodeMatchRedundantArm, "match arm is redundant")
			d.Tags = append(d.Tags, diagnostic.TagUnnecessary)
			d.AddNote(state.Reason)
			d.AddHelp("remove the redundant arm or move a more specific pattern before the arm that subsumes it")
		}
	}

	if !analysis.Reliable || len(analysis.Missing) == 0 {
		return
	}
	d := tc.addTypeDiagnostic(expr, CodeMatchNonExhaustive, "match is not exhaustive")
	missing := append([]string(nil), analysis.Missing...)
	for _, witness := range missing {
		d.AddNote("uncovered case: " + witness)
	}
	d.Data = map[string]interface{}{"counterexamples": missing}
	d.AddHelp("add an arm covering the missing case, or add a wildcard/binding arm when a catch-all is intentional")
}
