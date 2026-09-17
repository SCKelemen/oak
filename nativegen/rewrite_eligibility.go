package nativegen

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// LoopRewriteEligibility is a search-planning summary of the source-level
// loop rewrites whose exact matchers can fire in one checked function. It is
// not proof authority: the rewrite, seam checker, and verifier still decide
// every candidate that reaches materialization.
type LoopRewriteEligibility struct {
	Reduction       bool
	VectorReduction bool
	VectorMap       bool
	VectorFold      bool
	Constant        bool
}

// AnalyzeLoopRewriteEligibility runs the loop rewrites' existing recognizers
// once, before candidate search. It inspects a private copy after the same
// helper expansion and span forwarding that precede the rewrites in
// computeStages, so the scan neither mutates the checked source nor loses a
// site exposed by native helper expansion.
func AnalyzeLoopRewriteEligibility(fn *ast.FunctionStatement, functions map[string]*ast.FunctionStatement, tc *typechecker.TypeChecker) LoopRewriteEligibility {
	if fn == nil || fn.Body == nil {
		return LoopRewriteEligibility{}
	}
	body := inlineBody(fn, functions)
	body = cloneNode(body).(ast.Expression)
	body, _ = forwardSingleUseSpans(body)
	block, isBlock := body.(*ast.BlockExpression)
	if !isBlock || block.Block == nil {
		return LoopRewriteEligibility{}
	}

	types := declaredScalarTypes(block.Block.Statements)
	spans := map[string]span{}
	for _, parameter := range fn.Parameters {
		if parameter == nil || parameter.Name == nil || parameter.Variadic {
			continue
		}
		if sp, ok := spanOf(parameter.Type); ok {
			if !sp.atomic {
				spans[parameter.Name.Value] = sp
			}
			continue
		}
		if _, declared := types[parameter.Name.Value]; !declared {
			if scalar, ok := scalarOf(parameter.Type); ok && !scalar.isVec {
				types[parameter.Name.Value] = parameter.Type
			}
		}
	}

	var found LoopRewriteEligibility
	var visit func([]ast.Statement, lengthClasses)
	visit = func(statements []ast.Statement, equal lengthClasses) {
		var previous ast.Statement
		for _, statement := range statements {
			switch current := statement.(type) {
			case *ast.WhileStatement:
				if reduction, ok := recognizeReduction(current, types, body); ok {
					found.Reduction = true
					if _, _, vector := vectorShapeFor(reduction.accType); vector && freshVectorNames(body, reduction.acc) {
						found.VectorReduction = true
					}
				}
				if _, ok := recognizeMap(current, previous, types, spans, equal, body, tc); ok {
					found.VectorMap = true
				}
				if _, ok := recognizeFold(current, previous, types, spans, equal, body); ok {
					found.VectorFold = true
				}
				if _, ok := recognizeConstantLoop(current, previous, body); ok {
					found.Constant = true
				}
				if current.Body != nil {
					visit(current.Body.Statements, equal)
				}
			case *ast.ExpressionStatement:
				if inner, ok := current.Expression.(*ast.BlockExpression); ok && inner.Block != nil {
					visit(inner.Block.Statements, equal)
				}
				if match, ok := current.Expression.(*ast.MatchExpression); ok {
					for _, arm := range match.Arms {
						if inner, ok := arm.Body.(*ast.BlockExpression); ok && inner.Block != nil {
							visit(inner.Block.Statements, armFacts(match, arm, equal))
						}
					}
				}
			case *ast.BlockStatement:
				visit(current.Statements, equal)
			}
			previous = statement
		}
	}
	visit(block.Block.Statements, nil)
	return found
}
