package compiler

import (
	"fmt"
	"reflect"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/opt"
	"github.com/SCKelemen/oak/typechecker"
)

// canonicalBooleanRounds bounds reconsideration after a child rewrite exposes
// a new parent rewrite. Every rule below removes at least one Bool operator, so
// the bound affects optimization completeness only, never termination or
// semantics.
const canonicalBooleanRounds = 8

type canonicalBooleanSummary struct {
	count int
	rules map[string]int
}

type canonicalBooleanPass struct {
	tc       *typechecker.TypeChecker
	function string
	changed  int
	summary  map[string]*canonicalBooleanSummary
}

// canonicalizeBooleans runs after generic specialization. Its identities
// retain every non-literal operand exactly once and return an expression node
// the first checker already typed: this first increment never deletes a call,
// trap, borrow, effect, or protocol obligation merely because short-circuit
// control would keep it from executing.
func canonicalizeBooleans(program *ast.Program, tc *typechecker.TypeChecker) []OptimizationDecision {
	if program == nil || tc == nil {
		return nil
	}
	pass := &canonicalBooleanPass{tc: tc, summary: map[string]*canonicalBooleanSummary{}}
	for round := 0; round < canonicalBooleanRounds; round++ {
		before := pass.changed
		for _, statement := range program.Statements {
			pass.function = "<package>"
			if function, ok := statement.(*ast.FunctionStatement); ok && function.Name != nil {
				pass.function = function.Name.Value
			}
			visitor := &syntaxVisitor{expr: pass.visit}
			visitor.walk(reflect.ValueOf(statement), false)
		}
		if pass.changed == before {
			break
		}
	}
	return pass.decisions()
}

func (pass *canonicalBooleanPass) visit(slot reflect.Value) {
	expression, ok := slot.Interface().(ast.Expression)
	if !ok || expression == nil {
		return
	}
	replacement, rule := pass.rewrite(expression)
	if replacement == nil || replacement == expression {
		return
	}
	slot.Set(reflect.ValueOf(ast.Expression(replacement)))
	pass.changed++
	summary := pass.summary[pass.function]
	if summary == nil {
		summary = &canonicalBooleanSummary{rules: map[string]int{}}
		pass.summary[pass.function] = summary
	}
	summary.count++
	summary.rules[rule]++
}

func (pass *canonicalBooleanPass) rewrite(expression ast.Expression) (ast.Expression, string) {
	switch value := expression.(type) {
	case *ast.PrefixExpression:
		if value.Operator != "!" || value.Right == nil {
			return nil, ""
		}
		if inner, ok := value.Right.(*ast.PrefixExpression); ok && inner.Operator == "!" && inner.Right != nil {
			return inner.Right, "double-not"
		}
	case *ast.InfixExpression:
		// A user-defined operator has the spelling of an infix expression but
		// the semantics of its declared function. Only built-in Bool operators
		// participate in these canonical laws.
		if _, custom := pass.tc.OperatorCallee(value.Token); custom {
			return nil, ""
		}
		left, leftLiteral := value.Left.(*ast.Boolean)
		right, rightLiteral := value.Right.(*ast.Boolean)
		switch value.Operator {
		case "&&":
			if leftLiteral && left.Value {
				return value.Right, "and-identity"
			}
			if rightLiteral && right.Value {
				return value.Left, "and-identity"
			}
		case "||":
			if leftLiteral && !left.Value {
				return value.Right, "or-identity"
			}
			if rightLiteral && !right.Value {
				return value.Left, "or-identity"
			}
		case "==", "!=":
			if rightLiteral {
				return canonicalBooleanComparison(value.Operator, value.Left, right.Value)
			}
			if leftLiteral {
				return canonicalBooleanComparison(value.Operator, value.Right, left.Value)
			}
		}
	}
	return nil, ""
}

// canonicalBooleanComparison rewrites operand == literal and operand !=
// literal only where the checked operand itself is the result. Negative
// literal forms would need a new ! node; they wait for OptIR value metadata.
func canonicalBooleanComparison(operator string, operand ast.Expression, literal bool) (ast.Expression, string) {
	identity := operator == "==" && literal || operator == "!=" && !literal
	if identity {
		return operand, "compare-bool"
	}
	return nil, ""
}

func (pass *canonicalBooleanPass) decisions() []OptimizationDecision {
	names := make([]string, 0, len(pass.summary))
	for name := range pass.summary {
		names = append(names, name)
	}
	sort.Strings(names)
	out := make([]OptimizationDecision, 0, len(names))
	for _, name := range names {
		summary := pass.summary[name]
		rules := make([]string, 0, len(summary.rules))
		for rule, count := range summary.rules {
			rules = append(rules, fmt.Sprintf("%s=%d", rule, count))
		}
		sort.Strings(rules)
		out = append(out, OptimizationDecision{
			Kind:      opt.Passed,
			Transform: OptimizationCanonicalBool,
			Function:  name,
			Message:   fmt.Sprintf("canonicalized %d boolean expression(s): %s; post-specialization program re-typechecked", summary.count, strings.Join(rules, ", ")),
			Facts: []string{
				"operands have checked Bool types",
				"each non-literal operand is retained exactly once",
			},
		})
	}
	return out
}
