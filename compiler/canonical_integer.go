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

const canonicalIntegerRounds = 8

type canonicalIntegerPass struct {
	tc       *typechecker.TypeChecker
	function string
	changed  int
	summary  map[string]*canonicalBooleanSummary
}

// canonicalizeIntegers removes fixed-width identity operators after generic
// specialization. Every replacement is the already-checked non-literal
// operand itself; identities that would erase or duplicate that operand are
// deliberately outside this transform.
func canonicalizeIntegers(program *ast.Program, tc *typechecker.TypeChecker) []OptimizationDecision {
	if program == nil || tc == nil {
		return nil
	}
	pass := &canonicalIntegerPass{tc: tc, summary: map[string]*canonicalBooleanSummary{}}
	for round := 0; round < canonicalIntegerRounds; round++ {
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

func (pass *canonicalIntegerPass) visit(slot reflect.Value) {
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

func (pass *canonicalIntegerPass) rewrite(expression ast.Expression) (ast.Expression, string) {
	infix, ok := expression.(*ast.InfixExpression)
	if !ok || infix.Left == nil || infix.Right == nil {
		return nil, ""
	}
	if _, custom := pass.tc.OperatorCallee(infix.Token); custom {
		return nil, ""
	}
	resultType, fixedWidth := pass.fixedWidthInteger(infix)
	if !fixedWidth {
		return nil, ""
	}
	leftZero := pass.integerConstant(infix.Left, 0)
	rightZero := pass.integerConstant(infix.Right, 0)
	leftOne := pass.integerConstant(infix.Left, 1)
	rightOne := pass.integerConstant(infix.Right, 1)
	switch infix.Operator {
	case "+":
		if rightZero {
			return pass.existingOperand(resultType, infix.Left, "add-zero")
		}
		if leftZero {
			return pass.existingOperand(resultType, infix.Right, "add-zero")
		}
	case "-":
		if rightZero {
			return pass.existingOperand(resultType, infix.Left, "sub-zero")
		}
	case "*":
		if rightOne {
			return pass.existingOperand(resultType, infix.Left, "mul-one")
		}
		if leftOne {
			return pass.existingOperand(resultType, infix.Right, "mul-one")
		}
	case "/":
		if rightOne {
			return pass.existingOperand(resultType, infix.Left, "div-one")
		}
	case "|":
		if rightZero {
			return pass.existingOperand(resultType, infix.Left, "or-zero")
		}
		if leftZero {
			return pass.existingOperand(resultType, infix.Right, "or-zero")
		}
	case "^":
		if rightZero {
			return pass.existingOperand(resultType, infix.Left, "xor-zero")
		}
		if leftZero {
			return pass.existingOperand(resultType, infix.Right, "xor-zero")
		}
	case "<<", ">>":
		if rightZero {
			return pass.existingOperand(resultType, infix.Left, "shift-zero")
		}
	}
	return nil, ""
}

func (pass *canonicalIntegerPass) fixedWidthInteger(infix *ast.InfixExpression) (string, bool) {
	if name, ok := pass.tc.ArithmeticType(infix.Token); ok {
		return name, len(name) > 1 && (name[0] == 'i' || name[0] == 'u')
	}
	typ, ok := pass.tc.ExpressionTypeAt(infix.Token)
	primitive, ok := typ.(*typechecker.PrimitiveType)
	if !ok {
		return "", false
	}
	name := pass.tc.FixedWidthName(primitive.Name)
	return name, name != ""
}

func (pass *canonicalIntegerPass) existingOperand(resultType string, operand ast.Expression, rule string) (ast.Expression, string) {
	tok, positioned := ast.ExpressionToken(operand)
	if !positioned {
		return nil, ""
	}
	typ, checked := pass.tc.ExpressionTypeAt(tok)
	primitive, integer := typ.(*typechecker.PrimitiveType)
	if !checked || !integer || pass.tc.FixedWidthName(primitive.Name) != resultType {
		return nil, ""
	}
	return operand, rule
}

func (pass *canonicalIntegerPass) integerConstant(expression ast.Expression, want int64) bool {
	switch value := expression.(type) {
	case *ast.IntegerLiteral:
		return value.Value == want
	case *ast.InvocationExpression:
		name, named := value.Function.(*ast.Identifier)
		if !named || pass.tc.FixedWidthName(name.Value) == "" || len(value.Arguments) != 1 {
			return false
		}
		literal, ok := value.Arguments[0].(*ast.IntegerLiteral)
		return ok && literal.Value == want
	}
	return false
}

func (pass *canonicalIntegerPass) decisions() []OptimizationDecision {
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
			Transform: OptimizationCanonicalInteger,
			Function:  name,
			Message:   fmt.Sprintf("canonicalized %d fixed-width integer expression(s): %s; post-specialization program re-typechecked", summary.count, strings.Join(rules, ", ")),
			Facts: []string{
				"operator and retained operand have the same checked fixed-width integer type",
				"the non-literal operand is retained exactly once",
			},
		})
	}
	return out
}
