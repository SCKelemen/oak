package compiler

import (
	"fmt"
	"strings"

	"github.com/SCKelemen/oak/ast"
)

// Invariant theorems in the model-checker module (docs/spec/112-protocols.md
// section 4, docs/spec/125-verification.md section 2a). A theorem whose
// parameters are exactly a protocol's projected state and data is an
// invariant candidate `oak prove` decides on the reachable states; when its
// body is in the invariant subset it is also stated in the TLA+ module as
// `Invariant_<name>` and listed in the configuration, so TLC checks the
// same statement. The subset: a Bool expression over the state (`s ==
// .Locked`), data paths, literals, conversions, arithmetic and comparisons
// — the guard subset — or the accumulator form of a bounded loop:
//
//	ok: Bool = e0
//	i: u32 = 0
//	while i < B (&& i < B')* { <nested loop | ok = ok && e>* ; i = i + u32(1) }
//	ok
//
// which is `e0 /\ (\A i \in 0..B-1 : (i < B') => e /\ ...)`: a literal bound
// is the domain when one is written, the others become guards. Anything
// else — a call, an `if`, a store — leaves the theorem to the prover.

// InvariantTheorems lists the theorems over decl's projected state and data,
// in program order.
func InvariantTheorems(program *ast.Program, decl *ast.ProtocolDeclaration) []*ast.FunctionStatement {
	if program == nil || decl == nil || decl.Name == nil {
		return nil
	}
	name := decl.Name.Value
	var theorems []*ast.FunctionStatement
	for _, stmt := range program.Statements {
		fn, isFn := stmt.(*ast.FunctionStatement)
		if !isFn || !fn.Theorem || fn.Name == nil || len(fn.Parameters) == 0 || len(fn.Parameters) > 2 {
			continue
		}
		state, isIdent := fn.Parameters[0].Type.(*ast.Identifier)
		if !isIdent || state.Value != name+"State" {
			continue
		}
		hasData := decl.Data != nil
		if hasData != (len(fn.Parameters) == 2) {
			continue
		}
		if hasData {
			data, isIdent := fn.Parameters[1].Type.(*ast.Identifier)
			if !isIdent || data.Value != name+"Data" {
				continue
			}
		}
		theorems = append(theorems, fn)
	}
	return theorems
}

// tlaInvariant translates an invariant theorem's body, or says why it is
// outside the subset.
func tlaInvariant(fn *ast.FunctionStatement, base *tlaEnv) (string, error) {
	env := base.with("", false)
	env.stateVar = fn.Parameters[0].Name.Value
	env.dataRoot = "\x00none"
	if len(fn.Parameters) == 2 {
		env.dataRoot = fn.Parameters[1].Name.Value
	}
	env.boundVars = map[string]bool{}
	statements, ok := theoremStatements(fn.Body)
	if !ok {
		return "", fmt.Errorf("the body is not a block")
	}
	return tlaInvariantBlock(statements, env)
}

// theoremStatements unwraps a theorem body to its statements.
func theoremStatements(body ast.Expression) ([]ast.Statement, bool) {
	switch b := body.(type) {
	case *ast.BlockExpression:
		if b.Block == nil {
			return nil, false
		}
		return b.Block.Statements, true
	case nil:
		return nil, false
	default:
		return []ast.Statement{&ast.ExpressionStatement{Expression: body}}, true
	}
}

// tlaInvariantBlock reads the accumulator form, or a single Bool expression.
func tlaInvariantBlock(statements []ast.Statement, env *tlaEnv) (string, error) {
	if len(statements) == 0 {
		return "", fmt.Errorf("an empty body")
	}
	if len(statements) == 1 {
		expr, isExpr := statements[0].(*ast.ExpressionStatement)
		if !isExpr {
			return "", fmt.Errorf("a body of one statement that is not an expression")
		}
		return tlaExpr(expr.Expression, env)
	}
	accumulator := ""
	var terms []string
	for i, stmt := range statements {
		last := i == len(statements)-1
		switch s := stmt.(type) {
		case *ast.VariableDeclaration:
			if last {
				return "", fmt.Errorf("a declaration in result position")
			}
			if typeName, isIdent := s.Type.(*ast.Identifier); isIdent && typeName.Value == "Bool" && accumulator == "" {
				if s.Value == nil {
					return "", fmt.Errorf("the accumulator %s has no initial value", s.Name.Value)
				}
				init, err := tlaExpr(s.Value, env)
				if err != nil {
					return "", err
				}
				accumulator = s.Name.Value
				terms = append(terms, init)
				continue
			}
			if isCounterDeclaration(s) {
				env.boundVars[s.Name.Value] = true
				continue
			}
			return "", fmt.Errorf("the declaration of %s is neither the Bool accumulator nor a loop counter from 0", s.Name.Value)
		case *ast.WhileStatement:
			if last {
				return "", fmt.Errorf("a loop in result position")
			}
			if accumulator == "" {
				return "", fmt.Errorf("a loop before the Bool accumulator")
			}
			term, err := tlaInvariantLoop(s, accumulator, env)
			if err != nil {
				return "", err
			}
			terms = append(terms, term)
		case *ast.ExpressionStatement:
			if !last {
				return "", fmt.Errorf("an expression statement before the result")
			}
			result, isIdent := s.Expression.(*ast.Identifier)
			if !isIdent || result.Value != accumulator {
				return "", fmt.Errorf("the result is not the accumulator %s", accumulator)
			}
		default:
			return "", fmt.Errorf("a %T statement", stmt)
		}
	}
	if accumulator == "" {
		return "", fmt.Errorf("no Bool accumulator")
	}
	return strings.Join(terms, " /\\ "), nil
}

// isCounterDeclaration recognizes `i: u32 = 0` (or `u32(0)`).
func isCounterDeclaration(s *ast.VariableDeclaration) bool {
	typeName, isIdent := s.Type.(*ast.Identifier)
	if !isIdent || !conversionNames[typeName.Value] || s.Value == nil {
		return false
	}
	value := s.Value
	if call, isCall := value.(*ast.InvocationExpression); isCall && len(call.Arguments) == 1 {
		if fn, ok := call.Function.(*ast.Identifier); ok && conversionNames[fn.Value] {
			value = call.Arguments[0]
		}
	}
	lit, isLit := value.(*ast.IntegerLiteral)
	return isLit && lit.Value == 0
}

// tlaInvariantLoop translates `while i < B && i < B' { ... i = i + 1 }` over
// a declared counter into a bounded universal quantifier.
func tlaInvariantLoop(loop *ast.WhileStatement, accumulator string, env *tlaEnv) (string, error) {
	var bounds []ast.Expression
	counter := ""
	for _, term := range splitConjunction(loop.Condition) {
		infix, isInfix := term.(*ast.InfixExpression)
		if !isInfix || infix.Operator != "<" {
			return "", fmt.Errorf("a loop condition that is not `counter < bound`")
		}
		id, isIdent := infix.Left.(*ast.Identifier)
		if !isIdent || !env.boundVars[id.Value] || (counter != "" && counter != id.Value) {
			return "", fmt.Errorf("a loop condition over %s, which is not the loop's counter", infix.Left.String())
		}
		counter = id.Value
		bounds = append(bounds, infix.Right)
	}
	if counter == "" {
		return "", fmt.Errorf("a loop without a counter bound")
	}
	// A literal bound is the domain; every other bound guards the body.
	domainIndex := 0
	for i, bound := range bounds {
		if _, isLit := stripConversions(bound).(*ast.IntegerLiteral); isLit {
			domainIndex = i
			break
		}
	}
	var guards []string
	domain := ""
	for i, bound := range bounds {
		text, err := tlaExpr(bound, env)
		if err != nil {
			return "", err
		}
		if i == domainIndex {
			if _, isLit := stripConversions(bound).(*ast.IntegerLiteral); isLit {
				domain = fmt.Sprintf("0..%d", stripConversions(bound).(*ast.IntegerLiteral).Value-1)
			} else {
				domain = fmt.Sprintf("0..(%s - 1)", text)
			}
			continue
		}
		guards = append(guards, fmt.Sprintf("(%s < %s)", counter, text))
	}
	var body []string
	incremented := false
	for _, stmt := range loop.Body.Statements {
		switch s := stmt.(type) {
		case *ast.VariableDeclaration:
			if !isCounterDeclaration(s) {
				return "", fmt.Errorf("the declaration of %s inside a loop is not a counter from 0", s.Name.Value)
			}
			env.boundVars[s.Name.Value] = true
		case *ast.WhileStatement:
			term, err := tlaInvariantLoop(s, accumulator, env)
			if err != nil {
				return "", err
			}
			body = append(body, term)
		case *ast.AssignmentStatement:
			if s.Name.Value == counter {
				if !isIncrement(s.Value, counter) {
					return "", fmt.Errorf("the counter %s is not incremented by one", counter)
				}
				incremented = true
				continue
			}
			if s.Name.Value != accumulator {
				return "", fmt.Errorf("an assignment to %s, neither the accumulator nor the counter", s.Name.Value)
			}
			infix, isInfix := s.Value.(*ast.InfixExpression)
			left, leftIsIdent := infix.Left.(*ast.Identifier)
			if !isInfix || infix.Operator != "&&" || !leftIsIdent || left.Value != accumulator {
				return "", fmt.Errorf("the accumulator is updated other than by `%s = %s && e`", accumulator, accumulator)
			}
			term, err := tlaExpr(infix.Right, env)
			if err != nil {
				return "", err
			}
			body = append(body, term)
		default:
			return "", fmt.Errorf("a %T statement inside a loop", stmt)
		}
	}
	if !incremented {
		return "", fmt.Errorf("the loop over %s does not increment it", counter)
	}
	if len(body) == 0 {
		return "", fmt.Errorf("the loop over %s accumulates nothing", counter)
	}
	inner := strings.Join(body, " /\\ ")
	if len(body) > 1 {
		inner = "(" + inner + ")"
	}
	if len(guards) > 0 {
		inner = fmt.Sprintf("%s => %s", strings.Join(guards, " /\\ "), inner)
	}
	return fmt.Sprintf("(\\A %s \\in %s : %s)", counter, domain, inner), nil
}

// splitConjunction flattens `a && b && c`.
func splitConjunction(expr ast.Expression) []ast.Expression {
	if infix, isInfix := expr.(*ast.InfixExpression); isInfix && infix.Operator == "&&" {
		return append(splitConjunction(infix.Left), splitConjunction(infix.Right)...)
	}
	return []ast.Expression{expr}
}

// stripConversions removes width conversions around an expression.
func stripConversions(expr ast.Expression) ast.Expression {
	for {
		call, isCall := expr.(*ast.InvocationExpression)
		if !isCall || len(call.Arguments) != 1 {
			return expr
		}
		fn, ok := call.Function.(*ast.Identifier)
		if !ok || !conversionNames[fn.Value] {
			return expr
		}
		expr = call.Arguments[0]
	}
}

// isIncrement recognizes `i + 1` (or `i + u32(1)`).
func isIncrement(expr ast.Expression, counter string) bool {
	infix, isInfix := expr.(*ast.InfixExpression)
	if !isInfix || infix.Operator != "+" {
		return false
	}
	left, isIdent := infix.Left.(*ast.Identifier)
	lit, isLit := stripConversions(infix.Right).(*ast.IntegerLiteral)
	return isIdent && left.Value == counter && isLit && lit.Value == 1
}
