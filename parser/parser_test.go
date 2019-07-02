package parser

import (
	"fmt"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/scanner"
)

func TestTypeDeclarationStatements(t *testing.T) {
	input := `
	type ReaderWriterCloser 
		= Reader
		& Writer
		& Closer;

	type ReaderWriter
		= Reader
		& Writer;
	`

	lxr := scanner.New(input)
	p := New(lxr)

	program := p.ParseProgram()
	errors := p.Errors()
	if len(errors) != 0 {
		t.Errorf("parser had %d errors", len(errors))
		for _, msg := range errors {
			t.Errorf("parser error: %q", msg)
		}
		t.FailNow()
	}

	if program == nil {
		t.Fatalf("ParseProgram() return nil, which isn't ideal.")
	}
	if len(program.Statements) != 2 {
		t.Fatalf("program doesn't have the correct number of statements. Expected 2, received %d", len(program.Statements))
	}

	tests := []struct {
		expectedIdentifier string
	}{
		{"ReaderWriterCloser"},
		{"ReaderWriter"},
	}

	for i, tt := range tests {
		stmt := program.Statements[i]
		if stmt.TokenLiteral() != "type" {
			t.Errorf("s.TokenLiteral not 'type', received %q", stmt.TokenLiteral())
			return
		}

		typeDeclaration, ok := stmt.(*ast.TypeDeclarationStatement)
		if !ok {
			t.Errorf("statement not of type *ast.TypeDeclarationStatement, received %T", stmt)
			return
		}

		if typeDeclaration.Name.Value != tt.expectedIdentifier {
			t.Errorf("statement.Name.Value not '%s', received %s", tt.expectedIdentifier, typeDeclaration.Name.Value)
			return
		}

		if typeDeclaration.Name.TokenLiteral() != tt.expectedIdentifier {
			t.Errorf("statement.Name.TokenLiteral() not '%s', received %s", tt.expectedIdentifier, typeDeclaration.Name.TokenLiteral())
			return
		}

	}
}

func TestReturnStatements(t *testing.T) {
	tests := []struct {
		input       string
		expectedId  string
		expectedVal interface{}
	}{
		{"return x = 5;", "x", 5},
		{"return y = true;", "y", true},
		{"return foobar == y;", "foobar", "y"},
	}

	for _, tt := range tests {

		lxr := scanner.New(tt.input)
		p := New(lxr)

		program := p.ParseProgram()
		errors := p.Errors()
		if len(errors) != 0 {
			t.Errorf("parser had %d errors", len(errors))
			for _, msg := range errors {
				t.Errorf("parser error: %q", msg)
			}
			t.FailNow()
		}

		if len(program.Statements) != 1 {
			t.Fatalf("program doesn't have the correct number of statements. Expected 1, received %d", len(program.Statements))
		}

		stmt := program.Statements[0]
		returnStmt, ok := stmt.(*ast.ReturnStatement)
		if !ok {
			t.Fatalf("stmt not of type *ast.ReturnStatement, received %T", stmt)
		}

		if returnStmt.TokenLiteral() != "return" {
			t.Fatalf("returnStmt.TokenLiteral not 'return', received %q", returnStmt.TokenLiteral())
		}

		if !testLiteralExpression(t, returnStmt.ReturnValue, tt.expectedVal) {
			return
		}

	}

}

func TestIdentifierExpression(t *testing.T) {
	input := "foobar;"

	lxr := scanner.New(input)
	p := New(lxr)

	program := p.ParseProgram()
	errors := p.Errors()
	if len(errors) != 0 {
		t.Errorf("parser had %d errors", len(errors))
		for _, msg := range errors {
			t.Errorf("parser error: %q", msg)
		}
		t.FailNow()
	}

	if len(program.Statements) != 1 {
		t.Fatalf("Program has an unexpected number of statements. Expected 1, received %d", len(program.Statements))
	}

	stmt, ok := program.Statements[0].(*ast.ExpressionStatement)
	if !ok {
		t.Fatalf("program.Statements[0]  is not *ast.ExpressionStatement. Received %T", program.Statements[0])
	}

	ident, ok := stmt.Expression.(*ast.Identifier)
	if !ok {
		t.Fatalf("expression not of type *ast.Identifier, received %T", stmt.Expression)
	}

	if ident.Value != "foobar" {
		t.Errorf("ident.Value not %s, received %s", "foobar", ident.Value)
	}

	if ident.TokenLiteral() != "foobar" {
		t.Errorf("ident.TokenLiteral not %s, received %s", "foobar", ident.TokenLiteral())
	}
}

func TestIntegerLiteralExpression(t *testing.T) {
	input := "5;"

	lxr := scanner.New(input)
	p := New(lxr)

	program := p.ParseProgram()
	errors := p.Errors()
	if len(errors) != 0 {
		t.Errorf("parser had %d errors", len(errors))
		for _, msg := range errors {
			t.Errorf("parser error: %q", msg)
		}
		t.FailNow()
	}

	if len(program.Statements) != 1 {
		t.Fatalf("Program has an unexpected number of statements. Expected 1, received %d", len(program.Statements))
	}

	stmt, ok := program.Statements[0].(*ast.ExpressionStatement)
	if !ok {
		t.Fatalf("program.Statements[0]  is not of type *ast.ExpressionStatement, received %T", program.Statements[0])
	}

	literal, ok := stmt.Expression.(*ast.IntegerLiteral)
	if !ok {
		t.Fatalf("expression not of type *ast.IntegerLiteral, received %T", stmt.Expression)
	}

	if literal.Value != 5 {
		t.Errorf("literal.Value not %d, received %d", 5, literal.Value)
	}

	if literal.TokenLiteral() != "5" {
		t.Errorf("literal.TokenLiteral not %s, received %s", "5", literal.TokenLiteral())
	}

}

func TestFunctionLiteral(t *testing.T) {
	input := `func(x, y) { x + y; }`

	lxr := scanner.New(input)
	p := New(lxr)
	program := p.ParseProgram()
	errors := p.Errors()
	if len(errors) != 0 {
		t.Errorf("parser had %d errors", len(errors))
		for _, msg := range errors {
			t.Errorf("parser error: %q", msg)
		}
		t.FailNow()
	}

	if len(program.Statements) != 1 {
		t.Fatalf("Program has an unexpected number of statements. Expected 1, received %d", len(program.Statements))
	}

	stmt, ok := program.Statements[0].(*ast.ExpressionStatement)
	if !ok {
		t.Fatalf("program.Statements[0]  is not of type *ast.ExpressionStatement, received %T", program.Statements[0])
	}

	literal, ok := stmt.Expression.(*ast.FunctionLiteral)
	if !ok {
		t.Fatalf("expression not of type *ast.FunctionLiteral, received %T", stmt.Expression)
	}

	// arity check
	if len(literal.Arguments) != 2 {
		t.Fatalf("Function literal arguments list does not match arity of 2, received %d\n", len(literal.Arguments))
	}

	testLiteralExpression(t, literal.Arguments[0], "x")
	testLiteralExpression(t, literal.Arguments[1], "y")

	if len(literal.Body.Statements) != 1 {
		t.Fatalf("Function literal does not have 1 statement, received %d\n", len(literal.Body.Statements))
	}

	bStmt, ok := literal.Body.Statements[0].(*ast.ExpressionStatement)
	if !ok {
		t.Fatalf("function body stmt is not of type ast.ExpressionStatement, received %T", literal.Body.Statements[0])
	}

	testInfixExpression(t, bStmt.Expression, "x", "+", "y")
}

func TestFunctionArguments(t *testing.T) {
	tests := []struct {
		input    string
		expected []string
	}{
		{input: "func() {};", expected: []string{}},
		{input: "func(x) {};", expected: []string{"x"}},
		{input: "func(x, y, z) {};", expected: []string{"x", "y", "z"}},
	}

	for _, tt := range tests {
		lxr := scanner.New(tt.input)
		p := New(lxr)
		program := p.ParseProgram()
		errors := p.Errors()
		if len(errors) != 0 {
			t.Errorf("parser had %d errors", len(errors))
			for _, msg := range errors {
				t.Errorf("parser error: %q", msg)
			}
			t.FailNow()
		}

		stmt := program.Statements[0].(*ast.ExpressionStatement)
		function := stmt.Expression.(*ast.FunctionLiteral)

		if len(function.Arguments) != len(tt.expected) {
			t.Errorf("Incorrect argument arity. Expected %d, received %d\n", len(tt.expected), len(function.Arguments))
		}

		for i, id := range tt.expected {
			testLiteralExpression(t, function.Arguments[i], id)
		}
	}
}

func TestInvocationExpression(t *testing.T) {
	input := "add(1, 2 * 3, 4 + 5);"

	lxr := scanner.New(input)
	p := New(lxr)
	program := p.ParseProgram()
	errors := p.Errors()
	if len(errors) != 0 {
		t.Errorf("parser had %d errors", len(errors))
		for _, msg := range errors {
			t.Errorf("parser error: %q", msg)
		}
		t.FailNow()
	}

	if len(program.Statements) != 1 {
		t.Fatalf("program.Statements does not contain %d statements, received %d\n",
			1, len(program.Statements))
	}

	stmt, ok := program.Statements[0].(*ast.ExpressionStatement)
	if !ok {
		t.Fatalf("program.Statements[0] is not of type ast.ExpressionStatement, received %T",
			program.Statements[0])
	}

	expr, ok := stmt.Expression.(*ast.InvocationExpression)
	if !ok {
		t.Fatalf("expression not of type *ast.InvocationExpression, received %T", stmt.Expression)
	}

	if !testIdentifier(t, expr.Function, "add") {
		return
	}

	if len(expr.Arguments) != 3 {
		t.Fatalf("Unexpected length of arguments. Expected 3, received %d", len(expr.Arguments))
	}

	testLiteralExpression(t, expr.Arguments[0], 1)
	testInfixExpression(t, expr.Arguments[1], 2, "*", 3)
	testInfixExpression(t, expr.Arguments[2], 4, "+", 5)

}

func TestInvocationExpressionArguments(t *testing.T) {
	tests := []struct {
		input         string
		expectedIdent string
		expectedArgs  []string
	}{
		{
			input:         "add();",
			expectedIdent: "add",
			expectedArgs:  []string{},
		},
		{
			input:         "add(1);",
			expectedIdent: "add",
			expectedArgs:  []string{"1"},
		},
		{
			input:         "add(1, 2 * 3, 4 + 5);",
			expectedIdent: "add",
			expectedArgs:  []string{"1", "(2 * 3)", "(4 + 5)"},
		},
	}

	for _, tt := range tests {
		lxr := scanner.New(tt.input)
		p := New(lxr)
		program := p.ParseProgram()
		errors := p.Errors()
		if len(errors) != 0 {
			t.Errorf("parser had %d errors", len(errors))
			for _, msg := range errors {
				t.Errorf("parser error: %q", msg)
			}
			t.FailNow()
		}

		stmt := program.Statements[0].(*ast.ExpressionStatement)
		exp, ok := stmt.Expression.(*ast.InvocationExpression)
		if !ok {
			t.Fatalf("stmt.Expression is not of type ast.InvocationExpression, received %T",
				stmt.Expression)
		}

		if !testIdentifier(t, exp.Function, tt.expectedIdent) {
			return
		}

		if len(exp.Arguments) != len(tt.expectedArgs) {
			t.Fatalf("Unexpected argument length. Expected %d, received %d",
				len(tt.expectedArgs), len(exp.Arguments))
		}

		for i, arg := range tt.expectedArgs {
			if exp.Arguments[i].String() != arg {
				t.Errorf("Unexpected argument at position %d: Expected %q, received %q", i,
					arg, exp.Arguments[i].String())
			}
		}
	}
}

func TestParsingPrefixExpressions(t *testing.T) {
	prefixTests := []struct {
		input    string
		operator string
		value    interface{}
	}{
		{"!5;", "!", 5},
		{"-15;", "-", 15},
		{"!foobar;", "!", "foobar"},
		{"-foobar;", "-", "foobar"},
		{"!true;", "!", true},
		{"!false;", "!", false},
	}

	for _, tt := range prefixTests {
		lxr := scanner.New(tt.input)
		p := New(lxr)
		program := p.ParseProgram()
		errors := p.Errors()
		if len(errors) != 0 {
			t.Errorf("parser had %d errors", len(errors))
			for _, msg := range errors {
				t.Errorf("parser error: %q", msg)
			}
			t.FailNow()
		}

		if len(program.Statements) != 1 {
			t.Fatalf("program.Statements does not contain %d statements, received %d\n",
				1, len(program.Statements))
		}

		stmt, ok := program.Statements[0].(*ast.ExpressionStatement)
		if !ok {
			t.Fatalf("program.Statements[0] is not of type ast.ExpressionStatement, received %T",
				program.Statements[0])
		}

		exp, ok := stmt.Expression.(*ast.PrefixExpression)
		if !ok {
			t.Fatalf("stmt is not of type ast.PrefixExpression, received %T", stmt.Expression)
		}
		if exp.Operator != tt.operator {
			t.Fatalf("exp.Operator is not '%s', received %s",
				tt.operator, exp.Operator)
		}
		if !testLiteralExpression(t, exp.Right, tt.value) {
			return
		}
	}
}

func TestParsingInfixExpressions(t *testing.T) {
	infixTests := []struct {
		input      string
		leftValue  interface{}
		operator   string
		rightValue interface{}
	}{
		{"5 + 5;", 5, "+", 5},
		{"5 - 5;", 5, "-", 5},
		{"5 * 5;", 5, "*", 5},
		{"5 / 5;", 5, "/", 5},
		{"5 > 5;", 5, ">", 5},
		{"5 < 5;", 5, "<", 5},
		{"5 == 5;", 5, "==", 5},
		{"5 != 5;", 5, "!=", 5},
		{"true == true", true, "==", true},
		{"true != false", true, "!=", false},
		{"false == false", false, "==", false},
	}

	for _, tt := range infixTests {
		lxr := scanner.New(tt.input)
		p := New(lxr)
		program := p.ParseProgram()
		errors := p.Errors()
		if len(errors) != 0 {
			t.Errorf("parser had %d errors", len(errors))
			for _, msg := range errors {
				t.Errorf("parser error: %q", msg)
			}
			t.FailNow()
		}

		if len(program.Statements) != 1 {
			t.Fatalf("program.Statements does not contain %d statements, received %d\n",
				1, len(program.Statements))
		}

		stmt, ok := program.Statements[0].(*ast.ExpressionStatement)
		if !ok {
			t.Fatalf("program.Statements[0] is not of type ast.ExpressionStatement, received %T",
				program.Statements[0])
		}

		if !testInfixExpression(t, stmt.Expression, tt.leftValue,
			tt.operator, tt.rightValue) {
			return
		}
	}
}

func TestOperatorPrecedenceParsing(t *testing.T) {
	tests := []struct {
		input    string
		expected string
	}{
		{
			"-a * b",
			"((-a) * b)",
		},
		{
			"!-a",
			"(!(-a))",
		},
		{
			"a + b + c",
			"((a + b) + c)",
		},
		{
			"a + b - c",
			"((a + b) - c)",
		},
		{
			"a * b * c",
			"((a * b) * c)",
		},
		{
			"a * b / c",
			"((a * b) / c)",
		},
		{
			"a + b / c",
			"(a + (b / c))",
		},
		{
			"a + b * c + d / e - f",
			"(((a + (b * c)) + (d / e)) - f)",
		},
		{
			"3 + 4; -5 * 5",
			"(3 + 4)((-5) * 5)",
		},
		{
			"5 > 4 == 3 < 4",
			"((5 > 4) == (3 < 4))",
		},
		{
			"5 < 4 != 3 > 4",
			"((5 < 4) != (3 > 4))",
		},
		{
			"3 + 4 * 5 == 3 * 1 + 4 * 5",
			"((3 + (4 * 5)) == ((3 * 1) + (4 * 5)))",
		},
		{
			"1 + (2 + 3) + 4",
			"((1 + (2 + 3)) + 4)",
		},
		{
			"(5 + 5) * 2",
			"((5 + 5) * 2)",
		},
		{
			"2 / (5 + 5)",
			"(2 / (5 + 5))",
		},
		{
			"-(5 + 5)",
			"(-(5 + 5))",
		},
		{
			"!(true == true)",
			"(!(true == true))",
		},
		{
			"true",
			"true",
		},
		{
			"false",
			"false",
		},
		{
			"1337 > 9001 == false",
			"((1337 > 9001) == false)",
		},
		{
			"69 < 420 == true",
			"((69 < 420) == true)",
		},
		{
			"a + add(b * c) + d",
			"((a + add((b * c))) + d)",
		},
		{
			"add(a, b, 1, 2 * 3, 4 + 5, add(6, 7 * 8))",
			"add(a, b, 1, (2 * 3), (4 + 5), add(6, (7 * 8)))",
		},
		{
			"add(a + b + c * d / f + g)",
			"add((((a + b) + ((c * d) / f)) + g))",
		},
	}

	for _, tt := range tests {
		lxr := scanner.New(tt.input)
		p := New(lxr)
		program := p.ParseProgram()
		errors := p.Errors()
		if len(errors) != 0 {
			t.Errorf("parser had %d errors", len(errors))
			for _, msg := range errors {
				t.Errorf("parser error: %q", msg)
			}
			t.FailNow()
		}

		actual := program.String()
		if actual != tt.expected {
			t.Errorf("expected %q, received %q", tt.expected, actual)
		}
	}
}

func TestBooleanExpression(t *testing.T) {
	tests := []struct {
		input    string
		expected bool
	}{
		{"true;", true},
		{"false;", false},
	}

	for _, tt := range tests {
		lxr := scanner.New(tt.input)
		p := New(lxr)
		program := p.ParseProgram()
		errors := p.Errors()
		if len(errors) != 0 {
			t.Errorf("parser had %d errors", len(errors))
			for _, msg := range errors {
				t.Errorf("parser error: %q", msg)
			}
			t.FailNow()
		}

		if len(program.Statements) != 1 {
			t.Fatalf("program does not have enough statements, received %d",
				len(program.Statements))
		}

		stmt, ok := program.Statements[0].(*ast.ExpressionStatement)
		if !ok {
			t.Fatalf("program.Statements[0] is not of type ast.ExpressionStatement, received %T",
				program.Statements[0])
		}

		boolean, ok := stmt.Expression.(*ast.Boolean)
		if !ok {
			t.Fatalf("exp not of type *ast.Boolean, received %T", stmt.Expression)
		}
		if boolean.Value != tt.expected {
			t.Errorf("boolean.Value not %t. got=%t", tt.expected,
				boolean.Value)
		}
	}
}

func TestIfExpression(t *testing.T) {
	input := `if (x < y) { x } `

	lxr := scanner.New(input)
	p := New(lxr)
	program := p.ParseProgram()
	errors := p.Errors()
	if len(errors) != 0 {
		t.Errorf("parser had %d errors", len(errors))
		for _, msg := range errors {
			t.Errorf("parser error: %q", msg)
		}
		t.FailNow()
	}

	if len(program.Statements) != 1 {
		t.Fatalf("program does not contain enough statements, received %d",
			len(program.Statements))
	}

	stmt, ok := program.Statements[0].(*ast.ExpressionStatement)
	if !ok {
		t.Fatalf("program.Statements[0] is not of type ast.ExpressionStatement, received %T",
			program.Statements[0])
	}

	exp, ok := stmt.Expression.(*ast.IfExpression)
	if !ok {
		t.Fatalf("exp not of type *ast.IfExpression, received %T", stmt.Expression)
	}

	if !testInfixExpression(t, exp.Condition, "x", "<", "y") {
		return
	}

	if len(exp.Consequence.Statements) != 1 {
		t.Errorf("Number of statements in consequence was not 1, receive %d\n",
			len(exp.Consequence.Statements))
	}

	consequence, ok := exp.Consequence.Statements[0].(*ast.ExpressionStatement)
	if !ok {
		t.Fatalf("Statements[0] is not of type ast.ExpressionStatement, received %T",
			exp.Consequence.Statements[0])
	}

	if !testIdentifier(t, consequence.Expression, "x") {
		return
	}

	if exp.Alternative != nil {
		t.Errorf("exp.Alternative.Statements was not nil, received %+v", exp.Alternative)
	}

}

func TestIfElseExpression(t *testing.T) {
	input := `if (x < y) { x } else { y } `

	lxr := scanner.New(input)
	p := New(lxr)
	program := p.ParseProgram()
	errors := p.Errors()
	if len(errors) != 0 {
		t.Errorf("parser had %d errors", len(errors))
		for _, msg := range errors {
			t.Errorf("parser error: %q", msg)
		}
		t.FailNow()
	}

	if len(program.Statements) != 1 {
		t.Fatalf("program does not contain enough statements, received %d",
			len(program.Statements))
	}

	stmt, ok := program.Statements[0].(*ast.ExpressionStatement)
	if !ok {
		t.Fatalf("program.Statements[0] is not of type ast.ExpressionStatement, received %T",
			program.Statements[0])
	}

	exp, ok := stmt.Expression.(*ast.IfExpression)
	if !ok {
		t.Fatalf("exp not of type *ast.IfExpression, received %T", stmt.Expression)
	}

	if !testInfixExpression(t, exp.Condition, "x", "<", "y") {
		return
	}

	if len(exp.Consequence.Statements) != 1 {
		t.Errorf("Number of statements in consequence was not 1, receive %d\n",
			len(exp.Consequence.Statements))
	}

	consequence, ok := exp.Consequence.Statements[0].(*ast.ExpressionStatement)
	if !ok {
		t.Fatalf("Statements[0] is not of type ast.ExpressionStatement, received %T",
			exp.Consequence.Statements[0])
	}

	if !testIdentifier(t, consequence.Expression, "x") {
		return
	}

	if len(exp.Alternative.Statements) != 1 {
		t.Errorf("Number of statements in Alternative was not 1, receive %d\n",
			len(exp.Alternative.Statements))
	}

	alternative, ok := exp.Alternative.Statements[0].(*ast.ExpressionStatement)
	if !ok {
		t.Fatalf("Statements[0] is not of type ast.ExpressionStatement, received %T",
			exp.Alternative.Statements[0])
	}

	if !testIdentifier(t, alternative.Expression, "y") {
		return
	}

}

////////////
///////////
func testIntegerLiteral(t *testing.T, il ast.Expression, value int64) bool {
	integ, ok := il.(*ast.IntegerLiteral)
	if !ok {
		t.Errorf("il not of type *ast.IntegerLiteral, received %T", il)
		return false
	}

	if integ.Value != value {
		t.Errorf("integ.Value not %d, received %d", value, integ.Value)
		return false
	}

	if integ.TokenLiteral() != fmt.Sprintf("%d", value) {
		t.Errorf("integ.TokenLiteral not %d, received %s", value,
			integ.TokenLiteral())
		return false
	}

	return true
}

func testIdentifier(t *testing.T, exp ast.Expression, value string) bool {
	ident, ok := exp.(*ast.Identifier)
	if !ok {
		t.Errorf("exp not of type *ast.Identifier, received %T", exp)
		return false
	}

	if ident.Value != value {
		t.Errorf("ident.Value is not %s, received %s", value, ident.TokenLiteral())
		return false
	}

	if ident.TokenLiteral() != value {
		t.Errorf("ident.TokenLiteral is not %s, received %s", value, ident.TokenLiteral())
		return false
	}

	return true
}

func testLiteralExpression(t *testing.T, exp ast.Expression, expected interface{}) bool {
	switch v := expected.(type) {
	case int:
		return testIntegerLiteral(t, exp, int64(v))
	case int64:
		return testIntegerLiteral(t, exp, v)
	case string:
		return testIdentifier(t, exp, v)
	case bool:
		return testBooleanLiteral(t, exp, v)
	}
	t.Errorf("type of exp not handled, received %T", exp)
	return false
}

func testInfixExpression(t *testing.T, exp ast.Expression, left interface{},
	operator string, right interface{}) bool {

	opExp, ok := exp.(*ast.InfixExpression)
	if !ok {
		t.Errorf("exp is not of type ast.InfixExpression, received %T(%s)", exp, exp)
		return false
	}

	if !testLiteralExpression(t, opExp.Left, left) {
		return false
	}

	if opExp.Operator != operator {
		t.Errorf("exp.Operator is not '%s', received %q", operator, opExp.Operator)
		return false
	}

	if !testLiteralExpression(t, opExp.Right, right) {
		return false
	}

	return true
}

func testBooleanLiteral(t *testing.T, exp ast.Expression, value bool) bool {
	boole, ok := exp.(*ast.Boolean)
	if !ok {
		t.Errorf("Expression not of type *ast.Boolean, received %T", exp)
		return false
	}

	if boole.Value != value {
		t.Errorf("boole.Value not of type %t, received %t", value, boole.Value)
		return false
	}

	if boole.TokenLiteral() != fmt.Sprintf("%t", value) {
		t.Errorf("boole.TokenLiteral not of type %t, received %s", value, boole.TokenLiteral())
	}

	return true
}
