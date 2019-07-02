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
	input := `
	return 5;
	return 10;
	return 1337;
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
	if len(program.Statements) != 3 {
		t.Fatalf("program doesn't have the correct number of statements. Expected 3, received %d", len(program.Statements))
	}

	for _, stmt := range program.Statements {
		returnStmt, ok := stmt.(*ast.ReturnStatement)
		if !ok {
			t.Errorf("stmt not *ast.ReturnStatement, received %T", stmt)
			continue
		}
		if returnStmt.TokenLiteral() != "return" {
			t.Errorf("returnStmt.TokenLiteral not 'return', received %q", returnStmt.TokenLiteral())
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
		t.Fatalf("program.Statements[0]  is not *ast.ExpressionStatement. Received %T", program.Statements[0])
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

func TestPrefixExpressions(t *testing.T) {
	prefixTests := []struct {
		input        string
		operator     string
		integerValue int64
	}{
		{"!5;", "!", 5},
		{"-15;", "-", 15},
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
			t.Fatalf("Program has an unexpected number of statements. Expected 1, received %d", len(program.Statements))
		}

		stmt, ok := program.Statements[0].(*ast.ExpressionStatement)
		if !ok {
			t.Fatalf("program.Statements[0]  is not *ast.ExpressionStatement. Received %T", program.Statements[0])
		}

		exp, ok := stmt.Expression.(*ast.PrefixExpression)
		if !ok {

			t.Fatalf("stmt is not of type ast.PrefixExpression, received %T", stmt.Expression)
		}

		if exp.Operator != tt.operator {
			t.Fatalf("exp.Operator is not '%s', received %s", tt.operator, exp.Operator)
		}

		// test integer literals

		integ, ok := exp.Right.(*ast.IntegerLiteral)
		if !ok {
			t.Fatalf("exp.Right not of type *ast.IntegerLiteral, received %T", exp.Right)

		}

		if integ.Value != tt.integerValue {
			t.Fatalf("integ.Value not %d, received %d", tt.integerValue, integ.Value)

		}

		if integ.TokenLiteral() != fmt.Sprintf("%d", tt.integerValue) {
			t.Fatalf("integ.TokenLiteral not %d, received %s", tt.integerValue,
				integ.TokenLiteral())

		}
		// end

	}
}

func TestInfixExpressions(t *testing.T) {
	infixTests := []struct {
		input      string
		leftValue  int64
		operator   string
		rightValue int64
	}{
		{"5 + 5;", 5, "+", 5},
		{"5 - 5;", 5, "-", 5},
		{"5 * 5;", 5, "*", 5},
		{"5 / 5;", 5, "/", 5},
		{"5 > 5;", 5, ">", 5},
		{"5 < 5;", 5, "<", 5},
		{"5 == 5;", 5, "==", 5},
		{"5 != 5;", 5, "!=", 5},
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
			t.Fatalf("Program has an unexpected number of statements. Expected 1, received %d", len(program.Statements))
		}

		stmt, ok := program.Statements[0].(*ast.ExpressionStatement)
		if !ok {
			t.Fatalf("program.Statements[0]  is not *ast.ExpressionStatement. Received %T", program.Statements[0])
		}

		exp, ok := stmt.Expression.(*ast.InfixExpression)
		if !ok {

			t.Fatalf("stmt is not of type ast.InfixExpression, received %T", stmt.Expression)
		}

		if testIntegerLiteral(t, exp.Left, tt.leftValue) {
			return
		}

		if exp.Operator != tt.operator {
			t.Fatalf("exp.Operator is not '%s', received %s", tt.operator, exp.Operator)
		}

		if testIntegerLiteral(t, exp.Right, tt.rightValue) {
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
			t.Errorf("expected=%q, got=%q", tt.expected, actual)
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
			t.Fatalf("program has not enough statements. got=%d",
				len(program.Statements))
		}

		stmt, ok := program.Statements[0].(*ast.ExpressionStatement)
		if !ok {
			t.Fatalf("program.Statements[0] is not ast.ExpressionStatement. got=%T",
				program.Statements[0])
		}

		boolean, ok := stmt.Expression.(*ast.Boolean)
		if !ok {
			t.Fatalf("exp not *ast.Boolean. got=%T", stmt.Expression)
		}
		if boolean.Value != tt.expected {
			t.Errorf("boolean.Value not %t. got=%t", tt.expected,
				boolean.Value)
		}
	}
}

////////////
///////////
func testIntegerLiteral(t *testing.T, il ast.Expression, value int64) bool {
	integ, ok := il.(*ast.IntegerLiteral)
	if !ok {
		t.Errorf("il not *ast.IntegerLiteral. got=%T", il)
		return false
	}

	if integ.Value != value {
		t.Errorf("integ.Value not %d. got=%d", value, integ.Value)
		return false
	}

	if integ.TokenLiteral() != fmt.Sprintf("%d", value) {
		t.Errorf("integ.TokenLiteral not %d. got=%s", value,
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
	}
	t.Errorf("type of exp not handled, received %T", exp)
	return false
}

func testInfixExpression(t *testing.T, exp ast.Expression, left interface{}, operator string, right interface{}) bool {
	opExp, ok := exp.(*ast.InfixExpression)
	if !ok {
		t.Errorf("expression is not of type ast.InfixExpression, received %T(%s)", exp, exp)
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
