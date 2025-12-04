package parser

import (
	"fmt"
	"strconv"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/token"
)

type Parser struct {
	lxr          *scanner.Scanner
	currentToken token.Token
	peekToken    token.Token

	errors []string

	prefixParseFns map[token.TokenKind]prefixParseFn
	infixParseFns  map[token.TokenKind]infixParseFn
	// postfixParseFns map[token.TokenKind]postfixParseFn
}

func New(lxr *scanner.Scanner) *Parser {
	p := &Parser{
		lxr:    lxr,
		errors: []string{},
	}

	// register functions
	p.prefixParseFns = make(map[token.TokenKind]prefixParseFn)
	p.registerPrefix(token.IDENT, p.parseIdentifier)
	p.registerPrefix(token.INT, p.parseIntegerLiteral)
	p.registerPrefix(token.STRING, p.parseStringLiteral)
	p.registerPrefix(token.BANG, p.parsePrefixExpression)
	p.registerPrefix(token.NEG, p.parsePrefixExpression)
	p.registerPrefix(token.TRUE, p.parseBoolean)
	p.registerPrefix(token.FALSE, p.parseBoolean)
	p.registerPrefix(token.LPAREN, p.parseExpressionGroup)
	p.registerPrefix(token.IF, p.parseIfExpression)
	p.registerPrefix(token.FUNC, p.parseFunctionLiteral)
	p.registerPrefix(token.FN, p.parseFunctionLiteral)

	p.infixParseFns = make(map[token.TokenKind]infixParseFn)
	p.registerInfix(token.SUM, p.parseInfixExpression)
	p.registerInfix(token.NEG, p.parseInfixExpression)
	p.registerInfix(token.MUL, p.parseInfixExpression)
	p.registerInfix(token.QUO, p.parseInfixExpression)
	p.registerInfix(token.EQL, p.parseInfixExpression)
	p.registerInfix(token.NEQL, p.parseInfixExpression)
	p.registerInfix(token.LCHEV, p.parseInfixExpression)
	p.registerInfix(token.RCHEV, p.parseInfixExpression)
	p.registerInfix(token.LPAREN, p.parseInvocationExpression)

	// load the first 2 tokens
	p.nextToken()
	p.nextToken()

	return p
}

func (p *Parser) Errors() []string {
	return p.errors
}

func (p *Parser) registerPrefix(TokenKind token.TokenKind, fn prefixParseFn) {
	p.prefixParseFns[TokenKind] = fn
}

func (p *Parser) registerInfix(TokenKind token.TokenKind, fn infixParseFn) {
	p.infixParseFns[TokenKind] = fn
}

func (p *Parser) nextToken() {
	p.currentToken = p.peekToken
	p.peekToken = p.lxr.NextToken()
}

func (p *Parser) parseTypeDeclaration() *ast.TypeDeclarationStatement {
	stmt := &ast.TypeDeclarationStatement{Token: p.currentToken}

	if !p.expectPeek(token.IDENT) {
		return nil
	}

	stmt.Name = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
	if !p.expectPeek(token.EQL) {
		return nil
	}
	// TODO: skip shit
	for !p.currentTokenIs(token.SEMI) {
		p.nextToken()
	}
	return stmt
}

func (p *Parser) parseReturnStatement() *ast.ReturnStatement {
	stmt := &ast.ReturnStatement{Token: p.currentToken}

	p.nextToken()

	stmt.ReturnValue = p.parseExpression(LOWEST)

	for !p.currentTokenIs(token.SEMI) {
		p.nextToken()
	}

	return stmt
}

func (p *Parser) parseBlockStatement() *ast.BlockStatement {
	blocc := &ast.BlockStatement{Token: p.currentToken}
	blocc.Statements = []ast.Statement{}
	p.nextToken()
	for !p.currentTokenIs(token.RBRACE) && !p.currentTokenIs(token.EOF) {
		stmt := p.parseStatement()
		if stmt != nil {
			blocc.Statements = append(blocc.Statements, stmt)
		}
		p.nextToken()
	}

	return blocc
}

func (p *Parser) parseStatement() ast.Statement {
	switch p.currentToken.TokenKind {
	case token.PACKAGE:
		return p.parsePackageStatement()
	case token.IMPORT:
		return p.parseImportStatement()
	case token.TYPE:
		return p.parseADTType()
	case token.FN:
		return p.parseFunctionStatement()
	case token.RETURN:
		return p.parseReturnStatement()
	case token.WHILE:
		return p.parseWhileStatement()
	case token.UNSAFE:
		return p.parseUnsafeBlock()
	case token.IDENT:
		// Could be variable declaration (a: type) or assignment (a = b)
		if p.peekTokenIs(token.COLON) {
			return p.parseVariableDeclaration()
		} else if p.peekTokenIs(token.ASSIGN) {
			return p.parseAssignmentStatement()
		}
		fallthrough
	default:
		return p.parseExpressionStatement()
	}
}

func (p *Parser) parseExpressionStatement() *ast.ExpressionStatement {
	stmt := &ast.ExpressionStatement{Token: p.currentToken}

	stmt.Expression = p.parseExpression(LOWEST)

	if p.peekTokenIs(token.SEMI) {
		p.nextToken()
	}
	return stmt
}

func (p *Parser) parseExpression(precendece Precedence) ast.Expression {
	prefix := p.prefixParseFns[p.currentToken.TokenKind]
	if prefix == nil {
		p.noPrefixParseFn(p.currentToken.TokenKind)
		return nil
	}
	leftExp := prefix()

	for !p.peekTokenIs(token.SEMI) && precendece < p.peekPrecedence() {
		// Check for match expression (postfix ?)
		if p.peekTokenIs(token.QMARK) {
			p.nextToken() // consume ?
			leftExp = p.parseMatchExpression(leftExp)
			continue
		}

		infix := p.infixParseFns[p.peekToken.TokenKind]
		if infix == nil {
			return leftExp
		}

		p.nextToken()
		leftExp = infix(leftExp)
	}
	return leftExp
}

func (p *Parser) parseIdentifier() ast.Expression {
	// Check if this is a variant construction: .Variant or Type::Variant
	literal := p.currentToken.Literal
	if len(literal) > 0 && literal[0] == '.' {
		// This is a variant: .Ok
		return p.parseVariantExpression()
	}

	return &ast.Identifier{Token: p.currentToken, Value: literal}
}

// Parse variant expression: .Ok, .Some(value), or Type::Ok
func (p *Parser) parseVariantExpression() ast.Expression {
	expr := &ast.VariantExpression{Token: p.currentToken}

	literal := p.currentToken.Literal
	if len(literal) > 0 && literal[0] == '.' {
		// .Variant form - extract variant name
		variantName := literal[1:]
		expr.Variant = &ast.Identifier{Token: p.currentToken, Value: variantName}

		// Check for payload: .Some(value)
		if p.peekTokenIs(token.LPAREN) {
			p.nextToken() // consume (
			p.nextToken() // consume value
			expr.Payload = p.parseExpression(LOWEST)
			if !p.expectPeek(token.RPAREN) {
				return nil
			}
		}
	} else {
		// Type::Variant form - current token is Type
		expr.TypeName = &ast.Identifier{Token: p.currentToken, Value: literal}
		if !p.expectPeek(token.COLON) {
			return nil
		}
		// Check for second colon (::)
		if !p.peekTokenIs(token.COLON) {
			// Not Type::Variant, treat as regular identifier
			return &ast.Identifier{Token: p.currentToken, Value: literal}
		}
		p.nextToken() // consume first :
		p.nextToken() // consume second :
		if !p.expectPeek(token.IDENT) {
			return nil
		}
		expr.Variant = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}

		// Check for payload: Type::Some(value)
		if p.peekTokenIs(token.LPAREN) {
			p.nextToken() // consume (
			p.nextToken() // consume value
			expr.Payload = p.parseExpression(LOWEST)
			if !p.expectPeek(token.RPAREN) {
				return nil
			}
		}
	}

	return expr
}

func (p *Parser) parseIntegerLiteral() ast.Expression {
	lit := &ast.IntegerLiteral{Token: p.currentToken}

	value, err := strconv.ParseInt(p.currentToken.Literal, 0, 64)
	if err != nil {
		msg := fmt.Sprintf("could not parse %q as integer", p.currentToken.Literal)
		p.errors = append(p.errors, msg)
		return nil
	}
	lit.Value = value

	return lit
}

func (p *Parser) parseStringLiteral() ast.Expression {
	return &ast.StringLiteral{Token: p.currentToken, Value: p.currentToken.Literal}
}

func (p *Parser) parseFunctionLiteral() ast.Expression {
	lit := &ast.FunctionLiteral{Token: p.currentToken}

	if !p.expectPeek(token.LPAREN) {
		return nil
	}

	lit.Arguments = p.parseFunctionArgs()

	if !p.expectPeek(token.LBRACE) {
		return nil
	}

	lit.Body = p.parseBlockStatement()

	return lit
}

func (p *Parser) parseFunctionArgs() []*ast.Identifier {
	ids := []*ast.Identifier{}

	if p.peekTokenIs(token.RPAREN) {
		p.nextToken()
		return ids
	}

	p.nextToken()

	ident := &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
	ids = append(ids, ident)

	for p.peekTokenIs(token.COMMA) {
		p.nextToken() // consume the comma
		p.nextToken() // load token after comma
		ident := &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
		ids = append(ids, ident)
	}

	if !p.expectPeek(token.RPAREN) {
		return nil
	}

	return ids
}

func (p *Parser) parseInvocationExpression(function ast.Expression) ast.Expression {
	exp := &ast.InvocationExpression{Token: p.currentToken, Function: function}
	exp.Arguments = p.parseInvocationArguments()
	return exp
}

func (p *Parser) parseInvocationArguments() []ast.Expression {
	args := []ast.Expression{}

	p.nextToken()

	if p.currentTokenIs(token.RPAREN) {
		// return if this is a
		// parameterless invocation
		return args
	}

	args = append(args, p.parseExpression(LOWEST))
	for p.peekTokenIs(token.COMMA) {
		p.nextToken()
		p.nextToken()
		args = append(args, p.parseExpression(LOWEST))
	}

	if !p.expectPeek(token.RPAREN) {
		return nil
	}
	return args
}

func (p *Parser) parseBoolean() ast.Expression {
	return &ast.Boolean{Token: p.currentToken, Value: p.currentTokenIs(token.TRUE)}
}

func (p *Parser) parseIfExpression() ast.Expression {
	expr := &ast.IfExpression{Token: p.currentToken}

	if !p.expectPeek(token.LPAREN) {
		return nil
	}

	p.nextToken()
	expr.Condition = p.parseExpression(LOWEST)

	if !p.expectPeek(token.RPAREN) {
		return nil
	}

	if !p.expectPeek(token.LBRACE) {
		return nil
	}

	expr.Consequence = p.parseBlockStatement()

	if p.peekTokenIs(token.ELSE) {
		p.nextToken()

		if !p.expectPeek(token.LBRACE) {
			return nil
		}

		expr.Alternative = p.parseBlockStatement()
	}

	return expr
}

func (p *Parser) ParseProgram() *ast.Program {
	program := &ast.Program{}
	program.Statements = []ast.Statement{}

	for p.currentToken.TokenKind != token.EOF {
		stmt := p.parseStatement()
		if stmt != nil {
			program.Statements = append(program.Statements, stmt)
		}
		p.nextToken()
	}

	return program
}

func (p *Parser) currentTokenIs(t token.TokenKind) bool {
	return p.currentToken.TokenKind == t
}

func (p *Parser) peekTokenIs(t token.TokenKind) bool {
	return p.peekToken.TokenKind == t
}

func (p *Parser) expectPeek(t token.TokenKind) bool {
	if p.peekTokenIs(t) {
		p.nextToken()
		return true
	} else {
		p.peekError(t)
		return false
	}
}

func (p *Parser) peekError(t token.TokenKind) {
	msg := fmt.Sprintf("expected next token to be '%s', received %s", t, p.peekToken.TokenKind)
	p.errors = append(p.errors, msg)
}

// pratt and whitney parsing engines

type (
	prefixParseFn func() ast.Expression
	infixParseFn  func(ast.Expression) ast.Expression
	// postfixParseFn func() ast.Expression
)

// we should really move this father up (token.go/scanner.go)
type Precedence int

const (
	_ Precedence = iota
	LOWEST
	EQUALITY   // ==
	COMPARE    // > or <
	SUMMATION  // +
	PRODUCT    // *
	PREFIX     // -x or !x
	INVOCATION // aka Call, myfunction(x)

)

func (p *Parser) noPrefixParseFn(t token.TokenKind) {
	msg := fmt.Sprintf("no prefix parse function defined for TokenKind %s", t)
	p.errors = append(p.errors, msg)
}

func (p *Parser) parsePrefixExpression() ast.Expression {
	exp := &ast.PrefixExpression{
		Token:    p.currentToken,
		Operator: p.currentToken.Literal,
	}

	p.nextToken()
	exp.Right = p.parseExpression(PREFIX)
	return exp
}

func (p *Parser) parseInfixExpression(left ast.Expression) ast.Expression {
	exp := &ast.InfixExpression{
		Token:    p.currentToken,
		Operator: p.currentToken.Literal,
		Left:     left,
	}

	precedence := p.currentPrecedence()
	p.nextToken()
	exp.Right = p.parseExpression(precedence)

	return exp
}

func (p *Parser) parseExpressionGroup() ast.Expression {
	p.nextToken()
	exp := p.parseExpression(LOWEST)
	if !p.expectPeek(token.RPAREN) {
		return nil
	}

	return exp
}

// all of these should probably move down to the lexer/scanner
var precedences = map[token.TokenKind]Precedence{
	token.EQL:    EQUALITY,
	token.NEQL:   EQUALITY,
	token.LCHEV:  COMPARE,
	token.RCHEV:  COMPARE,
	token.NEG:    SUMMATION,
	token.SUM:    SUMMATION,
	token.MUL:    PRODUCT,
	token.QUO:    PRODUCT,
	token.LPAREN: INVOCATION,
	token.QMARK:  INVOCATION, // Match expression has high precedence
}

func (p *Parser) peekPrecedence() Precedence {
	if p, ok := precedences[p.peekToken.TokenKind]; ok {
		return p
	}
	return LOWEST
}

func (p *Parser) currentPrecedence() Precedence {
	if p, ok := precedences[p.currentToken.TokenKind]; ok {
		return p
	}

	return LOWEST
}

// Package statement
func (p *Parser) parsePackageStatement() *ast.PackageStatement {
	stmt := &ast.PackageStatement{Token: p.currentToken}

	if !p.expectPeek(token.IDENT) {
		return nil
	}

	stmt.Name = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
	return stmt
}

// Import statement
func (p *Parser) parseImportStatement() *ast.ImportStatement {
	stmt := &ast.ImportStatement{Token: p.currentToken}

	if !p.expectPeek(token.LPAREN) {
		return nil
	}

	if !p.expectPeek(token.IDENT) {
		return nil
	}

	stmt.Path = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}

	if !p.expectPeek(token.RPAREN) {
		return nil
	}

	// Optional alias: import(pkg) as alias
	if p.peekTokenIs(token.IDENT) && p.peekToken.Literal == "as" {
		p.nextToken() // consume 'as'
		if !p.expectPeek(token.IDENT) {
			return nil
		}
		stmt.Alias = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
	}

	return stmt
}

// ADT type definition
func (p *Parser) parseADTType() *ast.ADTType {
	adt := &ast.ADTType{Token: p.currentToken}

	if !p.expectPeek(token.IDENT) {
		return nil
	}

	adt.Name = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}

	if !p.expectPeek(token.COLON) {
		return nil
	}

	if !p.expectPeek(token.TYPE) {
		return nil
	}

	// Parse variants: = Variant1 | Variant2 | ...
	if !p.expectPeek(token.ASSIGN) {
		return nil
	}

	adt.Variants = []*ast.ADTVariant{}

	// Parse first variant
	p.nextToken()
	variant := p.parseADTVariant()
	if variant == nil {
		return nil
	}
	adt.Variants = append(adt.Variants, variant)

	// Parse remaining variants
	for p.peekTokenIs(token.PIPE) {
		p.nextToken() // consume |
		p.nextToken() // consume next token
		variant := p.parseADTVariant()
		if variant == nil {
			return nil
		}
		adt.Variants = append(adt.Variants, variant)
	}

	return adt
}

// ADT variant: Name | Name(T) | Name: literal
func (p *Parser) parseADTVariant() *ast.ADTVariant {
	variant := &ast.ADTVariant{Token: p.currentToken}

	if !p.currentTokenIs(token.IDENT) {
		p.peekError(token.IDENT)
		return nil
	}

	variant.Name = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}

	// Check for payload: Some(T)
	if p.peekTokenIs(token.LPAREN) {
		p.nextToken() // consume (
		p.nextToken() // consume type
		variant.Payload = p.parseTypeExpression()
		if !p.expectPeek(token.RPAREN) {
			return nil
		}
	}

	// Check for literal tag: Ok: 200
	if p.peekTokenIs(token.COLON) {
		p.nextToken() // consume :
		p.nextToken() // consume literal
		variant.Literal = p.parseLiteralExpression()
	}

	return variant
}

// Parse type expression (simplified - just identifier for now)
func (p *Parser) parseTypeExpression() ast.Expression {
	if p.currentTokenIs(token.IDENT) {
		return &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
	}
	return nil
}

// Parse literal expression (integer, string, or record literal)
func (p *Parser) parseLiteralExpression() ast.Expression {
	switch p.currentToken.TokenKind {
	case token.INT:
		return p.parseIntegerLiteral()
	case token.STRING:
		return p.parseStringLiteral()
	case token.LBRACE:
		return p.parseRecordLiteral()
	default:
		p.peekError(token.INT)
		return nil
	}
}

// Record literal: { field: value, ... }
func (p *Parser) parseRecordLiteral() ast.Expression {
	// For now, return a placeholder - proper record literal AST node needed
	// TODO: implement proper record literal parsing with RecordLiteral AST node
	// For now, parse as identifier to avoid errors
	return &ast.Identifier{Token: p.currentToken, Value: "{}"}
}

// Function statement (top-level function)
func (p *Parser) parseFunctionStatement() *ast.FunctionStatement {
	stmt := &ast.FunctionStatement{Token: p.currentToken}

	if !p.expectPeek(token.IDENT) {
		return nil
	}

	stmt.Name = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}

	if !p.expectPeek(token.LPAREN) {
		return nil
	}

	stmt.Parameters = p.parseFunctionParameters()

	if !p.expectPeek(token.ARROW) {
		return nil
	}

	p.nextToken() // consume ->
	stmt.ReturnType = p.parseTypeExpression()

	// Body can be expression or block
	p.nextToken()
	if p.currentTokenIs(token.LBRACE) {
		stmt.Body = p.parseBlockExpression()
	} else {
		stmt.Body = p.parseExpression(LOWEST)
	}

	return stmt
}

// Function parameters: name: Type, name2: Type2
func (p *Parser) parseFunctionParameters() []*ast.FunctionParameter {
	params := []*ast.FunctionParameter{}

	if p.peekTokenIs(token.RPAREN) {
		p.nextToken()
		return params
	}

	p.nextToken() // consume first param name
	param := &ast.FunctionParameter{
		Token: p.currentToken,
		Name:  &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal},
	}

	if !p.expectPeek(token.COLON) {
		return nil
	}

	p.nextToken() // consume type
	param.Type = p.parseTypeExpression()
	params = append(params, param)

	for p.peekTokenIs(token.COMMA) {
		p.nextToken() // consume comma
		p.nextToken() // consume param name
		param := &ast.FunctionParameter{
			Token: p.currentToken,
			Name:  &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal},
		}
		if !p.expectPeek(token.COLON) {
			return nil
		}
		p.nextToken() // consume type
		param.Type = p.parseTypeExpression()
		params = append(params, param)
	}

	if !p.expectPeek(token.RPAREN) {
		return nil
	}

	return params
}

// Block expression: { stmt1; stmt2; expr }
func (p *Parser) parseBlockExpression() ast.Expression {
	block := p.parseBlockStatement()
	// Convert block statement to expression
	// For now, return the last statement's expression
	if len(block.Statements) > 0 {
		if exprStmt, ok := block.Statements[len(block.Statements)-1].(*ast.ExpressionStatement); ok {
			return exprStmt.Expression
		}
	}
	return nil
}

// While statement
func (p *Parser) parseWhileStatement() *ast.WhileStatement {
	stmt := &ast.WhileStatement{Token: p.currentToken}

	p.nextToken()
	stmt.Condition = p.parseExpression(LOWEST)

	if !p.expectPeek(token.LBRACE) {
		return nil
	}

	stmt.Body = p.parseBlockStatement()
	return stmt
}

// Unsafe block
func (p *Parser) parseUnsafeBlock() *ast.UnsafeBlock {
	block := &ast.UnsafeBlock{Token: p.currentToken}

	if !p.expectPeek(token.LBRACE) {
		return nil
	}

	block.Body = p.parseBlockStatement()
	return block
}

// Match expression: expr ? | pattern -> expr | ...
func (p *Parser) parseMatchExpression(left ast.Expression) ast.Expression {
	match := &ast.MatchExpression{Token: p.currentToken}
	match.Scrutinee = left
	match.Arms = []*ast.MatchArm{}

	// Parse match arms
	if p.peekTokenIs(token.LBRACE) {
		// Braced form: ? { pattern -> expr | ... }
		p.nextToken() // consume {
		match.Arms = p.parseMatchArms()
		if !p.expectPeek(token.RBRACE) {
			return nil
		}
	} else {
		// Inline form: ? | pattern -> expr | ...
		match.Arms = p.parseMatchArms()
	}

	return match
}

// Parse match arms: | pattern -> expr | pattern2 -> expr2
func (p *Parser) parseMatchArms() []*ast.MatchArm {
	arms := []*ast.MatchArm{}

	// First arm (may or may not have leading |)
	if p.peekTokenIs(token.PIPE) {
		p.nextToken() // consume |
	}

	p.nextToken() // consume pattern token
	pattern := p.parsePattern()
	if pattern == nil {
		return nil
	}

	if !p.expectPeek(token.ARROW) {
		return nil
	}

	p.nextToken() // consume ->
	body := p.parseExpression(LOWEST)
	if body == nil {
		return nil
	}

	arm := &ast.MatchArm{
		Token:   p.currentToken,
		Pattern: pattern,
		Body:    body,
	}
	arms = append(arms, arm)

	// Parse remaining arms
	for p.peekTokenIs(token.PIPE) {
		p.nextToken() // consume |
		p.nextToken() // consume pattern token
		pattern := p.parsePattern()
		if pattern == nil {
			return nil
		}

		if !p.expectPeek(token.ARROW) {
			return nil
		}

		p.nextToken() // consume ->
		body := p.parseExpression(LOWEST)
		if body == nil {
			return nil
		}

		arm := &ast.MatchArm{
			Token:   p.currentToken,
			Pattern: pattern,
			Body:    body,
		}
		arms = append(arms, arm)
	}

	return arms
}

// Parse pattern: _ | x | 200 | "string" | .Ok | .Some(x)
func (p *Parser) parsePattern() ast.Pattern {
	switch p.currentToken.TokenKind {
	case token.IDENT:
		// Could be binding or variant
		if p.currentToken.Literal[0] == '.' || (len(p.currentToken.Literal) > 0 && p.currentToken.Literal[0] >= 'A' && p.currentToken.Literal[0] <= 'Z') {
			// Variant pattern: .Ok or Status::Ok
			return p.parseVariantPattern()
		}
		// Binding pattern: x
		return &ast.BindingPattern{
			Token: p.currentToken,
			Name:  &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal},
		}
	case token.INT:
		// Literal pattern: 200
		return &ast.LiteralPattern{
			Token: p.currentToken,
			Value: p.parseIntegerLiteral(),
		}
	case token.STRING:
		// Literal pattern: "string"
		return &ast.LiteralPattern{
			Token: p.currentToken,
			Value: p.parseStringLiteral(),
		}
	default:
		// Try wildcard if it's an identifier named "_"
		if p.currentTokenIs(token.IDENT) && p.currentToken.Literal == "_" {
			return &ast.WildcardPattern{Token: p.currentToken}
		}
		p.peekError(token.IDENT)
		return nil
	}
}

// Variant pattern: .Ok | .Some(x) | Status::Ok
func (p *Parser) parseVariantPattern() ast.Pattern {
	pattern := &ast.VariantPattern{Token: p.currentToken}

	// Handle .Variant or Type::Variant
	var variantName string
	literal := p.currentToken.Literal
	if len(literal) > 0 && literal[0] == '.' {
		variantName = literal[1:]
	} else if len(literal) > 2 && literal[1:3] == "::" {
		// Type::Variant - extract variant name after ::
		// For now, just use the full identifier
		variantName = literal
	} else {
		// Capitalized identifier treated as variant
		variantName = literal
	}

	pattern.Variant = &ast.Identifier{Token: p.currentToken, Value: variantName}

	// Check for payload: .Some(x)
	if p.peekTokenIs(token.LPAREN) {
		p.nextToken() // consume (
		p.nextToken() // consume pattern
		pattern.Payload = p.parsePattern()
		if !p.expectPeek(token.RPAREN) {
			return nil
		}
	}

	return pattern
}

// Parse variable declaration: a: type = value or a: type
func (p *Parser) parseVariableDeclaration() *ast.VariableDeclaration {
	stmt := &ast.VariableDeclaration{Token: p.currentToken}

	// Name is current token (IDENT)
	stmt.Name = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}

	// Expect colon
	if !p.expectPeek(token.COLON) {
		return nil
	}

	// Parse type annotation
	p.nextToken()
	stmt.Type = p.parseTypeExpression()

	// Check for optional assignment
	if p.peekTokenIs(token.ASSIGN) {
		p.nextToken() // consume =
		p.nextToken() // consume value
		stmt.Value = p.parseExpression(LOWEST)
	}

	if p.peekTokenIs(token.SEMI) {
		p.nextToken()
	}

	return stmt
}

// Parse assignment statement: a = b
func (p *Parser) parseAssignmentStatement() *ast.AssignmentStatement {
	stmt := &ast.AssignmentStatement{Token: p.currentToken}

	// Name is current token (IDENT)
	stmt.Name = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}

	// Expect assignment operator
	if !p.expectPeek(token.ASSIGN) {
		return nil
	}

	p.nextToken() // consume =
	p.nextToken() // consume value
	stmt.Value = p.parseExpression(LOWEST)

	if p.peekTokenIs(token.SEMI) {
		p.nextToken()
	}

	return stmt
}
