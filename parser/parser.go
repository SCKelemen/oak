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

	// Collected trivia tokens that will be attached to the next non-trivia node
	pendingTrivia []token.Token
}

func New(lxr *scanner.Scanner) *Parser {
	p := &Parser{
		lxr:           lxr,
		errors:        []string{},
		pendingTrivia: []token.Token{},
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
	p.registerPrefix(token.LBRACE, p.parseRecordLiteral)
	p.registerPrefix(token.LBRACK, p.parseArrayLiteral)
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
	p.registerInfix(token.DOT, p.parseIndexExpression)
	p.registerInfix(token.LBRACK, p.parseIndexExpression)
	p.registerInfix(token.LBRACK, p.parseIndexExpression)

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

	// Skip trivia and comment tokens for currentToken, collecting them as we go
	for p.currentToken.TokenKind == token.TRIVIA || p.currentToken.TokenKind == token.COMMENT {
		p.pendingTrivia = append(p.pendingTrivia, p.currentToken)
		p.currentToken = p.peekToken
		p.peekToken = p.lxr.NextToken()
	}

	// Also skip trivia and comment tokens for peekToken
	for p.peekToken.TokenKind == token.TRIVIA || p.peekToken.TokenKind == token.COMMENT {
		p.pendingTrivia = append(p.pendingTrivia, p.peekToken)
		p.peekToken = p.lxr.NextToken()
	}
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
	// Skip statement terminators (semicolons, etc.)
	if p.currentTokenIs(token.SEMI) {
		return nil
	}

	// Check for REPL directives: :exit, :quit, :help
	if p.currentTokenIs(token.COLON) {
		return p.parseREPLCommand()
	}

	switch p.currentToken.TokenKind {
	case token.PACKAGE:
		return p.parsePackageStatement()
	case token.IMPORT:
		return p.parseImportStatement()
	case token.TYPE:
		return p.parseADTType()
	case token.INTERFACE:
		return p.parseInterfaceType()
	case token.FN:
		return p.parseFunctionStatement()
	case token.WHILE:
		return p.parseWhileStatement()
	case token.UNSAFE:
		return p.parseUnsafeBlock()
	case token.IDENT:
		// Variable declarations and assignments:
		// - x := expr -> declaration with type inference (short declaration)
		// - x: T = expr -> declaration with type annotation
		// - x = expr -> assignment (must refer to existing variable)
		if p.peekTokenIs(token.COLON_ASSIGN) {
			// Short declaration: x := expr
			return p.parseShortVariableDeclaration()
		} else if p.peekTokenIs(token.COLON) {
			// Typed declaration: x: T = expr or x: T
			return p.parseVariableDeclaration()
		} else if p.peekTokenIs(token.ASSIGN) {
			// Assignment: x = expr (must refer to existing variable)
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
	// Check if currentToken can start an expression
	// If it's a token that can't start an expression (comma, semicolon, closing parens, operators that aren't prefix, etc.), return nil
	if p.currentTokenIs(token.COMMA) || p.currentTokenIs(token.SEMI) ||
		p.currentTokenIs(token.RPAREN) || p.currentTokenIs(token.RBRACE) ||
		p.currentTokenIs(token.RBRACK) || p.currentTokenIs(token.PIPE) {
		return nil
	}

	prefix := p.prefixParseFns[p.currentToken.TokenKind]
	if prefix == nil {
		// Check if it's an infix operator that can't start an expression
		// (SUM/+ can't start expressions, but NEG/- can as unary minus)
		if p.currentTokenIs(token.SUM) || p.currentTokenIs(token.MUL) ||
			p.currentTokenIs(token.QUO) || p.currentTokenIs(token.EQL) ||
			p.currentTokenIs(token.NEQL) || p.currentTokenIs(token.LCHEV) ||
			p.currentTokenIs(token.RCHEV) {
			// These operators can't start expressions - return nil silently
			return nil
		}
		p.noPrefixParseFn(p.currentToken.TokenKind)
		return nil
	}
	leftExp := prefix()

	// After prefix parse, currentToken is still the prefix token (prefix parsers don't advance)
	// peekToken is what comes after the expression
	// Stop if we see a comma, semicolon, closing paren, closing brace, or closing bracket (these terminate expressions)
	// Also stop if precedence is too low
	// Note: We stop at commas and brackets to allow array/record literal parsers to handle them
	for !p.peekTokenIs(token.SEMI) && !p.peekTokenIs(token.COMMA) && !p.peekTokenIs(token.RPAREN) && !p.peekTokenIs(token.RBRACE) && !p.peekTokenIs(token.RBRACK) {
		// Check precedence - if it's too low, stop
		if precendece >= p.peekPrecedence() {
			break
		}

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

		// After infix parse, check if we should stop
		// (infix parsers like parseIndexExpression may have advanced past stop tokens)
		// Also check currentToken in case the infix parser advanced past the stop token
		// IMPORTANT: Some infix parsers (like parseInvocationExpression) may consume the closing paren,
		// leaving currentToken as the stop token. However, we should only stop if peekToken is also
		// a stop token, because we might have more operators to parse (e.g., "1 + (2 + 3) + 4")
		if p.currentTokenIs(token.SEMI) || p.currentTokenIs(token.COMMA) || p.currentTokenIs(token.RBRACE) || p.currentTokenIs(token.RBRACK) {
			// These are always stop tokens
			break
		}
		// For RPAREN, only stop if peekToken is also a stop token
		// This allows expressions like "1 + (2 + 3) + 4" to continue parsing
		if p.currentTokenIs(token.RPAREN) {
			// Only stop if peekToken is also a stop token
			if p.peekTokenIs(token.SEMI) || p.peekTokenIs(token.COMMA) || p.peekTokenIs(token.RPAREN) || p.peekTokenIs(token.RBRACE) || p.peekTokenIs(token.RBRACK) || p.peekTokenIs(token.EOF) {
				break
			}
			// Otherwise, continue parsing (peekToken is likely an operator)
		}
		if p.peekTokenIs(token.SEMI) || p.peekTokenIs(token.COMMA) || p.peekTokenIs(token.RPAREN) || p.peekTokenIs(token.RBRACE) || p.peekTokenIs(token.RBRACK) {
			break
		}
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
	lit := &ast.StringLiteral{Token: p.currentToken, Value: p.currentToken.Literal}
	// Note: We don't advance the token here because parseExpression's loop handles it
	// The prefix parser should just return the AST node, and the expression parser advances
	return lit
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
	// currentToken is ( here (consumed by infix parser setup)
	// parseInvocationArguments expects currentToken to be ( and will consume it
	exp.Arguments = p.parseInvocationArguments()
	// After parseInvocationArguments returns:
	// - If no args: currentToken is ), peekToken is next token (; or EOF)
	// - If args: currentToken is last token of last arg, peekToken is )
	// In both cases, we need to consume the closing paren
	if p.currentTokenIs(token.RPAREN) {
		// No args case - already positioned at closing paren, consume it
		p.nextToken()
		return exp
	}
	// We have arguments, so peekToken should be the closing paren
	// But first verify we're positioned correctly
	if !p.peekTokenIs(token.RPAREN) {
		// peekToken is not the closing paren - this shouldn't happen
		// Check if we've somehow consumed it already
		if p.currentTokenIs(token.SEMI) {
			// We've gone too far - the closing paren was consumed
			p.peekError(token.RPAREN)
			return nil
		}
		// Try to provide helpful error
		p.peekError(token.RPAREN)
		return nil
	}
	// Consume the closing paren
	p.nextToken()
	return exp
}

// Parse field access: record.field or array indexing: array[index]
func (p *Parser) parseIndexExpression(left ast.Expression) ast.Expression {
	exp := &ast.IndexExpression{Token: p.currentToken, Left: left}

	if p.currentTokenIs(token.DOT) {
		// Record field access: record.field
		p.nextToken()
		if !p.currentTokenIs(token.IDENT) {
			p.peekError(token.IDENT)
			return nil
		}
		exp.Index = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
	} else if p.currentTokenIs(token.LBRACK) {
		// Array indexing: array[index]
		// The current token is [, next should be the index expression
		p.nextToken()

		// Parse the index expression
		indexExpr := p.parseExpression(LOWEST)
		if indexExpr == nil {
			return nil
		}
		exp.Index = indexExpr

		// After parseExpression, currentToken is the last token of the index expression
		// peekToken should be the closing bracket
		// Advance past the index expression to the closing bracket
		if !p.peekTokenIs(token.RBRACK) {
			p.peekError(token.RBRACK)
			return nil
		}
		p.nextToken() // Advance past index expression to ]
		p.nextToken() // Advance past ] to next token
		// After this, currentToken is past the ], peekToken is what comes after
		// The expression parser's loop will check peekToken, which should be a stop token
	} else {
		p.peekError(token.IDENT)
		return nil
	}

	return exp
}

func (p *Parser) parseInvocationArguments() []ast.Expression {
	args := []ast.Expression{}

	// currentToken should be ( here (consumed by infix parser setup before calling parseInvocationExpression)
	// But parseInvocationExpression is called with currentToken = (, so we need to consume it
	if !p.currentTokenIs(token.LPAREN) {
		// This shouldn't happen, but handle it
		p.peekError(token.LPAREN)
		return nil
	}
	p.nextToken() // currentToken is now first arg or closing paren

	if p.currentTokenIs(token.RPAREN) {
		// parameterless invocation - don't consume the closing paren here,
		// let parseInvocationExpression do that
		return args
	}

	// Parse arguments separated by commas
	for {
		// Parse current argument
		arg := p.parseExpression(LOWEST)
		if arg == nil {
			// If we failed to parse and we're at closing paren, that's ok (empty args already handled)
			if p.currentTokenIs(token.RPAREN) {
				break
			}
			return nil
		}
		args = append(args, arg)

		// After parsing expression, check what comes next
		// parseExpression should leave us positioned such that:
		// - currentToken is the last token of the expression
		// - peekToken is the next token (comma, closing paren, etc.)

		// Check if we're already at the closing paren (shouldn't happen, but handle it)
		if p.currentTokenIs(token.RPAREN) {
			// We've somehow consumed the closing paren - this is an error state
			// but try to recover by returning what we have
			break
		}

		// Check peekToken for what comes after the expression
		if p.peekTokenIs(token.RPAREN) {
			// No more arguments - exit loop, peekToken is the closing paren
			break
		}
		if p.peekTokenIs(token.COMMA) {
			// More arguments - consume comma and advance
			p.nextToken() // consume comma
			p.nextToken() // advance to next argument
			// Check for trailing comma
			if p.currentTokenIs(token.RPAREN) {
				// Trailing comma - error
				p.peekError(token.IDENT)
				return nil
			}
			continue
		}
		// Unexpected token - neither comma nor closing paren
		// This might happen if parseExpression consumed the closing paren
		// Check if we've gone past where we should be
		if p.currentTokenIs(token.SEMI) || p.peekTokenIs(token.SEMI) {
			// We've consumed too much - the closing paren was likely consumed by parseExpression
			// This is a bug, but try to provide a helpful error
			p.peekError(token.RPAREN)
			return nil
		}
		p.peekError(token.RPAREN)
		return nil
	}

	// After loop, peekToken should be closing paren
	// Don't consume it here - let parseInvocationExpression do that
	return args
}

func (p *Parser) parseBoolean() ast.Expression {
	return &ast.Boolean{Token: p.currentToken, Value: p.currentTokenIs(token.TRUE)}
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

// attachPendingTrivia attaches any pending trivia tokens to a node
func (p *Parser) attachPendingTrivia(node ast.Node) {
	if len(p.pendingTrivia) > 0 {
		node.SetLeadingTrivia(p.pendingTrivia)
		p.pendingTrivia = []token.Token{} // Clear pending trivia
	}
}

// collectTrailingTrivia collects trivia tokens that appear after a node
// This should be called after parsing a node to collect any trailing trivia
func (p *Parser) collectTrailingTrivia() []token.Token {
	trivia := []token.Token{}
	// Look ahead to collect trivia before the next non-trivia token
	peek := p.peekToken
	for peek.TokenKind == token.TRIVIA {
		trivia = append(trivia, peek)
		// Advance to get next peek
		oldCurrent := p.currentToken
		p.currentToken = peek
		p.peekToken = p.lxr.NextToken()
		peek = p.peekToken
		// Restore current if we didn't find more trivia
		if peek.TokenKind != token.TRIVIA {
			// Put back the last trivia as current, next peek is non-trivia
			p.currentToken = oldCurrent
		}
	}
	return trivia
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
	INDEX      // record.field or array[index] - highest precedence
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
	// Skip opening paren - currentToken is LPAREN, advance to expression
	p.nextToken()
	exp := p.parseExpression(LOWEST)
	// After parseExpression, currentToken is the last token of the expression
	// peekToken should be RPAREN
	if !p.expectPeek(token.RPAREN) {
		return nil
	}
	// After expectPeek, currentToken is RPAREN, peekToken is what comes after
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
	token.DOT:    INDEX,      // Field access has highest precedence
	token.LBRACK: INDEX,      // Array indexing has highest precedence
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

	// Parse optional type parameters: Name[T: Ordered]: type = ...
	if p.peekTokenIs(token.LBRACK) {
		adt.TypeParams = p.parseTypeParameters()
		if adt.TypeParams == nil {
			return nil // Error already reported
		}
	}

	if !p.expectPeek(token.COLON) {
		return nil
	}

	if !p.expectPeek(token.TYPE) {
		return nil
	}

	// Parse type definition: = Variant1 | Variant2 | ... OR = RecordType OR = TypeName & RecordType
	if !p.expectPeek(token.ASSIGN) {
		return nil
	}

	p.nextToken()

	// Check if this is a record type definition or record composition
	// Record type: { field: Type, ... }
	// Record composition: TypeName & { field: Type, ... } or TypeName & TypeName
	if p.currentTokenIs(token.LBRACE) {
		// This is a record type definition
		recordLit := p.parseRecordLiteral()
		if recordLit == nil {
			return nil
		}
		// Store as a single variant with record literal
		variant := &ast.ADTVariant{
			Token:   p.currentToken,
			Name:    adt.Name, // Use ADT name as variant name for record types
			Literal: recordLit,
		}
		adt.Variants = []*ast.ADTVariant{variant}
	} else if p.currentTokenIs(token.IDENT) {
		// Could be: TypeName (type alias) or TypeName & RecordType (composition)
		// Check if next token is & for composition
		if p.peekTokenIs(token.AMP) {
			// Record composition: TypeName & TypeName & { ... }
			composition := p.parseRecordComposition()
			if composition == nil {
				return nil
			}
			// Store composition as a variant with the composition expression
			variant := &ast.ADTVariant{
				Token:   p.currentToken,
				Name:    adt.Name,
				Literal: composition, // Store composition expression
			}
			adt.Variants = []*ast.ADTVariant{variant}
		} else {
			// Type alias: Name: type = OtherType
			// Parse as a variant with payload
			typeExpr := p.parseTypeExpressionSimple()
			if typeExpr == nil {
				return nil
			}
			variant := &ast.ADTVariant{
				Token:   p.currentToken,
				Name:    adt.Name,
				Payload: typeExpr, // Store type alias target
			}
			adt.Variants = []*ast.ADTVariant{variant}
		}
	} else {
		// Parse as ADT variants: Variant1 | Variant2 | ...
		adt.Variants = []*ast.ADTVariant{}
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
	}

	// Set end token to the last token we consumed (last variant's end)
	if len(adt.Variants) > 0 {
		lastVariant := adt.Variants[len(adt.Variants)-1]
		// Try to get end token from last variant's literal or name
		if lastVariant.Literal != nil {
			if recordLit, ok := lastVariant.Literal.(*ast.RecordLiteral); ok {
				adt.EndToken = recordLit.EndToken
			} else {
				// For other literals, use the literal's token
				adt.EndToken = p.currentToken
			}
		} else {
			adt.EndToken = lastVariant.Name.Token
		}
	} else {
		adt.EndToken = p.currentToken
	}

	return adt
}

// parseRecordComposition parses record composition: TypeName & TypeName & { ... }
// Returns an InfixExpression representing the composition chain
func (p *Parser) parseRecordComposition() ast.Expression {
	// We're already at the first identifier
	var left ast.Expression = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}

	// Parse composition chain: TypeName & TypeName & { ... }
	for p.peekTokenIs(token.AMP) {
		p.nextToken() // consume &
		p.nextToken() // consume next component

		var right ast.Expression
		if p.currentTokenIs(token.LBRACE) {
			// Record literal: { field: Type, ... }
			right = p.parseRecordLiteral()
		} else if p.currentTokenIs(token.IDENT) {
			// Type name
			right = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
		} else {
			p.errors = append(p.errors, fmt.Sprintf("expected type name or record literal in composition, got %s", p.currentToken.Literal))
			return nil
		}

		if right == nil {
			return nil
		}

		// Create intersection expression
		left = &ast.InfixExpression{
			Token:    p.currentToken,
			Left:     left,
			Operator: "&",
			Right:    right,
		}
	}

	return left
}

// Interface type definition: Name: interface = fn (self) method(...) -> ...
// Example: Reader: interface = fn (self) read(...) -> ...
// Example: IntrusiveListNode[T, Tag]: interface = fn (self: *T) hook( _: Tag ) -> *ListHook[T, Tag]
func (p *Parser) parseInterfaceType() *ast.InterfaceType {
	it := &ast.InterfaceType{Token: p.currentToken}

	if !p.expectPeek(token.IDENT) {
		return nil
	}

	it.Name = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}

	// Parse optional type parameters: Name[T, Tag]: interface = ...
	if p.peekTokenIs(token.LBRACK) {
		it.TypeParams = p.parseTypeParameters()
		if it.TypeParams == nil {
			return nil // Error already reported
		}
	}

	if !p.expectPeek(token.COLON) {
		return nil
	}

	if !p.expectPeek(token.INTERFACE) {
		return nil
	}

	if !p.expectPeek(token.ASSIGN) {
		return nil
	}

	// Parse method signature(s)
	// For now, we'll parse a single function signature
	// In the future, this could be a list of methods
	p.nextToken()

	// Parse the method as a function signature
	// Interface methods are function types: fn (self) method(...) -> ...
	if !p.currentTokenIs(token.FN) {
		p.errors = append(p.errors, fmt.Sprintf("expected 'fn' in interface definition, got %s", p.currentToken.Literal))
		return nil
	}

	// Parse function signature for the interface method
	method := p.parseInterfaceMethod()
	if method == nil {
		return nil
	}
	it.Methods = []*ast.InterfaceMethod{method}

	it.EndToken = p.currentToken

	return it
}

// parseInterfaceMethod parses a method signature for an interface
// Example: fn (self) read( buf: [*]Byte ) -> Result[u32, Error]
// Example: fn (self: *T) hook( _: Tag ) -> *ListHook[T, Tag]
func (p *Parser) parseInterfaceMethod() *ast.InterfaceMethod {
	method := &ast.InterfaceMethod{Token: p.currentToken}

	// We're already at 'fn', so parse the function signature
	// Parse receiver: (self) or (self: Type)
	if !p.expectPeek(token.LPAREN) {
		return nil
	}

	p.nextToken()
	if !p.currentTokenIs(token.IDENT) {
		return nil
	}

	// Check for receiver type annotation
	if p.peekTokenIs(token.COLON) {
		p.nextToken() // consume :
		p.nextToken() // consume type
		receiverType := p.parseTypeExpression()
		if receiverType == nil {
			return nil
		}
		method.ReceiverType = receiverType
	}

	if !p.expectPeek(token.RPAREN) {
		return nil
	}

	// Parse method name
	if !p.expectPeek(token.IDENT) {
		return nil
	}
	method.Name = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}

	// Parse parameters
	if !p.expectPeek(token.LPAREN) {
		return nil
	}
	method.Parameters = p.parseFunctionParameters()

	// Parse return type
	if !p.expectPeek(token.ARROW) {
		return nil
	}
	p.nextToken() // consume ->
	method.ReturnType = p.parseTypeExpression()
	if method.ReturnType == nil {
		return nil
	}

	return method
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

// Parse type expression: identifier, record type { field: Type, ... }, or array type [Type]
func (p *Parser) parseTypeExpression() ast.Expression {
	// Handle record type: { field: Type, ... }
	if p.currentTokenIs(token.LBRACE) {
		return p.parseRecordType()
	}

	// Handle array type: [Type] or [N]Type
	if p.currentTokenIs(token.LBRACK) {
		return p.parseArrayType()
	}

	// Handle unit type: ()
	if p.currentTokenIs(token.LPAREN) {
		if p.peekTokenIs(token.RPAREN) {
			// This is the unit type ()
			unitToken := p.currentToken
			p.nextToken() // consume (
			p.nextToken() // consume )
			return &ast.Identifier{Token: unitToken, Value: "()"}
		}
		// Otherwise, it might be a parenthesized type expression
		// For now, return nil - parenthesized types not yet supported
		return nil
	}

	// Handle identifier type
	if p.currentTokenIs(token.IDENT) {
		ident := &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
		// Note: We don't advance here - the caller is responsible for token management
		// This allows parseArrayType to check peekToken after parsing the element type
		return ident
	}

	// If we get here, we couldn't parse a type expression
	// This might happen if currentToken is not a valid type start token
	return nil
}

// Parse record type: { field: Type, field2: Type2, ... }
func (p *Parser) parseRecordType() ast.Expression {
	record := &ast.RecordLiteral{
		Token:  p.currentToken,
		Fields: make(map[string]ast.Expression),
	}

	// Skip opening brace (currentToken is {)
	p.nextToken()

	// Handle empty record type: {}
	if p.currentTokenIs(token.RBRACE) {
		record.EndToken = p.currentToken // } token
		p.nextToken()                    // consume }
		return record
	}

	// Parse fields until closing brace
	for {
		// Parse field name (identifier)
		if !p.currentTokenIs(token.IDENT) {
			p.peekError(token.IDENT)
			return nil
		}
		fieldName := p.currentToken.Literal

		// Expect colon
		if !p.expectPeek(token.COLON) {
			return nil
		}

		// Parse field type (not value - this is a type annotation)
		p.nextToken() // Advance past colon to the type
		fieldType := p.parseTypeExpression()
		if fieldType == nil {
			return nil
		}

		record.Fields[fieldName] = fieldType

		// Advance past the type expression
		// After parseTypeExpression returns, currentToken is the last token of the type
		// peekToken should be comma or closing brace
		if p.peekTokenIs(token.COMMA) {
			p.nextToken() // consume comma
			p.nextToken() // advance to next field
			continue
		}

		if p.peekTokenIs(token.RBRACE) {
			p.nextToken() // consume }
			record.EndToken = p.currentToken
			break
		}

		// Unexpected token
		p.peekError(token.RBRACE)
		return nil
	}

	return record
}

// Parse array type: [Type] or [N]Type
func (p *Parser) parseArrayType() ast.Expression {
	// Skip opening bracket (currentToken is [)
	p.nextToken()

	// Check for span type: [*]Type
	if p.currentTokenIs(token.MUL) {
		// This is a span type: [*]Type
		p.nextToken() // consume * - this advances to ]
		// Check for closing bracket
		if !p.currentTokenIs(token.RBRACK) {
			p.peekError(token.RBRACK)
			return nil
		}
		p.nextToken() // consume ] - this advances to the element type
		// Now parse the element type
		elementType := p.parseTypeExpression()
		if elementType == nil {
			return nil
		}
		// parseTypeExpression doesn't advance for identifiers, so if element type is an identifier,
		// we need to advance past it to position correctly for the caller
		if ident, ok := elementType.(*ast.Identifier); ok && ident.Value != "()" {
			// Advance past the identifier if we're still at it
			if p.currentTokenIs(token.IDENT) {
				p.nextToken()
			}
		}
		// Return as IndexExpression with "*" identifier for span
		return &ast.IndexExpression{
			Token: p.currentToken,
			Left:  elementType,
			Index: &ast.Identifier{Token: p.currentToken, Value: "*"},
		}
	}

	// Check for size: [N]Type
	var size *ast.IntegerLiteral
	if p.currentTokenIs(token.INT) {
		// Could be fixed-size array: [N]Type
		// But could also be array literal: [N, ...]
		// Check what comes after the integer
		size = p.parseIntegerLiteral().(*ast.IntegerLiteral)
		// parseIntegerLiteral doesn't advance, so currentToken is still the INT
		// Check peekToken to see if it's ] (array type) or , (array literal)
		if !p.peekTokenIs(token.RBRACK) {
			// Not an array type - this is an array literal
			// Don't reset here - let the caller handle it
			// Just return nil so caller knows to try parsing as value expression
			return nil
		}
		// Advance past the integer to get to the closing bracket
		p.nextToken() // advance past the size integer
		// Now currentToken should be ]
	}

	// Check if this is a slice type: []Type (no size, just closing bracket)
	if size == nil && p.currentTokenIs(token.RBRACK) {
		// This is a slice type: []Type
		// We need to advance past ] and then parse the element type
		p.nextToken() // consume ]
		// Now parse the element type
		elementType := p.parseTypeExpression()
		if elementType == nil {
			return nil
		}
		// parseTypeExpression doesn't advance for identifiers, so if element type is an identifier,
		// we need to advance past it to position correctly for the caller
		if ident, ok := elementType.(*ast.Identifier); ok && ident.Value != "()" {
			// Advance past the identifier if we're still at it
			if p.currentTokenIs(token.IDENT) {
				p.nextToken()
			}
		}
		// Return as IndexExpression with empty identifier for slice
		return &ast.IndexExpression{
			Token: p.currentToken,
			Left:  elementType,
			Index: &ast.Identifier{Token: p.currentToken, Value: ""},
		}
	}

	// This is a fixed-size array: [N]Type
	// After parsing the size, currentToken should be the closing bracket ]
	if size != nil {
		// Check for closing bracket after size
		if !p.currentTokenIs(token.RBRACK) {
			// Not an array type - likely an array literal
			// Return nil without error so caller can try parsing as value expression
			return nil
		}
		p.nextToken() // consume ] - this advances to the element type
		// Now currentToken should be the element type (IDENT, LBRACE, or LBRACK)
		elementType := p.parseTypeExpression()
		if elementType == nil {
			return nil
		}
		// parseTypeExpression doesn't advance for identifiers, so if element type is an identifier,
		// we need to advance past it to position correctly for the caller
		if ident, ok := elementType.(*ast.Identifier); ok && ident.Value != "()" {
			// Advance past the identifier if we're still at it
			if p.currentTokenIs(token.IDENT) {
				p.nextToken()
			}
		}
		// Return as IndexExpression with size as IntegerLiteral
		return &ast.IndexExpression{
			Token: p.currentToken,
			Left:  elementType,
			Index: size,
		}
	}

	// If we get here, we didn't match any array type pattern
	// This could be an array literal - return nil so caller can try parsing as value expression
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
	record := &ast.RecordLiteral{
		Token:  p.currentToken,
		Fields: make(map[string]ast.Expression),
	}

	// Skip opening brace (currentToken is {)
	p.nextToken()

	// Handle empty record: {}
	if p.currentTokenIs(token.RBRACE) {
		record.EndToken = p.currentToken // } token
		p.nextToken()                    // consume }
		return record
	}

	// Parse fields until closing brace
	for {
		// Parse field name (identifier)
		if !p.currentTokenIs(token.IDENT) {
			p.peekError(token.IDENT)
			return nil
		}
		fieldName := p.currentToken.Literal

		// Expect colon
		if !p.expectPeek(token.COLON) {
			return nil
		}

		// Parse field value
		p.nextToken() // Advance past colon to the value
		fieldValue := p.parseExpression(LOWEST)
		if fieldValue == nil {
			return nil
		}

		record.Fields[fieldName] = fieldValue

		// After parseExpression returns:
		// - For simple literals (string, int), currentToken is still the literal token
		//   (prefix parsers don't advance tokens)
		// - peekToken should be the comma or closing brace
		// We need to advance past the expression token to see what's next

		// Advance past the expression's last token
		p.nextToken()

		// Now currentToken should be comma or closing brace
		if p.currentTokenIs(token.COMMA) {
			p.nextToken() // Advance past comma to next field name
			// Continue loop - currentToken is now the next field name
		} else if p.currentTokenIs(token.RBRACE) {
			// We're done - closing brace consumed
			break
		} else {
			// Unexpected token - should be comma or closing brace
			// This might happen if expression parser consumed more than expected
			// Try to recover by checking peekToken
			if p.peekTokenIs(token.COMMA) {
				// We haven't advanced yet - do it now
				p.nextToken()
				p.nextToken()
				// Continue loop
			} else if p.peekTokenIs(token.RBRACE) {
				p.nextToken()
				p.nextToken()
				break
			} else {
				p.peekError(token.RBRACE)
				return nil
			}
		}
	}

	return record
}

// Array literal: [expr1, expr2, ...] or [N]Type{ expr1, expr2, ... }
func (p *Parser) parseArrayLiteral() ast.Expression {
	// Check if this is a typed array literal: [N]Type{ ... }
	// We need to peek ahead to see if it's [N]Type{ or just [ expr, ... ]
	// Save the opening bracket token
	openBracketToken := p.currentToken

	// Skip opening bracket (currentToken is [)
	p.nextToken()

	// Check if next token is an integer (array size)
	if p.currentTokenIs(token.INT) {
		// This might be [N]Type{ ... } - check ahead
		sizeToken := p.currentToken
		sizeValue := sizeToken.Literal

		// Check if next token after INT is ]
		if p.peekTokenIs(token.RBRACK) {
			// We have [N] - now check if after ] we have a type identifier and then {
			// Temporarily advance to see what's after ]
			p.nextToken() // move to ]
			p.nextToken() // move past ] to next token

			// Check if we have an identifier (type name) followed by {
			if p.currentTokenIs(token.IDENT) && p.peekTokenIs(token.LBRACE) {
				// This is [N]Type{ ... } - parse as typed array literal
				// Parse the size
				size, err := strconv.ParseInt(sizeValue, 10, 64)
				if err != nil {
					p.errors = append(p.errors, fmt.Sprintf("invalid array size: %s", sizeValue))
					return nil
				}
				sizeLit := &ast.IntegerLiteral{
					Token: sizeToken,
					Value: size,
				}

				// Parse element type
				elementType := &ast.Identifier{
					Token: p.currentToken,
					Value: p.currentToken.Literal,
				}

				return p.parseTypedArrayLiteral(sizeLit, elementType)
			}

			// Not a typed array literal - reset and parse as short array literal
			// Reset to the opening bracket
			p.currentToken = openBracketToken
			p.nextToken() // move past [
		}
	}

	// This is a short array literal: [ expr1, expr2, ... ]
	array := &ast.ArrayLiteral{
		Token:    openBracketToken,
		Elements: []ast.Expression{},
	}

	// Handle empty array: []
	if p.currentTokenIs(token.RBRACK) {
		p.nextToken() // consume ]
		return array
	}

	// Parse elements until closing bracket
	for {
		// Parse element expression
		elem := p.parseExpression(LOWEST)
		if elem == nil {
			return nil
		}
		array.Elements = append(array.Elements, elem)

		// After parseExpression, currentToken is the last token of the expression
		// peekToken should be comma or closing bracket
		// Check what comes next
		if p.peekTokenIs(token.COMMA) {
			p.nextToken() // Advance past expression token to comma
			p.nextToken() // Advance past comma to next element
			// Continue loop
		} else if p.peekTokenIs(token.RBRACK) {
			p.nextToken() // Advance past expression token to closing bracket
			p.nextToken() // Advance past closing bracket
			break
		} else {
			// Unexpected token
			p.peekError(token.RBRACK)
			return nil
		}
	}

	return array
}

// Parse typed array literal: [N]Type{ expr1, expr2, ... }
func (p *Parser) parseTypedArrayLiteral(size *ast.IntegerLiteral, elementType ast.Expression) ast.Expression {
	// Create array type expression
	arrayType := &ast.IndexExpression{
		Token: p.currentToken, // The [ token
		Left:  elementType,
		Index: size,
	}

	// Now parse the { ... } part
	if !p.expectPeek(token.LBRACE) {
		return nil
	}

	// Skip opening brace
	p.nextToken()

	// Create array literal with type
	array := &ast.ArrayLiteral{
		Token:    arrayType.Token,
		Elements: []ast.Expression{},
		Type:     arrayType, // Store the type
	}

	// Handle empty array: [4]u8{}
	if p.currentTokenIs(token.RBRACE) {
		p.nextToken() // consume }
		return array
	}

	// Parse elements until closing brace
	for {
		// Parse element expression
		elem := p.parseExpression(LOWEST)
		if elem == nil {
			return nil
		}
		array.Elements = append(array.Elements, elem)

		// Check what comes next
		if p.peekTokenIs(token.COMMA) {
			p.nextToken() // Advance past expression token to comma
			p.nextToken() // Advance past comma to next element
			// Continue loop
		} else if p.peekTokenIs(token.RBRACE) {
			p.nextToken() // Advance past expression token to closing brace
			p.nextToken() // Advance past closing brace
			break
		} else {
			// Unexpected token
			p.peekError(token.RBRACE)
			return nil
		}
	}

	return array
}

// Function statement (top-level function or method)
func (p *Parser) parseFunctionStatement() *ast.FunctionStatement {
	stmt := &ast.FunctionStatement{Token: p.currentToken}

	// Parse optional type parameters: fn [T: Reader, U: Writer] name(...)
	if p.peekTokenIs(token.LBRACK) {
		stmt.TypeParams = p.parseTypeParameters()
		if stmt.TypeParams == nil {
			return nil // Error already reported
		}
	}

	// Check if this is a method: fn (recv: Type) method(...)
	// vs regular function: fn name(...)
	if p.peekTokenIs(token.LPAREN) {
		// Look ahead to see if this is a receiver: fn ( ident : type )
		p.nextToken() // consume (
		if !p.expectPeek(token.IDENT) {
			return nil
		}
		// Save the identifier token before consuming it
		recvIdentToken := p.peekToken
		p.nextToken() // consume identifier, now currentToken is IDENT
		if p.peekTokenIs(token.COLON) {
			// This is a receiver: fn (recv: Type)
			receiver := &ast.FunctionParameter{
				Token: recvIdentToken, // Save the IDENT token
				Name:  &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal},
			}
			p.nextToken() // consume :
			p.nextToken() // consume type identifier
			receiver.Type = p.parseTypeExpression()
			if !p.expectPeek(token.RPAREN) {
				return nil
			}
			stmt.Receiver = receiver
			// Now parse method name
			if !p.expectPeek(token.IDENT) {
				return nil
			}
			stmt.Name = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
		} else {
			// Not a receiver, this is a regular function
			// Backtrack: we consumed ( and IDENT, but this is not a receiver
			// This shouldn't happen with our syntax, but handle it
			return nil
		}
	} else {
		// Regular function: fn name(...)
		if !p.expectPeek(token.IDENT) {
			return nil
		}
		stmt.Name = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
	}

	// Parse parameters
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

	// Set end token to the last token of the body
	// For expressions, this is the expression's last token
	// For blocks, we'd need to track the closing brace
	stmt.EndToken = p.currentToken

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

// parseTypeParameters parses a type parameter list: [T, U: Reader, V: Writer & Closer]
// Returns a list of TypeParameter nodes
func (p *Parser) parseTypeParameters() []*ast.TypeParameter {
	params := []*ast.TypeParameter{}

	if !p.expectPeek(token.LBRACK) {
		return nil
	}

	// Check for empty list: []
	if p.peekTokenIs(token.RBRACK) {
		p.nextToken() // consume ]
		return params
	}

	p.nextToken() // consume first type param name

	// Parse first type parameter
	param := p.parseTypeParameter()
	if param == nil {
		return nil
	}
	params = append(params, param)

	// Parse remaining type parameters
	for p.peekTokenIs(token.COMMA) {
		p.nextToken() // consume comma
		p.nextToken() // consume next type param name
		param := p.parseTypeParameter()
		if param == nil {
			return nil
		}
		params = append(params, param)
	}

	if !p.expectPeek(token.RBRACK) {
		return nil
	}

	return params
}

// parseTypeParameter parses a single type parameter: T or T: Constraint
// Constraint can be a single interface or intersection: Reader & Writer
func (p *Parser) parseTypeParameter() *ast.TypeParameter {
	param := &ast.TypeParameter{
		Token: p.currentToken,
		Name:  &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal},
	}

	// Check for constraint: T: Constraint
	if p.peekTokenIs(token.COLON) {
		p.nextToken() // consume :
		p.nextToken() // consume constraint start

		// Parse constraint expression (can be identifier or intersection)
		constraint := p.parseConstraintExpression()
		if constraint == nil {
			return nil
		}
		param.Constraint = constraint
	}

	return param
}

// parseConstraintExpression parses a constraint: Interface or Interface1 & Interface2 & ...
// This is essentially a type expression that can use intersection
func (p *Parser) parseConstraintExpression() ast.Expression {
	// Start with first interface name
	first := p.parseTypeExpression()
	if first == nil {
		return nil
	}

	// Check for intersection: & Interface2 & ...
	if !p.peekTokenIs(token.AMP) {
		return first
	}

	// Parse intersection: Interface1 & Interface2 & ...
	// We'll represent this as a chain of infix expressions with &
	// For now, parse as a left-associative chain
	left := first
	for p.peekTokenIs(token.AMP) {
		p.nextToken() // consume &
		p.nextToken() // consume next interface name
		right := p.parseTypeExpression()
		if right == nil {
			return nil
		}
		// Create intersection expression
		left = &ast.InfixExpression{
			Token:    p.currentToken,
			Left:     left,
			Operator: "&",
			Right:    right,
		}
	}

	return left
}

// parseTypeExpressionSimple parses a simple type expression (identifier only)
// Used for function parameters and return types
func (p *Parser) parseTypeExpressionSimple() ast.Expression {
	if !p.currentTokenIs(token.IDENT) {
		return nil
	}
	return &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
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
	// Empty block returns unit type ()
	return &ast.Identifier{Token: block.Token, Value: "()"}
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

// parseREPLCommand parses REPL directives like :exit, :quit, :help
func (p *Parser) parseREPLCommand() *ast.REPLCommand {
	stmt := &ast.REPLCommand{Token: p.currentToken}

	// Expect an identifier after the colon
	if !p.expectPeek(token.IDENT) {
		p.errors = append(p.errors, "expected REPL command name after ':' (exit, quit, help, clear, reset)")
		return nil
	}

	commandName := p.currentToken.Literal
	// Validate command name
	validCommands := map[string]bool{
		"exit":   true,
		"quit":   true,
		"help":   true,
		"clear":  true,
		"reset":  true,
		"typeof": true,
	}
	if !validCommands[commandName] {
		p.errors = append(p.errors, fmt.Sprintf("unknown REPL command: %s (valid: exit, quit, help, clear, reset, typeof)", commandName))
		return nil
	}

	stmt.Name = commandName

	// Parse arguments for commands that take them (e.g., typeof(expr))
	if commandName == "typeof" {
		if p.peekTokenIs(token.LPAREN) {
			p.nextToken() // consume (
			// typeof() can accept both value expressions and type expressions
			// We need to distinguish between array types and array literals
			// Strategy: try type expression first, but if it fails or positions incorrectly, try value expression
			var expr ast.Expression
			p.nextToken() // advance to the first token of the expression
			
			// Save initial state for potential reset
			initialToken := p.currentToken
			initialPeek := p.peekToken
			initialErrorCount := len(p.errors)
			
			// Try parsing as type expression if it looks like one
			if p.currentTokenIs(token.LBRACK) || p.currentTokenIs(token.LBRACE) || p.currentTokenIs(token.IDENT) || p.currentTokenIs(token.LPAREN) {
				expr = p.parseTypeExpression()
				newErrorCount := len(p.errors)
				
				// Check if we successfully parsed and are positioned at the closing paren
				if expr != nil && (p.currentTokenIs(token.RPAREN) || p.peekTokenIs(token.RPAREN)) {
					// Success! Advance to closing paren if needed
					if p.peekTokenIs(token.RPAREN) {
						p.nextToken() // advance to )
					}
				} else {
					// Parsing failed or wrong position - this might be a value expression
					// Reset token position and clear any errors from type expression parsing
					expr = nil
					p.currentToken = initialToken
					p.peekToken = initialPeek
					// Remove errors added during failed type expression parsing
					// But keep original errors if any
					if newErrorCount > initialErrorCount {
						p.errors = p.errors[:initialErrorCount]
					}
				}
			}
			
			// If type expression parsing didn't work, try value expression
			if expr == nil {
				expr = p.parseExpression(LOWEST)
				if expr != nil {
					// After parseExpression, currentToken is at the last token of the expression
					// peekToken should be the closing paren. Advance to it if needed.
					if p.peekTokenIs(token.RPAREN) {
						p.nextToken() // advance to )
					}
				}
			}
			
			if expr == nil {
				p.errors = append(p.errors, "expected expression or type in typeof()")
				return nil
			}
			
			// Now consume the closing paren
			if !p.currentTokenIs(token.RPAREN) {
				p.errors = append(p.errors, "expected ')' after expression in typeof()")
				return nil
			}
			p.nextToken() // consume )
			stmt.Args = []ast.Expression{expr}
		}
	}

	return stmt
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

	p.nextToken() // consume =, now currentToken is =
	// Now peekToken is the first token of the value expression
	// Don't call nextToken() here - parseExpression will handle token advancement
	stmt.Value = p.parseExpression(LOWEST)

	if p.peekTokenIs(token.SEMI) {
		p.nextToken()
	}

	return stmt
}

// Parse short variable declaration: a := value (type inference)
func (p *Parser) parseShortVariableDeclaration() *ast.VariableDeclaration {
	stmt := &ast.VariableDeclaration{Token: p.currentToken}

	// Name is current token (IDENT)
	stmt.Name = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}

	// Expect := operator
	if !p.expectPeek(token.COLON_ASSIGN) {
		return nil
	}

	// Parse value (type will be inferred)
	p.nextToken() // consume :=, now currentToken is :=
	// Now peekToken is the first token of the value expression
	// Don't call nextToken() here - parseExpression will handle token advancement
	stmt.Value = p.parseExpression(LOWEST)
	stmt.Type = nil // Type inference

	if p.peekTokenIs(token.SEMI) {
		p.nextToken()
	}

	return stmt
}
