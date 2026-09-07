package parser

import (
	"fmt"
	"strconv"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/token"
	"github.com/SCKelemen/oak/util"
)

type Parser struct {
	source       token.Source
	currentToken token.Token
	peekToken    token.Token

	diagnostics *diagnostic.DiagnosticCollector

	prefixParseFns map[token.TokenKind]prefixParseFn
	infixParseFns  map[token.TokenKind]infixParseFn

	// postfixParseFns map[token.TokenKind]postfixParseFn

	// Collected trivia tokens that will be attached to the next non-trivia node
	pendingTrivia []token.Token

	// braceLiteralDisabled suppresses the TypeName { ... } composite-literal
	// infix while parsing a statement-header expression (a while condition),
	// where '{' opens the statement's block — Go's composite-literal rule.
	braceLiteralDisabled bool
}

func New(source token.Source) *Parser {
	p := &Parser{
		source:        token.NewCursor(source),
		diagnostics:   diagnostic.NewDiagnosticCollector(),
		pendingTrivia: []token.Token{},
	}

	// register functions
	p.prefixParseFns = make(map[token.TokenKind]prefixParseFn)
	p.registerPrefix(token.IDENT, p.parseIdentifier)
	p.registerPrefix(token.INT, p.parseIntegerLiteral)
	p.registerPrefix(token.STRING, p.parseStringLiteral)
	p.registerPrefix(token.BANG, p.parsePrefixExpression)
	p.registerPrefix(token.NEG, p.parsePrefixExpression)
	p.registerPrefix(token.AMP, p.parsePrefixExpression) // address-of operator: &value
	p.registerPrefix(token.TRUE, p.parseBoolean)
	p.registerPrefix(token.DOT, p.parseDotVariantExpression)
	p.registerPrefix(token.FALSE, p.parseBoolean)
	p.registerPrefix(token.LPAREN, p.parseExpressionGroup)
	p.registerPrefix(token.STRUCT, p.parseStructLiteral)
	p.registerPrefix(token.LBRACE, p.parseRecordLiteral)
	p.registerPrefix(token.LBRACK, p.parseArrayLiteral)
	p.registerPrefix(token.FN, p.parseFunctionLiteral)

	p.infixParseFns = make(map[token.TokenKind]infixParseFn)
	p.registerInfix(token.SUM, p.parseInfixExpression)
	p.registerInfix(token.NEG, p.parseInfixExpression)
	p.registerInfix(token.MUL, p.parseInfixExpression)
	p.registerInfix(token.QUO, p.parseInfixExpression)
	p.registerInfix(token.EQL, p.parseInfixExpression)
	p.registerInfix(token.LAND, p.parseInfixExpression)
	p.registerInfix(token.LOR, p.parseInfixExpression)
	p.registerInfix(token.NEQL, p.parseInfixExpression)
	p.registerInfix(token.LCHEV, p.parseInfixExpression)
	p.registerInfix(token.LEQ, p.parseInfixExpression)
	p.registerInfix(token.GEQ, p.parseInfixExpression)
	p.registerInfix(token.RCHEV, p.parseInfixExpression)
	p.registerInfix(token.QMARK, p.parseMatchExpression)
	p.registerInfix(token.LPAREN, p.parseInvocationExpression)
	p.registerInfix(token.DOT, p.parseFieldAccess)
	p.registerInfix(token.LBRACK, p.parseIndexOrSliceExpression)
	p.registerInfix(token.LBRACE, p.parseTypeQualifiedLiteral)

	// load the first 2 tokens
	p.nextToken()
	p.nextToken()

	return p
}

// Errors returns errors as strings for backward compatibility
func (p *Parser) Errors() []string {
	errors := []string{}
	for _, d := range p.diagnostics.Errors() {
		errors = append(errors, d.Message)
	}
	return errors
}

// Diagnostics returns all diagnostics
func (p *Parser) Diagnostics() []*diagnostic.Diagnostic {
	return p.diagnostics.Diagnostics()
}

// AddDiagnostic adds a diagnostic to the parser
func (p *Parser) AddDiagnostic(d *diagnostic.Diagnostic) {
	p.diagnostics.AddDiagnostic(d)
}

// addErrorAtToken creates and adds a diagnostic from a token
func (p *Parser) addErrorAtToken(tok *token.Token, message string) {
	d := diagnostic.NewDiagnosticFromToken(tok, "parser", message)
	p.diagnostics.AddDiagnostic(d)
}

// addErrorAtCurrentToken creates and adds a diagnostic from the current token
func (p *Parser) addErrorAtCurrentToken(message string) {
	p.addErrorAtToken(&p.currentToken, message)
}

// addErrorAtPeekToken creates and adds a diagnostic from the peek token
func (p *Parser) addErrorAtPeekToken(message string) {
	p.addErrorAtToken(&p.peekToken, message)
}

func (p *Parser) registerPrefix(TokenKind token.TokenKind, fn prefixParseFn) {
	p.prefixParseFns[TokenKind] = fn
}

func (p *Parser) registerInfix(TokenKind token.TokenKind, fn infixParseFn) {
	p.infixParseFns[TokenKind] = fn
}

func (p *Parser) nextToken() {
	p.currentToken = p.peekToken
	p.peekToken = p.source.NextToken()

	// Skip ILLEGAL tokens and report errors
	// Note: zero-initialized tokens have TokenKind == 0 (ILLEGAL), but Line == 0 indicates uninitialized
	for p.currentToken.TokenKind == token.ILLEGAL && p.currentToken.Line > 0 {
		// Use the literal from the token (e.g., "unterminated block comment")
		errorMsg := p.currentToken.Literal
		if errorMsg == "" {
			errorMsg = fmt.Sprintf("illegal token at line %d, column %d", p.currentToken.Line, p.currentToken.Column)
		}
		p.addErrorAtToken(&p.currentToken, errorMsg)
		// Skip the illegal token and continue
		p.currentToken = p.peekToken
		p.peekToken = p.source.NextToken()
	}

	// Skip trivia and comment tokens for currentToken, collecting them as we go
	for p.currentToken.TokenKind == token.TRIVIA || p.currentToken.TokenKind == token.COMMENT {
		p.pendingTrivia = append(p.pendingTrivia, p.currentToken)
		p.currentToken = p.peekToken
		p.peekToken = p.source.NextToken()

		// Skip any ILLEGAL tokens that appear after trivia/comments
		for p.currentToken.TokenKind == token.ILLEGAL && p.currentToken.Line > 0 {
			errorMsg := p.currentToken.Literal
			if errorMsg == "" {
				errorMsg = fmt.Sprintf("illegal token at line %d, column %d", p.currentToken.Line, p.currentToken.Column)
			}
			p.addErrorAtToken(&p.currentToken, errorMsg)
			p.currentToken = p.peekToken
			p.peekToken = p.source.NextToken()
		}
	}

	// Skip ILLEGAL tokens in peekToken
	// Note: zero-initialized tokens have TokenKind == 0 (ILLEGAL), but Line == 0 indicates uninitialized
	for p.peekToken.TokenKind == token.ILLEGAL && p.peekToken.Line > 0 {
		errorMsg := p.peekToken.Literal
		if errorMsg == "" {
			errorMsg = fmt.Sprintf("illegal token at line %d, column %d", p.peekToken.Line, p.peekToken.Column)
		}
		p.addErrorAtToken(&p.peekToken, errorMsg)
		// Skip the illegal token
		p.peekToken = p.source.NextToken()
	}

	// Also skip trivia and comment tokens for peekToken
	for p.peekToken.TokenKind == token.TRIVIA || p.peekToken.TokenKind == token.COMMENT {
		p.pendingTrivia = append(p.pendingTrivia, p.peekToken)
		p.peekToken = p.source.NextToken()

		// Skip any ILLEGAL tokens that appear after trivia/comments
		for p.peekToken.TokenKind == token.ILLEGAL && p.peekToken.Line > 0 {
			errorMsg := p.peekToken.Literal
			if errorMsg == "" {
				errorMsg = fmt.Sprintf("illegal token at line %d, column %d", p.peekToken.Line, p.peekToken.Column)
			}
			p.addErrorAtToken(&p.peekToken, errorMsg)
			p.peekToken = p.source.NextToken()
		}
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
	// Only at statement level, not inside expressions
	// We check this before IDENT to catch :exit, :quit, etc.
	// But we need to be careful: if we have IDENT followed by COLON_ASSIGN (:=),
	// that's a variable declaration, not a REPL command
	if p.currentTokenIs(token.COLON) && p.peekTokenIs(token.IDENT) {
		// This could be a REPL command like :exit
		// But we need to check if it's actually := (which would be COLON_ASSIGN token)
		// Since := is a single token, if we see COLON here, it's not :=
		return p.parseREPLCommand()
	}

	// Each case guards against typed-nil pointers escaping into the
	// ast.Statement interface: a failed parse must return an untyped nil so
	// callers' nil checks hold and downstream stages never see nil nodes.
	switch p.currentToken.TokenKind {
	case token.PACKAGE:
		if stmt := p.parsePackageStatement(); stmt != nil {
			return stmt
		}
		return nil
	case token.IMPORT:
		if stmt := p.parseImportStatement(); stmt != nil {
			return stmt
		}
		return nil
	case token.TYPE:
		if stmt := p.parseADTType(); stmt != nil {
			return stmt
		}
		return nil
	case token.INTERFACE:
		if stmt := p.parseInterfaceType(); stmt != nil {
			return stmt
		}
		return nil
	case token.FN:
		if stmt := p.parseFunctionStatement(); stmt != nil {
			return stmt
		}
		return nil
	case token.WHILE:
		if stmt := p.parseWhileStatement(); stmt != nil {
			return stmt
		}
		return nil
	case token.UNSAFE:
		if stmt := p.parseUnsafeBlock(); stmt != nil {
			return stmt
		}
		return nil
	case token.IDENT:
		// Variable declarations and assignments:
		// - x := expr -> declaration with type inference (short declaration)
		// - x: T = expr -> declaration with type annotation
		// - x = expr -> assignment (must refer to existing variable)
		// - Name: type = ... -> type definition (ADT type)
		// - Name[E, Unit]: type = ... -> generic type definition
		if p.peekTokenIs(token.COLON_ASSIGN) {
			// Check if this is a type definition shorthand: Color := Red | Blue | Green
			// We need to peek ahead to see if it's followed by IDENT | IDENT pattern
			// Save the name for potential type definition
			name := &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
			// Consume := to check what follows
			p.nextToken() // consume :=, now currentToken is :=
			// Check if next token is IDENT followed by PIPE (variant list pattern)
			if p.peekTokenIs(token.IDENT) {
				// We need to check if the token after the IDENT is PIPE
				// We can't peek two ahead, so we'll advance and check
				p.nextToken() // advance to IDENT (first token of value)
				if p.peekTokenIs(token.PIPE) {
					// This is a type definition shorthand: Color := Red | Blue | Green
					// Convert to: Color: type = Red | Blue | Green
					// Parse as ADT type definition
					adt := &ast.ADTType{Token: name.Token, Name: name}
					adt.Variants = []*ast.ADTVariant{}

					// Parse first variant (we're already on it)
					variant := p.parseADTVariant()
					if variant == nil {
						return nil
					}
					adt.Variants = append(adt.Variants, variant)

					// Parse remaining variants
					for p.peekTokenIs(token.PIPE) {
						p.nextToken() // consume |
						p.nextToken() // next constructor name
						variant := p.parseADTVariant()
						if variant == nil {
							return nil
						}
						adt.Variants = append(adt.Variants, variant)
					}

					return adt
				}
				// Not a type definition, parse as variable declaration from current position
				// currentToken is already at the first token of the value expression (e.g., IDENT for ABCD)
				stmt := &ast.VariableDeclaration{Token: name.Token}
				stmt.Name = name
				stmt.Value = p.parseExpression(LOWEST)
				stmt.Type = nil
				return stmt
			}
			// Not starting with IDENT (value is not an identifier, e.g., x := 1 or x := { ... })
			// At line 242, we advanced to :=, so currentToken is :=
			// peekToken should be the first token of the value expression (e.g., INT for 1)
			// We need to advance past := to get to the value expression
			if !p.currentTokenIs(token.COLON_ASSIGN) {
				// This shouldn't happen - we should be at := here
				// But if we're not, maybe we're already at the value?
				if p.currentTokenIs(token.INT) || p.currentTokenIs(token.STRING) || p.currentTokenIs(token.LBRACE) || p.currentTokenIs(token.IDENT) {
					// We're already at the value, don't advance
				} else {
					p.addErrorAtCurrentToken(fmt.Sprintf("expected := or value expression, got %s", p.currentToken.TokenKind))
					return nil
				}
			} else {
				// We're at :=, peekToken should be the value expression token
				// Advance past := to the value
				// nextToken() sets currentToken = peekToken, so peekToken should already be the value
				if p.peekToken.TokenKind == token.EOF {
					p.addErrorAtCurrentToken("expected value expression after :=")
					return nil
				}
				p.nextToken() // advance past := to the value
				// After nextToken(), currentToken should be the first token of the value
			}
			stmt := &ast.VariableDeclaration{Token: name.Token}
			stmt.Name = name
			stmt.Value = p.parseExpression(LOWEST)
			stmt.Type = nil
			return stmt
		} else if p.peekTokenIs(token.COLON) {
			// Centralize IDENT ":" ... handling
			return p.parseIdentLedStatement()
		} else if p.peekTokenIs(token.LBRACK) && p.bracketGroupPrecedesColon() {
			// IDENT "[" ... "]" ":" is a generic type definition or annotated
			// declaration head: Name[E, Unit]: type = ...
			// Without the trailing ':', IDENT "[" starts an index or slice
			// expression statement (e.g. buf[0:8]) and falls through below.
			return p.parseIdentLedStatement()
		} else if p.peekTokenIs(token.ASSIGN) {
			// Assignment: x = expr (must refer to existing variable)
			return p.parseAssignmentStatement()
		} else if p.peekTokenIs(token.LPAREN) && p.callableDefinitionAhead() {
			// Colon-less definition form (docs/spec/10-syntax.md §3):
			// add(l: u32, r: u32): u32 = l + r
			name := &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
			p.nextToken() // move to '('
			fn := p.parseFunctionDefinitionFromName(name)
			if fn == nil {
				return nil
			}
			return fn
		}
		fallthrough
	default:
		stmt := p.parseExpressionStatement()
		if stmt == nil {
			return nil
		}
		// Index assignment: s[i] = value (docs/spec/50-borrowing.md: spans
		// and owners are writable; views are read-only).
		if target, ok := stmt.Expression.(*ast.IndexExpression); ok && p.peekTokenIs(token.ASSIGN) {
			p.nextToken() // move to '='
			assignToken := p.currentToken
			p.nextToken() // move to the value
			value := p.parseExpression(LOWEST)
			if value == nil {
				return nil
			}
			return &ast.IndexAssignmentStatement{Token: assignToken, Target: target, Value: value}
		}
		return stmt
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
		p.currentTokenIs(token.RBRACK) || p.currentTokenIs(token.PIPE) ||
		p.currentTokenIs(token.COLON) || p.currentTokenIs(token.COLON_ASSIGN) {
		// COLON_ASSIGN (:=) can't start an expression - it's an assignment operator
		return nil
	}

	prefix := p.prefixParseFns[p.currentToken.TokenKind]
	if prefix == nil {
		// Check if it's an infix operator that can't start an expression
		// (SUM/+ can't start expressions, but NEG/- can as unary minus)
		// AMP/& can start expressions as address-of, so it has a prefix parser
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
	// Stop if we see a comma, semicolon, closing paren, closing brace, closing bracket, or colon (these terminate expressions)
	// Colon terminates expressions because it's used in slice syntax [start:end] and type annotations
	// Also stop if precedence is too low
	// Note: We stop at commas and brackets to allow array/record literal parsers to handle them
	for !p.peekTokenIs(token.SEMI) && !p.peekTokenIs(token.COMMA) && !p.peekTokenIs(token.RPAREN) && !p.peekTokenIs(token.RBRACE) && !p.peekTokenIs(token.RBRACK) && !p.peekTokenIs(token.COLON) {
		// Type-qualified record construction: TypeName { field: value }.
		// Admitted only for an identifier receiver and outside statement
		// headers (Go's composite-literal rule), so 'while ready {' keeps
		// its block. Checked before the precedence gate: '{' carries no
		// operator precedence.
		if p.peekTokenIs(token.LBRACE) && !p.braceLiteralDisabled {
			if _, isIdent := leftExp.(*ast.Identifier); isIdent {
				p.nextToken() // move to '{'
				leftExp = p.parseTypeQualifiedLiteral(leftExp)
				if leftExp == nil {
					return nil
				}
				continue
			}
		}

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
		if p.currentTokenIs(token.SEMI) || p.currentTokenIs(token.COMMA) || p.currentTokenIs(token.RBRACE) {
			// These are always stop tokens
			break
		}
		// After an index expression currentToken is ']'; the expression
		// continues when an operator follows (v[i] < limit) — the loop head
		// decides from peekToken like everywhere else.
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
	// Check if this is a variant construction: .Variant or Type.Variant
	literal := p.currentToken.Literal
	if len(literal) > 0 && literal[0] == '.' {
		// This is a variant: .Ok
		return p.parseVariantExpression()
	}

	// Check if this might be Type.Variant (Type followed by DOT)
	// We'll check this in parseVariantExpression if needed
	// For now, return identifier and let field access handle Type.Variant
	return &ast.Identifier{Token: p.currentToken, Value: literal}
}

// parseDotVariantExpression parses bare variant construction in expression
// position: .Ok, .Some(value). The ADT is resolved from context (declared
// type, or unique variant name).
func (p *Parser) parseDotVariantExpression() ast.Expression {
	dotToken := p.currentToken
	if !p.expectPeek(token.IDENT) {
		return nil
	}
	expr := &ast.VariantExpression{Token: dotToken}
	expr.Variant = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
	if p.peekTokenIs(token.LPAREN) {
		p.nextToken() // move to '('
		p.nextToken() // move to the payload expression
		expr.Payload = p.parseExpression(LOWEST)
		if !p.expectPeek(token.RPAREN) {
			return nil
		}
	}
	return expr
}

// Parse variant expression: .Ok, .Some(value), or Type.Variant
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
		// Type.Variant form - current token is Type, next should be DOT
		expr.TypeName = &ast.Identifier{Token: p.currentToken, Value: literal}
		if !p.expectPeek(token.DOT) {
			// Not Type.Variant, treat as regular identifier
			return &ast.Identifier{Token: p.currentToken, Value: literal}
		}
		p.nextToken() // consume DOT
		if !p.expectPeek(token.IDENT) {
			return nil
		}
		p.nextToken() // consume variant name
		expr.Variant = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}

		// Check for payload: Type.Some(value)
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

	// Check if this is a radix literal (e.g., "16r1000", "2r1010")
	literal := p.currentToken.Literal
	if strings.ContainsAny(literal, "rR") {
		value, err := p.parseRadixLiteral(literal)
		if err != nil {
			p.addErrorAtCurrentToken(fmt.Sprintf("invalid radix literal %q: %v", literal, err))
			return nil
		}
		lit.Value = value
		return lit
	}

	value, err := strconv.ParseInt(literal, 10, 64)
	if err != nil {
		var msg string
		numErr, ok := err.(*strconv.NumError)
		if ok && numErr.Err == strconv.ErrRange {
			msg = fmt.Sprintf("integer literal out of range: %q", literal)
		} else {
			msg = fmt.Sprintf("could not parse %q as integer", literal)
		}
		p.addErrorAtCurrentToken(msg)
		return nil
	}

	lit.Value = value
	return lit
}

// parseRadixLiteral parses a radix literal like "16r1000" or "2r1010"
// Returns the integer value and nil error if successful, or 0 and error if not a radix literal or invalid
func (p *Parser) parseRadixLiteral(literal string) (int64, error) {
	// Find the 'r' or 'R' separator
	rIndex := -1
	for i, ch := range literal {
		if ch == 'r' || ch == 'R' {
			rIndex = i
			break
		}
	}
	if rIndex == -1 {
		return 0, fmt.Errorf("not a radix literal")
	}

	// Parse the radix (base)
	radixStr := util.NormalizeDigits(literal[:rIndex])
	radix, err := strconv.Atoi(radixStr)
	if err != nil {
		return 0, fmt.Errorf("invalid radix: %s", radixStr)
	}
	if radix < 2 || radix > 16 {
		return 0, fmt.Errorf("radix must be between 2 and 16, got %d", radix)
	}

	// Parse the digits after 'r' (skip the 'r' itself)
	digitsStr := util.NormalizeDigits(literal[rIndex+1:])
	if digitsStr == "" {
		return 0, fmt.Errorf("missing digits after radix separator")
	}
	if err := validateDigitSeparators(digitsStr); err != nil {
		return 0, err
	}
	digitsStrClean := strings.ReplaceAll(digitsStr, "_", "")
	if digitsStrClean == "" {
		return 0, fmt.Errorf("missing digits after radix separator")
	}

	// Convert from the given radix to int64
	value, err := strconv.ParseInt(digitsStrClean, radix, 64)
	if err != nil {
		if numErr, ok := err.(*strconv.NumError); ok && numErr.Err == strconv.ErrRange {
			return 0, fmt.Errorf("integer literal out of range for radix %d", radix)
		}
		return 0, fmt.Errorf("invalid digits for radix %d: %s", radix, digitsStrClean)
	}

	return value, nil
}

func validateDigitSeparators(digits string) error {
	prevUnderscore := false
	for i, ch := range digits {
		if ch != '_' {
			prevUnderscore = false
			continue
		}
		if i == 0 {
			return fmt.Errorf("digit separator '_' is not allowed at the beginning of digits")
		}
		if prevUnderscore {
			return fmt.Errorf("consecutive digit separators are not allowed")
		}
		prevUnderscore = true
	}
	if prevUnderscore {
		return fmt.Errorf("digit separator '_' is not allowed at the end of digits")
	}
	return nil
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
	args, ok := p.parseDelimited[*ast.Identifier](token.LPAREN, token.RPAREN, token.COMMA, false, func() (*ast.Identifier, bool) {
		return &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}, true
	})
	if !ok {
		return nil
	}
	return args
}
func (p *Parser) parseInvocationExpression(function ast.Expression) ast.Expression {
	exp := &ast.InvocationExpression{Token: p.currentToken, Function: function}
	// Inside parentheses a '{' can only be a composite literal, even when
	// the call sits in a statement header (Go's rule).
	wasDisabled := p.braceLiteralDisabled
	p.braceLiteralDisabled = false
	args, ok := p.parseDelimited[ast.Expression](
		token.LPAREN,
		token.RPAREN,
		token.COMMA,
		false,
		func() (ast.Expression, bool) {
			arg := p.parseExpression(LOWEST)
			return arg, arg != nil
		},
	)
	p.braceLiteralDisabled = wasDisabled
	if !ok {
		return nil
	}
	exp.Arguments = args
	return exp
}

// Parse field access: record.field
// Also handles Type.Variant (ADT constructor) - these are parsed as IndexExpression
// and converted to VariantExpression during type checking
func (p *Parser) parseFieldAccess(left ast.Expression) ast.Expression {
	// Record field access: record.field
	// Or ADT constructor: Type.Variant
	exp := &ast.IndexExpression{Token: p.currentToken, Left: left, Dot: true}
	p.nextToken()
	if !p.currentTokenIs(token.IDENT) {
		p.peekError(token.IDENT)
		return nil
	}
	exp.Index = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
	return exp
}

// parseIndexOrSliceExpression handles both array[index] and array[low:high] syntax
// This is a unified Pratt hook for '[' that pattern-matches on ':' to choose index vs slice
func (p *Parser) parseIndexOrSliceExpression(left ast.Expression) ast.Expression {
	tok := p.currentToken // '['
	p.nextToken()         // move to first token after '['

	// Case 1: a[:...] or a[:]
	if p.currentTokenIs(token.COLON) {
		// [:high] or [:]
		low := (ast.Expression)(nil)
		// skip ':'
		p.nextToken()
		var high ast.Expression
		if !p.currentTokenIs(token.RBRACK) {
			high = p.parseExpression(LOWEST)
			if high == nil {
				return nil
			}
		}
		if !p.expectPeek(token.RBRACK) {
			return nil
		}
		return &ast.SliceExpression{
			Token: tok,
			Seq:   left,
			Low:   low,
			High:  high,
		}
	}

	// Otherwise we expect an expression first: candidate for index or low bound.
	first := p.parseExpression(LOWEST)
	if first == nil {
		return nil
	}

	// Now inspect what comes next
	switch {
	case p.peekTokenIs(token.RBRACK):
		// a[expr] — index
		if !p.expectPeek(token.RBRACK) {
			return nil
		}
		return &ast.IndexExpression{
			Token: tok,
			Left:  left,
			Index: first,
		}
	case p.peekTokenIs(token.COLON):
		// a[expr:...]
		p.nextToken() // move to ':'
		p.nextToken() // move to start of high expr (or ']')
		var high ast.Expression
		if !p.currentTokenIs(token.RBRACK) {
			high = p.parseExpression(LOWEST)
			if high == nil {
				return nil
			}
		}
		if !p.expectPeek(token.RBRACK) {
			return nil
		}
		return &ast.SliceExpression{
			Token: tok,
			Seq:   left,
			Low:   first,
			High:  high,
		}
	default:
		// a[expr ???] – syntax error
		p.peekError(token.RBRACK)
		return nil
	}
}

func (p *Parser) parseBoolean() ast.Expression {
	return &ast.Boolean{Token: p.currentToken, Value: p.currentTokenIs(token.TRUE)}
}

func (p *Parser) ParseProgram() *ast.Program {
	program := &ast.Program{}
	program.Statements = []ast.Statement{}

	for p.currentToken.TokenKind != token.EOF {
		start := p.currentToken
		stmt := p.parseStatement()
		if stmt != nil {
			program.Statements = append(program.Statements, stmt)
		}
		// Check if currentToken is already at the start of the next statement
		// This can happen if parseStatement() left currentToken at the start of the next statement
		// (e.g., after parsing an ADT definition with variant lists)
		// In that case, we should NOT call p.nextToken() because we're already at the next statement
		// We detect this by checking if currentToken is a token that can start a statement
		// Note: trivia tokens are skipped by nextToken(), so if currentToken is TRIVIA,
		// we should call p.nextToken() to skip it and get to the actual next statement
		canStartStatement := (p.currentTokenIs(token.IDENT) ||
			p.currentTokenIs(token.FN) ||
			p.currentTokenIs(token.TYPE) ||
			p.currentTokenIs(token.INTERFACE) ||
			p.currentTokenIs(token.PACKAGE) ||
			p.currentTokenIs(token.IMPORT) ||
			p.currentTokenIs(token.WHILE) ||
			p.currentTokenIs(token.UNSAFE) ||
			p.currentTokenIs(token.COLON)) && // COLON for REPL commands like :exit
			!p.currentTokenIs(token.TRIVIA) &&
			!p.currentTokenIs(token.COMMENT)
		// A token can only be the START of the next top-level statement if it
		// sits on a later line than this statement began AND at the start of
		// its line (column 1): a statement-final identifier — a type name in
		// a value-less declaration, an identifier value, or an indented
		// final ADT variant — belongs to the statement just parsed and must
		// be advanced past, not re-parsed as a stray expression statement.
		// Always advance if peekToken is EOF, regardless of canStartStatement
		// This prevents infinite loops when currentToken looks like it can start a statement
		// but is actually the last token of the previous statement
		if !canStartStatement || p.currentToken.Line <= start.Line ||
			p.currentToken.Column != 1 || p.peekTokenIs(token.EOF) {
			// currentToken is not at the start of a statement (or is trivia), so advance it
			p.nextToken()
		}
		// Progress guard: if parseStatement made no token progress, force an advance to avoid infinite loops.
		// This keeps recovery moving on malformed or unsupported constructs.
		if p.currentToken.TokenKind == start.TokenKind &&
			p.currentToken.Line == start.Line &&
			p.currentToken.Column == start.Column &&
			p.currentToken.ByteStart == start.ByteStart &&
			p.currentToken.ByteEnd == start.ByteEnd &&
			p.currentToken.Literal == start.Literal {
			p.nextToken()
		}
		// If canStartStatement is true and peekToken is not EOF, currentToken is already at the start of the next statement,
		// so we don't call p.nextToken() - we'll parse it in the next iteration
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
		p.peekToken = p.source.NextToken()
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
	p.addErrorAtPeekToken(msg)
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
	CONDITION   // ? (match binds looser than any operator: x < 2 ? a | b)
	LOGICAL_OR  // ||
	LOGICAL_AND // &&
	EQUALITY    // ==
	COMPARE    // > or <
	SUMMATION  // +
	PRODUCT    // *
	PREFIX     // -x or !x
	INVOCATION // aka Call, myfunction(x)
	INDEX      // record.field or array[index] - highest precedence
)

func (p *Parser) noPrefixParseFn(t token.TokenKind) {
	msg := fmt.Sprintf("no prefix parse function defined for TokenKind %s", t)
	p.addErrorAtCurrentToken(msg)
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
	token.LOR:    LOGICAL_OR,
	token.LAND:   LOGICAL_AND,
	token.EQL:    EQUALITY,
	token.NEQL:   EQUALITY,
	token.LCHEV:  COMPARE,
	token.LEQ:    COMPARE,
	token.GEQ:    COMPARE,
	token.RCHEV:  COMPARE,
	token.NEG:    SUMMATION,
	token.SUM:    SUMMATION,
	token.MUL:    PRODUCT,
	token.QUO:    PRODUCT,
	token.LPAREN: INVOCATION,
	token.QMARK:  CONDITION, // the whole operator expression is the scrutinee
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
// This handles the "type Name: type = ..." syntax (when TYPE keyword is present).
// For "Name: type = ..." syntax, use parseADTTypeFromName instead.
func (p *Parser) parseADTType() *ast.ADTType {
	// currentToken is TYPE
	adt := &ast.ADTType{Token: p.currentToken}

	// Next should be IDENT (the type name)
	if !p.expectPeek(token.IDENT) {
		return nil
	}
	name := &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
	adt.Name = name

	// Parse optional type parameters: type Name[T: Ordered]: type = ...
	if p.peekTokenIs(token.LBRACK) {
		adt.TypeParams = p.parseTypeParameters()
		if adt.TypeParams == nil {
			return nil // Error already reported
		}
	}

	// Expect ':'
	if !p.expectPeek(token.COLON) {
		return nil
	}

	// Expect 'type'
	if !p.expectPeek(token.TYPE) {
		return nil
	}

	// Expect '='
	if !p.expectPeek(token.ASSIGN) {
		return nil
	}

	// Move to the first token of the body. Keep a leading `|` visible so
	// this prefix form follows the same constructor-list contract as
	// `Name: type = | ...`.
	p.nextToken()

	// Check if this is a semantic record, concrete struct, or record composition.
	// Both product forms go through the type parser; struct carries a distinct
	// STRUCT token so later semantic projection can select representation.
	if p.currentTokenIs(token.LBRACE) || p.currentTokenIs(token.STRUCT) {
		recordType := p.parseTypePrimary()
		if recordType == nil {
			return nil
		}
		variant := &ast.ADTVariant{
			Token:   p.currentToken,
			Name:    adt.Name,
			Literal: recordType,
		}
		adt.Variants = []*ast.ADTVariant{variant}
	} else if p.currentTokenIs(token.IDENT) {
		// Could be: TypeName (type alias) or TypeName & RecordType (composition)
		// Use parseTypeExpression which now handles intersections
		typeExpr := p.parseTypeExpression()
		if typeExpr == nil {
			return nil
		}
		// parseTypeExpression leaves currentToken at the last token of the type expression.
		// For "Point2 & { z: u8 }", currentToken is on '}' (last token of record type).
		// For "Point2", currentToken is on "Point2" (the identifier itself).

		// Check if it's an intersection (InfixExpression with &) or a simple type
		if infix, ok := typeExpr.(*ast.InfixExpression); ok && infix.Operator == "&" {
			// Record composition: TypeName & TypeName & { ... }
			// Store composition as a variant with the composition expression
			variant := &ast.ADTVariant{
				Token:   p.currentToken,
				Name:    adt.Name,
				Literal: typeExpr, // Store composition expression
			}
			adt.Variants = []*ast.ADTVariant{variant}
		} else {
			// Type alias: Name: type = OtherType
			// Parse as a variant with payload
			// parseTypeExpression leaves currentToken on the last token of the type.
			// For identifiers, that's the identifier itself, so we don't need to advance.
			variant := &ast.ADTVariant{
				Token:   p.currentToken,
				Name:    adt.Name,
				Payload: typeExpr, // Store type alias target
			}
			adt.Variants = []*ast.ADTVariant{variant}
		}
	} else {
		// Parse as ADT variants: | Variant1 | Variant2 | ...
		adt.Variants = []*ast.ADTVariant{}
		if p.currentTokenIs(token.PIPE) {
			p.nextToken() // first constructor name
		}
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
			p.addErrorAtCurrentToken(fmt.Sprintf("expected type name or record literal in composition, got %s", p.currentToken.Literal))
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
		p.addErrorAtCurrentToken(fmt.Sprintf("expected 'fn' in interface definition, got %s", p.currentToken.Literal))
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

	if p.peekTokenIs(token.COLON) {
		p.nextToken() // ':'
		p.nextToken() // payload type or literal tag
		switch p.currentToken.TokenKind {
		case token.INT, token.STRING:
			variant.Literal = p.parseLiteralExpression()
		default:
			variant.Payload = p.parseTypeExpression()
			if variant.Payload == nil {
				return nil
			}
			if p.peekTokenIs(token.ASSIGN) {
				p.nextToken() // '='
				p.nextToken() // default value
				variant.Literal = p.parseLiteralExpression()
				if variant.Literal == nil {
					return nil
				}
			}
		}
	} else if p.peekTokenIs(token.COLON_ASSIGN) {
		p.nextToken() // ':='
		p.nextToken() // inferred literal/default value
		variant.Literal = p.parseLiteralExpression()
		if variant.Literal == nil {
			return nil
		}
	}

	// An explicit result freezes constructor result indices:
	//     | Int: i64 => Expr[i64]
	// Constructors without this clause implicitly return the enclosing ADT
	// applied to its declared parameters.
	if p.peekTokenIs(token.FAT_ARROW) {
		p.nextToken() // '=>'
		p.nextToken() // first token of result type
		variant.Result = p.parseTypeExpression()
		if variant.Result == nil {
			p.addErrorAtCurrentToken("expected indexed constructor result type after '=>'")
			return nil
		}
	}

	// Contract: leave currentToken on the final token belonging to this
	// constructor and peekToken on the separator or following statement.
	return variant
}

// Parse type expression: identifier, record type { field: Type, ... }, struct{ ... }, array type [Type], or intersection Type1 & Type2
// parseTypeExpression parses type expressions like:
//
//	Point2
//	{ x: u8, y: u8 }
//	struct{ x: u8, y: u8 }
//	Point2 & { z: u8 }
//	(Point2 & Point3)
//
// Contract: It assumes currentToken is at the first token of the type
// and leaves currentToken at the last token of the type (does NOT advance beyond it).
func (p *Parser) parseTypeExpression() ast.Expression {
	// Debug: This should NEVER see TYPE as currentToken
	if p.currentTokenIs(token.TYPE) {
		p.addErrorAtCurrentToken(fmt.Sprintf("parseTypeExpression: routing bug - saw TYPE token (%q) at line %d. This should be handled by parseADTType/parseADTTypeFromName", p.currentToken.Literal, p.currentToken.Line))
		return nil
	}
	left := p.parseTypePrimary()
	if left == nil {
		return nil
	}

	// Handle left-associative intersections: T1 & T2 & T3
	for p.peekTokenIs(token.AMP) {
		p.nextToken() // move to '&'
		ampToken := p.currentToken

		p.nextToken() // move to start of RHS type
		right := p.parseTypePrimary()
		if right == nil {
			return nil
		}

		left = &ast.InfixExpression{
			Token:    ampToken,
			Left:     left,
			Operator: "&",
			Right:    right,
		}
		// Note: currentToken is whatever parseTypePrimary left us at
		// (the last token of `right`). We do not advance further here.
	}

	return left
}

// parseTypePrimary parses the "atomic" type forms: identifiers, records,
// struct{ ... }, array types, and parens/unit.
// Contract: Assumes currentToken is at the first token of the type,
// leaves currentToken at the last token of the type (does NOT advance beyond it).
func (p *Parser) parseTypePrimary() ast.Expression {
	switch p.currentToken.TokenKind {
	case token.STRUCT:
		return p.parseStructType()

	case token.LBRACE:
		return p.parseRecordType()

	case token.LBRACK:
		return p.parseArrayType()

	case token.LPAREN:
		openToken := p.currentToken
		if p.peekTokenIs(token.RPAREN) {
			p.nextToken() // move to ')'
			if p.peekTokenIs(token.ARROW) {
				// Nullary function type: () -> R
				p.nextToken() // move to '->'
				p.nextToken() // move to return type
				returnType := p.parseTypeExpression()
				if returnType == nil {
					return nil
				}
				return &ast.FunctionTypeExpression{Token: openToken, Return: returnType}
			}
			// Unit type: ()
			return &ast.Identifier{
				Token: openToken,
				Value: "()",
			}
		}
		// Parenthesized type (T), or function type (T1, T2, ...) -> R.
		p.nextToken() // move to inner type
		inner := p.parseTypeExpression()
		if inner == nil {
			return nil
		}
		parameters := []ast.Expression{inner}
		for p.peekTokenIs(token.COMMA) {
			p.nextToken() // move to ','
			p.nextToken() // move to next type
			next := p.parseTypeExpression()
			if next == nil {
				return nil
			}
			parameters = append(parameters, next)
		}
		if !p.expectPeek(token.RPAREN) {
			return nil
		}
		if p.peekTokenIs(token.ARROW) {
			p.nextToken() // move to '->'
			p.nextToken() // move to return type
			returnType := p.parseTypeExpression()
			if returnType == nil {
				return nil
			}
			return &ast.FunctionTypeExpression{Token: openToken, Parameters: parameters, Return: returnType}
		}
		if len(parameters) > 1 {
			p.addErrorAtCurrentToken("a parenthesized type list must be a function type: (T1, T2) -> R")
			return nil
		}
		// currentToken is ')', last token of the type
		return inner

	case token.TYPE:
		// TYPE keyword should never appear in a type expression
		// This is a routing bug - should have been handled by parseADTType/parseADTTypeFromName
		p.addErrorAtCurrentToken(fmt.Sprintf("parseTypePrimary: routing bug - saw TYPE token (%q) at line %d. This should be handled by parseADTType/parseADTTypeFromName. Current context suggests a variable declaration or type alias was incorrectly parsed as a type expression.", p.currentToken.Literal, p.currentToken.Line))
		return nil

	case token.IDENT:
		ident := &ast.Identifier{
			Token: p.currentToken,
			Value: p.currentToken.Literal,
		}
		// Qualified library type: c.Int32, c.Ptr, ... (docs/spec/92-ffi.md
		// section 2.1). The dotted name stays one identifier; the type
		// checker resolves the library member.
		if p.peekTokenIs(token.DOT) {
			p.nextToken() // move to '.'
			if !p.expectPeek(token.IDENT) {
				return nil
			}
			ident.Value = ident.Value + "." + p.currentToken.Literal
			return ident
		}
		// Check if this is a generic type: Name[TypeArg1, TypeArg2, ...]
		if p.peekTokenIs(token.LBRACK) {
			p.nextToken() // move to '['
			typeArgs, ok := p.parseDelimited[ast.Expression](
				token.LBRACK,
				token.RBRACK,
				token.COMMA,
				false,
				func() (ast.Expression, bool) {
					arg := p.parseTypeExpression()
					return arg, arg != nil
				},
			)
			if !ok {
				return nil
			}

			var result ast.Expression = ident
			for _, arg := range typeArgs {
				result = &ast.IndexExpression{
					Token: p.currentToken,
					Left:  result,
					Index: arg,
				}
			}
			return result
		}
		// Not a generic type - return identifier as-is
		// We do NOT advance here; caller/intersection loop
		// can decide when to step past the type.
		return ident

	default:
		msg := fmt.Sprintf("unexpected token in type expression: %s (%q)",
			p.currentToken.TokenKind, p.currentToken.Literal)
		p.addErrorAtCurrentToken(msg)
		return nil
	}
}

// parseRecordType parses a record *type*: { field: Type, field2: Type2, ... }
// Contract: Assumes currentToken is '{', consumes the closing '}' and leaves currentToken past it.
func (p *Parser) parseRecordType() ast.Expression {
	record := &ast.RecordLiteral{
		Token:  p.currentToken, // '{'
		Fields: make(map[string]ast.Expression),
	}

	// currentToken is '{'. Look ahead:
	if p.peekTokenIs(token.RBRACE) {
		p.nextToken() // move to '}'
		record.EndToken = p.currentToken
		// Leave currentToken at '}' (contract: parseTypePrimary leaves currentToken at last token)
		return record
	}

	// Move to first field name
	p.nextToken() // currentToken should be IDENT, RBRACE, or COMMA (leading comma)

	for {
		// Skip leading comma if present (allows: { , A: u32, B: u32 })
		if p.currentTokenIs(token.COMMA) {
			p.nextToken() // consume leading comma
		}

		// Check for closing brace (allows trailing comma: { A: u32, B: u32, })
		if p.currentTokenIs(token.RBRACE) {
			record.EndToken = p.currentToken
			// Leave currentToken at '}' (contract: parseTypePrimary leaves currentToken at last token)
			break
		}

		if !p.currentTokenIs(token.IDENT) {
			p.peekError(token.IDENT)
			return nil
		}
		fieldToken := p.currentToken
		fieldName := fieldToken.Literal

		if !p.expectPeek(token.COLON) {
			return nil
		}

		p.nextToken() // move to first token of field type
		fieldType := p.parseTypeExpression()
		if fieldType == nil {
			return nil
		}
		if !record.AddField(fieldToken, fieldName, fieldType) {
			p.addErrorAtCurrentToken(fmt.Sprintf("duplicate record field %q", fieldName))
			return nil
		}

		// parseTypeExpression() leaves currentToken at the last token of the field type.
		// For simple types like "u32", that's the identifier itself.
		// Next token should be ',' or '}' or another IDENT (for next field without comma).
		// We need to advance past the type to see what's next.
		p.nextToken() // advance past the type expression

		if p.currentTokenIs(token.COMMA) {
			p.nextToken() // move past ','
			// Continue loop - will handle leading comma on next iteration if present
			continue
		}

		if p.currentTokenIs(token.RBRACE) {
			record.EndToken = p.currentToken
			// Leave currentToken at '}' (contract: parseTypePrimary leaves currentToken at last token)
			break
		}

		// Allow fields without commas (newline-separated): { A: u32\n B: u32 }
		// If next token is IDENT, it's the next field name
		if p.currentTokenIs(token.IDENT) {
			// Continue loop - currentToken is already the next field name
			continue
		}

		// Anything else is a syntax error
		p.peekError(token.RBRACE)
		return nil
	}

	// After the loop, currentToken should be at the closing brace
	// (parseRecordType contract: leaves currentToken at '}' - last token of the type)
	// This matches the contract of parseTypePrimary/parseTypeExpression
	if !p.currentTokenIs(token.RBRACE) {
		// This shouldn't happen - we should have broken out of the loop when we saw '}'
		p.addErrorAtCurrentToken("parseRecordType: expected closing brace")
		return nil
	}
	record.EndToken = p.currentToken

	return record
}

// Parse struct type: struct{ field: Type, field2: Type2, ... }
func (p *Parser) parseStructType() ast.Expression {
	// currentToken is STRUCT
	structToken := p.currentToken
	p.nextToken() // consume struct

	// Expect opening brace
	if !p.currentTokenIs(token.LBRACE) {
		p.peekError(token.LBRACE)
		return nil
	}

	// Parse the record type (struct uses same syntax as record types)
	record := p.parseRecordType()
	if record == nil {
		return nil
	}

	// Mark this as a struct type by wrapping it or adding metadata
	// For now, we'll use the same RecordLiteral AST node but the STRUCT token
	// indicates it's a struct type
	if rl, ok := record.(*ast.RecordLiteral); ok {
		rl.Token = structToken // Use struct token instead of brace token
	}
	return record
}

// Parse struct literal: struct{ field: value, ... } (value context)
func (p *Parser) parseStructLiteral() ast.Expression {
	// currentToken is STRUCT
	structToken := p.currentToken
	p.nextToken() // consume struct

	// Expect opening brace
	if !p.currentTokenIs(token.LBRACE) {
		p.peekError(token.LBRACE)
		return nil
	}

	// Parse the record literal (struct uses same syntax as record literals)
	record := p.parseRecordLiteral()
	if record == nil {
		return nil
	}

	// Mark this as a struct literal by using the STRUCT token
	if rl, ok := record.(*ast.RecordLiteral); ok {
		rl.Token = structToken // Use struct token instead of brace token
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
		// parseTypeExpression leaves currentToken on the last token of the type.
		// For identifiers, that's the identifier itself.
		// We do NOT advance past it here - let the caller handle token positioning.
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
		// parseTypeExpression leaves currentToken on the last token of the type.
		// For identifiers, that's the identifier itself.
		// We do NOT advance past it here - let the caller handle token positioning.
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
		// parseTypeExpression leaves currentToken on the last token of the type.
		// For identifiers, that's the identifier itself.
		// We do NOT advance past it here - let the caller handle token positioning.
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

	// Contract: leaves currentToken ON the closing '}' (the last token of
	// the literal), like every other prefix/infix expression parser — the
	// Pratt loop and statement loop advance past it themselves.

	// Handle empty record: {}
	if p.currentTokenIs(token.RBRACE) {
		record.EndToken = p.currentToken // } token
		return record
	}

	// Parse fields until closing brace
	for {
		// Skip leading comma if present (allows: { , A: 1, B: 2 })
		if p.currentTokenIs(token.COMMA) {
			p.nextToken() // consume leading comma
		}

		// Check for closing brace (allows trailing comma: { A: 1, B: 2, })
		if p.currentTokenIs(token.RBRACE) {
			record.EndToken = p.currentToken
			break
		}

		// Parse field name (identifier)
		if !p.currentTokenIs(token.IDENT) {
			p.peekError(token.IDENT)
			return nil
		}
		fieldToken := p.currentToken
		fieldName := fieldToken.Literal

		// Expect colon (used for both type annotations and value assignments)
		if !p.expectPeek(token.COLON) {
			return nil
		}

		// Parse field value
		p.nextToken() // Advance past colon to the value
		fieldValue := p.parseExpression(LOWEST)
		if fieldValue == nil {
			return nil
		}

		if !record.AddField(fieldToken, fieldName, fieldValue) {
			p.addErrorAtCurrentToken(fmt.Sprintf("duplicate record field %q", fieldName))
			return nil
		}

		// After parseExpression returns:
		// - For simple literals (string, int), currentToken is still the literal token
		//   (prefix parsers don't advance tokens)
		// - peekToken should be the comma or closing brace
		// We need to advance past the expression token to see what's next

		// Advance past the expression's last token
		p.nextToken()

		// Now currentToken should be comma or closing brace
		if p.currentTokenIs(token.COMMA) {
			p.nextToken() // Advance past comma
			// Continue loop - will handle leading comma on next iteration if present
		} else if p.currentTokenIs(token.RBRACE) {
			// We're done - closing brace stays current (contract above)
			record.EndToken = p.currentToken
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
				record.EndToken = p.currentToken
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
	open := p.currentToken

	// Typed slice literal: []Type{ ... }.
	if p.lookaheadSignificant(1).TokenKind == token.RBRACK &&
		p.lookaheadSignificant(2).TokenKind == token.IDENT &&
		p.lookaheadSignificant(3).TokenKind == token.LBRACE {
		p.nextToken() // ]
		p.nextToken() // element type
		elementType := &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
		return p.parseTypedArrayLiteralWithToken(open, nil, elementType)
	}

	// Typed fixed array literal: [N]Type{ ... }.
	if p.lookaheadSignificant(1).TokenKind == token.INT &&
		p.lookaheadSignificant(2).TokenKind == token.RBRACK &&
		p.lookaheadSignificant(3).TokenKind == token.IDENT &&
		p.lookaheadSignificant(4).TokenKind == token.LBRACE {
		p.nextToken() // N
		sizeExpr := p.parseIntegerLiteral()
		size, ok := sizeExpr.(*ast.IntegerLiteral)
		if !ok || size == nil {
			return nil
		}
		p.nextToken() // ]
		p.nextToken() // element type
		elementType := &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
		return p.parseTypedArrayLiteralWithToken(open, size, elementType)
	}

	elements, ok := p.parseDelimited[ast.Expression](
		token.LBRACK,
		token.RBRACK,
		token.COMMA,
		false,
		func() (ast.Expression, bool) {
			element := p.parseExpression(LOWEST)
			return element, element != nil
		},
	)
	if !ok {
		return nil
	}
	return &ast.ArrayLiteral{Token: open, Elements: elements}
}

// Parse type-qualified literal: TypeName{ field: value, ... }
// This is called as an infix handler when we see TypeName {
func (p *Parser) parseTypeQualifiedLiteral(typeName ast.Expression) ast.Expression {
	// typeName is the left expression (the type identifier)
	// currentToken is LBRACE
	typeIdent, ok := typeName.(*ast.Identifier)
	if !ok {
		// Not a type-qualified literal - this shouldn't happen, but handle gracefully
		// Fall back to parsing as a regular record literal
		return p.parseRecordLiteral()
	}

	// Parse the record literal inside the braces
	// currentToken is LBRACE, parseRecordLiteral expects currentToken to be LBRACE
	record := p.parseRecordLiteral()
	if record == nil {
		return nil
	}

	// Attach the type name to the record literal
	if rl, ok := record.(*ast.RecordLiteral); ok {
		rl.TypeName = typeIdent
	}

	return record
}

// Parse typed array literal: [N]Type{ expr1, expr2, ... } or []Type{ expr1, expr2, ... }
// size can be nil for slice literals ([]Type{ ... })
// This is a wrapper that should not be called directly - use parseTypedArrayLiteralWithToken instead
// Kept for backward compatibility but will use a fallback token
func (p *Parser) parseTypedArrayLiteral(size *ast.IntegerLiteral, elementType ast.Expression) ast.Expression {
	// Fallback: try to use the element type's token as a reference
	// This is not ideal but maintains backward compatibility
	bracketToken := elementType.(*ast.Identifier).Token
	return p.parseTypedArrayLiteralWithToken(bracketToken, size, elementType)
}

// parseTypedArrayLiteralWithToken is the internal implementation that takes the bracket token
func (p *Parser) parseTypedArrayLiteralWithToken(bracketToken token.Token, size *ast.IntegerLiteral, elementType ast.Expression) ast.Expression {
	var index ast.Expression
	if size == nil {
		index = &ast.Identifier{Token: bracketToken, Value: ""}
	} else {
		index = size
	}
	arrayType := &ast.IndexExpression{Token: bracketToken, Left: elementType, Index: index}

	if !p.expectPeek(token.LBRACE) {
		return nil
	}
	elements, ok := p.parseDelimited[ast.Expression](
		token.LBRACE,
		token.RBRACE,
		token.COMMA,
		false,
		func() (ast.Expression, bool) {
			element := p.parseExpression(LOWEST)
			return element, element != nil
		},
	)
	if !ok {
		return nil
	}
	return &ast.ArrayLiteral{Token: bracketToken, Elements: elements, Type: arrayType}
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

	// Accept both:
	// - fn name(...): Type = body
	// - fn name(...) -> Type { body } / fn name(...) -> Type expr
	if !p.peekTokenIs(token.COLON) && !p.peekTokenIs(token.ARROW) {
		p.addErrorAtPeekToken("expected ':' or '->' before function return type")
		return nil
	}
	p.nextToken() // consume : or ->
	p.nextToken() // advance to type token (string, i32, etc.)
	stmt.ReturnType = p.parseTypeExpression()
	// parseTypeExpression advances past the type, so currentToken should be after the type
	// Check for supported function body forms:
	// - = expr
	// - { ... }
	// - trailing expression (single-expression body)
	if p.peekTokenIs(token.ASSIGN) {
		// Expression body: fn name(...): Type = expr
		p.nextToken() // consume =
		p.nextToken() // advance to body
		stmt.Body = p.parseExpression(LOWEST)
	} else if p.peekTokenIs(token.LBRACE) {
		// Block body: fn name(...): Type { ... }
		p.nextToken() // consume {
		stmt.Body = p.parseBlockExpression()
	} else {
		// Single-expression body without "=" or braces:
		// fn add(a: i32, b: i32) -> i32 a + b
		p.nextToken()
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
	params, ok := p.parseDelimited[*ast.FunctionParameter](token.LPAREN, token.RPAREN, token.COMMA, false, func() (*ast.FunctionParameter, bool) {
		param := &ast.FunctionParameter{
			Token: p.currentToken,
			Name:  &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal},
		}
		if !p.expectPeek(token.COLON) {
			return nil, false
		}
		p.nextToken()
		if p.currentTokenIs(token.ELLIPSIS) {
			// Variadic trailing parameter: rest: ...T (the element type).
			param.Variadic = true
			p.nextToken()
		}
		param.Type = p.parseTypeExpression()
		return param, true
	})
	if !ok {
		return nil
	}
	for i, param := range params {
		if param.Variadic && i != len(params)-1 {
			p.addErrorAtToken(&param.Token, "only the last parameter may be variadic")
			return nil
		}
	}
	return params
}

func (p *Parser) parseTypeParameters() []*ast.TypeParameter {
	if !p.expectPeek(token.LBRACK) {
		return nil
	}
	params, ok := p.parseDelimited[*ast.TypeParameter](token.LBRACK, token.RBRACK, token.COMMA, false, func() (*ast.TypeParameter, bool) {
		param := p.parseTypeParameter()
		return param, param != nil
	})
	if !ok {
		return nil
	}
	return params
}
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
// Every statement is retained so downstream checkers and backends see the
// whole body; the block's value is the trailing expression statement.
func (p *Parser) parseBlockExpression() ast.Expression {
	block := p.parseBlockStatement()
	return &ast.BlockExpression{Token: block.Token, Block: block}
}

// While statement
func (p *Parser) parseWhileStatement() *ast.WhileStatement {
	stmt := &ast.WhileStatement{Token: p.currentToken}

	p.nextToken()
	// The condition is a statement header: '{' after it opens the loop
	// body, never a composite literal.
	wasDisabled := p.braceLiteralDisabled
	p.braceLiteralDisabled = true
	stmt.Condition = p.parseExpression(LOWEST)
	p.braceLiteralDisabled = wasDisabled

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
		p.addErrorAtPeekToken("expected REPL command name after ':' (exit, quit, help, clear, reset)")
		return nil
	}

	commandName := p.currentToken.Literal
	// Validate command name
	validCommands := map[string]bool{
		"exit":    true,
		"quit":    true,
		"help":    true,
		"clear":   true,
		"reset":   true,
		"typeof":  true,
		"ptrsize": true,
		"intsize": true,
	}
	if !validCommands[commandName] {
		p.addErrorAtCurrentToken(fmt.Sprintf("unknown REPL command: %s (valid: exit, quit, help, clear, reset, typeof, ptrsize, intsize)", commandName))
		return nil
	}

	stmt.Name = commandName

	// Parse arguments for commands that take them
	if commandName == "ptrsize" || commandName == "intsize" {
		// These commands take an optional integer argument: :ptrsize(32) or :ptrsize()
		if p.peekTokenIs(token.LPAREN) {
			p.nextToken() // consume (
			if p.peekTokenIs(token.RPAREN) {
				// No argument: :ptrsize()
				p.nextToken()                  // consume )
				stmt.Args = []ast.Expression{} // empty args
			} else {
				// Parse integer argument
				p.nextToken() // advance to the integer
				if !p.currentTokenIs(token.INT) {
					p.addErrorAtCurrentToken(fmt.Sprintf("expected integer argument for :%s (e.g., :%s(32) or :%s(64))", commandName, commandName, commandName))
					return nil
				}
				intLit := p.parseIntegerLiteral()
				if intLit == nil {
					return nil
				}
				// Consume closing paren
				if !p.peekTokenIs(token.RPAREN) {
					p.addErrorAtPeekToken("expected ')' after integer argument")
					return nil
				}
				p.nextToken() // consume )
				stmt.Args = []ast.Expression{intLit}
			}
		}
		// If no parens, treat as no-arg version (just print current size)
	} else if commandName == "typeof" {
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
			initialErrorCount := len(p.diagnostics.Errors())

			// Try parsing as type expression if it looks like one
			if p.currentTokenIs(token.LBRACK) || p.currentTokenIs(token.LBRACE) || p.currentTokenIs(token.IDENT) || p.currentTokenIs(token.LPAREN) {
				expr = p.parseTypeExpression()
				newErrorCount := len(p.diagnostics.Errors())

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
					// Note: We can't easily rollback diagnostics, so we'll keep them
					// In a more sophisticated implementation, we'd snapshot/restore diagnostics
					_ = newErrorCount
					_ = initialErrorCount
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
				p.addErrorAtCurrentToken("expected expression or type in typeof()")
				return nil
			}

			// Now consume the closing paren
			if !p.currentTokenIs(token.RPAREN) {
				p.addErrorAtCurrentToken("expected ')' after expression in typeof()")
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
		if p.lookaheadSignificant(2).TokenKind == token.PIPE {
			// Braced arm list: ? { | pattern => expr | ... }
			p.nextToken() // consume {
			match.Arms = p.parseMatchArms()
			if !p.expectPeek(token.RBRACE) {
				return nil
			}
		} else {
			// Bool-condition sugar with a block true branch:
			// cond ? { stmts } [| else-branch]
			return p.parseConditionSugarArms(match)
		}
	} else if p.positionalArmsAhead() {
		// Bool-condition sugar: cond ? branch1 | branch2 (and the
		// leading-pipe multiline layout).
		return p.parseConditionSugarArms(match)
	} else {
		// Inline form: ? | pattern -> expr | ...
		match.Arms = p.parseMatchArms()
	}

	return match
}

// positionalArmsAhead reports whether the arms after '?' are the Bool
// condition sugar (docs/spec/10-syntax.md §3a): patternless branches
// separated by '|'. Detected by scanning the first arm segment — a
// depth-0 '|' before any '->'/'=>' means positional; an arrow means
// pattern arms. Leading pipes (multiline layout) are skipped.
func (p *Parser) positionalArmsAhead() bool {
	depth := 0
	leading := true
	const lookaheadLimit = 512
	for i := 1; i < lookaheadLimit; i++ {
		tok := p.lookaheadSignificant(i)
		switch tok.TokenKind {
		case token.PIPE:
			if leading {
				continue
			}
			if depth == 0 {
				return true
			}
		case token.ARROW, token.FAT_ARROW:
			if depth == 0 {
				return false
			}
		case token.LPAREN, token.LBRACK, token.LBRACE:
			depth++
		case token.RPAREN, token.RBRACK, token.RBRACE:
			depth--
			if depth < 0 {
				return false
			}
		case token.EOF:
			return false
		}
		leading = false
	}
	return false
}

// parseConditionSugarArms parses the Bool-condition sugar into ordinary
// true/false literal arms, so everything downstream sees one match form:
//
//	cond ? branch1 | branch2
//	cond ? | branch1 | branch2   (multiline layout)
//	cond ? { stmts } | { stmts } (block branches; else branch optional)
//
// currentToken is '?'.
func (p *Parser) parseConditionSugarArms(match *ast.MatchExpression) ast.Expression {
	qmark := p.currentToken

	// Multiline layout puts a leading '|' before the true branch.
	if p.peekTokenIs(token.PIPE) {
		p.nextToken()
	}
	trueBody := p.parseConditionBranch()
	if trueBody == nil {
		return nil
	}

	var falseBody ast.Expression
	if p.peekTokenIs(token.PIPE) {
		p.nextToken() // consume '|'
		falseBody = p.parseConditionBranch()
		if falseBody == nil {
			return nil
		}
	} else {
		// No else branch: the false arm is an empty (unit) block, so the
		// match stays exhaustive and statement-position use is natural.
		falseBody = &ast.BlockExpression{Token: qmark, Block: &ast.BlockStatement{Token: qmark}}
	}

	match.Arms = []*ast.MatchArm{
		{Token: qmark, Pattern: &ast.LiteralPattern{Token: qmark, Value: &ast.Boolean{Token: qmark, Value: true}}, Body: trueBody},
		{Token: qmark, Pattern: &ast.LiteralPattern{Token: qmark, Value: &ast.Boolean{Token: qmark, Value: false}}, Body: falseBody},
	}
	return match
}

// parseConditionBranch parses one sugar branch: a brace block or an
// expression. currentToken is the token before the branch.
func (p *Parser) parseConditionBranch() ast.Expression {
	if p.peekTokenIs(token.LBRACE) {
		p.nextToken() // move to '{'
		return p.parseBlockExpression()
	}
	p.nextToken() // move to the expression
	return p.parseExpression(LOWEST)
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

	// Accept both -> and => for pattern matching (canvas prefers =>)
	if !p.peekTokenIs(token.ARROW) && !p.peekTokenIs(token.FAT_ARROW) {
		p.peekError(token.ARROW)
		return nil
	}
	p.nextToken() // consume -> or =>
	p.nextToken() // advance to body token

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

		// Accept both -> and => for pattern matching (canvas prefers =>)
		if !p.peekTokenIs(token.ARROW) && !p.peekTokenIs(token.FAT_ARROW) {
			p.peekError(token.ARROW)
			return nil
		}
		p.nextToken() // consume -> or =>
		p.nextToken() // advance to body token

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
	// Check for .Variant shorthand (DOT followed by IDENT)
	if p.currentTokenIs(token.DOT) && p.peekTokenIs(token.IDENT) {
		// This is .Variant form - parse as variant pattern
		// We need to create a synthetic token with ".Variant" as the literal
		dotToken := p.currentToken
		p.nextToken() // consume DOT, now currentToken is IDENT
		// Create a variant pattern with the variant name
		pattern := &ast.VariantPattern{Token: dotToken}
		pattern.Variant = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
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

	switch p.currentToken.TokenKind {
	case token.IDENT:
		// Could be binding, variant, or Type.Variant
		// Check if this is Type.Variant (IDENT followed by DOT)
		if p.peekTokenIs(token.DOT) {
			// This could be Type.Variant - check if the identifier after DOT is capitalized
			// Save the type name
			typeNameToken := p.currentToken
			p.nextToken() // consume DOT
			if p.peekTokenIs(token.IDENT) {
				// This is Type.Variant form
				p.nextToken() // consume variant IDENT
				pattern := &ast.VariantPattern{Token: typeNameToken}
				pattern.TypeName = &ast.Identifier{Token: typeNameToken, Value: typeNameToken.Literal}
				pattern.Variant = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
				// Check for payload: Type.Some(x)
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
			// Not Type.Variant, backtrack (we consumed DOT and IDENT)
			// Actually, we can't easily backtrack, so this is an error
			p.addErrorAtCurrentToken("expected variant name after Type.")
			return nil
		}
		// Not Type.Variant, check if it's a bare variant
		if len(p.currentToken.Literal) > 0 && p.currentToken.Literal[0] >= 'A' && p.currentToken.Literal[0] <= 'Z' {
			// Capitalized identifier treated as variant (bare variant name)
			return p.parseVariantPattern()
		}
		// Binding pattern: x
		return &ast.BindingPattern{
			Token: p.currentToken,
			Name:  &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal},
		}
	case token.TRUE, token.FALSE:
		// Boolean literal patterns for the explicit conditional form:
		// cond ? | true => branch1 | false => branch2
		return &ast.LiteralPattern{
			Token: p.currentToken,
			Value: &ast.Boolean{Token: p.currentToken, Value: p.currentTokenIs(token.TRUE)},
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

// Variant pattern: .Ok | .Some(x) | Type.Variant
func (p *Parser) parseVariantPattern() ast.Pattern {
	pattern := &ast.VariantPattern{Token: p.currentToken}

	// Handle .Variant or Type.Variant
	var variantName string
	literal := p.currentToken.Literal
	if len(literal) > 0 && literal[0] == '.' {
		// .Variant form
		variantName = literal[1:]
		pattern.Variant = &ast.Identifier{Token: p.currentToken, Value: variantName}
	} else {
		// Might be Type.Variant - check if next token is DOT
		if p.peekTokenIs(token.DOT) {
			// Type.Variant form - store type name and variant name
			typeNameToken := p.currentToken
			pattern.TypeName = &ast.Identifier{Token: typeNameToken, Value: typeNameToken.Literal}
			p.nextToken() // consume DOT
			if !p.currentTokenIs(token.IDENT) {
				p.peekError(token.IDENT)
				return nil
			}
			variantName = p.currentToken.Literal
			pattern.Variant = &ast.Identifier{Token: p.currentToken, Value: variantName}
		} else {
			// Capitalized identifier treated as variant (bare variant name)
			variantName = literal
			pattern.Variant = &ast.Identifier{Token: p.currentToken, Value: variantName}
		}
	}

	// Check for payload: .Some(x) or Type.Some(x)
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

// bracketGroupPrecedesColon looks ahead, without consuming tokens, from a
// position where currentToken is IDENT and peekToken is '[': it reports
// whether the bracket group closes and is immediately followed by ':' —
// the shape of a generic type definition head (Name[E, Unit]: ...) as opposed
// to an index or slice expression statement (buf[0:8]).
func (p *Parser) bracketGroupPrecedesColon() bool {
	cursor, ok := p.source.(*token.Cursor)
	if !ok {
		// No lookahead available: preserve the historical routing.
		return true
	}
	depth := 1 // the '[' already sitting in peekToken
	offset := 0
	const lookaheadLimit = 4096
	for step := 0; step < lookaheadLimit; step++ {
		tok := cursor.Peek(offset)
		offset++
		switch tok.TokenKind {
		case token.LBRACK:
			depth++
		case token.RBRACK:
			depth--
			if depth == 0 {
				// Find the first significant token after the group.
				for step < lookaheadLimit {
					step++
					next := cursor.Peek(offset)
					offset++
					if next.TokenKind == token.TRIVIA || next.TokenKind == token.COMMENT {
						continue
					}
					return next.TokenKind == token.COLON
				}
				return false
			}
		case token.EOF:
			return false
		}
	}
	return false
}

// parameterListAhead looks ahead, without consuming tokens, from a position
// where currentToken is '(' after `name:`. It reports whether the group is a
// parameter list — a top-level colon before the matching ')', or an empty
// group whose ')' is followed by a return annotation (':' or '->').
func (p *Parser) parameterListAhead() bool {
	cursor, ok := p.source.(*token.Cursor)
	if !ok {
		return false
	}
	// The token stream position: currentToken is '(', peekToken is the first
	// token inside; cursor.Peek(0) is the token after peekToken.
	if p.peekTokenIs(token.RPAREN) {
		// Empty parameter list only when a return annotation follows.
		offset := 0
		const lookaheadLimit = 16
		for step := 0; step < lookaheadLimit; step++ {
			next := cursor.Peek(offset)
			offset++
			if next.TokenKind == token.TRIVIA || next.TokenKind == token.COMMENT {
				continue
			}
			return next.TokenKind == token.COLON || next.TokenKind == token.ARROW
		}
		return false
	}
	depth := 1
	if p.peekTokenIs(token.LPAREN) {
		depth++
	}
	if p.peekTokenIs(token.COLON) {
		return true
	}
	// Colons inside nested braces (record literals) or brackets (slices)
	// are not parameter annotations: f(Point { x: 1 }) and f(a[0:2]) are
	// calls, not signatures.
	braceDepth, bracketDepth := 0, 0
	if p.peekTokenIs(token.LBRACE) {
		braceDepth++
	}
	if p.peekTokenIs(token.LBRACK) {
		bracketDepth++
	}
	offset := 0
	const lookaheadLimit = 4096
	for step := 0; step < lookaheadLimit; step++ {
		tok := cursor.Peek(offset)
		offset++
		switch tok.TokenKind {
		case token.LPAREN:
			depth++
		case token.RPAREN:
			depth--
			if depth == 0 {
				return false
			}
		case token.LBRACE:
			braceDepth++
		case token.RBRACE:
			braceDepth--
		case token.LBRACK:
			bracketDepth++
		case token.RBRACK:
			bracketDepth--
		case token.COLON:
			if depth == 1 && braceDepth == 0 && bracketDepth == 0 {
				return true
			}
		case token.EOF:
			return false
		}
	}
	return false
}

// callableDefinitionAhead reports whether an IDENT-led statement whose next
// token is '(' is a colon-less function definition
// (docs/spec/10-syntax.md §3):
//
//	add(l: u32, r: u32): u32 = l + r
//
// rather than a call statement. The shape requires a parameter annotation
// colon at parenthesis depth 1 (outside nested braces/brackets), or an
// empty list, and a return annotation, '=', or block after the closing
// parenthesis. currentToken is the IDENT; peekToken is '('.
func (p *Parser) callableDefinitionAhead() bool {
	cursor, ok := p.source.(*token.Cursor)
	if !ok {
		return false
	}
	depth := 1
	braceDepth, bracketDepth := 0, 0
	sawAnnotation := false
	offset := 0
	const lookaheadLimit = 4096
	for step := 0; step < lookaheadLimit; step++ {
		tok := cursor.Peek(offset)
		offset++
		switch tok.TokenKind {
		case token.LPAREN:
			depth++
		case token.RPAREN:
			depth--
			if depth == 0 {
				// After the parameter list: a definition continues with a
				// return annotation, '=', or a brace block. Nullary shapes
				// require the annotation ('f() = x' and 'f() {' stay
				// expression territory).
				for rest := 0; rest < 16; rest++ {
					next := cursor.Peek(offset)
					offset++
					if next.TokenKind == token.TRIVIA || next.TokenKind == token.COMMENT {
						continue
					}
					switch next.TokenKind {
					case token.COLON, token.ARROW:
						return true
					case token.ASSIGN, token.LBRACE:
						return sawAnnotation
					default:
						return false
					}
				}
				return false
			}
		case token.LBRACE:
			braceDepth++
		case token.RBRACE:
			braceDepth--
		case token.LBRACK:
			bracketDepth++
		case token.RBRACK:
			bracketDepth--
		case token.COLON:
			if depth == 1 && braceDepth == 0 && bracketDepth == 0 {
				sawAnnotation = true
			}
		case token.EOF:
			return false
		}
	}
	return false
}

// parseFunctionDefinitionFromName parses the canonical declaration-form
// function definition. currentToken is '(' of the parameter list. Grouped
// names share one type: (a, b: i32, c: u8). The last group may be variadic.
func (p *Parser) parseFunctionDefinitionFromName(name *ast.Identifier) *ast.FunctionStatement {
	stmt := &ast.FunctionStatement{Token: name.Token, Name: name}

	// Parse parameter groups.
	params := []*ast.FunctionParameter{}
	if !p.peekTokenIs(token.RPAREN) {
		for {
			// Collect the group's names.
			group := []*ast.Identifier{}
			for {
				if !p.expectPeek(token.IDENT) {
					return nil
				}
				group = append(group, &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal})
				if p.peekTokenIs(token.COLON) {
					break
				}
				if !p.expectPeek(token.COMMA) {
					return nil
				}
			}
			if !p.expectPeek(token.COLON) {
				return nil
			}
			p.nextToken()
			variadic := false
			if p.currentTokenIs(token.ELLIPSIS) {
				variadic = true
				p.nextToken()
			}
			groupType := p.parseTypeExpression()
			if groupType == nil {
				return nil
			}
			if variadic && len(group) != 1 {
				p.addErrorAtCurrentToken("a variadic parameter group must name exactly one parameter")
				return nil
			}
			for _, groupName := range group {
				params = append(params, &ast.FunctionParameter{
					Token:    groupName.Token,
					Name:     groupName,
					Type:     groupType,
					Variadic: variadic,
				})
			}
			if p.peekTokenIs(token.RPAREN) {
				break
			}
			if !p.expectPeek(token.COMMA) {
				return nil
			}
		}
	}
	if !p.expectPeek(token.RPAREN) {
		return nil
	}
	for i, param := range params {
		if param.Variadic && i != len(params)-1 {
			p.addErrorAtToken(&param.Token, "only the last parameter may be variadic")
			return nil
		}
	}
	stmt.Parameters = params

	// Return annotation: ':' or '->'.
	if p.peekTokenIs(token.COLON) || p.peekTokenIs(token.ARROW) {
		p.nextToken()
		p.nextToken()
		stmt.ReturnType = p.parseTypeExpression()
		if stmt.ReturnType == nil {
			return nil
		}
	}

	// Body: '= expr', '= { block }', or a brace block.
	if p.peekTokenIs(token.ASSIGN) {
		p.nextToken()
		p.nextToken()
		if p.currentTokenIs(token.LBRACE) {
			// '= {' opens a block body: whole-body anonymous record
			// literals need a named form (docs/spec/10-syntax.md §3).
			stmt.Body = p.parseBlockExpression()
		} else {
			stmt.Body = p.parseExpression(LOWEST)
		}
	} else if p.peekTokenIs(token.LBRACE) {
		p.nextToken()
		stmt.Body = p.parseBlockExpression()
	} else {
		p.addErrorAtCurrentToken(fmt.Sprintf("function %s needs a definition: '= expression' or a brace block", name.Value))
		return nil
	}
	if stmt.Body == nil {
		return nil
	}
	stmt.EndToken = p.currentToken
	if symbol, ok := externBindingSymbol(stmt.Body); ok {
		stmt.ExternSymbol = symbol
	}
	return stmt
}

// externBindingSymbol recognizes the extern binding definition shape
// `c.extern("symbol")` (docs/spec/92-ffi.md section 2.3). Validation of the
// symbol and of the signature belongs to the type checker; the parser only
// records the shape.
func externBindingSymbol(body ast.Expression) (string, bool) {
	call, ok := body.(*ast.InvocationExpression)
	if !ok || len(call.Arguments) != 1 {
		return "", false
	}
	access, ok := call.Function.(*ast.IndexExpression)
	if !ok {
		return "", false
	}
	library, ok := access.Left.(*ast.Identifier)
	if !ok || library.Value != "c" {
		return "", false
	}
	member, ok := access.Index.(*ast.Identifier)
	if !ok || member.Value != "extern" {
		return "", false
	}
	symbol, ok := call.Arguments[0].(*ast.StringLiteral)
	if !ok {
		return "", false
	}
	return symbol.Value, true
}

// parseIdentLedStatement handles statements that start with IDENT ":" ...
// This centralizes routing between ADT type definitions and variable declarations.
func (p *Parser) parseIdentLedStatement() ast.Statement {
	// currentToken is IDENT (the name)
	identTok := p.currentToken
	name := &ast.Identifier{Token: identTok, Value: identTok.Literal}

	// Check if this is a generic type definition: Name[E, Unit]: type = ...
	// If peekToken is LBRACK, we need to parse the generic parameters first
	var typeParams []*ast.TypeParameter
	if p.peekTokenIs(token.LBRACK) {
		// This could be either:
		// 1. Generic type definition: Name[E, Unit]: type = ...
		// 2. Generic type application in variable: x: Name[E, Unit] = ...
		// We'll parse it and check what comes after the ]
		typeParams = p.parseTypeParameters()
		if typeParams == nil {
			return nil // Error already reported
		}
		// After parseTypeParameters, currentToken should be on the token after ]
		// For "Name[E, Unit]: type =", that should be COLON
	}

	// Expect colon - this advances currentToken to COLON and peekToken to next token
	if !p.expectPeek(token.COLON) {
		return nil
	}
	// After expectPeek(token.COLON):
	// - currentToken = COLON
	// - peekToken = token after COLON (should be TYPE for "Name: type =")

	// Look at the token *after* ':' by advancing
	p.nextToken()
	// After nextToken():
	// - currentToken = what was peekToken (should be TYPE for "Name: type =")
	// - peekToken = token after that

	if p.currentTokenIs(token.TYPE) {
		// We're in `Name: type = ...` or `Name[E, Unit]: type = ...` - ADT type definition
		adt := p.parseADTTypeFromName(name)
		if adt == nil {
			return nil
		}
		if len(typeParams) > 0 {
			// Attach the type parameters we parsed earlier
			adt.TypeParams = typeParams
		}
		return adt
	}

	// Canonical function definition (docs/spec/10-syntax.md section 3):
	// name: (params): Ret = body  /  name: (params) -> Ret = body.
	// A parenthesized group that is a parameter list (top-level colon inside,
	// or an empty group followed by a return annotation) defines a function;
	// anything else stays a type expression, so variables of function type
	// are unaffected.
	if p.currentTokenIs(token.LPAREN) && p.parameterListAhead() {
		fn := p.parseFunctionDefinitionFromName(name)
		if fn == nil {
			return nil
		}
		if len(typeParams) > 0 {
			fn.TypeParams = typeParams
		}
		return fn
	}

	// We're in `Name: <TypeExpr> (= ...)?` or `Name[E, Unit]: <TypeExpr> (= ...)?` - variable declaration
	// Safety check: this should never be TYPE at this point
	if p.currentTokenIs(token.TYPE) {
		p.addErrorAtCurrentToken(fmt.Sprintf("parseIdentLedStatement: routing bug - currentToken is TYPE after check, this should not happen for '%s'", name.Value))
		return nil
	}

	// Return an untyped nil on failure: a typed-nil *ast.VariableDeclaration
	// inside the ast.Statement interface would pass callers' nil checks and
	// crash downstream stages.
	if decl := p.parseVarDeclFromNameAndTypeStart(name); decl != nil {
		return decl
	}
	return nil
}

// parseADTTypeFromName parses an ADT type definition starting from the name.
// Assumes currentToken is TYPE (the "type" keyword).
func (p *Parser) parseADTTypeFromName(name *ast.Identifier) *ast.ADTType {
	adt := &ast.ADTType{Token: name.Token, Name: name}

	// We are currently on `type`
	// Check if the name had generic parameters: Name[E, Unit]: type = ...
	// This would have been parsed as a generic type application in parseTypePrimary
	// But we need to extract the type parameters from the name instead
	// For now, we'll check if peekToken is LBRACK (type parameters after 'type')
	// But actually, type parameters come BEFORE the colon: Name[E, Unit]: type = ...
	// So we need to check the name itself - but at this point name is just an Identifier
	// The generic syntax would have been parsed in parseIdentLedStatement before we got here
	// Actually, wait - if we have "Name[E, Unit]: type =", then in parseIdentLedStatement:
	// - currentToken starts as IDENT "Name"
	// - We check peekToken for COLON
	// - But if there's [E, Unit] between Name and :, we need to handle that

	// For now, check if there are type parameters after 'type' keyword
	// This handles: Name: type [T: Constraint] = ... (unusual but possible)
	// But the common case is: Name[T: Constraint]: type = ...
	// Which means we need to parse the [T: Constraint] BEFORE the colon

	// Actually, the issue is that when we have "Name[E, Unit]: type =",
	// parseIdentLedStatement sees "Name" as IDENT, then checks for COLON
	// But there's [E, Unit] between Name and :, so peekToken isn't COLON
	// So it doesn't match the "peekTokenIs(token.COLON)" check!

	// We need to handle: IDENT [ ... ] : type = ...
	// Let me check if the name identifier itself can have generic syntax
	// Actually, in parseIdentLedStatement, we're at IDENT "Name"
	// If peekToken is LBRACK, we should parse the generic part first
	// Then check what comes after the ]

	// For now, parse optional type parameters after 'type' keyword
	// This handles the case: Name: type [T: Constraint] = ... (unusual syntax)
	if p.peekTokenIs(token.LBRACK) {
		adt.TypeParams = p.parseTypeParameters()
		if adt.TypeParams == nil {
			return nil // Error already reported
		}
	}

	// Expect '=' after 'type'
	if !p.expectPeek(token.ASSIGN) {
		return nil
	}

	// Move to first token of body (after the '=' sign)
	p.nextToken()

	// Parse body: record type or variant list
	// Variant list can start with | (optional) or directly with variant name
	// Check for variant list: | Variant1 | Variant2 | ... OR Variant1 | Variant2 | ...
	isVariantList := false
	if p.currentTokenIs(token.PIPE) {
		// Leading pipe - definitely a variant list
		isVariantList = true
	} else if p.currentTokenIs(token.IDENT) && p.peekTokenIs(token.PIPE) {
		// IDENT followed by PIPE - variant list without leading pipe
		isVariantList = true
	} else if p.currentTokenIs(token.IDENT) && p.peekTokenIs(token.COLON) {
		// IDENT followed by COLON - a payload-carrying first variant without
		// a leading pipe: Shape: type = Circle: i32 | Square: i32 | Empty
		// (aliases are bare identifiers, records use braces, so the colon is
		// unambiguous here).
		isVariantList = true
	}

	if isVariantList {
		// Variant list: | Variant1 | Variant2 | ... OR Variant1 | Variant2 | ...
		adt.Variants = []*ast.ADTVariant{}

		// Skip leading pipe if present
		if p.currentTokenIs(token.PIPE) {
			p.nextToken() // consume leading |
		}

		// Parse first variant
		variant := p.parseADTVariant()
		if variant == nil {
			return nil
		}
		adt.Variants = append(adt.Variants, variant)

		// Parse remaining variants while the separator is the next token
		for p.peekTokenIs(token.PIPE) {
			p.nextToken() // consume |
			p.nextToken() // next constructor name
			variant := p.parseADTVariant()
			if variant == nil {
				return nil
			}
			adt.Variants = append(adt.Variants, variant)
		}
	} else if p.currentTokenIs(token.LBRACE) || p.currentTokenIs(token.STRUCT) {
		// Semantic records and concrete structs share product-type parsing. The
		// RecordLiteral AST retains the opening token: LBRACE means semantic shape;
		// STRUCT means a concrete representation policy was explicitly selected.
		recordType := p.parseTypePrimary()
		if recordType == nil {
			return nil
		}
		variant := &ast.ADTVariant{
			Token:   p.currentToken,
			Name:    adt.Name,
			Literal: recordType,
		}
		adt.Variants = []*ast.ADTVariant{variant}
	} else if p.currentTokenIs(token.IDENT) {
		// Could be: TypeName (type alias) or TypeName & RecordType (composition)
		// Use parseTypeExpression which now handles intersections
		typeExpr := p.parseTypeExpression()
		if typeExpr == nil {
			return nil
		}

		// Check if it's an intersection (InfixExpression with &) or a simple type
		if infix, ok := typeExpr.(*ast.InfixExpression); ok && infix.Operator == "&" {
			// Record composition: TypeName & TypeName & { ... }
			// Store composition as a variant with the composition expression
			variant := &ast.ADTVariant{
				Token:   p.currentToken,
				Name:    adt.Name,
				Literal: typeExpr, // Store composition expression
			}
			adt.Variants = []*ast.ADTVariant{variant}
		} else {
			// Type alias: Name: type = OtherType
			variant := &ast.ADTVariant{
				Token:   p.currentToken,
				Name:    adt.Name,
				Payload: typeExpr, // Store type alias target
			}
			adt.Variants = []*ast.ADTVariant{variant}
		}
	} else {
		// Unknown syntax
		p.addErrorAtCurrentToken(fmt.Sprintf("expected record type, type alias, or variant list after '=', got %s", p.currentToken.TokenKind))
		return nil
	}

	return adt
}

// parseVarDeclFromNameAndTypeStart parses a variable declaration starting from the type.
// Assumes currentToken is the first token of the type expression (after ':').
func (p *Parser) parseVarDeclFromNameAndTypeStart(name *ast.Identifier) *ast.VariableDeclaration {
	stmt := &ast.VariableDeclaration{Token: name.Token, Name: name}

	// Safety check: this should NEVER be called when currentToken is TYPE
	// If it is, routing is broken and we should have called parseADTTypeFromName instead
	if p.currentTokenIs(token.TYPE) {
		p.addErrorAtCurrentToken(fmt.Sprintf("parseVarDeclFromNameAndTypeStart: routing bug - saw TYPE token for variable '%s' at line %d. This should be handled by parseADTTypeFromName", name.Value, p.currentToken.Line))
		return nil
	}

	// Parse type annotation (currentToken is already the first token of the type)
	stmt.Type = p.parseTypeExpression()
	if stmt.Type == nil {
		return nil
	}

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

// Parse variable declaration: a: type = value or a: type
// This is kept for backward compatibility but should not be called directly
// from parseStatement - use parseIdentLedStatement instead.
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

	// expectPeek advanced past :=, so currentToken is now := (COLON_ASSIGN)
	// We need to advance one more time to get to the first token of the value expression
	p.nextToken() // advance past := to first token of value expression
	stmt.Value = p.parseExpression(LOWEST)
	stmt.Type = nil // Type inference

	if p.peekTokenIs(token.SEMI) {
		p.nextToken()
	}

	return stmt
}
