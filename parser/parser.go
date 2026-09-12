package parser

import (
	"fmt"
	"math"
	"strconv"
	"strings"
	"unicode"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/token"
	"github.com/SCKelemen/oak/util"
)

type Parser struct {
	source       token.Source
	currentToken token.Token
	peekToken    token.Token
	// blockDepth counts open statement blocks, so `defer` can be rejected
	// outside one; deferCounter names the temporaries that hold a block's
	// value while its deferred statements run.
	blockDepth   int
	deferCounter int

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
	// armDepth > 0 while parsing a bare-expression ?-match arm body, where
	// bare | is the arm separator, not bitwise or (parens re-enable).
	armDepth int
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
	p.registerPrefix(token.FLOAT, p.parseFloatLiteral)
	p.registerPrefix(token.STRING, p.parseStringLiteral)
	p.registerPrefix(token.BANG, p.parsePrefixExpression)
	p.registerPrefix(token.NEG, p.parsePrefixExpression)
	p.registerPrefix(token.AMP, p.parsePrefixExpression)   // address-of operator: &value
	p.registerPrefix(token.CARET, p.parsePrefixExpression) // bitwise complement: ^mask (Go-style)
	p.registerPrefix(token.TRUE, p.parseBoolean)
	p.registerPrefix(token.DOT, p.parseDotVariantExpression)
	p.registerPrefix(token.FALSE, p.parseBoolean)
	p.registerPrefix(token.LPAREN, p.parseExpressionGroup)
	p.registerPrefix(token.STRUCT, p.parseStructLiteral)
	p.registerPrefix(token.LBRACE, p.parseRecordLiteral)
	p.registerPrefix(token.LBRACK, p.parseArrayLiteral)
	p.registerPrefix(token.FN, p.parseFunctionLiteral)
	p.registerPrefix(token.IMPORT, p.parseImportExpression)
	p.registerPrefix(token.TYPE, p.parseTypeKindExpression)

	p.infixParseFns = make(map[token.TokenKind]infixParseFn)
	p.registerInfix(token.SUM, p.parseInfixExpression)
	p.registerInfix(token.AMP, p.parseInfixExpression)  // bitwise and
	p.registerInfix(token.PIPE, p.parseInfixExpression) // bitwise or (arm-separator rule: parenthesize inside ? arms)
	p.registerInfix(token.PIPE_FORWARD, p.parsePipelineExpression)
	p.registerInfix(token.CARET, p.parseInfixExpression) // bitwise xor
	p.registerInfix(token.SHL, p.parseInfixExpression)
	p.registerInfix(token.SHR, p.parseInfixExpression)
	p.registerInfix(token.NEG, p.parseInfixExpression)
	p.registerInfix(token.MUL, p.parseInfixExpression)
	p.registerInfix(token.QUO, p.parseInfixExpression)
	p.registerInfix(token.EQL, p.parseInfixExpression)
	p.registerInfix(token.REM, p.parseInfixExpression)
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
		p.addErrorAtToken(&p.currentToken, illegalTokenMessage(p.currentToken))
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
			p.addErrorAtToken(&p.currentToken, illegalTokenMessage(p.currentToken))
			p.currentToken = p.peekToken
			p.peekToken = p.source.NextToken()
		}
	}

	// Skip ILLEGAL tokens in peekToken
	// Note: zero-initialized tokens have TokenKind == 0 (ILLEGAL), but Line == 0 indicates uninitialized
	for p.peekToken.TokenKind == token.ILLEGAL && p.peekToken.Line > 0 {
		p.addErrorAtToken(&p.peekToken, illegalTokenMessage(p.peekToken))
		// Skip the illegal token
		p.peekToken = p.source.NextToken()
	}

	// Also skip trivia and comment tokens for peekToken
	for p.peekToken.TokenKind == token.TRIVIA || p.peekToken.TokenKind == token.COMMENT {
		p.pendingTrivia = append(p.pendingTrivia, p.peekToken)
		p.peekToken = p.source.NextToken()

		// Skip any ILLEGAL tokens that appear after trivia/comments
		for p.peekToken.TokenKind == token.ILLEGAL && p.peekToken.Line > 0 {
			p.addErrorAtToken(&p.peekToken, illegalTokenMessage(p.peekToken))
			p.peekToken = p.source.NextToken()
		}
	}
}

func (p *Parser) parseBlockStatement() *ast.BlockStatement {
	// A brace block restores '|' as bitwise or, wherever it sits inside a
	// ?-match arm (docs/spec/10-syntax.md section 3b).
	defer p.operatorPipe()()
	blocc := &ast.BlockStatement{Token: p.currentToken}
	blocc.Statements = []ast.Statement{}
	p.blockDepth++
	p.nextToken()
	for !p.currentTokenIs(token.RBRACE) && !p.currentTokenIs(token.EOF) {
		stmt := p.parseStatement()
		if stmt != nil {
			blocc.Statements = append(blocc.Statements, stmt)
		}
		p.nextToken()
	}
	p.blockDepth--
	p.desugarDefers(blocc)
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
	case token.BREAK:
		return &ast.BreakStatement{Token: p.currentToken}
	case token.DEFER:
		return p.parseDeferStatement()
	case token.UNSAFE:
		if stmt := p.parseUnsafeBlock(); stmt != nil {
			return stmt
		}
		return nil
	case token.PUB:
		if stmt := p.parsePubDeclaration(); stmt != nil {
			return stmt
		}
		return nil
	case token.LBRACE:
		if p.selectiveImportAhead() {
			if stmt := p.parseSelectiveImport(); stmt != nil {
				return stmt
			}
			return nil
		}
		// A bare `{ ... }` in statement position is a block statement with
		// a scope of its own (docs/spec/10-syntax.md section 4c), unless it
		// reads as record syntax — `{ x: 1, y: 2 }`, `{ r | name: string }`
		// — which the REPL and record tests evaluate as expressions.
		if p.recordLiteralAhead() {
			return p.parseExpressionStatementOrIndexAssignment()
		}
		return p.parseBlockStatement()
	case token.IDENT:
		// `open import(path)` binds every exported member unqualified
		// (docs/spec/83-modules.md section 3.2); `open` is contextual.
		if p.currentToken.Literal == "open" && p.peekTokenIs(token.IMPORT) {
			return p.parseOpenImport()
		}
		// `operator(SYM) name: (a: T, b: U): R = ...` binds SYM for a left
		// operand of type T (docs/spec/10-syntax.md section 14); `operator`
		// is contextual, so `operator := 1` stays an ordinary binding.
		if p.currentToken.Literal == "operator" && p.peekTokenIs(token.LPAREN) {
			return p.parseOperatorDeclaration()
		}
		// `kernel name: (gid: u32, ...): () = ...` declares a compute kernel
		// (docs/spec/56-kernels.md); `kernel` is contextual, so `kernel := 1`
		// and `kernel: u32 = 1` stay ordinary bindings.
		if p.currentToken.Literal == "kernel" && p.peekTokenIs(token.IDENT) && (p.lookaheadSignificant(2).TokenKind == token.COLON || p.lookaheadSignificant(2).TokenKind == token.LBRACK) {
			return p.parseKernelDeclaration()
		}
		// `export("symbol") pub name: (...)` gives a pub function a C ABI
		// symbol (docs/spec/92-ffi.md section 2.9); `export` is contextual,
		// so `export := 1` stays an ordinary binding.
		if p.currentToken.Literal == "export" && p.peekTokenIs(token.LPAREN) && p.lookaheadSignificant(2).TokenKind == token.STRING {
			return p.parseExportDeclaration()
		}
		// `module name { ... }` declares a nested module (section 3.5);
		// `module` is contextual, so `module := 1` stays an ordinary binding.
		if p.currentToken.Literal == "module" && p.peekTokenIs(token.IDENT) && p.lookaheadSignificant(2).TokenKind == token.LBRACE {
			return p.parseModuleDeclaration()
		}
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
		} else if p.peekTokenIs(token.ASSIGN) && p.currentToken.Literal == "_" {
			// Explicit discard: _ = expr (docs/spec/85-discipline.md §6)
			return p.parseDiscardStatement()
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
		return p.parseExpressionStatementOrIndexAssignment()
	}
}

// parseExpressionStatementOrIndexAssignment is the statement fallback: an
// expression statement, or an index/field assignment when '=' follows.
func (p *Parser) parseExpressionStatementOrIndexAssignment() ast.Statement {
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
		p.currentTokenIs(token.PIPE_FORWARD) ||
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
			if _, isIdent := leftExp.(*ast.Identifier); isIdent || p.qualifiedTypeReceiver(leftExp) {
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

		// A '.' opening a NEW LINE starts a bare-variant expression (a new
		// statement), never a continuation of the previous line: a
		// statement-final call followed by `.Some(v)` must not glue into a
		// member access on the call's result.
		if p.peekTokenIs(token.DOT) && p.peekToken.Line != p.currentToken.Line {
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
	name := p.currentToken.Literal
	first, _ := firstRune(name)
	if unicode.IsLower(first) {
		return &ast.FieldAccessorExpression{
			Token: dotToken,
			Field: &ast.Identifier{Token: p.currentToken, Value: name},
		}
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

// parseFloatLiteral parses a FLOAT token (docs/spec/20-types.md section
// 11.3.2). The text is kept for width-correct rounding in the typechecker;
// a literal that does not even fit f64 is rejected here.
func (p *Parser) parseFloatLiteral() ast.Expression {
	lit := &ast.FloatLiteral{Token: p.currentToken, Text: p.currentToken.Literal}
	value, err := strconv.ParseFloat(lit.Text, 64)
	if err != nil {
		if numErr, ok := err.(*strconv.NumError); ok && numErr.Err == strconv.ErrRange && !math.IsInf(value, 0) {
			// Underflow to zero or a subnormal is the IEEE result, not an error.
			lit.Value = value
			return lit
		}
		p.addErrorAtCurrentToken(fmt.Sprintf("floating-point literal out of range: %q", lit.Text))
		return nil
	}
	lit.Value = value
	return lit
}

// illegalTokenMessage explains an illegal token; the scanner's own message
// (e.g. "unterminated block comment") wins, known foreign spellings get a
// hint, and anything else names its position.
func illegalTokenMessage(tok token.Token) string {
	switch tok.Literal {
	case "":
		return fmt.Sprintf("illegal token at line %d, column %d", tok.Line, tok.Column)
	case "~":
		return "unexpected ~: bitwise complement is the prefix operator ^ in Oak (Go style), e.g. x & ^mask"
	}
	return tok.Literal
}

func (p *Parser) parseIntegerLiteral() ast.Expression {
	lit := &ast.IntegerLiteral{Token: p.currentToken}

	// Check if this is a radix literal (e.g., "16r1000", "2r1010")
	literal := p.currentToken.Literal
	if strings.ContainsAny(literal, "rR") {
		value, wide, err := p.parseRadixLiteral(literal)
		if err != nil {
			p.addErrorAtCurrentToken(fmt.Sprintf("invalid radix literal %q: %v", literal, err))
			return nil
		}
		lit.Value = value
		lit.Wide = wide
		return lit
	}

	value, err := strconv.ParseInt(literal, 10, 64)
	if err != nil {
		var msg string
		numErr, ok := err.(*strconv.NumError)
		if ok && numErr.Err == strconv.ErrRange {
			// Above the signed range: the full u64 range is still a literal
			// (docs/spec/20-types.md), carried as its bit pattern.
			if wide, wideErr := strconv.ParseUint(literal, 10, 64); wideErr == nil {
				lit.Value = int64(wide)
				lit.Wide = true
				return lit
			}
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
func (p *Parser) parseRadixLiteral(literal string) (int64, bool, error) {
	// Find the 'r' or 'R' separator
	rIndex := -1
	for i, ch := range literal {
		if ch == 'r' || ch == 'R' {
			rIndex = i
			break
		}
	}
	if rIndex == -1 {
		return 0, false, fmt.Errorf("not a radix literal")
	}

	// Parse the radix (base)
	radixStr := util.NormalizeDigits(literal[:rIndex])
	radix, err := strconv.Atoi(radixStr)
	if err != nil {
		return 0, false, fmt.Errorf("invalid radix: %s", radixStr)
	}
	if radix < 2 || radix > 16 {
		return 0, false, fmt.Errorf("radix must be between 2 and 16, got %d", radix)
	}

	// Parse the digits after 'r' (skip the 'r' itself)
	digitsStr := util.NormalizeDigits(literal[rIndex+1:])
	if digitsStr == "" {
		return 0, false, fmt.Errorf("missing digits after radix separator")
	}
	if err := validateDigitSeparators(digitsStr); err != nil {
		return 0, false, err
	}
	digitsStrClean := strings.ReplaceAll(digitsStr, "_", "")
	if digitsStrClean == "" {
		return 0, false, fmt.Errorf("missing digits after radix separator")
	}

	// Convert from the given radix: the full u64 range is admitted, values
	// above the signed range travel as their bit pattern with Wide set.
	value, err := strconv.ParseInt(digitsStrClean, radix, 64)
	if err != nil {
		if numErr, ok := err.(*strconv.NumError); ok && numErr.Err == strconv.ErrRange {
			if wide, wideErr := strconv.ParseUint(digitsStrClean, radix, 64); wideErr == nil {
				return int64(wide), true, nil
			}
			return 0, false, fmt.Errorf("integer literal out of range for radix %d", radix)
		}
		return 0, false, fmt.Errorf("invalid digits for radix %d: %s", radix, digitsStrClean)
	}

	return value, false, nil
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

// parseFunctionLiteral parses a function literal in expression position
// (docs/spec/10-syntax.md section 3c). Two shapes share the node:
//
//	fn(a, b) { ... }                       untyped names, block body
//	fn(a: T, b: U): R { ... }              typed parameters, optional return
//	fn(a: T): R = expr                     typed parameters, expression body
//
// The typed shape is recognized by `name :` (or `)` followed by a return
// annotation) right after the opening parenthesis. Arguments always holds
// the parameter names, so every walker that only needs names is unchanged;
// Parameters and ReturnType carry the annotations.
func (p *Parser) parseFunctionLiteral() ast.Expression {
	lit := &ast.FunctionLiteral{Token: p.currentToken}

	if !p.expectPeek(token.LPAREN) {
		return nil
	}

	second, third := p.lookaheadSignificant(1), p.lookaheadSignificant(2)
	typed := (second.TokenKind == token.IDENT && third.TokenKind == token.COLON) ||
		(second.TokenKind == token.RPAREN && (third.TokenKind == token.COLON || third.TokenKind == token.ARROW))
	if !typed {
		lit.Arguments = p.parseFunctionArgs()
		if !p.expectPeek(token.LBRACE) {
			return nil
		}
		lit.Body = p.parseBlockStatement()
		return lit
	}

	lit.Parameters = p.parseFunctionParameters()
	if lit.Parameters == nil && !p.currentTokenIs(token.RPAREN) {
		return nil
	}
	for _, param := range lit.Parameters {
		if param == nil || param.Name == nil {
			return nil
		}
		if param.Variadic {
			p.addErrorAtToken(&param.Token, "a function literal takes no variadic parameter")
			return nil
		}
		lit.Arguments = append(lit.Arguments, param.Name)
	}
	if p.peekTokenIs(token.COLON) || p.peekTokenIs(token.ARROW) {
		p.nextToken()
		p.nextToken()
		lit.ReturnType = p.parseTypeExpression()
		if lit.ReturnType == nil {
			return nil
		}
	}
	switch {
	case p.peekTokenIs(token.LBRACE):
		p.nextToken()
		lit.Body = p.parseBlockStatement()
	case p.peekTokenIs(token.ASSIGN):
		p.nextToken() // =
		p.nextToken() // first token of the expression
		if p.currentTokenIs(token.LBRACE) {
			lit.Body = p.parseBlockStatement()
		} else {
			value := p.parseExpression(LOWEST)
			if value == nil {
				return nil
			}
			lit.ExpressionBody = true
			lit.Body = &ast.BlockStatement{Token: lit.Token, Statements: []ast.Statement{&ast.ExpressionStatement{Token: lit.Token, Expression: value}}}
		}
	default:
		p.peekError(token.LBRACE)
		return nil
	}
	if lit.Body == nil {
		return nil
	}
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
	defer p.operatorPipe()()
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
// isMessageSendAccess reports whether expr is the library access
// `c.msg_send` (docs/spec/92-ffi.md section 2.12), whose bracket argument
// is a boundary function type rather than a value.
func isMessageSendAccess(expr ast.Expression) bool {
	access, isAccess := expr.(*ast.IndexExpression)
	if !isAccess || !access.Dot {
		return false
	}
	base, isIdent := access.Left.(*ast.Identifier)
	member, memberIsIdent := access.Index.(*ast.Identifier)
	return isIdent && memberIsIdent && base.Value == "c" && member.Value == "msg_send"
}

func (p *Parser) parseIndexOrSliceExpression(left ast.Expression) ast.Expression {
	tok := p.currentToken // '['
	defer p.operatorPipe()()
	p.nextToken() // move to first token after '['

	// `c.msg_send[(params) -> ret](receiver, selector, args...)` (docs/spec/
	// 92-ffi.md section 2.12): the bracket carries a boundary function
	// type, not a value, so it is read with the type grammar. The callee
	// is the one place a function type appears in expression position.
	if isMessageSendAccess(left) && p.currentTokenIs(token.LPAREN) {
		signature := p.parseTypeExpression()
		if signature == nil {
			return nil
		}
		if _, isFn := signature.(*ast.FunctionTypeExpression); !isFn {
			p.addErrorAtCurrentToken("c.msg_send takes a function type in brackets: c.msg_send[(params) -> ret]")
			return nil
		}
		if !p.expectPeek(token.RBRACK) {
			return nil
		}
		if !p.peekTokenIs(token.LPAREN) {
			p.peekError(token.LPAREN)
			return nil
		}
		return &ast.IndexExpression{Token: tok, Left: left, Index: signature}
	}

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
		if high != nil && !p.expectPeek(token.RBRACK) {
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

	// Comma-separated explicit type arguments normalize to the existing
	// nested application AST. In expression position they must be called;
	// ordinary subscripts and slices keep their existing grammar.
	if p.peekTokenIs(token.COMMA) {
		var application ast.Expression = &ast.IndexExpression{Token: tok, Left: left, Index: first}
		for p.peekTokenIs(token.COMMA) {
			p.nextToken()
			p.nextToken()
			if p.currentTokenIs(token.RBRACK) || p.currentTokenIs(token.EOF) || p.currentTokenIs(token.COMMA) {
				p.addErrorAtCurrentToken("expected a type argument after comma")
				return nil
			}
			arg := p.parseExpression(LOWEST)
			if arg == nil {
				return nil
			}
			application = &ast.IndexExpression{Token: tok, Left: application, Index: arg}
		}
		if !p.expectPeek(token.RBRACK) {
			return nil
		}
		if !p.peekTokenIs(token.LPAREN) {
			p.peekError(token.LPAREN)
			return nil
		}
		return application
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
		if high != nil && !p.expectPeek(token.RBRACK) {
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

// functionTypeAhead reports whether the parenthesized group at currentToken
// is followed by `->`, i.e. spells a function type `(T1, T2) -> R`.
func (p *Parser) functionTypeAhead() bool {
	cursor, ok := p.source.(*token.Cursor)
	if !ok {
		return false
	}
	depth := 1
	next := func(i int) token.Token {
		if i == 0 {
			return p.peekToken
		}
		return cursor.Peek(i - 1)
	}
	const lookaheadLimit = 4096
	for i := 0; i < lookaheadLimit; i++ {
		tok := next(i)
		switch tok.TokenKind {
		case token.LPAREN:
			depth++
		case token.RPAREN:
			depth--
			if depth == 0 {
				for rest := i + 1; rest < i+16; rest++ {
					after := next(rest)
					if after.TokenKind == token.TRIVIA || after.TokenKind == token.COMMENT {
						continue
					}
					return after.TokenKind == token.ARROW
				}
				return false
			}
		case token.EOF:
			return false
		}
	}
	return false
}

// qualifiedTypeReceiver reports whether leftExp is `pkg.Type` immediately
// followed (same line) by `{`: a package-qualified typed record literal
// (docs/spec/83-modules.md section 3.4). The same-line rule keeps a field
// access that ends a line from swallowing a following block.
func (p *Parser) qualifiedTypeReceiver(leftExp ast.Expression) bool {
	access, isAccess := leftExp.(*ast.IndexExpression)
	if !isAccess || !access.Dot {
		return false
	}
	_, baseOK := access.Left.(*ast.Identifier)
	member, memberOK := access.Index.(*ast.Identifier)
	return baseOK && memberOK && member.Token.Line == p.peekToken.Line
}

// foldImportBinding turns a top-level binding whose whole initializer is
// `import(path)` into an ImportStatement carrying the binding name and the
// optional sealing signature (docs/spec/83-modules.md section 3.2).
func (p *Parser) foldImportBinding(stmt ast.Statement) ast.Statement {
	decl, ok := stmt.(*ast.VariableDeclaration)
	if !ok {
		return stmt
	}
	imp, isImport := decl.Value.(*ast.ImportExpression)
	if !isImport {
		return stmt
	}
	if decl.Exported {
		p.addErrorAtToken(&decl.Token, "an import binding cannot be pub")
		return stmt
	}
	return &ast.ImportStatement{BaseNode: decl.BaseNode, Token: imp.Token, Path: imp.Path, Alias: decl.Name, Signature: decl.Type, Arguments: imp.Arguments}
}

func (p *Parser) ParseProgram() *ast.Program {
	program := &ast.Program{}
	program.Statements = []ast.Statement{}

	for p.currentToken.TokenKind != token.EOF {
		start := p.currentToken
		stmt := p.parseStatement()
		if stmt != nil {
			program.Statements = append(program.Statements, p.foldImportBinding(stmt))
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
			p.currentTokenIs(token.PUB) ||
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
	PIPELINE    // |>
	LOGICAL_OR  // ||
	LOGICAL_AND // &&
	EQUALITY    // ==
	COMPARE     // > or <
	SUMMATION   // +
	PRODUCT     // *
	PREFIX      // -x or !x
	INVOCATION  // aka Call, myfunction(x)
	INDEX       // record.field or array[index] - highest precedence
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

func firstRune(s string) (rune, int) {
	for _, r := range s {
		return r, len(string(r))
	}
	return 0, 0
}

// Pipelines lower to ordinary calls. A pre-applied right side receives the
// piped value last: value |> f(a) becomes f(a, value).
func (p *Parser) parsePipelineExpression(left ast.Expression) ast.Expression {
	tok := p.currentToken
	precedence := p.currentPrecedence()
	p.nextToken()
	right := p.parseExpression(precedence)
	if right == nil {
		return nil
	}
	if accessor, ok := right.(*ast.FieldAccessorExpression); ok {
		return &ast.IndexExpression{Token: tok, Left: left, Index: accessor.Field, Dot: true}
	}
	if call, ok := right.(*ast.InvocationExpression); ok {
		call.Arguments = append(call.Arguments, left)
		return call
	}
	return &ast.InvocationExpression{Token: tok, Function: right, Arguments: []ast.Expression{left}}
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

// operatorPipe re-enables '|' as bitwise or for the extent of a bracketed
// construct inside a ?-match arm body: parentheses, call arguments, index
// brackets, and array and record literals all close before the arm can
// (docs/spec/10-syntax.md section 3b). The returned function restores the
// arm depth; callers defer it.
func (p *Parser) operatorPipe() func() {
	saved := p.armDepth
	p.armDepth = 0
	return func() { p.armDepth = saved }
}

func (p *Parser) parseExpressionGroup() ast.Expression {
	// Skip opening paren - currentToken is LPAREN, advance to expression.
	defer p.operatorPipe()()
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
	token.PIPE_FORWARD: PIPELINE,
	token.LOR:          LOGICAL_OR,
	token.LAND:         LOGICAL_AND,
	token.EQL:          EQUALITY,
	token.NEQL:         EQUALITY,
	token.LCHEV:        COMPARE,
	token.LEQ:          COMPARE,
	token.GEQ:          COMPARE,
	token.RCHEV:        COMPARE,
	token.NEG:          SUMMATION,
	token.SUM:          SUMMATION,
	token.PIPE:         SUMMATION, // bitwise or (Go's precedence model)
	token.CARET:        SUMMATION, // bitwise xor
	token.AMP:          PRODUCT,   // bitwise and
	token.SHL:          PRODUCT,
	token.SHR:          PRODUCT,
	token.MUL:          PRODUCT,
	token.QUO:          PRODUCT,
	token.REM:          PRODUCT,
	token.LPAREN:       INVOCATION,
	token.QMARK:        CONDITION, // the whole operator expression is the scrutinee
	token.DOT:          INDEX,     // Field access has highest precedence
	token.LBRACK:       INDEX,     // Array indexing has highest precedence
}

func (p *Parser) peekPrecedence() Precedence {
	// Inside a bare-expression ?-match arm body, '|' is the arm separator,
	// never bitwise or — parenthesize (a | b) to use the operator there.
	// Parens and brace blocks reset the suppression.
	if p.armDepth > 0 && p.peekToken.TokenKind == token.PIPE {
		return LOWEST
	}
	// A call or an index never continues across a line break: a line that
	// starts with '(' or '[' begins a new statement (F18). Go's rule, without
	// the semicolon insertion.
	// The same holds for '-': a line that starts with a minus negates what
	// follows, it does not subtract from the line above (an operator that
	// continues an expression sits at the END of a line). '!' has no infix
	// reading, so it already starts a statement.
	if (p.peekToken.TokenKind == token.LPAREN || p.peekToken.TokenKind == token.LBRACK || p.peekToken.TokenKind == token.NEG) &&
		p.peekToken.Line > p.currentToken.Line && p.currentToken.Line > 0 {
		return LOWEST
	}
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
	// A generic package declares its parameters after the name
	// (docs/spec/83-modules.md section 6.7).
	if p.peekTokenIs(token.LBRACK) {
		stmt.TypeParams = p.parseTypeParameters()
		if stmt.TypeParams == nil {
			return nil
		}
	}
	return stmt
}

// Import statement (docs/spec/83-modules.md section 3): import(path).
func (p *Parser) parseImportStatement() *ast.ImportStatement {
	stmt := &ast.ImportStatement{Token: p.currentToken}
	path, arguments, ok := p.parseImportPath()
	if !ok {
		return nil
	}
	stmt.Path, stmt.Arguments = path, arguments
	return stmt
}

// parseImportPath parses `( path )` after `import`. The path is a string
// literal; a bare identifier is sugar for a single-segment path
// (`import(std)`).
func (p *Parser) parseImportPath() (*ast.Identifier, []ast.Expression, bool) {
	if !p.expectPeek(token.LPAREN) {
		return nil, nil, false
	}
	p.nextToken()
	var path *ast.Identifier
	switch p.currentToken.TokenKind {
	case token.STRING, token.IDENT:
		path = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
	default:
		p.addErrorAtCurrentToken(fmt.Sprintf("import path must be a string literal or identifier, got %s", p.currentToken.TokenKind))
		return nil, nil, false
	}
	if !p.expectPeek(token.RPAREN) {
		return nil, nil, false
	}
	// Generic package instantiation: import("...")[u8, 8].
	var arguments []ast.Expression
	if p.peekTokenIs(token.LBRACK) {
		p.nextToken()
		args, ok := p.parseDelimited[ast.Expression](
			token.LBRACK, token.RBRACK, token.COMMA, false,
			func() (ast.Expression, bool) {
				if p.currentTokenIs(token.INT) {
					return p.parseIntegerLiteral(), true
				}
				arg := p.parseTypeExpression()
				return arg, arg != nil
			},
		)
		if !ok {
			return nil, nil, false
		}
		arguments = args
	}
	return path, arguments, true
}

// selectiveImportAhead reports whether currentToken `{` opens
// `{ name, name } := import(...)` (docs/spec/83-modules.md section 3.2).
func (p *Parser) selectiveImportAhead() bool {
	cursor, ok := p.source.(*token.Cursor)
	if !ok {
		return false
	}
	next := func(i int) token.Token {
		if i == 0 {
			return p.peekToken
		}
		return cursor.Peek(i - 1)
	}
	i := 0
	expectIdent := true
	for ; i < 256; i++ {
		tok := next(i)
		if tok.TokenKind == token.TRIVIA || tok.TokenKind == token.COMMENT {
			continue
		}
		if expectIdent {
			if tok.TokenKind != token.IDENT {
				return false
			}
			expectIdent = false
			continue
		}
		switch tok.TokenKind {
		case token.COMMA:
			expectIdent = true
		case token.RBRACE:
			// `:=` then `import`, skipping trivia.
			seen := 0
			for j := i + 1; j < i+64; j++ {
				after := next(j)
				if after.TokenKind == token.TRIVIA || after.TokenKind == token.COMMENT {
					continue
				}
				if seen == 0 {
					if after.TokenKind != token.COLON_ASSIGN {
						return false
					}
					seen++
					continue
				}
				return after.TokenKind == token.IMPORT
			}
			return false
		default:
			return false
		}
	}
	return false
}

// parseSelectiveImport parses `{ f, g } := import(path)`.
func (p *Parser) parseSelectiveImport() ast.Statement {
	var names []*ast.Identifier
	for {
		if !p.expectPeek(token.IDENT) {
			return nil
		}
		names = append(names, &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal})
		if p.peekTokenIs(token.COMMA) {
			p.nextToken()
			continue
		}
		break
	}
	if !p.expectPeek(token.RBRACE) || !p.expectPeek(token.COLON_ASSIGN) || !p.expectPeek(token.IMPORT) {
		return nil
	}
	stmt := &ast.ImportStatement{Token: p.currentToken, Names: names}
	path, arguments, ok := p.parseImportPath()
	if !ok {
		return nil
	}
	stmt.Path, stmt.Arguments = path, arguments
	return stmt
}

// parseModuleDeclaration parses `module name { declarations }`.
func (p *Parser) parseModuleDeclaration() ast.Statement {
	stmt := &ast.ModuleDeclaration{Token: p.currentToken}
	if !p.expectPeek(token.IDENT) {
		return nil
	}
	stmt.Name = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
	if !p.expectPeek(token.LBRACE) {
		return nil
	}
	stmt.Body = p.parseBlockStatement()
	if stmt.Body == nil {
		return nil
	}
	// The block is a package body: `x := import(...)` and `x: Sig = import(...)`
	// are import statements there, as at the top of a file.
	for i, inner := range stmt.Body.Statements {
		stmt.Body.Statements[i] = p.foldImportBinding(inner)
	}
	return stmt
}

// parseOpenImport parses `open import(path)`.
func (p *Parser) parseOpenImport() ast.Statement {
	if !p.expectPeek(token.IMPORT) {
		return nil
	}
	stmt := &ast.ImportStatement{Token: p.currentToken, Open: true}
	path, arguments, ok := p.parseImportPath()
	if !ok {
		return nil
	}
	stmt.Path, stmt.Arguments = path, arguments
	return stmt
}

// parseImportExpression parses `import(path)` in expression position. Only a
// top-level binding initializer is legal (ParseProgram folds it into an
// ImportStatement); the loader rejects any other placement.
func (p *Parser) parseImportExpression() ast.Expression {
	expr := &ast.ImportExpression{Token: p.currentToken}
	path, arguments, ok := p.parseImportPath()
	if !ok {
		return nil
	}
	expr.Path, expr.Arguments = path, arguments
	return expr
}

// parseTypeKindExpression admits the keyword `type` as a member type inside
// a signature shape (`{ Key: type, hash: (k: Key): u64 }`,
// docs/spec/83-modules.md section 6.3). Elsewhere the type checker rejects
// `type` as a value.
func (p *Parser) parseTypeKindExpression() ast.Expression {
	return &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
}

// parsePubDeclaration parses `pub decl` and `pub(opaque) decl`
// (docs/spec/83-modules.md section 6). pub applies to package-level
// declarations only; pub(opaque) applies to type declarations only.
// operatorSymbols are the symbols an operator declaration may bind
// (docs/spec/10-syntax.md section 14): arithmetic and comparison. Bool and
// bitwise operators keep their fixed meaning and are not bindable.
var operatorSymbols = map[token.TokenKind]string{
	token.SUM: "+", token.NEG: "-", token.MUL: "*", token.QUO: "/", token.REM: "%",
	token.EQL: "==", token.NEQL: "!=", token.LCHEV: "<", token.LEQ: "<=", token.RCHEV: ">", token.GEQ: ">=",
}

// parseOperatorDeclaration parses `operator(SYM)` followed by a function
// declaration and records the bound symbol on it.
func (p *Parser) parseOperatorDeclaration() ast.Statement {
	marker := p.currentToken
	p.nextToken() // (
	p.nextToken() // the symbol
	symbol, bindable := operatorSymbols[p.currentToken.TokenKind]
	if !bindable {
		p.addErrorAtCurrentToken(fmt.Sprintf("operator(%s): only + - * / %% == != < <= > >= can be bound (docs/spec/10-syntax.md section 14)", p.currentToken.Literal))
		return nil
	}
	if !p.expectPeek(token.RPAREN) {
		return nil
	}
	if p.peekTokenIs(token.EOF) {
		p.addErrorAtToken(&marker, "operator(%s) must be followed by a function declaration")
		return nil
	}
	p.nextToken()
	stmt := p.parseStatement()
	if stmt == nil {
		return nil
	}
	fn, isFunction := stmt.(*ast.FunctionStatement)
	if !isFunction {
		p.addErrorAtToken(&marker, "operator("+symbol+") must be followed by a function declaration")
		return nil
	}
	fn.Operator = symbol
	return fn
}

// parseKernelDeclaration parses the `kernel` marker followed by a function
// declaration (docs/spec/56-kernels.md section 1).
func (p *Parser) parseKernelDeclaration() ast.Statement {
	marker := p.currentToken
	p.nextToken()
	stmt := p.parseStatement()
	if stmt == nil {
		return nil
	}
	fn, isFunction := stmt.(*ast.FunctionStatement)
	if !isFunction {
		p.addErrorAtToken(&marker, "kernel must be followed by a function declaration")
		return nil
	}
	fn.Kernel = true
	return fn
}

// parseExportDeclaration parses `export("symbol")` followed by a `pub`
// function declaration and records the C ABI symbol on it
// (docs/spec/92-ffi.md section 2.9). The symbol's grammar, uniqueness, and
// the function's shape are checked by the type checker (OAK-F0108/F0109);
// the parser only fixes the syntax: a string literal, then a pub function.
func (p *Parser) parseExportDeclaration() ast.Statement {
	marker := p.currentToken
	p.nextToken() // (
	p.nextToken() // the symbol
	symbol := p.currentToken.Literal
	if !p.expectPeek(token.RPAREN) {
		return nil
	}
	if !p.peekTokenIs(token.PUB) {
		p.addErrorAtToken(&marker, "export(\""+symbol+"\") must be followed by a pub function declaration (docs/spec/92-ffi.md section 2.9)")
		return nil
	}
	p.nextToken()
	stmt := p.parsePubDeclaration()
	if stmt == nil {
		return nil
	}
	fn, isFunction := stmt.(*ast.FunctionStatement)
	if !isFunction || fn.Receiver != nil {
		p.addErrorAtToken(&marker, "export(\""+symbol+"\") must be followed by a pub function declaration (docs/spec/92-ffi.md section 2.9)")
		return nil
	}
	fn.ExportSymbol = symbol
	return fn
}

func (p *Parser) parsePubDeclaration() ast.Statement {
	pubToken := p.currentToken
	opaque := false
	if p.peekTokenIs(token.LPAREN) {
		p.nextToken() // (
		if !p.expectPeek(token.IDENT) {
			return nil
		}
		if p.currentToken.Literal != "opaque" {
			p.addErrorAtCurrentToken(fmt.Sprintf("pub accepts only the opaque modifier, got pub(%s)", p.currentToken.Literal))
			return nil
		}
		if !p.expectPeek(token.RPAREN) {
			return nil
		}
		opaque = true
	}
	if p.peekTokenIs(token.EOF) {
		p.addErrorAtToken(&pubToken, "pub must be followed by a declaration")
		return nil
	}
	p.nextToken()
	stmt := p.parseStatement()
	if stmt == nil {
		return nil
	}
	isType := false
	switch decl := stmt.(type) {
	case *ast.FunctionStatement:
		decl.Exported, decl.Opaque = true, opaque
	case *ast.VariableDeclaration:
		decl.Exported, decl.Opaque = true, opaque
	case *ast.ADTType:
		decl.Exported, decl.Opaque = true, opaque
		isType = true
	case *ast.InterfaceType:
		decl.Exported, decl.Opaque = true, opaque
	case *ast.TagDeclaration:
		decl.Exported, decl.Opaque = true, opaque
	case *ast.ProtocolDeclaration:
		decl.Exported = true
	default:
		p.addErrorAtToken(&pubToken, "pub applies only to package-level declarations (functions, values, types, interfaces, tag schemas, protocols)")
		return nil
	}
	if opaque && !isType {
		p.addErrorAtToken(&pubToken, "pub(opaque) applies only to type declarations")
		return nil
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
	// `type` in type position is the abstract type member of an import
	// signature shape (docs/spec/83-modules.md section 6.3); parseTypePrimary
	// admits it as an identifier the type checker interprets.
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
// parseEffectNameList parses `{ A.B, C.D }` after an `effects`/`forbids`
// keyword at currentToken, leaving currentToken at '}'.
func (p *Parser) parseEffectNameList() ([]*ast.EffectName, bool) {
	if !p.expectPeek(token.LBRACE) {
		return nil, false
	}
	names := []*ast.EffectName{}
	for !p.peekTokenIs(token.RBRACE) {
		if !p.expectPeek(token.IDENT) {
			return nil, false
		}
		effect := &ast.EffectName{Token: p.currentToken, Namespace: p.currentToken.Literal}
		if !p.expectPeek(token.DOT) {
			return nil, false
		}
		if !p.expectPeek(token.IDENT) {
			return nil, false
		}
		effect.Name = p.currentToken.Literal
		names = append(names, effect)
		if p.peekTokenIs(token.COMMA) {
			p.nextToken()
		} else if !p.peekTokenIs(token.RBRACE) {
			p.peekError(token.RBRACE)
			return nil, false
		}
	}
	p.nextToken() // '}'
	return names, true
}

// parseFunctionTypeRow reads an optional effect row after a function type's
// return type (docs/spec/60-effects-allocation.md section 2a): `effects {
// A.B, ... }`, contextual, at most once. The row binds to the innermost
// function type; a function statement returning a function type and
// declaring its own clause parenthesizes the return type.
func (p *Parser) parseFunctionTypeRow(ft *ast.FunctionTypeExpression) ast.Expression {
	if p.peekTokenIs(token.IDENT) && p.peekToken.Literal == "effects" {
		p.nextToken()
		names, ok := p.parseEffectNameList()
		if !ok {
			return nil
		}
		ft.Effects, ft.EffectsDeclared = names, true
	}
	return ft
}

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
				return p.parseFunctionTypeRow(&ast.FunctionTypeExpression{Token: openToken, Return: returnType})
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
			return p.parseFunctionTypeRow(&ast.FunctionTypeExpression{Token: openToken, Parameters: parameters, Return: returnType})
		}
		if len(parameters) > 1 {
			p.addErrorAtCurrentToken("a parenthesized type list must be a function type: (T1, T2) -> R")
			return nil
		}
		// currentToken is ')', last token of the type
		return inner

	case token.TYPE:
		// `type` as a member type: an abstract type member of an import
		// signature shape (docs/spec/83-modules.md section 6.3). The type
		// checker rejects it anywhere else.
		return &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}

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
			// A qualified package type may still take type arguments
			// (pkg.Ring[u8, 8]); fall through to the generic check.
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
					// Const parameters: integer literals are type arguments
					// (Ring[u8, 16] — docs/spec/20-types.md).
					if p.currentTokenIs(token.INT) {
						return p.parseIntegerLiteral(), true
					}
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

	// Move to first field name or row variable.
	p.nextToken() // currentToken should be IDENT, RBRACE, or COMMA (leading comma)
	if p.currentTokenIs(token.IDENT) && p.peekTokenIs(token.PIPE) {
		record.Extension = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
		p.nextToken() // move to |
		p.nextToken() // move to first required field
	}

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
		// Grouped field names share one type: { a, b: u8 } declares both a
		// and b as u8, in written order (docs/spec/40-records.md §1). A bare
		// name followed by ',' has no other reading in type position.
		fieldTokens := []token.Token{p.currentToken}
		for p.peekTokenIs(token.COMMA) {
			p.nextToken() // to ','
			if !p.expectPeek(token.IDENT) {
				return nil
			}
			fieldTokens = append(fieldTokens, p.currentToken)
		}

		// Optional per-field spec, mirroring the struct clause:
		// id(align: 8, json: "user_id"): u64. `align` is the reserved
		// representation key; every other name must be a declared tag
		// schema (checked by the typechecker — unknown namespaces are
		// errors, never silent metadata). Packing is a property of
		// placement BETWEEN fields, so it belongs to the container.
		var fieldAlign uint32
		var fieldTags []ast.FieldTag
		if p.peekTokenIs(token.LPAREN) {
			p.nextToken() // to (
			align, tags, ok := p.parseFieldSpec()
			if !ok {
				return nil
			}
			fieldAlign = align
			fieldTags = tags
			// parseFieldSpec leaves the cursor after ')'.
			if !p.currentTokenIs(token.COLON) {
				p.peekError(token.COLON)
				return nil
			}
		} else if !p.expectPeek(token.COLON) {
			return nil
		}

		p.nextToken() // move to first token of field type
		fieldType := p.parseTypeExpression()
		if fieldType == nil {
			return nil
		}
		// A shared type member of a signature: `Key: type = u64`
		// (docs/spec/83-modules.md section 6.3).
		var manifest ast.Expression
		if kind, isKind := fieldType.(*ast.Identifier); isKind && kind.Value == "type" && p.peekTokenIs(token.ASSIGN) {
			p.nextToken() // to '='
			p.nextToken() // to the shared type
			manifest = p.parseTypeExpression()
			if manifest == nil {
				return nil
			}
		}
		for _, fieldToken := range fieldTokens {
			if !record.AddField(fieldToken, fieldToken.Literal, fieldType) {
				p.addErrorAtCurrentToken(fmt.Sprintf("duplicate record field %q", fieldToken.Literal))
				return nil
			}
			record.FieldOrder[len(record.FieldOrder)-1].Manifest = manifest
			// The declared alignment and tags ride on the ordered entry
			// AddField just appended; AddField's proven construction
			// contract (Oak.SemanticRecord) covers name/value, not
			// representation or metadata.
			record.FieldOrder[len(record.FieldOrder)-1].Align = fieldAlign
			record.FieldOrder[len(record.FieldOrder)-1].Tags = fieldTags
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

// Parse struct type: struct{ field: Type, ... } with an optional declared
// layout spec: struct(packed) { ... }, struct(align: 64) { ... },
// struct(packed, align: 4) { ... } (docs/spec/40-records.md).
func (p *Parser) parseStructType() ast.Expression {
	// currentToken is STRUCT
	structToken := p.currentToken
	p.nextToken() // consume struct

	var layout *ast.RecordLayoutSpec
	if p.currentTokenIs(token.LPAREN) {
		layout = p.parseRecordLayoutSpec()
		if layout == nil {
			return nil
		}
	}

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
		rl.Layout = layout
	}
	return record
}

// parseFieldSpec parses the parenthesized per-field clause: `align: N`
// (reserved representation key) and `namespace: value` tag entries,
// comma-separated. Leaves the cursor after ')'.
func (p *Parser) parseFieldSpec() (uint32, []ast.FieldTag, bool) {
	var align uint32
	var tags []ast.FieldTag
	seen := map[string]bool{}
	p.nextToken() // consume (
	for {
		if !p.currentTokenIs(token.IDENT) {
			p.addErrorAtCurrentToken("expected 'align' or a tag namespace in field spec")
			return 0, nil, false
		}
		switch p.currentToken.Literal {
		case "packed":
			p.addErrorAtCurrentToken("'packed' is a struct-level spec: padding lives between fields; use a nested struct(packed) for a dense region")
			return 0, nil, false
		case "align":
			if align != 0 {
				p.addErrorAtCurrentToken("duplicate 'align' in field spec")
				return 0, nil, false
			}
			if !p.peekTokenIs(token.COLON) {
				p.addErrorAtCurrentToken("expected ':' after 'align' in field spec")
				return 0, nil, false
			}
			p.nextToken() // to :
			if !p.peekTokenIs(token.INT) {
				p.addErrorAtCurrentToken("expected integer alignment after 'align:'")
				return 0, nil, false
			}
			p.nextToken() // to the integer
			value, err := strconv.ParseUint(p.currentToken.Literal, 10, 32)
			if err != nil || value == 0 || value&(value-1) != 0 {
				p.addErrorAtCurrentToken("field alignment must be a nonzero power-of-two u32")
				return 0, nil, false
			}
			align = uint32(value)
			p.nextToken()
		default:
			namespace := p.currentToken
			name := namespace.Literal
			// A tag schema of an imported package: alias.schema
			// (docs/spec/83-modules.md section 6.8).
			if p.peekTokenIs(token.DOT) {
				p.nextToken()
				if !p.expectPeek(token.IDENT) {
					return 0, nil, false
				}
				name = name + "." + p.currentToken.Literal
			}
			if seen[name] {
				p.addErrorAtCurrentToken(fmt.Sprintf("duplicate tag namespace %q in field spec", name))
				return 0, nil, false
			}
			seen[name] = true
			if !p.expectPeek(token.COLON) {
				return 0, nil, false
			}
			p.nextToken() // to the value
			value := p.parseFieldTagValue()
			if value == nil {
				return 0, nil, false
			}
			tags = append(tags, ast.FieldTag{Token: namespace, Name: name, Value: value})
			p.nextToken() // past the value's last token
		}
		if p.currentTokenIs(token.COMMA) {
			p.nextToken()
			continue
		}
		break
	}
	if !p.currentTokenIs(token.RPAREN) {
		p.peekError(token.RPAREN)
		return 0, nil, false
	}
	p.nextToken() // consume )
	return align, tags, true
}

// parseTagDeclarationFromName parses a tag schema declaration after the
// name and ':' were consumed: json: tag = { name: string, omit: Bool }.
// currentToken sits on the contextual `tag` identifier.
func (p *Parser) parseTagDeclarationFromName(name *ast.Identifier) *ast.TagDeclaration {
	decl := &ast.TagDeclaration{Token: name.Token, Name: name}
	p.nextToken() // consume `tag`; currentToken is '='
	if !p.currentTokenIs(token.ASSIGN) {
		p.peekError(token.ASSIGN)
		return nil
	}
	p.nextToken() // to '{'
	if !p.currentTokenIs(token.LBRACE) {
		p.peekError(token.LBRACE)
		return nil
	}
	schema := p.parseRecordType()
	if schema == nil {
		return nil
	}
	recordLit, isRecord := schema.(*ast.RecordLiteral)
	if !isRecord || len(recordLit.FieldOrder) == 0 {
		p.addErrorAtCurrentToken("tag schema requires at least one field")
		return nil
	}
	decl.Schema = recordLit
	decl.EndToken = recordLit.EndToken
	return decl
}

// parseProtocolDeclarationFromName parses the body of `Name: protocol = {
// ... }`: `resource T`, `initial S`, and transition lines
// `name(param: T)?: From -> To (via callable)?`, separated by newlines or
// commas. The cursor is on `protocol`. Structure only: states are the
// names the transitions and `initial` mention, and the compiler checks
// that the initial state exists and that names are unique.
func (p *Parser) parseProtocolDeclarationFromName(name *ast.Identifier) *ast.ProtocolDeclaration {
	decl := &ast.ProtocolDeclaration{Token: name.Token, Name: name}
	p.nextToken() // consume `protocol`; currentToken is '='
	if !p.currentTokenIs(token.ASSIGN) {
		p.peekError(token.ASSIGN)
		return nil
	}
	p.nextToken() // to '{'
	if !p.currentTokenIs(token.LBRACE) {
		p.peekError(token.LBRACE)
		return nil
	}
	p.nextToken() // first entry, or '}'
	for {
		for p.currentTokenIs(token.COMMA) || p.currentTokenIs(token.SEMI) {
			p.nextToken()
		}
		if p.currentTokenIs(token.RBRACE) {
			decl.EndToken = p.currentToken
			break
		}
		if p.currentTokenIs(token.EOF) {
			p.addErrorAtCurrentToken("protocol declaration is missing its closing brace")
			return nil
		}
		if !p.currentTokenIs(token.IDENT) {
			p.addErrorAtCurrentToken("protocol entries are `resource T`, `initial S`, or `name: From -> To`")
			return nil
		}
		switch p.currentToken.Literal {
		case "data", "init":
			keyword := p.currentToken.Literal
			if !p.expectPeek(token.LBRACE) {
				return nil
			}
			if keyword == "data" {
				if decl.Data != nil {
					p.addErrorAtCurrentToken("protocol declares its data record once")
					return nil
				}
				shape := p.parseRecordType()
				record, ok := shape.(*ast.RecordLiteral)
				if !ok || record == nil {
					return nil
				}
				decl.Data = record
			} else {
				if decl.Init != nil {
					p.addErrorAtCurrentToken("protocol declares its initial data once")
					return nil
				}
				values := p.parseRecordLiteral()
				record, ok := values.(*ast.RecordLiteral)
				if !ok || record == nil {
					return nil
				}
				decl.Init = record
			}
			p.nextToken()
		case "resource", "initial":
			keyword := p.currentToken.Literal
			if !p.expectPeek(token.IDENT) {
				return nil
			}
			ident := &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
			if keyword == "resource" {
				decl.Resources = append(decl.Resources, ident)
			} else {
				if decl.Initial != nil {
					p.addErrorAtCurrentToken("protocol declares its initial state once")
					return nil
				}
				decl.Initial = ident
			}
			p.nextToken()
		default:
			transition := &ast.ProtocolTransition{Token: p.currentToken, Name: &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}}
			if p.peekTokenIs(token.LPAREN) {
				p.nextToken() // (
				if !p.expectPeek(token.IDENT) {
					return nil
				}
				param := &ast.FunctionParameter{Token: p.currentToken, Name: &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}}
				if !p.expectPeek(token.COLON) {
					return nil
				}
				p.nextToken()
				param.Type = p.parseTypeExpression()
				if param.Type == nil {
					return nil
				}
				if !p.expectPeek(token.RPAREN) {
					return nil
				}
				transition.Param = param
			}
			if !p.expectPeek(token.COLON) {
				return nil
			}
			if !p.expectPeek(token.IDENT) {
				return nil
			}
			transition.From = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
			if !p.expectPeek(token.ARROW) {
				return nil
			}
			if !p.expectPeek(token.IDENT) {
				return nil
			}
			transition.To = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
			if p.peekTokenIs(token.IDENT) && p.peekToken.Literal == "when" {
				p.nextToken() // when
				p.nextToken() // first token of the guard
				transition.Guard = p.parseExpression(LOWEST)
				if transition.Guard == nil {
					return nil
				}
			}
			if p.peekTokenIs(token.IDENT) && p.peekToken.Literal == "then" {
				p.nextToken() // then
				if !p.expectPeek(token.LBRACE) {
					return nil
				}
				transition.Effects = p.parseBlockStatement()
				if transition.Effects == nil {
					return nil
				}
			}
			if p.peekTokenIs(token.IDENT) && p.peekToken.Literal == "via" {
				p.nextToken() // via
				if !p.parseViaClause(transition) {
					return nil
				}
			}
			decl.Transitions = append(decl.Transitions, transition)
			p.nextToken()
		}
	}
	return decl
}

// recordLiteralAhead decides, with the cursor on a statement-position `{`,
// whether the braces hold record syntax rather than a block
// (docs/spec/10-syntax.md section 4c). Record syntax is `IDENT :` followed
// at nesting depth zero by `,` or `}` before any `=`, `:=`, or `;` — a
// block's first statement `x: T = v` reaches `=` first — or `IDENT |`, the
// extensible record type. Anything else (an empty brace, a call, an
// assignment, a `:=` declaration, a nested block) is a block.
func (p *Parser) recordLiteralAhead() bool {
	first := p.peekToken
	if first.TokenKind != token.IDENT {
		return false
	}
	second := p.lookaheadSignificant(2)
	if second.TokenKind == token.PIPE {
		return true
	}
	if second.TokenKind != token.COLON {
		return false
	}
	cursor, ok := p.source.(*token.Cursor)
	if !ok {
		return false
	}
	depth := 0
	const lookaheadLimit = 4096
	for offset, step := 0, 0; step < lookaheadLimit; step++ {
		tok := cursor.Peek(offset)
		offset++
		switch tok.TokenKind {
		case token.TRIVIA, token.COMMENT:
			continue
		case token.LPAREN, token.LBRACK, token.LBRACE:
			depth++
		case token.RPAREN, token.RBRACK:
			depth--
		case token.RBRACE:
			if depth == 0 {
				return true
			}
			depth--
		case token.COMMA:
			if depth == 0 {
				return true
			}
		case token.ASSIGN, token.COLON_ASSIGN, token.SEMI:
			if depth == 0 {
				return false
			}
		case token.EOF:
			return false
		}
	}
	return false
}

// parseViaClause parses what follows `via` on a protocol transition line
// (docs/spec/112-protocols.md section 5). The cursor is on `via`; on
// success it rests on the last token of the clause.
//
//	via [unsafe] callable [ '(' entry {',' entry} ')' ] [ ':' result ]
//	callable := IDENT | IDENT '.' IDENT            // a function, or Type.method
//	entry    := mode IDENT                         // a resource parameter, or `receiver`
//	          | IDENT '(' [cmode {',' cmode}] ')' [':' 'fresh']   // a callable contract
//	mode     := 'borrowed' ['mut'] | 'consumed'
//	cmode    := mode | '_'
//	result   := 'fresh' | 'alias' IDENT | 'borrow' ['mut'] IDENT {',' IDENT}
//
// The vocabulary is closed: every word in a mode or result position must
// be one of the words above, so a misspelling is a parse error here rather
// than a silently weaker contract downstream.
func (p *Parser) parseViaClause(transition *ast.ProtocolTransition) bool {
	if p.peekTokenIs(token.UNSAFE) {
		p.nextToken()
		transition.Trusted = true
		transition.TrustedToken = p.currentToken
	}
	if !p.expectPeek(token.IDENT) {
		return false
	}
	transition.Callable = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
	if p.peekTokenIs(token.DOT) {
		p.nextToken() // .
		if !p.expectPeek(token.IDENT) {
			return false
		}
		transition.CallableType = transition.Callable
		transition.Callable = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
	}
	// parseMode reads `borrowed`, `borrowed mut`, or `consumed` at the
	// peek token, or `_` when underscore is admitted; it returns the
	// spelling and whether a word was read.
	parseMode := func(underscore bool) (string, token.Token, bool) {
		if !p.peekTokenIs(token.IDENT) {
			p.peekError(token.IDENT)
			return "", token.Token{}, false
		}
		p.nextToken()
		word := p.currentToken
		switch word.Literal {
		case "borrowed":
			if p.peekTokenIs(token.IDENT) && p.peekToken.Literal == "mut" {
				p.nextToken()
				return "borrowed mut", word, true
			}
			return "borrowed", word, true
		case "consumed":
			return "consumed", word, true
		case "_":
			if underscore {
				return "_", word, true
			}
		}
		expected := "borrowed, borrowed mut, consumed"
		if underscore {
			expected += ", _"
		}
		p.addErrorAtCurrentToken(fmt.Sprintf("via: expected a parameter mode (%s), got %s", expected, word.Literal))
		return "", token.Token{}, false
	}
	if p.peekTokenIs(token.LPAREN) {
		p.nextToken() // (
		for !p.peekTokenIs(token.RPAREN) {
			if !p.peekTokenIs(token.IDENT) {
				p.peekError(token.IDENT)
				return false
			}
			// A parameter name followed by `(` is a callable contract;
			// anything else is a mode word.
			if next := p.lookaheadSignificant(2); next.TokenKind == token.LPAREN {
				p.nextToken() // the parameter name
				entry := &ast.ProtocolParameterMode{Token: p.currentToken, Name: &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}}
				p.nextToken() // (
				contract := &ast.ProtocolCallableContract{Token: p.currentToken}
				for !p.peekTokenIs(token.RPAREN) {
					mode, word, ok := parseMode(true)
					if !ok {
						return false
					}
					contract.Modes = append(contract.Modes, mode)
					contract.ModeTokens = append(contract.ModeTokens, word)
					if p.peekTokenIs(token.COMMA) {
						p.nextToken()
					} else if !p.peekTokenIs(token.RPAREN) {
						p.peekError(token.RPAREN)
						return false
					}
				}
				p.nextToken() // )
				if p.peekTokenIs(token.COLON) {
					p.nextToken() // :
					if !p.expectPeek(token.IDENT) {
						return false
					}
					if p.currentToken.Literal != "fresh" {
						p.addErrorAtCurrentToken(fmt.Sprintf("via: a callable contract's result is `fresh`, got %s", p.currentToken.Literal))
						return false
					}
					contract.ReturnsFresh = true
				}
				entry.Contract = contract
				transition.Modes = append(transition.Modes, entry)
			} else {
				mode, word, ok := parseMode(false)
				if !ok {
					return false
				}
				entry := &ast.ProtocolParameterMode{Token: word, Mode: mode}
				if !p.expectPeek(token.IDENT) {
					return false
				}
				entry.Name = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
				transition.Modes = append(transition.Modes, entry)
			}
			if p.peekTokenIs(token.COMMA) {
				p.nextToken()
			} else if !p.peekTokenIs(token.RPAREN) {
				p.peekError(token.RPAREN)
				return false
			}
		}
		p.nextToken() // )
	}
	if p.peekTokenIs(token.COLON) {
		p.nextToken() // :
		if !p.expectPeek(token.IDENT) {
			return false
		}
		result := &ast.ProtocolResultClause{Token: p.currentToken, Kind: p.currentToken.Literal}
		switch result.Kind {
		case "fresh":
		case "alias":
			if !p.expectPeek(token.IDENT) {
				return false
			}
			result.Names = append(result.Names, &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal})
		case "borrow":
			if p.peekTokenIs(token.IDENT) && p.peekToken.Literal == "mut" {
				p.nextToken()
				result.Kind = "borrow mut"
			}
			for {
				if !p.expectPeek(token.IDENT) {
					return false
				}
				result.Names = append(result.Names, &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal})
				if !p.peekTokenIs(token.COMMA) {
					break
				}
				p.nextToken() // ,
			}
		default:
			p.addErrorAtCurrentToken(fmt.Sprintf("via: expected a result identity (fresh, alias NAME, borrow NAME, borrow mut NAME), got %s", result.Kind))
			return false
		}
		transition.Result = result
	}
	return true
}

// parseFieldTagValue parses one tag value in a field clause: a bare
// literal (string, integer, true/false — bound to the schema's first
// declared field) or a record literal over schema fields. The closed
// value vocabulary is deliberate: tag values are compile-time data for
// projections, not expressions.
func (p *Parser) parseFieldTagValue() ast.Expression {
	switch p.currentToken.TokenKind {
	case token.STRING:
		return &ast.StringLiteral{Token: p.currentToken, Value: p.currentToken.Literal}
	case token.INT:
		return p.parseIntegerLiteral()
	case token.TRUE, token.FALSE:
		return &ast.Boolean{Token: p.currentToken, Value: p.currentTokenIs(token.TRUE)}
	case token.LBRACE:
		return p.parseRecordLiteral()
	default:
		p.addErrorAtCurrentToken("tag value must be a string, integer, true/false, or a record literal")
		return nil
	}
}

// parseRecordLayoutSpec parses the parenthesized layout clause after
// `struct`: comma-separated entries, each either the word `packed` or
// `align: <integer literal>`. Anything else is a parse error — the layout
// vocabulary is closed. On success the cursor sits on the token after `)`.
func (p *Parser) parseRecordLayoutSpec() *ast.RecordLayoutSpec {
	spec := &ast.RecordLayoutSpec{}
	p.nextToken() // consume (
	for {
		if !p.currentTokenIs(token.IDENT) {
			p.addErrorAtCurrentToken("expected 'packed' or 'align' in struct layout spec")
			return nil
		}
		switch p.currentToken.Literal {
		case "packed":
			if spec.Packed {
				p.addErrorAtCurrentToken("duplicate 'packed' in struct layout spec")
				return nil
			}
			spec.Packed = true
			p.nextToken()
		case "align":
			if spec.Align != 0 {
				p.addErrorAtCurrentToken("duplicate 'align' in struct layout spec")
				return nil
			}
			if !p.peekTokenIs(token.COLON) {
				p.addErrorAtCurrentToken("expected ':' after 'align' in struct layout spec")
				return nil
			}
			p.nextToken() // to :
			if !p.peekTokenIs(token.INT) {
				p.addErrorAtCurrentToken("expected integer alignment after 'align:'")
				return nil
			}
			p.nextToken() // to the integer
			value, err := strconv.ParseUint(p.currentToken.Literal, 10, 32)
			if err != nil || value == 0 || value&(value-1) != 0 {
				p.addErrorAtCurrentToken("struct alignment must be a nonzero power-of-two u32")
				return nil
			}
			spec.Align = uint32(value)
			p.nextToken()
		default:
			p.addErrorAtCurrentToken("expected 'packed' or 'align' in struct layout spec")
			return nil
		}
		if p.currentTokenIs(token.COMMA) {
			p.nextToken()
			continue
		}
		break
	}
	if !p.currentTokenIs(token.RPAREN) {
		p.peekError(token.RPAREN)
		return nil
	}
	p.nextToken() // consume )
	return spec
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

// peekTokenIsArithmetic reports whether the next token is an arithmetic
// operator, the start of a const-arithmetic array length.
func (p *Parser) peekTokenIsArithmetic() bool {
	switch p.peekToken.TokenKind {
	case token.SUM, token.NEG, token.MUL, token.QUO, token.REM:
		return true
	}
	return false
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

	// Arithmetic length: [M*K]T or [N+1]T over const parameters, folded to
	// a literal at instantiation (docs/spec/20-types.md section 11.0). Type
	// position has no literal ambiguity, so the length is an ordinary
	// expression up to the closing bracket.
	if (p.currentTokenIs(token.IDENT) || p.currentTokenIs(token.INT)) && p.peekTokenIsArithmetic() {
		length := p.parseExpression(LOWEST)
		if length == nil || !p.expectPeek(token.RBRACK) {
			return nil
		}
		p.nextToken() // move to the element type
		elementType := p.parseTypeExpression()
		if elementType == nil {
			return nil
		}
		return &ast.IndexExpression{
			Token: p.currentToken,
			Left:  elementType,
			Index: length,
		}
	}

	// Symbolic length: [N]T inside a generic template, where N is a const
	// parameter substituted at instantiation (docs/spec/20-types.md).
	if p.currentTokenIs(token.IDENT) && p.peekTokenIs(token.RBRACK) {
		lengthParam := &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
		p.nextToken() // move to ']'
		p.nextToken() // move to the element type
		elementType := p.parseTypeExpression()
		if elementType == nil {
			return nil
		}
		return &ast.IndexExpression{
			Token: p.currentToken,
			Left:  elementType,
			Index: lengthParam,
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
	defer p.operatorPipe()()

	// Skip opening brace (currentToken is {)
	p.nextToken()

	// Contract: leaves currentToken ON the closing '}' (the last token of
	// the literal), like every other prefix/infix expression parser — the
	// Pratt loop and statement loop advance past it themselves.

	// Extensible record type: { r | field: Type, ... }.
	if p.currentTokenIs(token.IDENT) && p.peekTokenIs(token.PIPE) {
		record.Extension = &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
		p.nextToken()
		p.nextToken()
	}

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
		var fieldValue ast.Expression
		if p.currentTokenIs(token.LPAREN) && p.functionTypeAhead() {
			// A function-typed member of a signature shape declared as
			// `Name: type = { hash: (Key) -> u64 }` (docs/spec/83-modules.md
			// section 6.3): the group is a type, not a value.
			fieldValue = p.parseTypeExpression()
		} else {
			fieldValue = p.parseExpression(LOWEST)
		}
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

	// Typed nested array literal: [N][M]Type{ ... } — the element type is
	// itself an array type, parsed by the type grammar.
	if p.lookaheadSignificant(1).TokenKind == token.INT &&
		p.lookaheadSignificant(2).TokenKind == token.RBRACK &&
		p.lookaheadSignificant(3).TokenKind == token.LBRACK {
		p.nextToken() // N
		size, isInt := p.parseIntegerLiteral().(*ast.IntegerLiteral)
		if !isInt {
			return nil
		}
		p.nextToken() // ]
		p.nextToken() // [ opening the element type
		elementType := p.parseArrayType()
		if elementType == nil {
			return nil
		}
		return p.parseTypedArrayLiteralWithToken(open, size, elementType)
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
		// A package-qualified type (pkg.Point { ... }, docs/spec/83-modules.md
		// section 3.4): keep the dotted name as one identifier for the
		// module elaborator to resolve, exactly like type position does.
		if access, isAccess := typeName.(*ast.IndexExpression); isAccess && access.Dot {
			base, baseOK := access.Left.(*ast.Identifier)
			member, memberOK := access.Index.(*ast.Identifier)
			if baseOK && memberOK {
				typeIdent = &ast.Identifier{Token: base.Token, Value: base.Value + "." + member.Value}
				ok = true
			}
		}
		if !ok {
			p.addErrorAtCurrentToken("a typed record literal requires a type name before {")
			return nil
		}
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
	defer p.operatorPipe()()
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
		// expectPeek consumed the identifier and left it current. Advancing here
		// would skip ':' and corrupt every receiver declaration into a nil AST.
		recvIdentToken := p.currentToken
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
		// Expression body: fn name(...): Type = expr. `= {` opens a block
		// body, as in the declaration form (docs/spec/10-syntax.md §3): a
		// whole-body record literal must use its named form.
		p.nextToken() // consume =
		p.nextToken() // advance to body
		if p.currentTokenIs(token.LBRACE) {
			stmt.Body = p.parseBlockExpression()
		} else {
			stmt.Body = p.parseExpression(LOWEST)
		}
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
		"exit":        true,
		"quit":        true,
		"help":        true,
		"clear":       true,
		"reset":       true,
		"typeof":      true,
		"ptrsize":     true,
		"obligations": true,
		"strict":      true,
		"lean":        true,
		"intsize":     true,
	}
	if !validCommands[commandName] {
		p.addErrorAtCurrentToken(fmt.Sprintf("unknown REPL command: %s (valid: exit, quit, help, clear, reset, typeof, ptrsize, intsize, obligations, strict, lean)", commandName))
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
		// A Bool conditional has two arms. A third bare '|' after them is
		// the classic misreading of a bitwise or inside an arm (F16): it
		// used to parse as an or over the whole conditional. Refuse it and
		// say what to write instead.
		if _, block := falseBody.(*ast.BlockExpression); !block && p.peekTokenIs(token.PIPE) {
			p.addErrorAtPeekToken("a `?` conditional has two arms and this `|` would start a third: inside a bare arm `|` is the arm separator, so write a bitwise or as `(a | b)` or brace the arm `{ a | b }`")
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
	p.armDepth++
	defer func() { p.armDepth-- }()
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

	body := p.parseMatchArmBody()
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

		body := p.parseMatchArmBody()
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

// parseMatchArmBody parses one arm body: a brace block (statements, the
// block's trailing expression as its value) or an expression. currentToken
// is the body's first token.
func (p *Parser) parseMatchArmBody() ast.Expression {
	if p.currentTokenIs(token.LBRACE) {
		return p.parseBlockExpression()
	}
	p.armDepth++
	defer func() { p.armDepth-- }()
	return p.parseExpression(LOWEST)
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

	// Effect clauses (docs/spec/60-effects-allocation.md section 2), in
	// either order, each at most once: effects { A.B, ... } forbids { ... }.
	// `effects` and `forbids` are contextual: only this position reads them.
	for p.peekTokenIs(token.IDENT) && (p.peekToken.Literal == "effects" || p.peekToken.Literal == "forbids") {
		p.nextToken()
		keyword := p.currentToken.Literal
		if (keyword == "effects" && stmt.EffectsDeclared) || (keyword == "forbids" && stmt.Forbids != nil) {
			p.addErrorAtCurrentToken(fmt.Sprintf("a function declares one %s clause", keyword))
			return nil
		}
		names, ok := p.parseEffectNameList()
		if !ok {
			return nil
		}
		if keyword == "effects" {
			stmt.Effects, stmt.EffectsDeclared = names, true
		} else {
			stmt.Forbids = names
		}
	}

	// Operator laws (docs/spec/10-syntax.md section 14a): `laws { associative,
	// commutative }`, contextual like the effect clauses, at most once.
	if p.peekTokenIs(token.IDENT) && p.peekToken.Literal == "laws" {
		p.nextToken()
		if stmt.Laws != nil {
			p.addErrorAtCurrentToken("a function declares one laws clause")
			return nil
		}
		if !p.expectPeek(token.LBRACE) {
			return nil
		}
		stmt.Laws = []string{}
		for !p.peekTokenIs(token.RBRACE) {
			if !p.expectPeek(token.IDENT) {
				return nil
			}
			stmt.Laws = append(stmt.Laws, p.currentToken.Literal)
			if p.peekTokenIs(token.COMMA) {
				p.nextToken()
			} else if !p.peekTokenIs(token.RBRACE) {
				p.peekError(token.RBRACE)
				return nil
			}
		}
		p.nextToken() // '}'
		if len(stmt.Laws) == 0 {
			p.addErrorAtCurrentToken("a laws clause names at least one law (associative, commutative)")
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
		// Definition-less declaration: the typed interface of a function
		// whose body an asm translation unit provides
		// (docs/spec/94-assembler.md §2). Legality — a unit must exist —
		// is the compilation's to decide, not the parser's.
		stmt.EndToken = p.currentToken
		return stmt
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

	// Tag schema declaration: json: tag = { name: string }. `tag` is
	// contextual (it stays a legal field/variable name); only the exact
	// shape IDENT ':' tag '=' '{' reads as a declaration.
	if p.currentTokenIs(token.IDENT) && p.currentToken.Literal == "tag" && p.peekTokenIs(token.ASSIGN) {
		return p.parseTagDeclarationFromName(name)
	}
	// Protocol declaration: Name: protocol = { ... } (docs/spec/112-protocols.md).
	// `protocol` is contextual too.
	if p.currentTokenIs(token.IDENT) && p.currentToken.Literal == "protocol" && p.peekTokenIs(token.ASSIGN) {
		if decl := p.parseProtocolDeclarationFromName(name); decl != nil {
			return decl
		}
		return nil
	}
	// Theorem declaration: name: theorem (params) { Bool }
	// (docs/spec/125-verification.md). `theorem` is contextual: only the
	// shape IDENT ':' theorem '(' reads as one. The parameters are the
	// function grammar's; the result type is Bool and is never written.
	if p.currentTokenIs(token.IDENT) && p.currentToken.Literal == "theorem" && p.peekTokenIs(token.LPAREN) {
		kind := p.currentToken
		p.nextToken()
		fn := p.parseFunctionDefinitionFromName(name)
		if fn == nil {
			return nil
		}
		if fn.ReturnType != nil {
			p.addErrorAtToken(&kind, "a theorem's result is Bool; it declares no return type")
			return nil
		}
		if fn.Body == nil {
			p.addErrorAtToken(&kind, "a theorem states a Bool expression; it has no definition-less form")
			return nil
		}
		boolToken := kind
		boolToken.TokenKind = token.IDENT
		boolToken.Literal = "Bool"
		fn.ReturnType = &ast.Identifier{Token: boolToken, Value: "Bool"}
		fn.Theorem = true
		if len(typeParams) > 0 {
			fn.TypeParams = typeParams
		}
		return fn
	}

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

	// Refinement: Name: type = Base where <Bool over value>
	// (docs/spec/20-types.md section 12). `where` is contextual; the base
	// is the single variant's type, whichever branch above read it.
	if len(adt.Variants) == 1 && p.peekToken.Literal == "where" {
		base := adt.Variants[0]
		if base.Payload == nil && base.Literal == nil && base.Name != nil {
			base.Payload = &ast.Identifier{Token: base.Name.Token, Value: base.Name.Value}
			base.Name = adt.Name
		}
		if base.Payload == nil {
			p.addErrorAtCurrentToken("a refinement names a base type before `where`")
			return nil
		}
		p.nextToken()
		p.nextToken()
		adt.Refinement = p.parseExpression(LOWEST)
		if adt.Refinement == nil {
			return nil
		}
		adt.EndToken = p.currentToken
		return adt
	}

	return adt
}

// validSectionName admits ELF (.shared) and Mach-O (__DATA,__shared)
// section spellings and nothing that could escape a C string literal.
func validSectionName(name string) bool {
	if name == "" {
		return false
	}
	for _, r := range name {
		switch {
		case r >= 'a' && r <= 'z', r >= 'A' && r <= 'Z', r >= '0' && r <= '9', r == '_', r == '.', r == ',', r == '$':
		default:
			return false
		}
	}
	return true
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

	// Optional placement clause: name: Type (section: "shared"). The
	// section name is validated here so nothing but a plain section
	// spelling can reach generated C.
	if p.peekTokenIs(token.LPAREN) {
		p.nextToken() // to (
		if !p.expectPeek(token.IDENT) || p.currentToken.Literal != "section" {
			p.addErrorAtCurrentToken("placement clause takes the form (section: \"name\")")
			return nil
		}
		if !p.expectPeek(token.COLON) || !p.expectPeek(token.STRING) {
			return nil
		}
		if !validSectionName(p.currentToken.Literal) {
			p.addErrorAtCurrentToken(fmt.Sprintf("section name %q must match [A-Za-z0-9_.,$]+", p.currentToken.Literal))
			return nil
		}
		stmt.Section = p.currentToken.Literal
		if !p.expectPeek(token.RPAREN) {
			return nil
		}
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

// parseDiscardStatement parses the explicit discard form `_ = expr`
// (docs/spec/85-discipline.md section 6). It is an expression statement
// marked Discard: the value is evaluated and its result deliberately
// dropped; `_` binds nothing and is never a variable.
func (p *Parser) parseDiscardStatement() *ast.ExpressionStatement {
	stmt := &ast.ExpressionStatement{Token: p.currentToken, Discard: true}
	if !p.expectPeek(token.ASSIGN) {
		return nil
	}
	p.nextToken() // consume =, now at the first token of the value
	stmt.Expression = p.parseExpression(LOWEST)
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
