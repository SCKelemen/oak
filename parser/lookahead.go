package parser

import "github.com/SCKelemen/oak/token"

// lookaheadSignificant returns the nth non-trivia token relative to currentToken.
// distance 0 is currentToken; distance 1 is peekToken. Parser.New always wraps
// its input in token.Cursor, so larger lookahead remains non-consuming.
func (p *Parser) lookaheadSignificant(distance int) token.Token {
	if distance <= 0 {
		return p.currentToken
	}
	if distance == 1 {
		return p.peekToken
	}
	cursor, ok := p.source.(*token.Cursor)
	if !ok {
		return token.Token{TokenKind: token.ILLEGAL, Literal: "parser token source is not buffered"}
	}

	remaining := distance - 1
	for raw := 0; ; raw++ {
		tok := cursor.Peek(raw)
		if tok.TokenKind == token.TRIVIA || tok.TokenKind == token.COMMENT {
			continue
		}
		remaining--
		if remaining == 0 || tok.TokenKind == token.EOF {
			return tok
		}
	}
}
