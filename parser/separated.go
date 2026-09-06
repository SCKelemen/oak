package parser

import "github.com/SCKelemen/oak/token"

// parseSeparated parses a delimiter-contained sequence of T using the parser's
// existing two-token cursor convention. currentToken must be the opening
// delimiter when called. parseItem receives currentToken positioned at the
// first token of an item and must leave it at that item's final token.
//
// This is the common mechanism behind function parameters, call arguments,
// generic arguments, type parameters, array elements, and similar grammar
// forms. Go 1.27 generic methods let the operation live on Parser instead of
// proliferating type-specific package helpers.
//
// Existing grammar productions should migrate onto this one at a time, keeping
// their parser tests green after each change. Reducing duplicated token
// movement is useful; changing several positioning contracts at once is not.
func (p *Parser) parseSeparated[T any](
	close token.TokenKind,
	separator token.TokenKind,
	allowTrailing bool,
	parseItem func() (T, bool),
) ([]T, bool) {
	items := make([]T, 0)

	if p.peekTokenIs(close) {
		p.nextToken()
		return items, true
	}

	p.nextToken()
	for {
		item, ok := parseItem()
		if !ok {
			return nil, false
		}
		items = append(items, item)

		if p.peekTokenIs(close) {
			p.nextToken()
			return items, true
		}
		if !p.peekTokenIs(separator) {
			p.peekError(close)
			return nil, false
		}

		p.nextToken() // separator
		if allowTrailing && p.peekTokenIs(close) {
			p.nextToken()
			return items, true
		}
		p.nextToken() // first token of next item
	}
}
