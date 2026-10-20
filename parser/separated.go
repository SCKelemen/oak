package parser

import "github.com/SCKelemen/oak/token"

// parseDelimited is the canonical contract for delimiter-contained sequences.
//
// Precondition: currentToken is open.
// Success postcondition: currentToken is close.
// parseItem starts on the first token of an item and leaves currentToken on the
// item's final token. Empty sequences and, when requested, trailing separators
// obey the same postcondition.
func (p *Parser) parseDelimited[T any](
	open token.TokenKind,
	close token.TokenKind,
	separator token.TokenKind,
	allowTrailing bool,
	parseItem func() (T, bool),
) ([]T, bool) {
	if !p.currentTokenIs(open) {
		p.addErrorAtCurrentToken("delimited parser entered on wrong opening token")
		return nil, false
	}
	return p.parseSeparated(close, separator, allowTrailing, parseItem)
}

// parseSeparated implements the sequence after the opening delimiter has been
// established by the caller. It is kept as the small common primitive used by
// existing productions while they migrate to parseDelimited.
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

	errorsBefore := len(p.diagnostics.Errors())
	p.nextToken()
	for {
		itemToken := p.currentToken
		item, ok := parseItem()
		if !ok {
			// A failed required item is never a successful empty sequence.
			// Preserve a production's own error, or diagnose its silent failure.
			if len(p.diagnostics.Errors()) == errorsBefore {
				p.addErrorAtToken(&itemToken, "expected list item")
			}
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

		// Include lexical errors found while advancing to the required item.
		errorsBefore = len(p.diagnostics.Errors())
		p.nextToken() // separator
		if allowTrailing && p.peekTokenIs(close) {
			p.nextToken()
			return items, true
		}
		p.nextToken() // first token of next item
	}
}
