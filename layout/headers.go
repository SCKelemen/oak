package layout

import "github.com/SCKelemen/oak/token"

// headerCursor recognizes balanced surface spans, not their validity or meaning.
// The parser remains responsible for parameter/type/clause validation. This cursor
// only finds where a callable may start an indentation-delimited body.
type headerCursor struct {
	tokens []token.Token
	index  int
	last   int
}

func (c *headerCursor) kind() token.TokenKind {
	if c.index >= len(c.tokens) {
		return token.EOF
	}
	return c.tokens[c.index].TokenKind
}

func (c *headerCursor) advance() {
	c.last = c.index
	c.index++
	for c.index < len(c.tokens) && (c.kind() == token.TRIVIA || c.kind() == token.COMMENT) {
		c.index++
	}
}

func (c *headerCursor) group() bool {
	var close token.TokenKind
	switch c.kind() {
	case token.LPAREN:
		close = token.RPAREN
	case token.LBRACK:
		close = token.RBRACK
	case token.LBRACE:
		close = token.RBRACE
	default:
		return false
	}
	c.advance()
	for c.kind() != close {
		switch c.kind() {
		case token.EOF, token.RPAREN, token.RBRACK, token.RBRACE:
			return false
		case token.LPAREN, token.LBRACK, token.LBRACE:
			if !c.group() {
				return false
			}
		default:
			c.advance()
		}
	}
	c.advance()
	return true
}

func callableHeaderEnd(tokens []token.Token, start, indent int) (int, bool) {
	c := headerCursor{tokens: tokens, index: start}
	keyword := c.kind() == token.FN
	theorem := false
	if keyword {
		c.advance()
		if c.kind() == token.LBRACK && !c.group() {
			return 0, false
		}
		if c.kind() == token.LPAREN {
			// A receiver group is followed by a method name and its own
			// parameters. Otherwise this group belongs to a function literal.
			receiver := c
			if !receiver.group() {
				return 0, false
			}
			if receiver.kind() == token.IDENT {
				c = receiver
			}
		}
		if c.kind() == token.IDENT {
			c.advance()
		}
	} else {
		// Quantifiers have an explicit brace grammar, not callable syntax.
		if tokens[start].Literal == "forall" || tokens[start].Literal == "exists" {
			return 0, false
		}
		c.advance() // declaration name
		if c.kind() == token.LBRACK && !c.group() {
			return 0, false
		}
		if c.kind() == token.COLON {
			c.advance()
			if c.kind() == token.IDENT && c.tokens[c.index].Literal == "theorem" {
				theorem = true
				c.advance()
			}
		}
	}
	if c.kind() != token.LPAREN {
		return 0, false
	}
	// Match the parser's callable/ordinary-call distinction: an annotated
	// parameter at the outer level, or an empty list with a result annotation.
	params := c
	params.advance()
	empty := params.kind() == token.RPAREN
	annotated := false
	for params.kind() != token.RPAREN {
		switch params.kind() {
		case token.EOF:
			return 0, false
		case token.LPAREN, token.LBRACK, token.LBRACE:
			if !params.group() {
				return 0, false
			}
		default:
			annotated = annotated || params.kind() == token.COLON
			params.advance()
		}
	}
	params.advance()
	if !keyword && !theorem && !annotated && !(empty && (params.kind() == token.COLON || params.kind() == token.ARROW)) {
		return 0, false
	}
	c = params
	if c.kind() == token.COLON || c.kind() == token.ARROW {
		c.advance()
		if !c.typeSpan() {
			return 0, false
		}
	}
	// Callable markers and the closed set of semantic clauses. Their
	// contents are balanced only; the owning parser validates each one.
	if c.kind() == token.LPAREN {
		marker := c
		marker.advance()
		if marker.kind() == token.IDENT && marker.tokens[marker.index].Literal == "kernel" {
			marker.advance()
			if marker.kind() == token.RPAREN {
				marker.advance()
				// A legacy bare expression body may itself be `(kernel)`.
				// Only a following definition/clause, or an indented body,
				// makes this the callable marker rather than that expression.
				clause := !keyword || marker.kind() == token.ASSIGN || marker.kind() == token.LBRACE
				if marker.kind() == token.IDENT {
					switch marker.tokens[marker.index].Literal {
					case "effects", "forbids", "laws", "dispatch":
						clause = true
					}
				}
				if marker.kind() != token.EOF {
					next := marker.tokens[marker.index]
					clause = clause || (next.Line > marker.tokens[marker.last].EndLine && next.Column > indent)
				}
				if clause {
					c = marker
				}
			}
		}
	}
	for c.kind() == token.IDENT {
		switch c.tokens[c.index].Literal {
		case "effects", "forbids", "laws", "dispatch":
			clause := c
			clause.advance()
			if clause.kind() != token.LBRACE {
				// These are ordinary identifiers unless the clause's
				// opening brace follows: a body can bind `effects := 1`.
				return c.last, true
			}
			c = clause
			if !c.group() {
				return 0, false
			}
		default:
			return c.last, true
		}
	}
	return c.last, true
}

// typeSpan skips the structural extent of a type, including a result that is
// itself a function type. It never constructs types or accepts source: a span
// recognized here is still parsed and checked through the ordinary front end.
func (c *headerCursor) typeSpan() bool {
	switch c.kind() {
	case token.IDENT, token.TYPE:
		c.advance()
		for c.kind() == token.DOT {
			c.advance()
			if c.kind() != token.IDENT {
				return false
			}
			c.advance()
		}
		if c.kind() == token.LBRACK && !c.group() {
			return false
		}
	case token.LBRACK:
		if !c.group() || !c.typeSpan() {
			return false
		}
	case token.LPAREN:
		if !c.group() {
			return false
		}
		if c.kind() == token.ARROW {
			c.advance()
			if !c.typeSpan() {
				return false
			}
		}
	case token.STRUCT:
		c.advance()
		if c.kind() == token.LPAREN && !c.group() {
			return false
		}
		if c.kind() != token.LBRACE || !c.group() {
			return false
		}
	case token.LBRACE:
		if !c.group() {
			return false
		}
	default:
		return false
	}
	if c.kind() == token.AMP {
		c.advance()
		return c.typeSpan()
	}
	return true
}

// Interface methods declare a signature, never a body. The `fn` belongs to
// `Name: interface = fn ...` (or its prefix compatibility spelling), so its
// full header is a continuation span but must not require/open a layout body.
func interfaceMethodHeader(tokens []token.Token, start int) bool {
	if tokens[start].TokenKind != token.FN {
		return false
	}
	previous := func() token.TokenKind {
		for start--; start >= 0; start-- {
			kind := tokens[start].TokenKind
			if kind != token.TRIVIA && kind != token.COMMENT {
				return kind
			}
		}
		return token.EOF
	}
	return previous() == token.ASSIGN && previous() == token.INTERFACE
}

// declaredTypeEnd recognizes type-position extents that can contain explicit
// record fields: annotations, type-definition right-hand sides, and struct
// forms. It suppresses declaration lookahead only, never braces or expression
// parsing. Value-only tokens distinguish parenthesized/record expressions from
// type spans when a colon is also usable as a record-value field separator.
func declaredTypeEnd(tokens []token.Token, start int) (int, bool) {
	c := headerCursor{tokens: tokens, index: start}
	switch c.kind() {
	case token.STRUCT:
	case token.TYPE:
		c.advance()
		if c.kind() != token.ASSIGN {
			return 0, false
		}
		c.advance()
	case token.COLON:
		c.advance()
	default:
		return 0, false
	}
	if !c.typeSpan() {
		return 0, false
	}
	for i := start; i <= c.last; i++ {
		switch tokens[i].TokenKind {
		case token.FN, token.QMARK, token.COLON_ASSIGN, token.WHILE, token.RETURN, token.DEFER, token.UNSAFE:
			return 0, false
		}
	}
	return c.last, true
}
