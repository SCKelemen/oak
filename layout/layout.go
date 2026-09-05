// Package layout normalizes Oak's optional indentation-delimited statement bodies
// into the same brace-delimited token structure consumed by the parser.
//
// Layout is syntax sugar only. Synthetic tokens use the ordinary LBRACE/RBRACE
// kinds and are marked Token.Synthetic so later tooling can preserve source style.
package layout

import "github.com/SCKelemen/oak/token"

// Source is the minimal token source shared by the scanner and normalizer.
type Source interface {
	NextToken() token.Token
}

// Normalizer presents a normalized token stream.
type Normalizer struct {
	tokens []token.Token
	index  int
}

// New consumes source once and constructs a deterministic normalized stream.
// The compiler-side allocation here is intentional: normalization is tooling,
// not target runtime code, and a materialized stream makes equivalence testing
// and diagnostics straightforward.
func New(source Source) *Normalizer {
	raw := make([]token.Token, 0, 256)
	for {
		tok := source.NextToken()
		raw = append(raw, tok)
		if tok.TokenKind == token.EOF {
			break
		}
	}
	return &Normalizer{tokens: normalize(raw)}
}

// NextToken implements Source.
func (n *Normalizer) NextToken() token.Token {
	if n.index >= len(n.tokens) {
		return token.Token{TokenKind: token.EOF}
	}
	tok := n.tokens[n.index]
	n.index++
	return tok
}

type pendingBody struct {
	active bool
	kind   token.TokenKind
	indent int
	line   int
}

func normalize(raw []token.Token) []token.Token {
	out := make([]token.Token, 0, len(raw)+8)
	layoutIndents := make([]int, 0, 8)

	var pending pendingBody
	var previous token.Token
	havePrevious := false
	parenDepth := 0
	bracketDepth := 0
	line := 0
	lineIndent := 1

	for _, tok := range raw {
		if tok.TokenKind == token.TRIVIA || tok.TokenKind == token.COMMENT {
			out = append(out, tok)
			continue
		}

		if tok.TokenKind == token.EOF {
			for len(layoutIndents) > 0 {
				out = append(out, synthetic(token.RBRACE, tok))
				layoutIndents = layoutIndents[:len(layoutIndents)-1]
			}
			out = append(out, tok)
			break
		}

		newLine := havePrevious && tok.Line > previous.Line
		if tok.Line != line {
			line = tok.Line
			lineIndent = tok.Column
		}

		// Parenthesized and bracketed forms are continuation contexts. Indentation
		// inside them never opens or closes a statement body.
		continuation := parenDepth > 0 || bracketDepth > 0

		if newLine && !continuation {
			if pending.active && !headerContinues(pending.kind, tok) {
				if tok.Column <= pending.indent {
					out = append(out, token.Token{
						TokenKind: token.ILLEGAL,
						Literal:   "expected indented body",
						Line:      tok.Line,
						Column:    tok.Column,
						ByteStart: tok.ByteStart,
						ByteEnd:   tok.ByteStart,
						Synthetic: true,
					})
					pending.active = false
				} else {
					out = append(out, synthetic(token.LBRACE, tok))
					layoutIndents = append(layoutIndents, tok.Column)
					pending.active = false
				}
			} else if !pending.active {
				for len(layoutIndents) > 0 && tok.Column < layoutIndents[len(layoutIndents)-1] {
					out = append(out, synthetic(token.RBRACE, tok))
					layoutIndents = layoutIndents[:len(layoutIndents)-1]
				}
			}
		}

		// An explicit block always wins. It cancels layout synthesis for the body
		// currently being introduced but remains an ordinary source token.
		if tok.TokenKind == token.LBRACE && pending.active {
			pending.active = false
		}

		// Oak currently permits expression-bodied functions using '='. Do not
		// synthesize a block for those functions.
		if tok.TokenKind == token.ASSIGN && pending.active && pending.kind == token.FN {
			pending.active = false
		}

		out = append(out, tok)

		switch tok.TokenKind {
		case token.FN, token.WHILE, token.UNSAFE:
			pending = pendingBody{
				active: true,
				kind:   tok.TokenKind,
				indent: lineIndent,
				line:   tok.Line,
			}
		case token.LPAREN:
			parenDepth++
		case token.RPAREN:
			if parenDepth > 0 {
				parenDepth--
			}
		case token.LBRACK:
			bracketDepth++
		case token.RBRACK:
			if bracketDepth > 0 {
				bracketDepth--
			}
		}

		previous = tok
		havePrevious = true
	}

	return out
}

func headerContinues(kind token.TokenKind, next token.Token) bool {
	// A function return annotation may start on the line after its parameter
	// list. Keeping this tiny and explicit is preferable to a second parser in
	// the layout layer.
	if kind == token.FN && next.TokenKind == token.COLON {
		return true
	}
	return false
}

func synthetic(kind token.TokenKind, at token.Token) token.Token {
	literal := "{"
	if kind == token.RBRACE {
		literal = "}"
	}
	return token.Token{
		TokenKind: kind,
		Literal:   literal,
		Line:      at.Line,
		Column:    at.Column,
		ByteStart: at.ByteStart,
		ByteEnd:   at.ByteStart,
		Synthetic: true,
	}
}