// Package layout normalizes Oak's optional indentation-delimited statement bodies
// into the same brace-delimited token structure consumed by the parser.
//
// Layout is syntax sugar only. Synthetic tokens use the ordinary LBRACE/RBRACE
// kinds and are marked Token.Synthetic so later tooling can preserve source style.
package layout

import (
	"github.com/SCKelemen/oak/source"
	"github.com/SCKelemen/oak/token"
)

// Source is kept as a compatibility alias while token.Source becomes the shared
// compiler-wide token stream contract.
type Source = token.Source

// Normalizer presents a normalized token stream.
type Normalizer struct {
	tokens []token.Token
	index  int
	file   *source.File
}

// New consumes source once and constructs a deterministic normalized stream.
// The compiler-side allocation here is intentional: normalization is tooling,
// not target runtime code, and a materialized stream makes equivalence testing
// and diagnostics straightforward.
func New(src token.Source) *Normalizer {
	raw := make([]token.Token, 0, 256)
	for {
		tok := src.NextToken()
		raw = append(raw, tok)
		if tok.TokenKind == token.EOF {
			break
		}
	}

	var file *source.File
	if located, ok := src.(token.LocatedSource); ok {
		file = located.SourceFile()
	}
	return &Normalizer{tokens: normalize(raw), file: file}
}

// NextToken implements token.Source.
func (n *Normalizer) NextToken() token.Token {
	if n.index >= len(n.tokens) {
		return token.Token{TokenKind: token.EOF}
	}
	tok := n.tokens[n.index]
	n.index++
	return tok
}

// SourceFile preserves source identity across normalization.
func (n *Normalizer) SourceFile() *source.File { return n.file }

type pendingBody struct {
	active   bool
	kind     token.TokenKind
	indent   int
	optional bool // identifier-first signatures may be definition-less asm declarations
}

func normalize(raw []token.Token) []token.Token {
	out := make([]token.Token, 0, len(raw)+8)
	type layoutBody struct {
		indent, explicitDepth int
	}
	bodies := make([]layoutBody, 0, 8)
	headers := make(map[int]pendingBody)
	explicitDepth := 0
	headerEnd := -1
	typeEnd := -1

	var pending pendingBody
	var previous token.Token
	havePrevious := false
	parenDepth := 0
	bracketDepth := 0
	line := 0
	lineIndent := 1

	for i, tok := range raw {
		if tok.TokenKind == token.TRIVIA || tok.TokenKind == token.COMMENT {
			out = append(out, tok)
			continue
		}

		if tok.TokenKind == token.EOF {
			for len(bodies) > 0 {
				out = append(out, synthetic(token.RBRACE, tok))
				bodies = bodies[:len(bodies)-1]
			}
			out = append(out, tok)
			break
		}

		newLine := havePrevious && tok.Line > previous.Line
		if tok.Line != line {
			line = tok.Line
			lineIndent = tok.Column
		}

		// Parentheses, brackets, and recognized callable headers are continuation
		// contexts. Indentation inside them never opens or closes a body.
		continuation := parenDepth > 0 || bracketDepth > 0 || i <= headerEnd

		// Braces delimit their own extent irrespective of indentation. In
		// particular, a left-aligned line inside an explicit block cannot
		// close a layout body outside that block.
		if tok.TokenKind == token.RBRACE {
			for len(bodies) > 0 && bodies[len(bodies)-1].explicitDepth >= explicitDepth {
				out = append(out, synthetic(token.RBRACE, tok))
				bodies = bodies[:len(bodies)-1]
			}
			pending.active = false
		}

		// An explicit body or initializer on the next line still belongs to
		// the callable header. Check this before indentation.
		if pending.active && (tok.TokenKind == token.LBRACE || (tok.TokenKind == token.ASSIGN && pending.kind == token.FN)) {
			pending.active = false
		}

		if newLine && !continuation {
			if pending.active {
				if tok.Column > pending.indent {
					out = append(out, synthetic(token.LBRACE, tok))
					bodies = append(bodies, layoutBody{tok.Column, explicitDepth})
				} else if !pending.optional {
					out = append(out, token.Token{
						TokenKind: token.ILLEGAL,
						Literal:   "expected indented body",
						Line:      tok.Line,
						Column:    tok.Column,
						EndLine:   tok.Line,
						EndColumn: tok.Column,
						ByteStart: tok.ByteStart,
						ByteEnd:   tok.ByteStart,
						Synthetic: true,
					})
				}
				pending.active = false
			}
			for len(bodies) > 0 && bodies[len(bodies)-1].explicitDepth == explicitDepth && tok.Column < bodies[len(bodies)-1].indent {
				out = append(out, synthetic(token.RBRACE, tok))
				bodies = bodies[:len(bodies)-1]
			}
		}

		// A callable's same-line continuation is an expression body or
		// initializer. `unsafe` likewise is a marker in `via unsafe f(...)`.
		if pending.active && !newLine && (pending.kind == token.FN || pending.kind == token.UNSAFE) {
			pending.active = false
		}

		// Locate only the boundary of a callable header, without interpreting
		// its types or clauses. Waiting until that boundary keeps multiline
		// parameters, return types, and clause braces out of layout decisions.
		if tok.TokenKind == token.FN || (tok.TokenKind == token.IDENT && !continuation && i > typeEnd) {
			if end, ok := callableHeaderEnd(raw, i, lineIndent); ok {
				if end > headerEnd {
					headerEnd = end
				}
				if _, found := headers[end]; !found && !interfaceMethodHeader(raw, i) {
					headers[end] = pendingBody{active: true, kind: token.FN, indent: lineIndent, optional: tok.TokenKind != token.FN}
				}
			}
		}

		// Type spans contain fields, not local declarations. In particular,
		// `callback: () -> T` inside an explicit record must never open a
		// layout body merely because its next field is more indented.
		if i >= typeEnd {
			if end, ok := declaredTypeEnd(raw, i); ok {
				typeEnd = end
			}
		}

		out = append(out, tok)

		switch tok.TokenKind {
		case token.WHILE, token.UNSAFE:
			pending = pendingBody{
				active: true,
				kind:   tok.TokenKind,
				indent: lineIndent,
			}
		case token.LBRACE:
			explicitDepth++
		case token.RBRACE:
			if explicitDepth > 0 {
				explicitDepth--
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

		if header, ok := headers[i]; ok {
			pending = header
			delete(headers, i)
		}

		previous = tok
		havePrevious = true
	}

	return out
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
		EndLine:   at.Line,
		EndColumn: at.Column,
		ByteStart: at.ByteStart,
		ByteEnd:   at.ByteStart,
		Synthetic: true,
	}
}
