package token

import (
	"fmt"

	"github.com/SCKelemen/oak/source"
)

// Cursor adds deterministic, non-consuming lookahead to any token Source.
// It buffers only tokens that have already been requested or peeked; normal
// parsing remains a single forward pass with no source re-lexing.
type Cursor struct {
	source Source
	file   *source.File
	tokens []Token
	pos    int
}

func NewCursor(src Source) *Cursor {
	var file *source.File
	if located, ok := src.(LocatedSource); ok {
		file = located.SourceFile()
	}
	return &Cursor{source: src, file: file, tokens: make([]Token, 0, 16)}
}

func (c *Cursor) NextToken() Token {
	if c.pos < len(c.tokens) {
		tok := c.tokens[c.pos]
		c.pos++
		return tok
	}
	if c.source == nil {
		return Token{TokenKind: EOF}
	}
	tok := c.source.NextToken()
	c.tokens = append(c.tokens, tok)
	c.pos++
	return tok
}

// Peek returns the raw token offset places after the next unread token without
// advancing the cursor. offset=0 is the next token NextToken would return.
func (c *Cursor) Peek(offset int) Token {
	if offset < 0 {
		return Token{TokenKind: ILLEGAL, Literal: "negative token lookahead"}
	}
	index := c.pos + offset
	for len(c.tokens) <= index {
		if c.source == nil {
			return Token{TokenKind: EOF}
		}
		tok := c.source.NextToken()
		c.tokens = append(c.tokens, tok)
		if tok.TokenKind == EOF && len(c.tokens) <= index {
			return tok
		}
	}
	return c.tokens[index]
}

func (c *Cursor) Mark() int { return c.pos }

func (c *Cursor) Reset(mark int) error {
	if mark < 0 || mark > len(c.tokens) {
		return fmt.Errorf("invalid token cursor mark %d", mark)
	}
	c.pos = mark
	return nil
}

func (c *Cursor) SourceFile() *source.File { return c.file }
