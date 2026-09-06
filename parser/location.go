package parser

import (
	"fmt"

	"github.com/SCKelemen/oak/source"
	"github.com/SCKelemen/oak/token"
)

// SourceFile returns the source identity preserved by the token pipeline, when
// available. Parser semantics do not depend on source paths; diagnostics and
// tooling may project them from this optional metadata.
func (p *Parser) SourceFile() *source.File {
	if located, ok := p.source.(token.LocatedSource); ok {
		return located.SourceFile()
	}
	return nil
}

// SourceSpan converts a token's canonical UTF-8 byte offsets to a checked span.
func (p *Parser) SourceSpan(tok token.Token) (source.Span, error) {
	file := p.SourceFile()
	if file == nil {
		return source.Span{}, fmt.Errorf("parser token source has no source-file identity")
	}
	return file.Span(tok.ByteStart, tok.ByteEnd)
}

// Location returns the conventional filename:line:column form used by VS Code
// terminal linkification and compiler diagnostics.
func (p *Parser) Location(tok token.Token) (string, error) {
	file := p.SourceFile()
	if file == nil {
		return "", fmt.Errorf("parser token source has no source-file identity")
	}
	span, err := p.SourceSpan(tok)
	if err != nil {
		return "", err
	}
	return file.Location(span)
}

// VSCodeURI returns an explicit vscode://file hyperlink for tok.
func (p *Parser) VSCodeURI(tok token.Token) (string, error) {
	file := p.SourceFile()
	if file == nil {
		return "", fmt.Errorf("parser token source has no source-file identity")
	}
	span, err := p.SourceSpan(tok)
	if err != nil {
		return "", err
	}
	return file.VSCodeURI(span)
}
