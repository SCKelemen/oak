package parser

import "github.com/SCKelemen/oak/token"

// NewSource is a compatibility spelling for New. Parser itself owns the
// token.Source directly; there is no scanner adapter in this path.
func NewSource(source token.Source) *Parser {
	return New(source)
}
