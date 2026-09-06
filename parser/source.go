package parser

import (
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/token"
)

// NewSource constructs a parser from any token.Source.
//
// Parser historically stores *scanner.Scanner internally. scanner.FromSource
// is a narrow compatibility adapter so callers can compose Scanner -> Layout ->
// Parser today without duplicating the parser. The concrete field can disappear
// once parser.go itself is migrated to token.Source.
func NewSource(source token.Source) *Parser {
	return New(scanner.FromSource(source))
}
