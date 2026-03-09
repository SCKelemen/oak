package util

import (
	uax31 "github.com/SCKelemen/unicode/uax31"
	"unicode"
)

func IsDigit(ch rune) bool {
	return ('0' <= ch && ch <= '9') || unicode.IsDigit(ch)
}

func IsLetter(ch rune) bool {
	return ('a' <= ch && ch <= 'z') || ('A' <= ch && ch <= 'Z') || ch == '_' || uax31.IsXIDStart(ch)
}

func IsWhitespace(ch rune) bool {
	return ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r'
}

// Identifiers start with Letters or _
// Identifiers may contain Letters, _, or Digits

func IsIdentifierInitialChar(ch rune) bool {
	return ch == '_' || uax31.IsValidIdentifierStart(ch) || IsLetter(ch)
}
func IsIdentifierChar(ch rune) bool {
	return ch == '_' || uax31.IsValidIdentifierContinue(ch) || IsLetter(ch) || IsDigit(ch)
}

// Numbers start with Digits
// May contain [0-9] || _

func IsNumericInitialChar(ch rune) bool {
	return IsDigit(ch)
}

func IsNumericChar(ch rune) bool {
	return IsDigit(ch) || ch == '_'
}

func IsQuote(ch rune) bool {
	return ch == '"'
}
