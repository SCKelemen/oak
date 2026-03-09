package util

import (
	uax31 "github.com/SCKelemen/unicode/uax31"
	"unicode"
	"unicode/utf8"
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

// DigitValue returns the decimal value (0..9) for a Unicode decimal digit.
// The second return value is false when r is not a decimal digit.
func DigitValue(r rune) (int, bool) {
	if '0' <= r && r <= '9' {
		return int(r - '0'), true
	}

	// unicode.Digit contains all Nd code points. Nd blocks are structured as
	// sequences of ten decimal digits in increasing order.
	for _, rr := range unicode.Digit.R16 {
		lo := rune(rr.Lo)
		hi := rune(rr.Hi)
		stride := rune(rr.Stride)
		if r < lo || r > hi {
			continue
		}
		if stride == 0 || (r-lo)%stride != 0 {
			continue
		}
		idx := (r - lo) / stride
		return int(idx % 10), true
	}
	for _, rr := range unicode.Digit.R32 {
		lo := rune(rr.Lo)
		hi := rune(rr.Hi)
		stride := rune(rr.Stride)
		if r < lo || r > hi {
			continue
		}
		if stride == 0 || (r-lo)%stride != 0 {
			continue
		}
		idx := (r - lo) / stride
		return int(idx % 10), true
	}
	return 0, false
}

// NormalizeDigits rewrites Unicode decimal digits in s to ASCII digits.
// Non-digit runes are preserved unchanged.
func NormalizeDigits(s string) string {
	// Fast path for pure ASCII.
	isASCII := true
	for i := 0; i < len(s); i++ {
		if s[i] >= utf8.RuneSelf {
			isASCII = false
			break
		}
	}
	if isASCII {
		return s
	}

	out := make([]rune, 0, len(s))
	for _, r := range s {
		if d, ok := DigitValue(r); ok {
			out = append(out, rune('0'+d))
			continue
		}
		out = append(out, r)
	}
	return string(out)
}
