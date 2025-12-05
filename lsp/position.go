package lsp

import (
	"strings"
	"unicode/utf8"
)

// Position represents a position in a text document (LSP-style, zero-based)
type Position struct {
	Line      int // Zero-based line number
	Character int // Zero-based character offset (UTF-16 code units for LSP)
}

// Range represents a range in a text document (LSP-style)
type Range struct {
	Start Position
	End   Position
}

// Location represents a location inside a resource (LSP-style)
type Location struct {
	URI   string // Document URI
	Range Range
}

// UTF8ToUTF16Offset converts a UTF-8 byte offset to a UTF-16 code unit offset
// This is needed because LSP uses UTF-16 for character offsets
func UTF8ToUTF16Offset(text string, utf8Offset int) int {
	if utf8Offset < 0 || utf8Offset > len(text) {
		return utf8Offset
	}

	// Count UTF-16 code units up to the UTF-8 byte offset
	utf16Offset := 0
	byteOffset := 0
	for byteOffset < utf8Offset && byteOffset < len(text) {
		r, size := utf8.DecodeRuneInString(text[byteOffset:])
		if r == utf8.RuneError && size == 1 {
			// Invalid UTF-8, skip one byte
			byteOffset++
			utf16Offset++
			continue
		}
		byteOffset += size
		// Count UTF-16 code units for this rune
		if r <= 0xFFFF {
			utf16Offset++
		} else {
			// Surrogate pair
			utf16Offset += 2
		}
	}

	return utf16Offset
}

// UTF16ToUTF8Offset converts a UTF-16 code unit offset to a UTF-8 byte offset
func UTF16ToUTF8Offset(text string, utf16Offset int) int {
	if utf16Offset < 0 {
		return utf16Offset
	}

	utf16Count := 0
	byteOffset := 0
	for byteOffset < len(text) && utf16Count < utf16Offset {
		r, size := utf8.DecodeRuneInString(text[byteOffset:])
		if r == utf8.RuneError && size == 1 {
			// Invalid UTF-8, skip one byte
			byteOffset++
			utf16Count++
			continue
		}
		// Count UTF-16 code units for this rune
		if r <= 0xFFFF {
			utf16Count++
		} else {
			utf16Count += 2
		}
		if utf16Count > utf16Offset {
			// We've overshot, return the byte offset before this rune
			return byteOffset
		}
		byteOffset += size
	}

	return byteOffset
}

// ConvertUTF8RangeToUTF16 converts a UTF-8 byte range to a UTF-16 code unit range
// text: the full source text
// startByte: UTF-8 byte offset of range start
// endByte: UTF-8 byte offset of range end
// startLine: line number (1-based, will be converted to 0-based)
// endLine: end line number (1-based, will be converted to 0-based)
func ConvertUTF8RangeToUTF16(text string, startByte, endByte, startLine, endLine int) Range {
	// Split text into lines for accurate line-based conversion
	lines := splitLines(text)
	
	// Convert to zero-based line numbers
	startLineZero := startLine - 1
	endLineZero := endLine - 1
	
	if startLineZero < 0 {
		startLineZero = 0
	}
	if endLineZero < 0 {
		endLineZero = 0
	}
	if startLineZero >= len(lines) {
		startLineZero = len(lines) - 1
	}
	if endLineZero >= len(lines) {
		endLineZero = len(lines) - 1
	}
	
	// Calculate byte offsets within each line
	startLineBytes := 0
	for i := 0; i < startLineZero && i < len(lines); i++ {
		startLineBytes += len(lines[i]) + 1 // +1 for newline
	}
	
	endLineBytes := 0
	for i := 0; i < endLineZero && i < len(lines); i++ {
		endLineBytes += len(lines[i]) + 1 // +1 for newline
	}
	
	// Get the line text
	startLineText := ""
	if startLineZero < len(lines) {
		startLineText = lines[startLineZero]
	}
	endLineText := ""
	if endLineZero < len(lines) {
		endLineText = lines[endLineZero]
	}
	
	// Calculate character offset within the line (UTF-8 byte offset from start of line)
	startCharBytes := startByte - startLineBytes
	endCharBytes := endByte - endLineBytes
	
	// Convert to UTF-16 offsets
	startCharUTF16 := UTF8ToUTF16Offset(startLineText, startCharBytes)
	endCharUTF16 := UTF8ToUTF16Offset(endLineText, endCharBytes)
	
	return Range{
		Start: Position{
			Line:      startLineZero,
			Character: startCharUTF16,
		},
		End: Position{
			Line:      endLineZero,
			Character: endCharUTF16,
		},
	}
}

// splitLines splits text into lines, preserving line endings
func splitLines(text string) []string {
	var lines []string
	var current strings.Builder
	
	for i, r := range text {
		if r == '\n' {
			lines = append(lines, current.String())
			current.Reset()
		} else if r == '\r' {
			// Check if next is \n
			if i+1 < len(text) && text[i+1] == '\n' {
				// \r\n - skip this, will be handled by \n
				continue
			}
			// Standalone \r
			lines = append(lines, current.String())
			current.Reset()
		} else {
			current.WriteRune(r)
		}
	}
	
	// Add last line if any
	if current.Len() > 0 {
		lines = append(lines, current.String())
	}
	
	return lines
}

// ConvertUTF8PositionToUTF16 converts a UTF-8 byte position to a UTF-16 position
// text: the full source text
// byteOffset: UTF-8 byte offset
// line: line number (1-based, will be converted to 0-based)
func ConvertUTF8PositionToUTF16(text string, byteOffset, line int) Position {
	lines := splitLines(text)
	
	// Convert to zero-based line number
	lineZero := line - 1
	if lineZero < 0 {
		lineZero = 0
	}
	if lineZero >= len(lines) {
		lineZero = len(lines) - 1
	}
	
	// Calculate byte offset within the line
	lineBytes := 0
	for i := 0; i < lineZero && i < len(lines); i++ {
		lineBytes += len(lines[i]) + 1 // +1 for newline
	}
	
	lineText := ""
	if lineZero < len(lines) {
		lineText = lines[lineZero]
	}
	
	charBytes := byteOffset - lineBytes
	charUTF16 := UTF8ToUTF16Offset(lineText, charBytes)
	
	return Position{
		Line:      lineZero,
		Character: charUTF16,
	}
}

