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
// endByte: UTF-8 byte offset of range end (exclusive)
// startLine: line number (1-based, will be converted to 0-based)
// endLine: end line number (1-based, will be converted to 0-based)
func ConvertUTF8RangeToUTF16(text string, startByte, endByte, startLine, endLine int) Range {
	// Use the simpler position conversion for start and end
	startPos := ConvertUTF8PositionToUTF16(text, startByte, startLine)
	endPos := ConvertUTF8PositionToUTF16(text, endByte, endLine)
	
	return Range{
		Start: startPos,
		End:   endPos,
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
	if byteOffset < 0 {
		byteOffset = 0
	}
	if byteOffset > len(text) {
		byteOffset = len(text)
	}
	
	// Split text into lines
	lines := splitLines(text)
	
	// Convert to zero-based line number
	lineZero := line - 1
	if lineZero < 0 {
		lineZero = 0
	}
	if lineZero >= len(lines) {
		lineZero = len(lines) - 1
	}
	
	// Calculate byte offset to start of line
	lineStartBytes := 0
	for i := 0; i < lineZero && i < len(lines); i++ {
		// Count bytes in line plus newline character(s)
		lineStartBytes += len(lines[i])
		// Check for newline after this line
		nextPos := lineStartBytes
		if nextPos < len(text) {
			if text[nextPos] == '\r' && nextPos+1 < len(text) && text[nextPos+1] == '\n' {
				lineStartBytes += 2 // \r\n
			} else if text[nextPos] == '\n' || text[nextPos] == '\r' {
				lineStartBytes += 1 // \n or \r
			}
		}
	}
	
	// Get the line text
	lineText := ""
	if lineZero < len(lines) {
		lineText = lines[lineZero]
	}
	
	// Calculate character offset within the line (UTF-8 byte offset from start of line)
	charBytes := byteOffset - lineStartBytes
	if charBytes < 0 {
		charBytes = 0
	}
	if charBytes > len(lineText) {
		charBytes = len(lineText)
	}
	
	// Convert to UTF-16 offset
	charUTF16 := UTF8ToUTF16Offset(lineText, charBytes)
	
	return Position{
		Line:      lineZero,
		Character: charUTF16,
	}
}

