package lsp

// PositionIndex reuses line boundaries across source-position conversions.
// It borrows the immutable Go source string and never rebuilds its lines per
// token. Columns retain ConvertUTF8PositionToUTF16's UTF-16/clamping semantics.
type PositionIndex struct {
	text  string
	lines []sourceLine
}

type sourceLine struct {
	start int
	end   int
}

func NewPositionIndex(text string) *PositionIndex {
	index := &PositionIndex{text: text}
	start := 0
	for at := 0; at < len(text); at++ {
		if text[at] != '\n' && text[at] != '\r' {
			continue
		}
		index.lines = append(index.lines, sourceLine{start, at})
		if text[at] == '\r' && at+1 < len(text) && text[at+1] == '\n' {
			at++
		}
		start = at + 1
	}
	// Legacy conversion omits a trailing empty line.
	if start < len(text) || len(index.lines) == 0 {
		index.lines = append(index.lines, sourceLine{start, len(text)})
	}
	return index
}

func (index *PositionIndex) Position(byteOffset, line int) Position {
	line--
	if line < 0 {
		line = 0
	}
	if line >= len(index.lines) {
		line = len(index.lines) - 1
	}
	span := index.lines[line]
	if byteOffset < span.start {
		byteOffset = span.start
	}
	if byteOffset > span.end {
		byteOffset = span.end
	}
	return Position{
		Line:      line,
		Character: UTF8ToUTF16Offset(index.text[span.start:span.end], byteOffset-span.start),
	}
}
