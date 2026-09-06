package source

import (
	"fmt"
	"net/url"
	"path/filepath"
	"sort"
	"strings"
	"unicode/utf16"
	"unicode/utf8"
)

// ID is a stable source-file identity inside one compilation.
type ID uint32

// Span is a half-open UTF-8 byte range [Start, End).
// Byte offsets are the canonical source-location representation.
type Span struct {
	Start int
	End   int
}

// Position is a human/editor position. Line and Column are 1-based and Column
// is measured in UTF-16 code units so it agrees with VS Code/LSP coordinates.
type Position struct {
	Line   int
	Column int
}

// LSPPosition is the same position using LSP's 0-based convention.
type LSPPosition struct {
	Line      int
	Character int
}

// File owns source text and its line index. The line index is immutable after
// construction, so location queries are deterministic and allocation-free.
type File struct {
	ID   ID
	Path string
	Text string

	lineStarts []int
}

func NewFile(id ID, path, text string) *File {
	starts := make([]int, 1, strings.Count(text, "\n")+1)
	starts[0] = 0
	for i := 0; i < len(text); i++ {
		if text[i] == '\n' {
			starts = append(starts, i+1)
		}
	}
	return &File{ID: id, Path: path, Text: text, lineStarts: starts}
}

func (f *File) Span(start, end int) (Span, error) {
	span := Span{Start: start, End: end}
	if err := f.ValidateSpan(span); err != nil {
		return Span{}, err
	}
	return span, nil
}

func (f *File) ValidateSpan(span Span) error {
	if f == nil {
		return fmt.Errorf("nil source file")
	}
	if span.Start < 0 || span.End < span.Start || span.End > len(f.Text) {
		return fmt.Errorf("invalid source span [%d,%d) for %d-byte file", span.Start, span.End, len(f.Text))
	}
	if !utf8Boundary(f.Text, span.Start) || !utf8Boundary(f.Text, span.End) {
		return fmt.Errorf("source span [%d,%d) is not aligned to UTF-8 rune boundaries", span.Start, span.End)
	}
	return nil
}

// PositionAt returns a 1-based VS Code compatible position for a UTF-8 byte offset.
func (f *File) PositionAt(offset int) (Position, error) {
	lsp, err := f.LSPPositionAt(offset)
	if err != nil {
		return Position{}, err
	}
	return Position{Line: lsp.Line + 1, Column: lsp.Character + 1}, nil
}

// LSPPositionAt converts a canonical byte offset to 0-based UTF-16 coordinates.
func (f *File) LSPPositionAt(offset int) (LSPPosition, error) {
	if f == nil {
		return LSPPosition{}, fmt.Errorf("nil source file")
	}
	if offset < 0 || offset > len(f.Text) {
		return LSPPosition{}, fmt.Errorf("source offset %d outside [0,%d]", offset, len(f.Text))
	}
	if !utf8Boundary(f.Text, offset) {
		return LSPPosition{}, fmt.Errorf("source offset %d is not on a UTF-8 rune boundary", offset)
	}

	line := sort.Search(len(f.lineStarts), func(i int) bool { return f.lineStarts[i] > offset }) - 1
	if line < 0 {
		line = 0
	}
	lineStart := f.lineStarts[line]
	units := 0
	for _, r := range f.Text[lineStart:offset] {
		if n := utf16.RuneLen(r); n > 0 {
			units += n
		} else {
			units++
		}
	}
	return LSPPosition{Line: line, Character: units}, nil
}

// Location formats a compiler/editor link in the conventional path:line:column form.
func (f *File) Location(span Span) (string, error) {
	if err := f.ValidateSpan(span); err != nil {
		return "", err
	}
	pos, err := f.PositionAt(span.Start)
	if err != nil {
		return "", err
	}
	return fmt.Sprintf("%s:%d:%d", f.Path, pos.Line, pos.Column), nil
}

// VSCodeURI returns a vscode://file URI for the start of span. Editors can use
// Location for terminal linkification; this form is useful for explicit hyperlinks.
func (f *File) VSCodeURI(span Span) (string, error) {
	if err := f.ValidateSpan(span); err != nil {
		return "", err
	}
	pos, err := f.PositionAt(span.Start)
	if err != nil {
		return "", err
	}
	path := filepath.ToSlash(f.Path)
	if !strings.HasPrefix(path, "/") {
		path = "/" + path
	}
	u := url.URL{Scheme: "vscode", Host: "file", Path: path}
	return fmt.Sprintf("%s:%d:%d", u.String(), pos.Line, pos.Column), nil
}

func utf8Boundary(text string, offset int) bool {
	return offset == 0 || offset == len(text) || (offset > 0 && offset < len(text) && utf8.RuneStart(text[offset]))
}
