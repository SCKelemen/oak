package lsp

import "testing"

func TestPositionIndexMatchesLegacy(t *testing.T) {
	for _, source := range []string{
		"a", "a\n", "\n", "a\n\n", "\r\n", "a\rb\r", "a\r\nb\n",
		"α😀\r\n世界\nlast", "\n\n😀\r\n",
	} {
		index := NewPositionIndex(source)
		for line := -1; line <= 7; line++ {
			for offset := -1; offset <= len(source)+1; offset++ {
				want := ConvertUTF8PositionToUTF16(source, offset, line)
				if got := index.Position(offset, line); got != want {
					t.Fatalf("source=%q line=%d offset=%d: got %+v, want %+v", source, line, offset, got, want)
				}
			}
		}
	}
}

func TestPositionIndexEmpty(t *testing.T) {
	if got := NewPositionIndex("").Position(10, 20); got != (Position{}) {
		t.Fatalf("empty source position: %+v", got)
	}
}
