package lsp

import (
	"testing"
)

func TestUTF8ToUTF16Offset(t *testing.T) {
	tests := []struct {
		name       string
		text       string
		utf8Offset int
		want       int
	}{
		{
			name:       "ASCII only",
			text:       "hello",
			utf8Offset: 3,
			want:       3,
		},
		{
			name:       "UTF-8 multi-byte",
			text:       "a𐐀b", // 𐐀 is 4 bytes in UTF-8, 2 code units in UTF-16
			utf8Offset: 1,
			want:       1,
		},
		{
			name:       "UTF-8 multi-byte at boundary",
			text:       "a𐐀b",
			utf8Offset: 5, // After 𐐀 (1 byte for 'a' + 4 bytes for 𐐀)
			want:       4, // 'a' (1) + 𐐀 (2 code units) + 'b' (1) = 4, but we're at position 5 in UTF-8
		},
		{
			name:       "Empty string",
			text:       "",
			utf8Offset: 0,
			want:       0,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := UTF8ToUTF16Offset(tt.text, tt.utf8Offset)
			if got != tt.want {
				t.Errorf("UTF8ToUTF16Offset(%q, %d) = %d, want %d", tt.text, tt.utf8Offset, got, tt.want)
			}
		})
	}
}

func TestConvertUTF8PositionToUTF16(t *testing.T) {
	text := "hello\nworld\ntest"
	
	// Position at 'w' in "world" (line 2, column 0 in 1-based)
	pos := ConvertUTF8PositionToUTF16(text, 6, 2)
	
	if pos.Line != 1 { // Zero-based, so line 2 is index 1
		t.Errorf("Expected line 1 (zero-based), got %d", pos.Line)
	}
	if pos.Character != 0 {
		t.Errorf("Expected character 0, got %d", pos.Character)
	}
}

