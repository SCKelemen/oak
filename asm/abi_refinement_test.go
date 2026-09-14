package asm

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// The argument layout against its Lean transliteration
// (spec/lean/Oak/ArgumentLayout.lean): each case renders LayoutArguments'
// places — and compositeChunks' class — as the `example … := by decide`
// line the Lean file states and Lean's kernel checks, so the Go and the
// model cannot drift.
func TestArgumentLayoutMatchesLeanTransliteration(t *testing.T) {
	lean, err := os.ReadFile(filepath.Join("..", "spec", "lean", "Oak", "ArgumentLayout.lean"))
	if err != nil {
		t.Fatal(err)
	}
	text := string(lean)
	scalar := func(bytes int64) ArgClass { return ArgClass{Words: 1, Bytes: bytes, Align: bytes} }
	span := ArgClass{Words: 2, Bytes: 16, Align: 8}
	record := func(chunks int) ArgClass { return ArgClass{Words: chunks, Bytes: int64(chunks) * 8, Align: 8} }
	type layoutCase struct {
		name   string
		args   []ArgClass
		packed bool
	}
	cases := []layoutCase{
		{"three words", []ArgClass{scalar(8), scalar(4), scalar(1)}, false},
		{"a span then a two-chunk record", []ArgClass{span, record(2), scalar(8)}, false},
		{"nine words, the ninth on the stack", []ArgClass{scalar(8), scalar(8), scalar(8), scalar(8), scalar(8), scalar(8), scalar(8), scalar(8), scalar(4)}, false},
		{"a span that does not fit goes to the stack with what follows", []ArgClass{scalar(8), scalar(8), scalar(8), scalar(8), scalar(8), scalar(8), scalar(8), span, scalar(8)}, false},
		{"packed narrow scalars", []ArgClass{scalar(8), scalar(8), scalar(8), scalar(8), scalar(8), scalar(8), scalar(8), scalar(8), scalar(1), scalar(2), scalar(4), record(2)}, true},
		{"standard rounding of narrow scalars", []ArgClass{scalar(8), scalar(8), scalar(8), scalar(8), scalar(8), scalar(8), scalar(8), scalar(8), scalar(1), scalar(2)}, false},
	}
	var missing []string
	for _, tc := range cases {
		places, total := LayoutArguments(tc.args, tc.packed)
		var argText, placeText []string
		for i, a := range tc.args {
			argText = append(argText, fmt.Sprintf("⟨%d, %d, %d⟩", a.Words, a.Bytes, a.Align))
			p := places[i]
			size, align := int64(0), int64(0)
			if p.OnStack {
				size, align = int64(a.Words)*8, 8
				if tc.packed {
					size, align = a.Bytes, a.Align
				}
				if align < 1 {
					align = 1
				}
			}
			placeText = append(placeText, fmt.Sprintf("⟨%d, %d, %v, %d, %d, %d⟩", p.Reg, p.Regs, p.OnStack, p.Offset, size, align))
		}
		line := fmt.Sprintf("example : layoutArguments [%s] %v = ([%s], %d) := by decide", strings.Join(argText, ", "), tc.packed, strings.Join(placeText, ", "), total)
		if !strings.Contains(text, line) {
			missing = append(missing, tc.name+":\n  "+line)
		}
	}
	for _, size := range []int64{1, 4, 8, 9, 16, 17, 32} {
		regs, indirect := compositeChunks(size)
		line := fmt.Sprintf("example : compositeChunks %d = (%d, %v) := by decide", size, regs, indirect)
		if !strings.Contains(text, line) {
			missing = append(missing, fmt.Sprintf("record of %d bytes:\n  %s", size, line))
		}
	}
	if len(missing) != 0 {
		t.Fatalf("%d layout(s) not stated in spec/lean/Oak/ArgumentLayout.lean — update the Lean file or the layout:\n%s", len(missing), strings.Join(missing, "\n"))
	}
}
