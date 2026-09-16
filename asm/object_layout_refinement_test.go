package asm

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// ObjectLayout.lean is the mathematical bounds model for the target-neutral
// relocation admission check. Every public/live kind and every boundary below
// is executed by Go and required to appear as a kernel-checked Lean example.
// This pins footprint admission only, not relocation or linker semantics.
func TestObjectRelocationLayoutMatchesLean(t *testing.T) {
	contents, err := os.ReadFile(filepath.Join("..", "spec", "lean", "Oak", "ObjectLayout.lean"))
	if err != nil {
		t.Fatal(err)
	}
	lean := string(contents)
	var missing []string
	require := func(name, line string) {
		if !strings.Contains(lean, line) {
			missing = append(missing, name+":\n  "+line)
		}
	}
	renderInt := func(value int) string {
		if value < 0 {
			return fmt.Sprintf("(%d)", value)
		}
		return fmt.Sprint(value)
	}
	seen := make(map[string]bool, len(relocationKindFootprints))
	for _, classified := range relocationKindFootprints {
		kind, width := classified.kind, classified.width
		if seen[kind] {
			t.Fatalf("duplicate relocation classification for %q", kind)
		}
		seen[kind] = true
		if got, known := relocationFootprint(kind); !known || got != width {
			t.Fatalf("relocationFootprint(%q) = (%d, %v), inventory says %d", kind, got, known, width)
		}
		require(kind+" footprint", fmt.Sprintf("example : relocationFootprint %q = some %d := by decide", kind, width))
		for _, boundary := range []struct {
			name            string
			textLen, offset int
		}{
			{name: "negative", textLen: width, offset: -1},
			{name: "one byte short", textLen: width - 1, offset: 0},
			{name: "exact", textLen: width, offset: 0},
			{name: "nonzero exact", textLen: width + 4, offset: 4},
			{name: "nonzero one past", textLen: width + 4, offset: 5},
		} {
			accepted := relocationFits(boundary.textLen, boundary.offset, kind)
			line := fmt.Sprintf("example : relocationFits %d %s %q = %v := by decide",
				boundary.textLen, renderInt(boundary.offset), kind, accepted)
			require(kind+" "+boundary.name, line)
		}
	}
	if width, known := relocationFootprint("unknown"); known || width != 0 {
		t.Fatalf("relocationFootprint(unknown) = (%d, %v), want (0, false)", width, known)
	}
	require("unknown footprint", `example : relocationFootprint "unknown" = none := by decide`)
	require("unknown fit", `example : relocationFits 4 0 "unknown" = false := by decide`)
	if relocationFits(8, int(^uint(0)>>1), "adrl21") {
		t.Fatal("maximum machine-int relocation offset wrapped into an accepted footprint")
	}
	if len(missing) != 0 {
		t.Fatalf("%d object-layout decision(s) are not stated in ObjectLayout.lean:\n%s", len(missing), strings.Join(missing, "\n"))
	}
}
