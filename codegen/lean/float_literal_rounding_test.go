package lean

import (
	"strings"
	"testing"
)

// Pin the same decimal-to-bits seam as asm.TestSourceFloatLiteralRounding.
// The Lean model starts from these bits; it does not prove decimal parsing.
func TestExtractionFloatLiteralRounding(t *testing.T) {
	for _, tc := range []struct {
		text, bits string
	}{
		{"1.00000005960464477550", "0x3F800001"},
		{"1.00000017881393432617", "0x3F800001"},
		{"1.000000059604644775390625", "0x3F800000"},
		{"1.000000178813934326171875", "0x3F800002"},
		{"0x1.00000100000000000001p0", "0x3F800001"},
	} {
		t.Run(tc.text, func(t *testing.T) {
			out, err := extract(t, "f: (a: f32) -> f32 = a + "+tc.text+"\n")
			if err != nil {
				t.Fatal(err)
			}
			want := "(Float32.ofBits (" + tc.bits + " : UInt32) /- " + tc.text + " -/)"
			if !strings.Contains(out, want) {
				t.Fatalf("extraction lacks %q:\n%s", want, out)
			}
		})
	}
}
