package compiler

import (
	"strings"
	"testing"
)

// Strings compare by their bytes (docs/spec/30-adts-patterns.md section
// 14): `==`/`!=` on string values route through one generated helper
// instead of a C struct comparison that would not compile.
func TestE2EStringEquality(t *testing.T) {
	src := `
greet: (): string = "hi"

same: (a: string, b: string): Bool = a == b

differ: (a: string, b: string): Bool = a != b

main: (): i32 {
  s: string = greet()
  t: string = "hi"
  u: string = "ho"
  e: string = ""
  total: u32 = 0
  total = total + (same(s, t) ? u32(1) | u32(0))
  total = total + (differ(s, u) ? u32(2) | u32(0))
  total = total + (same(e, "") ? u32(4) | u32(0))
  total = total + (same("hi", "hip") ? u32(0) | u32(8))
  i32_bits_u32(total)
}
`
	output, err := New().WithSource("streq.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if !strings.Contains(output, "static inline Bool oak_eq_string( string a, string b )") {
		t.Fatalf("string equality helper not emitted:\n%s", output)
	}
	if !strings.Contains(output, "oak_eq_string( a, b )") || !strings.Contains(output, "!oak_eq_string( a, b )") {
		t.Fatalf("string comparisons should route through the helper:\n%s", output)
	}
	code, abnormal := buildAndRun(t, "streq", src)
	if abnormal || code != 15 {
		t.Fatalf("exit = (%d, abnormal=%v), want 15", code, abnormal)
	}
}
