package lean

import (
	"strings"
	"testing"
)

// assert_eq and assert_ne trap exactly when their comparison fails; the
// extraction models the trap as `none`, not the values a hosted build prints
// (docs/spec/85-discipline.md section 5).
func TestExtractionAssertValues(t *testing.T) {
	src := `
check: (a: u32, b: u32): u32 {
  assert_eq(a + u32(1), b)
  assert_ne(a, u32(7))
  a
}
`
	out, err := extract(t, src)
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"let () ← (if (a + (1 : UInt32)) == b then pure () else none)",
		"let () ← (if a == (7 : UInt32) then none else pure ())",
	} {
		if !strings.Contains(out, want) {
			t.Fatalf("extraction lacks %q:\n%s", want, out)
		}
	}
}
