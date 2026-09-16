package compiler

import (
	"strings"
	"testing"
)

// A value-position ADT match may have a block arm whose tail is another
// value-position match. The source inliner must not hoist a helper's argument
// and local declarations into that nested match: the portable C backend emits
// the Bool match as a ternary expression, where declarations are not C99.
const inlineMatchContextProgram = `
Choice: type = Direct: u32 | Conditional: u32

plus_two: (x: u32): u32 {
  next: u32 = x + u32(1)
  next + u32(1)
}

main: (): i32 {
  choice: Choice = Choice.Conditional(u32(40))
  enabled: Bool = false
  result: u32 = choice ?
   | .Direct(value) => value
   | .Conditional(value) => {
    enabled ? value | plus_two(value)
  }
  i32_bits_u32(result)
}
`

func TestE2EInlineDoesNotPutStatementsInValueMatchArm(t *testing.T) {
	generated, err := New().WithSource("inline_match_context.oak", inlineMatchContextProgram).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(generated, "__inl") {
		t.Fatalf("value-position match arm acquired inlined statements:\n%s", generated)
	}
	if _, code, abnormal := buildAndRunFrom(t, "inline_match_context", New().WithSource("inline_match_context.oak", inlineMatchContextProgram)); abnormal || code != 42 {
		t.Fatalf("nested value match = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
