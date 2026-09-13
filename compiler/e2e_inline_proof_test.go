package compiler

import (
	"regexp"
	"strings"
	"testing"
)

// Proof-preserving inlining (compiler/inline.go, docs/spec/90-backend.md
// section 9): a private leaf helper is spliced into its caller before the
// type checker runs, so the caller's guard proves the helper's element
// access. The helper's own definition keeps its check (its parameter is
// unconstrained), the inlined copies carry none, and the program computes
// the same value either way.
const inlineHelperProgram = `// A read helper: the index is unconstrained inside it.
byte_at: (buf: [8]u8, i: u32) -> u8 {
  buf[i]
}

// A helper with a local of its own, called in operand position.
weighted: (buf: [8]u8, i: u32) -> u32 {
  w: u32 = i + u32(1)
  u32(buf[i]) * w
}

// A helper whose result is a Bool used in a guard's right operand: it
// stays a call there (nothing crosses a short-circuit operator).
small: (v: u8) -> Bool {
  v < u8(16)
}

sum_guarded: (buf: [8]u8, n: u32) -> u32 {
  acc: u32 = u32(0)
  n <= u32(8) ? {
    i: u32 = u32(0)
    while i < n {
      acc = acc + u32(byte_at(buf, i)) + weighted(buf, i)
      i = i + u32(1)
    }
  } | { }
  acc
}

first_small: (buf: [8]u8) -> u32 {
  i: u32 = u32(0)
  found: u32 = u32(8)
  while i < u32(8) && found == u32(8) {
    found = small(byte_at(buf, i)) ? i | found
    i = i + u32(1)
  }
  found
}

main: (): i32 {
  data: [8]u8
  data[0] = u8(40)
  data[3] = u8(2)
  // 40 + 40*1 + 2 + 2*4 = 90; first small byte is index 1 (zero).
  i32_bits_u32(sum_guarded(data, u32(4)) + first_small(data) - u32(91))
}
`

func TestE2EInlinedHelperCarriesCallerProof(t *testing.T) {
	code, err := New().WithSource("inline.oak", inlineHelperProgram).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	body := regexp.MustCompile(`(?s)\nu32 oak_sum_guarded\([^)]*\) \{.*?\n}\n`).FindString(code)
	if body == "" {
		t.Fatal("sum_guarded not emitted")
	}
	if strings.Contains(body, "oak_index") || strings.Contains(body, "oak_lv_idx") {
		t.Errorf("sum_guarded carries a bounds check after inlining:\n%s", body)
	}
	if strings.Contains(body, "oak_byte_at(") || strings.Contains(body, "oak_weighted(") {
		t.Errorf("sum_guarded still calls its helpers:\n%s", body)
	}
	if !strings.Contains(body, "__inl") {
		t.Errorf("sum_guarded shows no inlined temporaries:\n%s", body)
	}
	firstSmall := regexp.MustCompile(`(?s)\nu32 oak_first_small\([^)]*\) \{.*?\n}\n`).FindString(code)
	if firstSmall == "" {
		t.Fatal("first_small not emitted")
	}
	if strings.Contains(firstSmall, "oak_index") {
		t.Errorf("first_small carries a bounds check after inlining:\n%s", firstSmall)
	}
	// The helper definitions keep their own checks: their indices are
	// unconstrained.
	helper := regexp.MustCompile(`(?s)\nOAK_INLINE u8 oak_byte_at\([^)]*\) \{.*?\n}\n`).FindString(code)
	if helper == "" || !strings.Contains(helper, "oak_index") {
		t.Errorf("byte_at's own definition lost its check:\n%s", helper)
	}
	if _, exit, abnormal := buildAndRunFrom(t, "inline_helpers", New().WithSource("inline.oak", inlineHelperProgram)); abnormal || exit != 0 {
		t.Fatalf("inlined program: exit = (%d, abnormal=%v), want 0", exit, abnormal)
	}
}

// The semantic model is the program as written: the language server and
// the prover see the calls, not their expansions.
func TestInliningLeavesSemanticModelAlone(t *testing.T) {
	model, err := New().WithSource("inline.oak", inlineHelperProgram).Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(model.Tree.Root.String(), "__inl") {
		t.Fatal("Check() inlined helpers without a code-emitting stage")
	}
}
