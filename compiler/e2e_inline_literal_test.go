package compiler

import (
	"regexp"
	"strings"
	"testing"
)

// A literal argument substitutes for the parameter when the inliner merges
// a helper (compiler/inline.go literalArgument): the merged body reads
// `v[u32(4) + u32(3)]` under `len(v) >= u32(4) + u32(4)`, constants the
// extents checker folds (typechecker/extents.go constantIndex) and proves,
// so neither backend emits a bounds check. A temporary would have left
// `len(v) >= t + 4`, which proves nothing about `v[t + 3]`.
const inlineLiteralProgram = `
word_at: (v: []u8, at: u32): u32 {
  len(v) >= at + u32(4) ? {
    u32(v[at]) | (u32(v[at + u32(1)]) << u32(8)) | (u32(v[at + u32(2)]) << u32(16)) | (u32(v[at + u32(3)]) << u32(24))
  } | { u32(0) }
}

second: (v: []u8): u32 = word_at(v, 4)

third: (v: []u8): u32 = word_at(v, u32(8))

main: (): i32 {
  buf: [12]u8 = [u8(1), u8(2), u8(3), u8(4), u8(5), u8(6), u8(7), u8(8), u8(9), u8(10), u8(11), u8(12)]
  v: []u8 = view(&buf)
  i32_bits_u32((second(v) >> u32(24)) + (third(v) & u32(255)) + word_at(v, u32(9)))
}
`

func TestE2EInlineLiteralArguments(t *testing.T) {
	want := interpretChecked(t, inlineLiteralProgram)
	code, err := New().WithSource("literal.oak", inlineLiteralProgram).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	for _, fn := range []string{"second", "third"} {
		body := regexp.MustCompile(`(?s)\n(?:OAK_INLINE )?u32 oak_` + fn + `\([^)]*\) \{.*?\n}\n`).FindString(code)
		if body == "" {
			t.Fatalf("%s not emitted:\n%s", fn, code)
		}
		if strings.Contains(body, "oak_word_at(") {
			t.Errorf("%s still calls word_at:\n%s", fn, body)
		}
		if strings.Contains(body, "_arg1") {
			t.Errorf("%s copies the literal argument into a temporary instead of substituting it:\n%s", fn, body)
		}
		if strings.Contains(body, "oak_index") || strings.Contains(body, "oak_lv_idx") {
			t.Errorf("%s carries a bounds check the folded constants should have discharged:\n%s", fn, body)
		}
	}
	if _, exit, abnormal := buildAndRunFrom(t, "inline_literal", New().WithSource("literal.oak", inlineLiteralProgram)); abnormal || int64(exit) != want%256 {
		t.Fatalf("exit = (%d, abnormal=%v), want %d", exit, abnormal, want%256)
	}
}

// A record literal names each field expression twice, in FieldOrder and in
// the Fields map. When a field's whole value is a parameter (`a: x`),
// substituting a literal argument must replace both references, or the map
// keeps the renamed parameter and the merged body names a variable no
// declaration introduces (`undefined variable: __inl2_arg0`). A parameter
// inside a larger expression (`b: k * u32(3)`) is replaced within a node
// both references share.
const inlineLiteralRecordProgram = `
Pair: type = struct { a: u64, b: u32 }

mk_pair: (x: u64, k: u32) -> Pair = Pair { a: x, b: k * u32(3) }

main: (): i32 {
  p: Pair = mk_pair(u64(10), u32(2))
  q: Pair = mk_pair(u64(20), 4)
  i32_bits_u32(u32_trunc_u64(p.a + q.a) + p.b + q.b)
}
`

func TestE2EInlineLiteralArgumentsIntoRecordLiteral(t *testing.T) {
	want := interpretChecked(t, inlineLiteralRecordProgram)
	if _, exit, abnormal := buildAndRunFrom(t, "inline_literal_record", New().WithSource("literal.oak", inlineLiteralRecordProgram)); abnormal || int64(exit) != want%256 {
		t.Fatalf("exit = (%d, abnormal=%v), want %d", exit, abnormal, want%256)
	}
}
