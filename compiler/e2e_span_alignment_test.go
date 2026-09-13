package compiler

import (
	"strings"
	"testing"
)

// The alignment fact on spans and views (docs/spec/50-borrowing.md section
// 2a): `[* align N]T` is a span whose base is a multiple of N, derived by
// the checker from the owner's declared layout, carried through literal
// subslices, and required by a parameter without a runtime check.
func TestSpanAlignmentFacts(t *testing.T) {
	src := `
Sector: type = struct(align: 4096) { bytes: [8192]u8, tail: u32 }
Line: type = struct { head: u32, cells(align: 64): [16]u8 }
needs_sector: (region: [* align 4096]u8): u32 = len(region)
needs_line: (cells: [* align 64]u8): u32 = len(cells)
needs_eight: (words: [* align 8]u64): u32 = len(words)
reads_aligned: (v: [align 4096]u8): u8 = v[u32(0)]
takes_plain: (region: [*]u8): u32 = len(region)
// The fact flows from the record's layout into the declared type.
check_sector: (): Bool {
  store: Sector
  region: [* align 4096]u8 = span(&store.bytes)
  needs_sector(region) == u32(8192)
}
// A borrow expression carries the fact directly.
check_direct: (): Bool {
  store: Sector
  needs_sector(span(&store.bytes)) == u32(8192)
}
// Weakened freely: the aligned span stands where [*]u8 is required.
check_weaken: (): Bool {
  store: Sector
  region: [* align 4096]u8 = span(&store.bytes)
  takes_plain(region) == u32(8192)
}
// A literal-multiple subslice keeps the fact: the second sector.
check_second: (): Bool {
  store: Sector
  region: [* align 4096]u8 = span(&store.bytes)
  second: [* align 4096]u8 = subslice(region, u32(4096), u32(4096))
  needs_sector(second) == u32(4096)
}
// A field's own alignment, and an element's natural alignment.
check_line: (): Bool {
  line: Line
  needs_line(span(&line.cells)) == u32(16)
}
check_words: (): Bool {
  words: [4]u64
  needs_eight(span(&words)) == u32(4)
}
check_view: (): Bool {
  store: Sector
  reads_aligned(view(&store.bytes)) == u8(0)
}
main: (): i32 {
  check_sector() && check_direct() && check_weaken() && check_second() && check_line() && check_words() && check_view() ? 42 | 1
}
`
	code, abnormal := buildAndRun(t, "span_alignment", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if got := interpretChecked(t, src); got != 42 {
		t.Fatalf("interpreter: got %d, want 42", got)
	}
	output, err := New().WithSource("span_alignment.oak", src).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(output, "align 4096") {
		t.Fatalf("the alignment fact leaked into the C representation:\n%s", output)
	}
}

func TestSpanAlignmentRejections(t *testing.T) {
	cases := map[string]struct{ src, want string }{
		"plain array has no fact": {`
needs_sector: (region: [* align 4096]u8): u32 = len(region)
main: (): i32 {
  store: [8192]u8
  needs_sector(span(&store)) == u32(0) ? 1 | 0
}
`, "expected [* align 4096]u8, got [*]u8"},
		"second field of an aligned record": {`
Sector: type = struct(align: 4096) { head: u32, bytes: [8192]u8 }
needs_sector: (region: [* align 4096]u8): u32 = len(region)
main: (): i32 {
  store: Sector
  needs_sector(span(&store.bytes)) == u32(0) ? 1 | 0
}
`, "expected [* align 4096]u8, got [*]u8"},
		"unaligned subslice loses the fact": {`
Sector: type = struct(align: 4096) { bytes: [8192]u8 }
needs_sector: (region: [* align 4096]u8): u32 = len(region)
main: (): i32 {
  store: Sector
  region: [* align 4096]u8 = span(&store.bytes)
  needs_sector(subslice(region, u32(8), u32(4096))) == u32(0) ? 1 | 0
}
`, "expected [* align 4096]u8, got [*]u8"},
		"weaker fact": {`
Sector: type = struct(align: 64) { bytes: [8192]u8 }
needs_sector: (region: [* align 4096]u8): u32 = len(region)
main: (): i32 {
  store: Sector
  needs_sector(span(&store.bytes)) == u32(0) ? 1 | 0
}
`, "expected [* align 4096]u8, got [* align 64]u8"},
		"declared fact stronger than the borrow": {`
main: (): i32 {
  store: [64]u8
  region: [* align 64]u8 = span(&store)
  0
}
`, "[* align 64]u8"},
		"not a power of two": {`
f: (region: [* align 100]u8): u32 = len(region)
main: (): i32 = 0
`, "nonzero power-of-two"},
	}
	for name, c := range cases {
		_, err := New().WithSource("bad.oak", c.src).EmitC().Get()
		if err == nil || !strings.Contains(err.Error(), c.want) {
			t.Fatalf("%s: want %q, got %v", name, c.want, err)
		}
	}
}
