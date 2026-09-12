package compiler

import (
	"strings"
	"testing"
)

// The binary-search laws (docs/spec/50-borrowing.md, midpoint and
// decreasing bound): `mid = lo + (hi - lo) / 2` under `lo < hi` is below
// `hi`, and a loop whose only writes to `hi` are `hi = mid` keeps
// `hi <= len(keys)` alive, so `keys[mid]` is proven on every iteration.
// The same holds against a literal bound (`b: u32 = 512`, `page[m]`).
func TestE2EExtentsBinarySearch(t *testing.T) {
	src := `
search: (keys: []u64, target: u64): u32 {
  lo: u32 = 0
  hi: u32 = len(keys)
  found: u32 = 0
  while lo < hi && found == u32(0) {
    mid: u32 = lo + (hi - lo) / u32(2)
    k: u64 = keys[mid]
    k == target ? { found = mid + u32(1) }
    | k < target ? { lo = mid + u32(1) }
    | { hi = mid }
  }
  found
}

probe: (keys: []u64, target: u64): u32 {
  page: []u64 = subslice(keys, u32(0), u32(8))
  a: u32 = 0
  b: u32 = 8
  hits: u32 = 0
  while a < b {
    m: u32 = a + (b - a) / u32(2)
    page[m] <= target ? { a = m + u32(1) } | { b = m }
  }
  a
}

main: (): i32 {
  keys: [8]u64 = [8]u64{ 2, 3, 5, 7, 11, 13, 17, 19 }
  v: []u64 = view(&keys)
  i32_bits_u32(search(v, u64(11)) * u32(10) + probe(v, u64(12)))
}
`
	output, err := New().WithSource("bsearch.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if got := strings.Count(output, "oak_view_index_u64( "); got != 0 {
		t.Fatalf("both probes should be proven, found %d checked reads:\n%s", got, output)
	}
	// search finds 11 at index 4 (found = 5); probe counts 5 keys <= 12.
	code, abnormal := buildAndRun(t, "bsearch", src)
	if abnormal || code != 55 {
		t.Fatalf("exit = (%d, abnormal=%v), want 55", code, abnormal)
	}

	// A write that does not lower the bound, a midpoint that is not the
	// body's first statement, or a bound the guard does not relate keep
	// the check.
	for _, bad := range []struct{ name, src string }{
		{"raise", "f: (keys: []u64): u64 {\n  lo: u32 = 0\n  hi: u32 = len(keys)\n  acc: u64 = 0\n  while lo < hi {\n    mid: u32 = lo + (hi - lo) / u32(2)\n    acc = acc + keys[mid]\n    hi = mid + u32(1)\n    lo = lo + u32(1)\n  }\n  acc\n}\nmain: (): i32 = 0\n"},
		{"late", "f: (keys: []u64): u64 {\n  lo: u32 = 0\n  hi: u32 = len(keys)\n  acc: u64 = 0\n  while lo < hi {\n    hi = hi + u32(0)\n    mid: u32 = lo + (hi - lo) / u32(2)\n    acc = acc + keys[mid]\n    hi = mid\n  }\n  acc\n}\nmain: (): i32 = 0\n"},
		{"unrelated", "f: (keys: []u64, n: u32): u64 {\n  lo: u32 = 0\n  hi: u32 = n\n  acc: u64 = 0\n  while lo < hi {\n    mid: u32 = lo + (hi - lo) / u32(2)\n    acc = acc + keys[mid]\n    hi = mid\n  }\n  acc\n}\nmain: (): i32 = 0\n"},
	} {
		output, err := New().WithSource(bad.name+".oak", bad.src).EmitC().Get()
		if err != nil {
			t.Fatalf("%s: compilation failed: %v", bad.name, err)
		}
		if got := strings.Count(output, "oak_view_index_u64( "); got != 1 {
			t.Fatalf("%s: the read must stay checked, found %d:\n%s", bad.name, got, output)
		}
	}
}
