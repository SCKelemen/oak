package compiler

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// Inbound buffers (docs/spec/92-ffi.md section 2.7): inside an unsafe block,
// c.borrow[T](ptr, count) views runtime-owned memory and c.borrow_mut[T]
// writes through it, each for the block's extent. A C helper compiled
// alongside owns two static buffers; Oak reads one back element by element
// and fills the other, and the helper verifies the writes.
func TestE2EInboundBuffers(t *testing.T) {
	helper := filepath.Join(t.TempDir(), "helper.c")
	if err := os.WriteFile(helper, []byte(`
#include <stdint.h>
static uint32_t table[8] = { 1, 2, 3, 4, 5, 6, 7, 8 };
static float out[4];
void *oak_probe_table(void) { return table; }
void *oak_probe_out(void) { return out; }
int oak_probe_out_ok(void) {
  return out[0] == 0.5f && out[1] == 1.5f && out[2] == 2.5f && out[3] == 3.5f;
}
`), 0o644); err != nil {
		t.Fatal(err)
	}
	src := `
table_ptr: (): c.Ptr = c.extern("oak_probe_table")
out_ptr: (): c.Ptr = c.extern("oak_probe_out")
out_ok: (): c.Int = c.extern("oak_probe_out_ok")

sum_table: (): u32 {
  total: u32 = 0
  p: c.Ptr = table_ptr()
  unsafe {
    v: []u32 = c.borrow[u32](p, u32(8))
    i: u32 = 0
    while i < len(v) {
      total = total + v[i]
      i = i + u32(1)
    }
    half: []u32 = subslice(v, u32(2), u32(3))
    total = total + half[0] * u32(100)
  }
  total
}

fill_out: (): () {
  q: c.Ptr = out_ptr()
  unsafe {
    s: [*]f32 = c.borrow_mut[f32](q, u32(4))
    i: u32 = 0
    while i < len(s) {
      s[i] = f32_round_u32(i) + 0.5
      i = i + u32(1)
    }
  }
}

main: (): i32 {
  assert(sum_table() == u32(336))
  fill_out()
  assert(i32(out_ok()) == 1)
  42
}
`
	_, code, abnormal := buildAndRunFrom(t, "ffi_inbound", New().WithSource("ffi_inbound.oak", src), helper)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

// The placement rules fail closed: outside unsafe, not an initializer, a
// non-boundary element type, the wrong pointer or count type, and the ways
// the borrow could outlive its block — an unsafe block is a statement, so
// the only exits are assigning the borrow, or a reborrow a region-indexed
// call returned, to an outer binding.
func TestInboundBufferRejections(t *testing.T) {
	prelude := "table_ptr: (): c.Ptr = c.extern(\"oak_probe_table\")\n"
	cases := map[string]struct{ src, want string }{
		"outside unsafe": {prelude + `
f: (): u32 {
  p: c.Ptr = table_ptr()
  v: []u32 = c.borrow[u32](p, u32(8))
  v[0]
}
main: (): i32 = 0
`, "OAK-F0107"},
		"not an initializer": {prelude + `
first: (v: []u32): u32 = v[0]
f: (): u32 {
  p: c.Ptr = table_ptr()
  r: u32 = 0
  unsafe { r = first(c.borrow[u32](p, u32(8))) }
  r
}
main: (): i32 = 0
`, "OAK-F0107"},
		"element type": {prelude + `
f: (): u32 {
  p: c.Ptr = table_ptr()
  unsafe {
    v: []string = c.borrow[string](p, u32(8))
  }
  0
}
main: (): i32 = 0
`, "OAK-F0104"},
		"count type": {prelude + `
f: (): u32 {
  p: c.Ptr = table_ptr()
  unsafe {
    v: []u32 = c.borrow[u32](p, u64(8))
  }
  0
}
main: (): i32 = 0
`, "u32 element count"},
		"pointer type": {`
f: (): u32 {
  unsafe {
    v: []u32 = c.borrow[u32](u32(0), u32(8))
  }
  0
}
main: (): i32 = 0
`, "takes a c.Ptr"},
		"escape through a region call": {prelude + `
head: (xs: []u32): []u32 = subslice(xs, u32(0), u32(1))
f: (xs: []u32): u32 {
  p: c.Ptr = table_ptr()
  kept: []u32 = xs
  unsafe {
    v: []u32 = c.borrow[u32](p, u32(8))
    kept = head(v)
  }
  kept[0]
}
main: (): i32 = 0
`, "OAK-B"},
		"escape by assignment": {prelude + `
f: (xs: []u32): u32 {
  p: c.Ptr = table_ptr()
  kept: []u32 = xs
  unsafe {
    v: []u32 = c.borrow[u32](p, u32(8))
    kept = v
  }
  kept[0]
}
main: (): i32 = 0
`, "OAK-B"},
	}
	for name, c := range cases {
		_, err := New().WithSource(name+".oak", c.src).EmitC().Get()
		if err == nil {
			t.Fatalf("%s: expected a diagnostic mentioning %q", name, c.want)
		}
		if !strings.Contains(err.Error(), c.want) {
			t.Fatalf("%s: diagnostics should mention %q, got:\n%v", name, c.want, err)
		}
	}
}

// An accepted borrow records the assumption as an auditable OAK-B0110
// warning, like every other unsafe assumption.
func TestInboundBufferRecordsAssumption(t *testing.T) {
	model, err := New().WithSource("assume.oak", `
table_ptr: (): c.Ptr = c.extern("oak_probe_table")
f: (): u32 {
  p: c.Ptr = table_ptr()
  total: u32 = 0
  unsafe {
    v: []u32 = c.borrow[u32](p, u32(8))
    total = v[0]
  }
  total
}
main: (): i32 = 0
`).Check().Get()
	if err != nil {
		t.Fatalf("check failed: %v", err)
	}
	for _, d := range model.Diagnostics {
		if strings.Contains(string(d.Code), "B0110") && strings.Contains(d.Message, "foreign buffer contract") {
			return
		}
	}
	t.Fatalf("no OAK-B0110 assumption recorded for the foreign borrow")
}
