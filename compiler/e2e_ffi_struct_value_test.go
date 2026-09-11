package compiler

import (
	"os"
	"path/filepath"
	"testing"
)

// Structs by value at the boundary (docs/spec/92-ffi.md section 2.3): an
// extern binding may take or return a declared struct whose fields are
// boundary types. libc's div returns div_t by value; a C helper compiled
// alongside takes a struct by value and returns a field sum. The Oak struct
// typedef and the helper's struct share the natural layout the backend
// asserts, which is what makes the by-value pass ABI-correct.
func TestE2EFFIStructByValue(t *testing.T) {
	helper := filepath.Join(t.TempDir(), "helper.c")
	if err := os.WriteFile(helper, []byte(`
struct pair { int x; int y; };
int oak_probe_sum(struct pair p) { return p.x + p.y; }
struct pair oak_probe_swap(struct pair p) { struct pair q = { p.y, p.x }; return q; }
`), 0o644); err != nil {
		t.Fatal(err)
	}
	src := `
Pair: type = struct { x: i32, y: i32 }
DivResult: type = struct { quot: i32, rem: i32 }
sum: (p: Pair): c.Int = c.extern("oak_probe_sum")
swap: (p: Pair): Pair = c.extern("oak_probe_swap")
div: (a: c.Int, b: c.Int): DivResult = c.extern("div")
main: (): i32 {
  p: Pair = Pair { x: i32(40), y: i32(2) }
  assert(i32(sum(p)) == 42)
  q: Pair = swap(p)
  assert(q.x == 2 && q.y == 40)
  r: DivResult = div(c.Int(7), c.Int(2))
  assert(r.quot == 3 && r.rem == 1)
  42
}
`
	_, code, abnormal := buildAndRunFrom(t, "ffi_struct_value", New().WithSource("ffi_struct_value.oak", src), helper)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
