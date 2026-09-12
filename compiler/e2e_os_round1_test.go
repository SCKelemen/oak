package compiler

import (
	"strings"
	"testing"
)

// The OS pilot's first round (docs/notes/os-language-requests-2026-09.md):
// several live instances of a stateful record behind one span, read and
// written in place (R1); never-written scalar globals as C constants (R2);
// bounds-check elision over top-level tables (R3); the sound spelling of a
// multi-byte read guard (R4); shifts in global initializers (R5).

func TestE2EOSLiveInstancesInPlace(t *testing.T) {
	src := `
Big: type = struct { pool: [64]u32, count: u32 }
bump: (s: [*]Big, i: u32, v: u32): () {
  s[i].pool[s[i].count] = v
  s[i].count = s[i].count + u32(1)
}
peek: (v: []Big, i: u32): u32 = v[i].count
main: (): i32 {
  states: [3]Big
  true ? {
    s: [*]Big = span(&states)
    bump(s, 0, 7)
    bump(s, 2, 9)
    bump(s, 2, 11)
  }
  n: u32 = peek(view(&states), 2)
  states[0].count == u32(1) && n == u32(2) && states[2].pool[1] == u32(11) && states[0].pool[0] == u32(7) ? 42 | 1
}
`
	code, abnormal := buildAndRun(t, "os_instances", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	emitted, err := New().WithSource("os.oak", src).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	// Field reads through a span or view element select the element in
	// place; no helper returns the record by value.
	for _, want := range []string{
		"( s ).base[ oak_lv_idx( (u64)( i ), (u64)( ( s ).len ) ) ].count",
		"( v ).base[ oak_lv_idx( (u64)( i ), (u64)( ( v ).len ) ) ].count",
	} {
		if !strings.Contains(emitted, want) {
			t.Fatalf("missing %q:\n%s", want, emitted)
		}
	}
	for _, unwanted := range []string{"oak_span_index_oak_Big( s", "oak_view_index_oak_Big( v"} {
		if strings.Contains(emitted, unwanted) {
			t.Fatalf("a record element must not be read by value: %q", unwanted)
		}
	}
}

func TestE2EOSConstantGlobals(t *testing.T) {
	src := `
page_size: u64 = 16384
INVALID: u32 = (u32(65535) << 16) | u32(65535)
counter: u32 = 0
TABLE: [4]u8 = [1, 2, 3, 4]
pa_index: (pa: u64): u64 = pa / page_size
tick: (): u32 { counter = counter + u32(1)
  counter }
sum_table: (): u32 {
  total: u32 = 0
  i: u32 = 0
  while i < len(TABLE) {
    total = total + u32(TABLE[i])
    i = i + u32(1)
  }
  total
}
main: (): i32 {
  pa_index(u64(32768)) == u64(2) && INVALID == u32(4294967295) && tick() == u32(1) && sum_table() == u32(10) ? 42 | 1
}
`
	code, abnormal := buildAndRun(t, "os_constants", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	emitted, err := New().WithSource("os.oak", src).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"static const u64 page_size = 16384;",
		"static const u32 INVALID = ( ((u32)( ((u32)( 65535 )) ) << 16 ) | ((u32)( 65535 )) );",
		"static u32 counter = 0;",
		"static oak_arr_u8_4 TABLE = { { 1, 2, 3, 4 } };",
		// The loop over the top-level table proves its index: direct access.
		"TABLE.v[ i ]",
	} {
		if !strings.Contains(emitted, want) {
			t.Fatalf("missing %q:\n%s", want, emitted)
		}
	}
	if strings.Contains(emitted, "oak_index( TABLE") {
		t.Fatalf("the table loop must not stay checked:\n%s", emitted)
	}
}

// The sound guard for a multi-byte read is the subtraction form: fixed-width
// `o + 3` wraps, so `o + 3 < len(b)` proves nothing (and is reported as
// OAK-T0701), while `len(b) >= 4 && o <= len(b) - 4` proves b[o..o+3].
func TestE2EOSMultiByteGuard(t *testing.T) {
	src := `
read_be32: (b: []u8, o: u32): u32 {
  len(b) >= u32(4) && o <= len(b) - u32(4) ? {
    (u32(b[o]) << 24) | (u32(b[o + 1]) << 16) | (u32(b[o + 2]) << 8) | u32(b[o + 3])
  } | { 0 }
}
wrapped: (b: []u8, o: u32): u32 {
  o + 3 < len(b) ? { u32(b[o]) + u32(b[o + 3]) } | { 0 }
}
main: (): i32 {
  xs: [8]u8 = [0, 0, 0, 42, 0, 0, 0, 0]
  read_be32(view(&xs), 0) == u32(42) && wrapped(view(&xs), 2) == u32(0) ? 42 | 1
}
`
	code, abnormal := buildAndRun(t, "os_guard", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	emitted, err := New().WithSource("os.oak", src).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if strings.Count(emitted, "( b ).base[") != 4 || strings.Count(emitted, "oak_view_index_u8( b") != 2 {
		t.Fatalf("the subtraction guard proves the four reads and the wrapping guard none:\n%s", emitted)
	}
}
