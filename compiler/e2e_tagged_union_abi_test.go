package compiler

// Tagged unions at the C boundary (docs/spec/92-ffi.md section 2.6, the
// vgic/hypervisor port ask #7): a union with payloads has one C shape — a
// u32 tag holding the variant's declaration index, then the payload union —
// asserted by cc, admitted by the layout builtins and as a boundary-span
// element, and readable from hand-written C through that shape alone.

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// The emitted union carries a fixed-width tag and a cc-ratified layout
// assertion; size_of/align_of/offset_of answer for it like for a record.
func TestE2ETaggedUnionLayoutIsProven(t *testing.T) {
	src := `
Effect: type = None | Send: u32 | Yield: u8
Wide: type = A: u64 | B: u8
Mode: type = Idle | Busy
Point: type = struct { x: i32, y: i32 }
Shape: type = Dot: Point | Empty
main: (): i32 {
  assert(size_of[Effect]() == 8)
  assert(align_of[Effect]() == 4)
  assert(offset_of[Effect](tag) == 0)
  assert(offset_of[Effect](payload) == 4)
  assert(size_of[Wide]() == 16)
  assert(offset_of[Wide](payload) == 8)
  assert(size_of[Mode]() == 4)
  assert(size_of[Shape]() == 12)
  assert(offset_of[Shape](payload) == 4)
  static_assert(size_of[Effect]() == u32(8))
  42
}
`
	output, err := New().WithSource("unionlayout.oak", src).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"u32 tag;",
		"typedef char oak_union_layout_Effect[ (sizeof(oak_Effect) == 8u && _Alignof(oak_Effect) == 4u && offsetof(oak_Effect, tag) == 0u && offsetof(oak_Effect, payload) == 4u) ? 1 : -1 ];",
		"typedef char oak_union_layout_Mode[ (sizeof(oak_Mode) == 4u && _Alignof(oak_Mode) == 4u && offsetof(oak_Mode, tag) == 0u) ? 1 : -1 ];",
		"typedef char oak_union_layout_Shape[ (sizeof(oak_Shape) == 12u",
	} {
		if !strings.Contains(output, want) {
			t.Fatalf("generated C lacks %q:\n%s", want, output)
		}
	}
	if strings.Contains(output, "_tag tag;") {
		t.Fatalf("the tag must be a fixed-width u32, not the enum:\n%s", output)
	}
	code, abnormal := buildAndRun(t, "unionlayout", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// A record may embed a declared tagged union: the union's proven layout
// places the record, and cc ratifies both.
func TestE2ERecordEmbedsTaggedUnion(t *testing.T) {
	src := `
Effect: type = None | Send: u32
Step: type = struct { tick: u64, effect: Effect }
main: (): i32 {
  s: Step = Step { tick: 7, effect: .Send(35) }
  assert(offset_of[Step](effect) == 8)
  assert(size_of[Step]() == 16)
  s.effect ?
    | .Send(n) => i32_bits_u32(n + u32_trunc_u64(s.tick))
    | .None => 1
}
`
	output, err := New().WithSource("stepunion.oak", src).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(output, "OAK_UNSUPPORTED") {
		t.Fatalf("record embedding a union must be placeable:\n%s", output)
	}
	code, abnormal := buildAndRun(t, "stepunion", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// Hand-written C consumes an exported Oak function's tagged-union result
// through the documented shape alone — its own mirror typedef, no generated
// header — and Oak reads the C verdict back through an extern binding.
func TestE2ETaggedUnionReadFromC(t *testing.T) {
	src := `
Effect: type = None | Send: u32 | Yield: u8
probe: (): c.UInt = c.extern("probe_effect")
pub next_effect: (n: u32): Effect {
  e: Effect = .None
  n > 0 ? { e = .Send(n) }
  e
}
main: (): i32 {
  assert(u32(probe()) == 42)
  42
}
`
	consumer := `
#include <stdint.h>
/* The Oak tagged-union shape (docs/spec/92-ffi.md section 2.6), mirrored
   by hand: a uint32_t tag (declaration index), then the payload union. */
typedef struct { uint32_t tag; union { uint32_t Send; uint8_t Yield; } payload; } effect_t;
extern effect_t oak_next_effect(uint32_t n);
unsigned int probe_effect(void) {
  effect_t sent = oak_next_effect(40u);
  effect_t none = oak_next_effect(0u);
  if (sent.tag != 1u || none.tag != 0u) { return 0u; }
  return sent.payload.Send + 2u;
}
`
	dir := t.TempDir()
	consumerPath := filepath.Join(dir, "consumer.c")
	if err := os.WriteFile(consumerPath, []byte(consumer), 0o644); err != nil {
		t.Fatal(err)
	}
	_, code, abnormal := buildAndRunOutput(t, "unionabi", src, consumerPath)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// A view of tagged unions crosses as a boundary span — the base pointer and
// the element count — and C walks it through the mirrored shape.
func TestE2ETaggedUnionBoundarySpan(t *testing.T) {
	consumer := `
#include <stddef.h>
#include <stdint.h>
typedef struct { uint32_t tag; union { uint32_t Send; } payload; } effect_t;
unsigned int sum_sends(const void *data, size_t count) {
  const effect_t *effects = data;
  unsigned int total = 0;
  for (size_t i = 0; i < count; i++) {
    if (effects[i].tag == 1u) { total += effects[i].payload.Send; }
  }
  return total;
}
`
	dir := t.TempDir()
	consumerPath := filepath.Join(dir, "sum_sends.c")
	if err := os.WriteFile(consumerPath, []byte(consumer), 0o644); err != nil {
		t.Fatal(err)
	}
	src := `
sum_sends: (data: c.Ptr, count: c.Size): c.UInt = c.extern("sum_sends")
Effect: type = None | Send: u32
main: (): i32 {
  arr: [3]Effect
  first: Effect = .Send(40)
  last: Effect = .Send(2)
  arr[0] = first
  arr[2] = last
  v: []Effect = view(&arr)
  assert(u32(sum_sends(c.span_of(v))) == 42)
  42
}
`
	output, err := New().WithSource("unionspan.oak", src).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(output, "sum_sends( (void *)( v ).base, (size_t)( v ).len )") {
		t.Fatalf("the span must lower to base pointer and element count:\n%s", output)
	}
	_, code, abnormal := buildAndRunOutput(t, "unionspan", src, consumerPath)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// A union whose payload has no single meaning across the boundary (a
// string) is rejected as a span element, and a generic union too.
func TestTaggedUnionBoundaryRejections(t *testing.T) {
	cases := []struct{ name, src, want string }{
		{"string-payload", `
write: (fd: c.Int, data: c.Ptr, count: c.Size): c.Long = c.extern("write")
Msg: type = Text: string | Quiet
emit: (v: []Msg): () { _ = write(c.Int(1), c.span_of(v)) }
main: (): i32 { 0 }
`, "OAK-F0104"},
		{"offset-of-unknown-field", `
Effect: type = None | Send: u32
main: (): i32 { i32(offset_of[Effect](Send)) }
`, "has the fields tag and payload"},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			_, err := New().WithSource(c.name+".oak", c.src).Check().Get()
			if err == nil || !strings.Contains(err.Error(), c.want) {
				t.Fatalf("%s: want %q, got %v", c.name, c.want, err)
			}
		})
	}
}
