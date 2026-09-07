package compiler

import (
	"strings"
	"testing"
)

// Declared record layout (docs/spec/40-records.md): struct(packed) places
// fields densely for wire formats and hardware registers; struct(align: N)
// raises record alignment for cache-line separation. Both are enforced by
// the emitted C99 layout assertions — cc itself verifies every claimed
// sizeof, offsetof, and alignment, so a passing run is a proven layout.

// Packed wire header: u32 + u8 + u16 is 7 bytes packed (natural layout is
// 8), and a packed record nested in a natural one starts fields right after
// it (crc at offset 7 — the whole point of packing a header).
func TestE2EPackedWire(t *testing.T) {
	src := `
Wire: type = struct(packed) {
  magic: u32
  kind: u8
  length: u16
}

Framed: type = struct {
  header: Wire
  crc: u8
}

frame: Framed

main: (): i32 {
  frame.header.magic = u32(305419896)
  frame.header.kind = u8(7)
  frame.header.length = u16(35)
  frame.crc = u8(9)
  i32(frame.header.length) + i32(frame.header.kind)
}
`
	output, err := New().WithSource("packedwire.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	for _, want := range []string{
		"__attribute__((packed))",
		"sizeof(oak_Wire) == 7u",
		"offsetof(oak_Wire, length) == 5u",
		"offsetof(oak_Framed, crc) == 7u",
	} {
		if !strings.Contains(output, want) {
			t.Fatalf("emitted C lacks %q:\n%s", want, output)
		}
	}
	code, abnormal := buildAndRun(t, "packedwire", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// Cache-line alignment: an align(64) record around an atomic cell is the
// false-sharing cure — producer and consumer cursors each own a line. The
// emitted _Alignof assertion makes cc prove the alignment claim.
func TestE2EAlignedCacheLine(t *testing.T) {
	src := `
Line: type = struct(align: 64) {
  cell: Atomic[u32]
}

producerLane: Line
consumerLane: Line

main: (): i32 {
  atomic_store_relaxed(producerLane.cell, u32(30))
  atomic_store_relaxed(consumerLane.cell, u32(12))
  p: u32 = atomic_load_relaxed(producerLane.cell)
  c: u32 = atomic_load_relaxed(consumerLane.cell)
  assert(p + c == u32(42))
  42
}
`
	output, err := New().WithSource("alignedline.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	for _, want := range []string{
		"__attribute__((aligned(64)))",
		"sizeof(oak_Line) == 64u",
		"_Alignof(oak_Line) == 64u",
	} {
		if !strings.Contains(output, want) {
			t.Fatalf("emitted C lacks %q:\n%s", want, output)
		}
	}
	code, abnormal := buildAndRun(t, "alignedline", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// Layout specs are part of a record template and carry to every
// instantiation: Slot[u32] under struct(align: 16) monomorphizes to an
// aligned struct.
func TestE2ELayoutSpecOnTemplate(t *testing.T) {
	src := `
Slot[T]: type = struct(align: 16) {
  value: T
}

slot: Slot[u32]

main: (): i32 {
  slot.value = u32(42)
  assert(slot.value == u32(42))
  42
}
`
	output, err := New().WithSource("alignedslot.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	for _, want := range []string{
		"__attribute__((aligned(16)))",
		"sizeof(oak_Slot_u32) == 16u",
		"_Alignof(oak_Slot_u32) == 16u",
	} {
		if !strings.Contains(output, want) {
			t.Fatalf("emitted C lacks %q:\n%s", want, output)
		}
	}
	code, abnormal := buildAndRun(t, "alignedslot", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// Per-field alignment: both queue cursors carry their own cache line
// inside ONE struct — no wrapper records. offsetof(tail) == 64 and
// sizeof == 128 are asserted in the emitted C, so cc proves the false
// sharing is gone by construction.
func TestE2EPerFieldAlignment(t *testing.T) {
	src := `
Queue: type = struct {
  head(align: 64): Atomic[u32]
  tail(align: 64): Atomic[u32]
  buffer: [8]u8
}

q: Queue

main: (): i32 {
  atomic_store_relaxed(q.head, u32(30))
  atomic_store_relaxed(q.tail, u32(11))
  q.buffer[u32(3)] = u8(1)
  h: u32 = atomic_load_relaxed(q.head)
  t: u32 = atomic_load_relaxed(q.tail)
  assert(h + t == u32(41))
  42
}
`
	output, err := New().WithSource("fieldalign.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	for _, want := range []string{
		"head __attribute__((aligned(64)))",
		"offsetof(oak_Queue, tail) == 64u",
		"offsetof(oak_Queue, buffer) == 68u",
		"sizeof(oak_Queue) == 128u",
	} {
		if !strings.Contains(output, want) {
			t.Fatalf("emitted C lacks %q:\n%s", want, output)
		}
	}
	code, abnormal := buildAndRun(t, "fieldalign", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// Under-alignment of a field (align below the type's natural alignment)
// is packing semantics and fails closed: the record is never emitted
// with a guessed layout.
func TestE2EUnderAlignedFieldFailsClosed(t *testing.T) {
	src := `
Bad: type = struct {
  wide(align: 2): u64
}
`
	output, err := New().WithSource("underalign.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if !strings.Contains(output, "OAK_UNSUPPORTED_RECORD_LAYOUT(oak_Bad)") {
		t.Fatalf("under-aligned field must fail closed:\n%s", output)
	}
}

// Typed field tags are metadata-axis only: the emitted C is byte-identical
// with and without them, and no tag value leaks into the artifact. Go's
// tag ergonomics, statically checked, zero cost.
func TestE2ETypedTagsAreZeroCost(t *testing.T) {
	tagged := `
json: tag = { name: string, omit: Bool }
pb: tag = { field: u32 }

User: type = struct {
  id(align: 8, json: "user_id", pb: 1): u64
  score(json: { name: "score", omit: true }): u32
}

u: User

main: (): i32 {
  u.id = u64(7)
  u.score = u32(42)
  assert(u.id == u64(7))
  42
}
`
	untagged := `
User: type = struct {
  id(align: 8): u64
  score: u32
}

u: User

main: (): i32 {
  u.id = u64(7)
  u.score = u32(42)
  assert(u.id == u64(7))
  42
}
`
	taggedC, err := New().WithSource("tagged.oak", tagged).EmitC().Get()
	if err != nil {
		t.Fatalf("tagged compilation failed: %v", err)
	}
	untaggedC, err := New().WithSource("tagged.oak", untagged).EmitC().Get()
	if err != nil {
		t.Fatalf("untagged compilation failed: %v", err)
	}
	// Source-position provenance comments necessarily differ (the tag
	// declarations occupy lines); everything else must be byte-identical.
	stripProvenance := func(c string) string {
		lines := strings.Split(c, "\n")
		kept := lines[:0]
		for _, line := range lines {
			if strings.HasPrefix(strings.TrimSpace(line), "// @source:") {
				continue
			}
			kept = append(kept, line)
		}
		return strings.Join(kept, "\n")
	}
	if stripProvenance(taggedC) != stripProvenance(untaggedC) {
		t.Fatalf("tags changed the emitted C — metadata leaked into representation:\n--- tagged ---\n%s\n--- untagged ---\n%s", taggedC, untaggedC)
	}
	if strings.Contains(taggedC, "user_id") {
		t.Fatal("tag value leaked into the emitted C")
	}
	code, abnormal := buildAndRun(t, "tagged", tagged)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
