package compiler

import (
	"strings"
	"testing"
)

// struct(no_padding) (docs/spec/40-records.md section 6a): the claim that
// the natural placement is dense — every byte a field byte — checked by the
// compiler with a diagnostic naming the padded field, and ratified by the C
// compiler through the emitted sum-of-members assertion. The fields keep
// their natural alignment, which packing would not give.
func TestE2ENoPaddingFrame(t *testing.T) {
	src := `
import(std)
Frame: type = struct(no_padding) {
  checksum: u128
  op: u64
  size: u32
  kind: u16
  flags: u8
  reserved: u8
}
Envelope: type = struct(no_padding) {
  frame: Frame
  tail: [16]u8
}
Wire: type = struct(packed) {
  magic: u32
  kind: u8
}
Carrier: type = struct(no_padding) {
  wire: Wire
  pad: [3]u8
  crc: u32
}
main: (): i32 {
  static_assert(size_of[Frame]() == u32(32))
  static_assert(offset_of[Frame](kind) == u32(28))
  static_assert(size_of[Envelope]() == u32(48))
  static_assert(size_of[Carrier]() == u32(12))
  e: Envelope
  e.frame.checksum = u128(7)
  e.frame.kind = u16(2)
  e.tail[u32(3)] = u8(5)
  e.frame.checksum == u128(7) && e.frame.kind == u16(2) && e.frame.reserved == u8(0) && e.tail[u32(3)] == u8(5) ? 42 | 1
}
`
	output, err := New().WithSource("frame.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	for _, want := range []string{
		"typedef char oak_layout_dense_Frame[ (sizeof(oak_Frame) == (sizeof(((oak_Frame *)0)->checksum) + sizeof(((oak_Frame *)0)->op)",
		"oak_layout_dense_Envelope",
		"oak_layout_dense_Carrier",
		"sizeof(oak_Frame) == 32u",
	} {
		if !strings.Contains(output, want) {
			t.Fatalf("emitted C lacks %q:\n%s", want, output)
		}
	}
	if strings.Contains(output, "__attribute__((packed)) oak_Frame") {
		t.Fatal("no_padding must not pack: the fields keep their natural alignment")
	}
	code, abnormal := buildAndRun(t, "no_padding_frame", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// A broken claim is a diagnostic that names the field and the bytes.
func TestNoPaddingRejections(t *testing.T) {
	cases := map[string]struct{ src, want string }{
		"padding between fields": {`
Bad: type = struct(no_padding) { a: u8, b: u32 }
main: (): i32 = 0
`, "record Bad declares no_padding, but 3 bytes of padding before field \"b\" at offset 4"},
		"tail padding": {`
Bad: type = struct(no_padding) { a: u32, b: u8 }
main: (): i32 = 0
`, "3 bytes of tail padding after field \"b\" (the fields end at offset 5)"},
		"tail padding from a raised alignment": {`
Bad: type = struct(no_padding, align: 16) { a: u64, b: u32 }
main: (): i32 = 0
`, "4 bytes of tail padding after field \"b\""},
		"nested natural record": {`
Inner: type = struct { a: u8, b: u32 }
Bad: type = struct(no_padding) { inner: Inner, c: u32 }
main: (): i32 = 0
`, "field inner is a Inner, which does not itself declare no_padding or packed"},
		"view field": {`
Bad: type = struct(no_padding) { bytes: []u8, n: u32 }
main: (): i32 = 0
`, "field bytes is a view or span"},
		"platform width": {`
Bad: type = struct(no_padding) { n: uint }
main: (): i32 = 0
`, "field n is uint, whose width the target chooses"},
		"packed and no_padding": {`
Bad: type = struct(packed, no_padding) { a: u8, b: u32 }
main: (): i32 = 0
`, "packed is dense by construction"},
		"template": {`
Bad[T]: type = struct(no_padding) { value: T, n: u32 }
main: (): i32 = 0
`, "no_padding is declared on a template"},
		"duplicate clause": {`
Bad: type = struct(no_padding, no_padding) { a: u32 }
main: (): i32 = 0
`, "duplicate 'no_padding'"},
	}
	for name, c := range cases {
		_, err := New().WithSource("bad.oak", c.src).EmitC().Get()
		if err == nil || !strings.Contains(err.Error(), c.want) {
			t.Fatalf("%s: want %q, got %v", name, c.want, err)
		}
	}
}
