package compiler

import (
	"strings"
	"testing"
)

// derive.reserved_zero (docs/spec/83-modules.md section 6.6): a wire
// record's reserved bytes are zero on both sides. The derived predicate
// reads the declaration for the fields named reserved or reserved_*, walks
// fixed arrays in a bounded loop, and asks a nested record that holds
// reserved fields through its own helper; compiled and interpreted agree.
const reservedProgram = `
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
  reserved_tail: [16]u8
}
Flagged: type = struct { on: Bool, reserved_flag: Bool, reserved_words: [2]u64 }
frame_reserved_zero: (f: Frame): Bool = derive.reserved_zero
envelope_reserved_zero: (e: Envelope): Bool = derive.reserved_zero
flagged_reserved_zero: (f: Flagged): Bool = derive.reserved_zero
main: (): i32 {
  e: Envelope
  e.frame.checksum = u128(7)
  e.frame.op = u64(9)
  e.frame.flags = u8(255)
  ok: Bool = frame_reserved_zero(e.frame) && envelope_reserved_zero(e)
  e.reserved_tail[u32(5)] = u8(1)
  ok = ok && !envelope_reserved_zero(e) && frame_reserved_zero(e.frame)
  e.reserved_tail[u32(5)] = u8(0)
  e.frame.reserved = u8(2)
  ok = ok && !frame_reserved_zero(e.frame) && !envelope_reserved_zero(e)
  e.frame.reserved = u8(0)
  ok = ok && envelope_reserved_zero(e)
  g: Flagged
  g.on = true
  ok = ok && flagged_reserved_zero(g)
  g.reserved_flag = true
  ok = ok && !flagged_reserved_zero(g)
  g.reserved_flag = false
  g.reserved_words[u32(1)] = u64(3)
  ok = ok && !flagged_reserved_zero(g)
  ok ? 42 | 1
}
`

func TestE2EDeriveReservedZeroCompiled(t *testing.T) {
	code, abnormal := buildAndRun(t, "reserved_zero", reservedProgram)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestE2EDeriveReservedZeroInterpreted(t *testing.T) {
	if got := interpretChecked(t, reservedProgram); got != 42 {
		t.Fatalf("interpreter: got %d, want 42", got)
	}
}

func TestDeriveReservedZeroRejections(t *testing.T) {
	cases := map[string]struct{ src, want string }{
		"nothing reserved": {`
Plain: type = struct { a: u32, b: u32 }
check: (v: Plain): Bool = derive.reserved_zero
main: (): i32 = 0
`, "no field is named reserved or reserved_*"},
		"reserved view": {`
Bad: type = struct { a: u32, reserved: []u8 }
check: (v: Bad): Bool = derive.reserved_zero
main: (): i32 = 0
`, "reserved field reserved must be a fixed-width integer, Bool, or a fixed array of those"},
		"reserved record": {`
Inner: type = struct { a: u32 }
Bad: type = struct { reserved_inner: Inner }
check: (v: Bad): Bool = derive.reserved_zero
main: (): i32 = 0
`, "reserved field reserved_inner must be"},
		"signature": {`
Frame: type = struct { reserved: u8 }
check: (v: Frame): u32 = derive.reserved_zero
main: (): i32 = 0
`, "derive.reserved_zero requires the signature (v: T): Bool"},
		"sum type": {`
Kind: type = | A | B
check: (v: Kind): Bool = derive.reserved_zero
main: (): i32 = 0
`, "reserved fields belong to a record"},
	}
	for name, c := range cases {
		_, err := New().WithSource("bad.oak", c.src).EmitC().Get()
		if err == nil || !strings.Contains(err.Error(), c.want) {
			t.Fatalf("%s: want %q, got %v", name, c.want, err)
		}
	}
}
