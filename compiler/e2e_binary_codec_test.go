package compiler

import (
	"strings"
	"testing"
)

// The derived binary codec (docs/spec/71-codecs.md section 22, dbs ask 9):
// a fixed-layout record with per-field endianness, a nested record, a byte
// array, a Bool, and signed integers. The expected bytes are written out by
// hand; the record round-trips; a short destination is refused unchanged;
// a short input and a Bool byte above one are rejected. The interpreter and
// the compiled program agree.
const binaryCodecProgram = `import(std)
bin: tag = { endian: string }
Inner: type = struct {
  a: u16
  b(bin: "be"): u16
}
Header: type = struct {
  magic(bin: "be"): u32
  version: u16
  flags: [4]u8
  count(bin: { endian: "be" }): u64
  ok: Bool
  inner: Inner
  delta: i32
  small: i8
  lanes: [2]Inner
}

same: (x: Header, y: Header): Bool {
  x.magic == y.magic && x.version == y.version && x.flags[0] == y.flags[0] && x.flags[3] == y.flags[3] &&
    x.count == y.count && x.ok == y.ok && x.inner.a == y.inner.a && x.inner.b == y.inner.b &&
    x.delta == y.delta && x.small == y.small && x.lanes[1].a == y.lanes[1].a && x.lanes[1].b == y.lanes[1].b
}

err_code: (e: BinaryDecodeError): u32 = e ? | .InputTooShort => u32(1) | .InvalidBool => u32(2) | .InvalidPresence => u32(3)
decode_code: (r: Result[Header, BinaryDecodeError]): u32 = r ? | .Ok(v) => u32(0) | .Err(e) => err_code(e)

main: (): i32 {
  h: Header
  h.magic = u32(0xCAFEBABE)
  h.version = u16(0x0102)
  h.flags[0] = u8(1)
  h.flags[1] = u8(2)
  h.flags[2] = u8(3)
  h.flags[3] = u8(4)
  h.count = u64(0x0A0B)
  h.ok = true
  h.inner.a = u16(0x1122)
  h.inner.b = u16(0x3344)
  h.delta = i32_bits_u32(u32(0xFFFFFFFE))
  h.small = i8_bits_u8(u8(0xFF))
  h.lanes[0].a = u16(5)
  h.lanes[0].b = u16(6)
  h.lanes[1].a = u16(0xABCD)
  h.lanes[1].b = u16(0xEF01)
  assert(binary_result_value(encoded_size[Header, Binary](h)) == u32(36))
  data: [36]u8
  true ? {
    dst: [*]u8 = span(&data)
    assert(binary_result_value(encode[Header, Binary](h, dst)) == u32(36))
  }
  expected: [36]u8
  expected[0] = u8(0xCA)
  expected[1] = u8(0xFE)
  expected[2] = u8(0xBA)
  expected[3] = u8(0xBE)
  expected[4] = u8(0x02)
  expected[5] = u8(0x01)
  expected[6] = u8(1)
  expected[7] = u8(2)
  expected[8] = u8(3)
  expected[9] = u8(4)
  expected[16] = u8(0x0A)
  expected[17] = u8(0x0B)
  expected[18] = u8(1)
  expected[19] = u8(0x22)
  expected[20] = u8(0x11)
  expected[21] = u8(0x33)
  expected[22] = u8(0x44)
  expected[23] = u8(0xFE)
  expected[24] = u8(0xFF)
  expected[25] = u8(0xFF)
  expected[26] = u8(0xFF)
  expected[27] = u8(0xFF)
  expected[28] = u8(5)
  expected[29] = u8(0)
  expected[30] = u8(0)
  expected[31] = u8(6)
  expected[32] = u8(0xCD)
  expected[33] = u8(0xAB)
  expected[34] = u8(0xEF)
  expected[35] = u8(0x01)
  i: u32 = 0
  while i < u32(36) {
    assert(data[i] == expected[i])
    i = i + u32(1)
  }
  decoded: Header = decode[Header, Binary](view(&data)) ?
    | .Ok(v) => v
    | .Err(e) => h
  assert(same(decoded, h))
  assert(decoded.count == u64(0x0A0B) && decoded.delta == i32_bits_u32(u32(0xFFFFFFFE)))
  // the fluent spellings are the same operations
  fluent: [36]u8
  assert(binary_result_value(from[Header](h).to[Binary](span(&fluent))) == u32(36))
  assert(fluent[35] == u8(0x01) && fluent[0] == u8(0xCA))
  back: Header = from[Binary](view(&fluent)).to[Header]() ?
    | .Ok(v) => v
    | .Err(e) => decoded
  assert(same(back, h))
  // a short destination is refused and left unchanged
  short: [35]u8
  short[0] = u8(77)
  assert(!binary_result_ok(encode[Header, Binary](h, span(&short))))
  assert(short[0] == u8(77) && short[34] == u8(0))
  // a short input, and a Bool byte above one
  prefix: [35]u8
  i = u32(0)
  while i < u32(35) {
    prefix[i] = data[i]
    i = i + u32(1)
  }
  assert(decode_code(decode[Header, Binary](view(&prefix))) == u32(1))
  data[18] = u8(2)
  assert(decode_code(decode[Header, Binary](view(&data))) == u32(2))
  assert(decode_code(decode[Header, Binary](view(&fluent))) == u32(0))
  42
}
`

func TestE2EBinaryCodec(t *testing.T) {
	if got := interpretChecked(t, binaryCodecProgram); got != 42 {
		t.Fatalf("interpreter: %d", got)
	}
	_, code, abnormal := buildAndRunOutput(t, "binary_codec", binaryCodecProgram)
	if abnormal || code != 42 {
		t.Fatalf("compiled: exit %d abnormal %v", code, abnormal)
	}
}

// Zero cost, verified in the C (docs/spec/71-codecs.md section 4): the
// unchecked writer and reader call no byte helper and check no capacity;
// the checked entry checks once; the size is the constant; the fluent
// spellings emit the same C as the direct ones.
func TestBinaryCodecLowering(t *testing.T) {
	emitted, err := New().WithSource("binary_codec.oak", binaryCodecProgram).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, forbidden := range []string{"malloc(", "calloc(", "OAK_UNSUPPORTED"} {
		if strings.Contains(emitted, forbidden) {
			t.Fatalf("unexpected lowering: %s", forbidden)
		}
	}
	// The prelude's endian helpers exist in the C; the generated codec must
	// not call them: every byte is a shift, a truncation, and a store.
	unchecked := cFunctionBody(t, emitted, "oak___oak_bin_write_unchecked_Header")
	reader := cFunctionBody(t, emitted, "oak___oak_bin_read_unchecked_Header")
	for _, body := range []string{unchecked, reader} {
		for _, forbidden := range []string{"bytes_write_", "bytes_read_", "bytes_range_fits", "oak_assert("} {
			if strings.Contains(body, forbidden) {
				t.Fatalf("a generated unchecked function contains %q:\n%s", forbidden, body)
			}
		}
	}
	if !strings.Contains(unchecked, "oak___oak_bin_write_unchecked_Inner(") {
		t.Fatalf("the nested record does not write through its unchecked writer:\n%s", unchecked)
	}
	checked := cFunctionBody(t, emitted, "oak___oak_bin_write_Header")
	if strings.Count(checked, "oak_bytes_range_fits(") != 1 {
		t.Fatalf("the checked writer checks %d times:\n%s", strings.Count(checked, "oak_bytes_range_fits("), checked)
	}
	size := cFunctionBody(t, emitted, "oak___oak_bin_encoded_size_Header")
	if !strings.Contains(size, "36") {
		t.Fatalf("the size is not the constant 36:\n%s", size)
	}
	direct := strings.ReplaceAll(binaryCodecProgram, "from[Header](h).to[Binary](span(&fluent))", "encode[Header, Binary](h, span(&fluent))")
	direct = strings.ReplaceAll(direct, "from[Binary](view(&fluent)).to[Header]()", "decode[Header, Binary](view(&fluent))")
	directC, err := New().WithSource("binary_codec.oak", direct).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if emitted != directC {
		t.Fatal("the fluent codec spellings emitted different C from the direct calls")
	}
}

// The shapes the layout refuses, each with its reason.
func TestBinaryCodecRejects(t *testing.T) {
	for name, c := range map[string][2]string{
		"string field":     {"import(std)\nR: type = struct { a: string }\nmain: (): i32 {\n r: R\n d: [8]u8\n _ = encode[R, Binary](r, span(&d))\n 0\n}\n", "unsupported field"},
		"endian on record": {"import(std)\nbin: tag = { endian: string }\nI: type = struct { a: u16 }\nR: type = struct { i(bin: \"be\"): I }\nmain: (): i32 {\n r: R\n d: [8]u8\n _ = encode[R, Binary](r, span(&d))\n 0\n}\n", "endianness applies to integer fields"},
		"endian on a byte": {"import(std)\nbin: tag = { endian: string }\nR: type = struct { a(bin: \"be\"): u8 }\nmain: (): i32 {\n r: R\n d: [8]u8\n _ = encode[R, Binary](r, span(&d))\n 0\n}\n", "no endianness"},
		"bad endian":       {"import(std)\nbin: tag = { endian: string }\nR: type = struct { a(bin: \"middle\"): u32 }\nmain: (): i32 {\n r: R\n d: [8]u8\n _ = encode[R, Binary](r, span(&d))\n 0\n}\n", "\"le\" or \"be\""},
		"located decode":   {"import(std)\nR: type = struct { a: u32 }\nmain: (): i32 {\n d: [8]u8\n _ = decode_located[R, Binary](view(&d))\n 0\n}\n", "JSON operation"},
	} {
		_, err := New().WithSource(name+".oak", c[0]).Check().Get()
		if err == nil || !strings.Contains(err.Error(), c[1]) {
			t.Errorf("%s: %v", name, err)
		}
	}
}

// Presence fields and byte runs (docs/spec/71-codecs.md section 22): the
// frame is 14 bytes — kind 2, count 1 + 4, seen 1 + 1, payload 4, tail 1. An
// Option field is a presence byte and a fixed payload; a View[u8, R] field
// with a bytes count is a zero-copy subslice of the input, and the decoded
// record borrows the input. Exact bytes, the round trip in both
// realizations, and the refusals: a presence byte above one, a view of the
// wrong length, and a write to the input while the decoded record lives.
const binaryFrameProgram = `import(std)
bin: tag = { endian: string, bytes: u32 }
Frame[R]: type = struct {
  kind: u16
  count(bin: "be"): Option[u32]
  seen: Option[Bool]
  payload(bin: { bytes: 4 }): View[u8, R]
  tail: u8
}

frame_err: (e: BinaryDecodeError): u32 = e ? | .InputTooShort => u32(1) | .InvalidBool => u32(2) | .InvalidPresence => u32(3)
frame_code[R]: (r: Result[Frame[R], BinaryDecodeError]): u32 = r ? | .Ok(f) => u32(0) | .Err(e) => frame_err(e)

// A decoded frame re-encodes to its own bytes: the region-carrying record
// is passed straight back to the derived encoder.
reencode[R]: (f: Frame[R], dst: [*]u8): u32 = binary_result_value(encode[Frame, Binary](f, dst))

main: (): i32 {
  data: [15]u8
  data[0] = u8(0x02)
  data[1] = u8(0x01)
  data[2] = u8(1)
  data[3] = u8(0x11)
  data[4] = u8(0x22)
  data[5] = u8(0x33)
  data[6] = u8(0x44)
  data[7] = u8(0)
  data[8] = u8(0)
  data[9] = u8(0xAA)
  data[10] = u8(0xBB)
  data[11] = u8(0xCC)
  data[12] = u8(0xDD)
  data[13] = u8(9)
  data[14] = u8(0)
  out: [15]u8
  true ? {
    decoded: Result[Frame, BinaryDecodeError] = decode[Frame, Binary](view(&data))
    decoded ?
      | .Ok(g) => {
        assert(g.kind == u16(0x0102) && g.tail == u8(9))
        assert(option_or[u32](g.count, u32(0)) == u32(0x11223344))
        assert(len(g.payload) == u32(4) && g.payload[0] == u8(0xAA) && g.payload[3] == u8(0xDD))
        absent: Bool = g.seen ? | .None => true | .Some(b) => false
        assert(absent)
        assert(binary_result_value(encoded_size[Frame, Binary](g)) == u32(14))
        assert(reencode(g, span(&out)) == u32(14))
      }
      | .Err(e) => assert(false)
  }
  i: u32 = 0
  while i < u32(15) {
    assert(out[i] == data[i])
    i = i + u32(1)
  }
  // an absent count writes zeros; a present Bool payload reads back
  blank: [15]u8
  blank[2] = u8(0)
  blank[3] = u8(0xFF)
  blank[7] = u8(1)
  blank[8] = u8(1)
  blank[9] = u8(0xEE)
  again: [15]u8
  again[3] = u8(0x77)
  true ? {
    decoded: Result[Frame, BinaryDecodeError] = decode[Frame, Binary](view(&blank))
    decoded ?
      | .Ok(g) => {
        none: Bool = g.count ? | .None => true | .Some(c) => false
        assert(none)
        assert(option_or[Bool](g.seen, false))
        assert(g.payload[0] == u8(0xEE))
        assert(reencode(g, span(&again)) == u32(14))
      }
      | .Err(e) => assert(false)
  }
  assert(again[2] == u8(0) && again[3] == u8(0) && again[7] == u8(1) && again[8] == u8(1) && again[9] == u8(0xEE))
  // a presence byte above one, a Bool payload byte above one, and a short input
  data[2] = u8(2)
  assert(frame_code(decode[Frame, Binary](view(&data))) == u32(3))
  data[2] = u8(1)
  blank[8] = u8(7)
  assert(frame_code(decode[Frame, Binary](view(&blank))) == u32(2))
  prefix: [13]u8
  assert(frame_code(decode[Frame, Binary](view(&prefix))) == u32(1))
  42
}
`

func TestE2EBinaryCodecPresenceAndViews(t *testing.T) {
	if got := interpretChecked(t, binaryFrameProgram); got != 42 {
		t.Fatalf("interpreter: %d", got)
	}
	_, code, abnormal := buildAndRunOutput(t, "binary_frame", binaryFrameProgram)
	if abnormal || code != 42 {
		t.Fatalf("compiled: exit %d abnormal %v", code, abnormal)
	}
	// The decoded record borrows its input: writing the input while the
	// record lives is the borrow checker's business.
	borrowed := strings.Replace(binaryFrameProgram, "        assert(absent)\n", "        assert(absent)\n        data[0] = u8(5)\n", 1)
	if _, err := New().WithSource("borrowed.oak", borrowed).Check().Get(); err == nil || !strings.Contains(err.Error(), "OAK-B01") {
		t.Fatalf("a write to the viewed input while the decoded frame lives was not rejected: %v", err)
	}
	for name, c := range map[string][2]string{
		"view without bytes": {"import(std)\nbin: tag = { endian: string, bytes: u32 }\nF[R]: type = struct { p: View[u8, R] }\nmain: (): i32 {\n d: [8]u8\n _ = decode[F, Binary](view(&d))\n 0\n}\n", "needs its byte count"},
		"array of option":    {"import(std)\nR: type = struct { a: [2]Option[u32] }\nmain: (): i32 {\n r: R\n d: [16]u8\n _ = encode[R, Binary](r, span(&d))\n 0\n}\n", "unsupported field"},
	} {
		_, err := New().WithSource(name+".oak", c[0]).Check().Get()
		if err == nil || !strings.Contains(err.Error(), c[1]) {
			t.Errorf("%s: %v", name, err)
		}
	}
}
