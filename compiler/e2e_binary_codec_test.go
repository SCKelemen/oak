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

err_code: (e: BinaryDecodeError): u32 = e ? | .InputTooShort => u32(1) | .InvalidBool => u32(2)
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
		"option field":     {"import(std)\nR: type = struct { a: Option[u32] }\nmain: (): i32 {\n r: R\n d: [8]u8\n _ = encode[R, Binary](r, span(&d))\n 0\n}\n", "no fixed binary layout"},
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
