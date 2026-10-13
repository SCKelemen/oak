package compiler

import (
	"bytes"
	"fmt"
	"os/exec"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

// These are implementation/rejection tests, not protocol-conformance or proof
// certificates. Both realizations must execute the same checked Oak source.
func runBoundedReaderAPDUProgram(t *testing.T, name, source string) {
	t.Helper()
	if _, err := exec.LookPath("cc"); err != nil {
		t.Fatalf("compiled coverage requires authenticated cc on PATH: %v", err)
	}
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/" + name + "\noak 0.1.0\n",
		"main.oak": source,
	})
	comp := New().WithPackageDir(root)
	code, err := comp.EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, forbidden := range []string{"malloc(", "calloc(", "realloc(", "OAK_UNSUPPORTED"} {
		if strings.Contains(code, forbidden) {
			t.Fatalf("%s emitted forbidden %q", name, forbidden)
		}
	}
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	env := object.NewEnvironment()
	env.SetArithmeticWidths(model.TypeChecker.ArithmeticType)
	if result := evaluator.Eval(model.Tree.Root, env); result != nil {
		if evalErr, ok := result.(*object.Error); ok {
			t.Fatalf("%s interpreter initialization: %s", name, evalErr.Message)
		}
	}
	call := parser.New(layout.New(scanner.New("main()"))).ParseProgram()
	result := evaluator.Eval(call, env)
	integer, ok := result.(*object.Integer)
	if !ok || integer.Value != 42 {
		t.Fatalf("%s interpreter result: %v", name, result)
	}
	status, abnormal := buildPackageAndRun(t, comp)
	if abnormal || status != 42 {
		t.Fatalf("%s compiled result: exit=%d abnormal=%v", name, status, abnormal)
	}
}

const boundedReaderProgram = `package main
import("encoding/reader")

reader_error: (reason: reader.Error): u32 = reason ?
  | .InvalidWindow => u32(1)
  | .InsufficientData => u32(2)

main: (): i32 {
  storage: [4]u8 = [4]u8{ u8(17), u8(34), u8(51), u8(68) }
  src: []u8 = view(&storage)
  original: reader.Window = reader.Window { next: u32(1), end: u32(3) }
  made: Result[reader.Window, reader.Error] = reader.window(src, u32(1), u32(2))
  reader_check_01: Bool = made ? | .Ok(w) => w.next == u32(1) && w.end == u32(3) | .Err(e) => false
  assert(reader_check_01)
  reader_check_02: Bool = reader.remaining(original, src) ? | .Ok(n) => n == u32(2) | .Err(e) => false
  assert(reader_check_02)
  reader_check_03: Bool = reader.take(original, src, u32(2)) ? | .Ok(r) => r.offset == u32(1) && r.length == u32(2) && r.rest.next == u32(3) && r.rest.end == u32(3) | .Err(e) => false
  assert(reader_check_03)
  reader_check_04: Bool = reader.take(original, src, u32(3)) ? | .Ok(r) => false | .Err(e) => reader_error(e) == u32(2)
  assert(reader_check_04)
  assert(original.next == u32(1) && original.end == u32(3))
  reader_check_05: Bool = reader.read_u8(original, src) ? | .Ok(r) => r.value == u8(34) && r.rest.next == u32(2) && r.rest.end == u32(3) | .Err(e) => false
  assert(reader_check_05)
  reader_check_06: Bool = reader.read_u16_be(original, src) ? | .Ok(r) => r.value == u16(8755) && r.rest.next == u32(3) && r.rest.end == u32(3) | .Err(e) => false
  assert(reader_check_06)

  at_end: reader.Window = reader.Window { next: u32(4), end: u32(4) }
  reader_check_07: Bool = reader.window(src, u32(4), u32(0)) ? | .Ok(w) => w.next == u32(4) && w.end == u32(4) | .Err(e) => false
  assert(reader_check_07)
  reader_check_08: Bool = reader.take(at_end, src, u32(0)) ? | .Ok(r) => r.offset == u32(4) && r.length == u32(0) && r.rest.next == u32(4) && r.rest.end == u32(4) | .Err(e) => false
  assert(reader_check_08)
  reader_check_09: Bool = reader.read_u8(at_end, src) ? | .Ok(r) => false | .Err(e) => reader_error(e) == u32(2)
  assert(reader_check_09)
  reader_check_10: Bool = reader.read_u16_be(at_end, src) ? | .Ok(r) => false | .Err(e) => reader_error(e) == u32(2)
  assert(reader_check_10)
  reader_check_11: Bool = reader.take(at_end, src, u32(4294967295)) ? | .Ok(r) => false | .Err(e) => reader_error(e) == u32(2)
  assert(reader_check_11)

  narrow: reader.Window = reader.Window { next: u32(1), end: u32(2) }
  reader_check_12: Bool = reader.read_u16_be(narrow, src) ? | .Ok(r) => false | .Err(e) => reader_error(e) == u32(2)
  assert(reader_check_12)
  assert(narrow.next == u32(1) && narrow.end == u32(2))
  invalid_next: reader.Window = reader.Window { next: u32(3), end: u32(2) }
  invalid_end: reader.Window = reader.Window { next: u32(0), end: u32(5) }
  invalid_max: reader.Window = reader.Window { next: u32(4294967295), end: u32(4294967295) }
  reader_check_13: Bool = reader.remaining(invalid_next, src) ? | .Ok(n) => false | .Err(e) => reader_error(e) == u32(1)
  assert(reader_check_13)
  reader_check_14: Bool = reader.take(invalid_next, src, u32(0)) ? | .Ok(r) => false | .Err(e) => reader_error(e) == u32(1)
  assert(reader_check_14)
  reader_check_15: Bool = reader.read_u8(invalid_end, src) ? | .Ok(r) => false | .Err(e) => reader_error(e) == u32(1)
  assert(reader_check_15)
  reader_check_16: Bool = reader.read_u16_be(invalid_max, src) ? | .Ok(r) => false | .Err(e) => reader_error(e) == u32(1)
  assert(reader_check_16)
  reader_check_17: Bool = reader.window(src, u32(5), u32(0)) ? | .Ok(w) => false | .Err(e) => reader_error(e) == u32(1)
  assert(reader_check_17)
  reader_check_18: Bool = reader.window(src, u32(4), u32(1)) ? | .Ok(w) => false | .Err(e) => reader_error(e) == u32(1)
  assert(reader_check_18)
  reader_check_19: Bool = reader.window(src, u32(4294967295), u32(1)) ? | .Ok(w) => false | .Err(e) => reader_error(e) == u32(1)
  assert(reader_check_19)
  reader_check_20: Bool = reader.window(src, u32(1), u32(4294967295)) ? | .Ok(w) => false | .Err(e) => reader_error(e) == u32(1)
  assert(reader_check_20)

  // Direct BE16 golden 0x0000: preserve the input and narrower window.
  true ? {
    word_storage: [4]u8 = [4]u8{ u8(91), u8(0), u8(0), u8(92) }
    word_src: []u8 = view(&word_storage)
    word_state: reader.Window = reader.Window { next: u32(1), end: u32(3) }
    reader_check_21: Bool = reader.read_u16_be(word_state, word_src) ? | .Ok(r) => r.value == u16(0) && r.rest.next == u32(3) && r.rest.end == u32(3) | .Err(e) => false
    assert(reader_check_21)
    assert(word_state.next == u32(1) && word_state.end == u32(3))
    assert(word_storage[0] == u8(91) && word_storage[1] == u8(0) && word_storage[2] == u8(0) && word_storage[3] == u8(92))
  }

  // Direct BE16 golden 0x0001: preserve the input and narrower window.
  true ? {
    word_storage: [4]u8 = [4]u8{ u8(91), u8(0), u8(1), u8(92) }
    word_src: []u8 = view(&word_storage)
    word_state: reader.Window = reader.Window { next: u32(1), end: u32(3) }
    reader_check_22: Bool = reader.read_u16_be(word_state, word_src) ? | .Ok(r) => r.value == u16(1) && r.rest.next == u32(3) && r.rest.end == u32(3) | .Err(e) => false
    assert(reader_check_22)
    assert(word_state.next == u32(1) && word_state.end == u32(3))
    assert(word_storage[0] == u8(91) && word_storage[1] == u8(0) && word_storage[2] == u8(1) && word_storage[3] == u8(92))
  }

  // Direct BE16 golden 0x00ff: preserve the input and narrower window.
  true ? {
    word_storage: [4]u8 = [4]u8{ u8(91), u8(0), u8(255), u8(92) }
    word_src: []u8 = view(&word_storage)
    word_state: reader.Window = reader.Window { next: u32(1), end: u32(3) }
    reader_check_23: Bool = reader.read_u16_be(word_state, word_src) ? | .Ok(r) => r.value == u16(255) && r.rest.next == u32(3) && r.rest.end == u32(3) | .Err(e) => false
    assert(reader_check_23)
    assert(word_state.next == u32(1) && word_state.end == u32(3))
    assert(word_storage[0] == u8(91) && word_storage[1] == u8(0) && word_storage[2] == u8(255) && word_storage[3] == u8(92))
  }

  // Direct BE16 golden 0x0100: preserve the input and narrower window.
  true ? {
    word_storage: [4]u8 = [4]u8{ u8(91), u8(1), u8(0), u8(92) }
    word_src: []u8 = view(&word_storage)
    word_state: reader.Window = reader.Window { next: u32(1), end: u32(3) }
    reader_check_24: Bool = reader.read_u16_be(word_state, word_src) ? | .Ok(r) => r.value == u16(256) && r.rest.next == u32(3) && r.rest.end == u32(3) | .Err(e) => false
    assert(reader_check_24)
    assert(word_state.next == u32(1) && word_state.end == u32(3))
    assert(word_storage[0] == u8(91) && word_storage[1] == u8(1) && word_storage[2] == u8(0) && word_storage[3] == u8(92))
  }

  // Direct BE16 golden 0xffff: preserve the input and narrower window.
  true ? {
    word_storage: [4]u8 = [4]u8{ u8(91), u8(255), u8(255), u8(92) }
    word_src: []u8 = view(&word_storage)
    word_state: reader.Window = reader.Window { next: u32(1), end: u32(3) }
    reader_check_25: Bool = reader.read_u16_be(word_state, word_src) ? | .Ok(r) => r.value == u16(65535) && r.rest.next == u32(3) && r.rest.end == u32(3) | .Err(e) => false
    assert(reader_check_25)
    assert(word_state.next == u32(1) && word_state.end == u32(3))
    assert(word_storage[0] == u8(91) && word_storage[1] == u8(255) && word_storage[2] == u8(255) && word_storage[3] == u8(92))
  }

  empty: []u8 = src[u32(0):u32(0)]
  zero: reader.Window = reader.Window { next: u32(0), end: u32(0) }
  reader_check_26: Bool = reader.window(empty, u32(0), u32(0)) ? | .Ok(w) => w.next == u32(0) && w.end == u32(0) | .Err(e) => false
  assert(reader_check_26)
  reader_check_27: Bool = reader.take(zero, empty, u32(0)) ? | .Ok(r) => r.offset == u32(0) && r.length == u32(0) && r.rest.next == u32(0) | .Err(e) => false
  assert(reader_check_27)
  reader_check_28: Bool = reader.read_u8(zero, empty) ? | .Ok(r) => false | .Err(e) => reader_error(e) == u32(2)
  assert(reader_check_28)
  reader_check_29: Bool = reader.read_u16_be(zero, empty) ? | .Ok(r) => false | .Err(e) => reader_error(e) == u32(2)
  assert(reader_check_29)
  reader_check_30: Bool = reader.remaining(original, empty) ? | .Ok(n) => false | .Err(e) => reader_error(e) == u32(1)
  assert(reader_check_30)
  assert(storage[0] == u8(17) && storage[1] == u8(34) && storage[2] == u8(51) && storage[3] == u8(68))
  42
}
`

func TestE2EStdlibBoundedReader(t *testing.T) {
	runBoundedReaderAPDUProgram(t, "bounded-reader", boundedReaderProgram)
}

const apduAssertions = `
case_number: (form: apdu.CommandCase): u32 = form ?
  | .Case1 => u32(1)
  | .Case2Short => u32(2)
  | .Case3Short => u32(3)
  | .Case4Short => u32(4)
  | .Case2Extended => u32(5)
  | .Case3Extended => u32(6)
  | .Case4Extended => u32(7)
error_number: (reason: apdu.Error): u32 = reason ?
  | .TooLong => u32(1)
  | .TruncatedHeader => u32(2)
  | .TruncatedLength => u32(3)
  | .ZeroDataLength => u32(4)
  | .TruncatedData => u32(5)
  | .TrailingBytes => u32(6)
expect_command: (src: []u8, form: u32, at: u32, count: u32, response: u32): Bool = apdu.decode(src) ?
  | .Err(e) => false
  | .Ok(command) => {
    response_matches: Bool = command.response_length ?
      | .None => response == u32(0)
      | .Some(n) => n > u32(0) && n == response
    case_number(command.form) == form && command.cla == src[0] && command.ins == src[1] &&
      command.p1 == src[2] && command.p2 == src[3] && command.data_at == at &&
      command.data_length == count && response_matches && command.consumed == len(src) &&
      bytes.range_fits(len(src), command.data_at, command.data_length)
  }
expect_error: (src: []u8, reason: u32): Bool = apdu.decode(src) ?
  | .Ok(command) => false
  | .Err(e) => error_number(e) == reason
`

type commandAPDUFixture struct {
	name                  string
	wire                  []byte
	form, at, count, want uint32
	err                   uint32
}

// Construct the positive corpus directly from each grammar production. This
// does not run a second procedural decoder that could mirror the same bug.
func commandAPDUSmallFixtures() []commandAPDUFixture {
	header := []byte{0xe1, 0xf2, 0xc3, 0xd4} // Raw bytes, not a permitted command.
	frame := func(parts ...[]byte) []byte {
		out := append([]byte(nil), header...)
		for _, part := range parts {
			out = append(out, part...)
		}
		return out
	}
	cases := []commandAPDUFixture{{name: "case1", wire: frame(), form: 1, at: 4}}
	for _, le := range []byte{0, 1, 255} {
		want := uint32(le)
		if le == 0 {
			want = 256
		}
		cases = append(cases, commandAPDUFixture{name: fmt.Sprintf("case2s-%d", le), wire: frame([]byte{le}), form: 2, at: 5, want: want})
	}
	for _, nc := range []int{1, 2, 254, 255} {
		data := bytes.Repeat([]byte{0xa5}, nc)
		cases = append(cases, commandAPDUFixture{name: fmt.Sprintf("case3s-%d", nc), wire: frame([]byte{byte(nc)}, data), form: 3, at: 5, count: uint32(nc)})
		for _, le := range []byte{0, 1, 255} {
			want := uint32(le)
			if le == 0 {
				want = 256
			}
			cases = append(cases, commandAPDUFixture{name: fmt.Sprintf("case4s-%d-%d", nc, le), wire: frame([]byte{byte(nc)}, data, []byte{le}), form: 4, at: 5, count: uint32(nc), want: want})
		}
	}
	for _, le := range []uint32{0, 1, 255, 256, 65535} {
		want := le
		if le == 0 {
			want = 65536
		}
		cases = append(cases, commandAPDUFixture{name: fmt.Sprintf("case2e-%d", le), wire: frame([]byte{0, byte(le >> 8), byte(le)}), form: 5, at: 7, want: want})
	}
	for _, nc := range []int{1, 255, 256} {
		data := bytes.Repeat([]byte{0xa5}, nc)
		lc := []byte{0, byte(nc >> 8), byte(nc)}
		cases = append(cases, commandAPDUFixture{name: fmt.Sprintf("case3e-%d", nc), wire: frame(lc, data), form: 6, at: 7, count: uint32(nc)})
		for _, le := range []uint32{0, 1, 255, 256, 65535} {
			want := le
			if le == 0 {
				want = 65536
			}
			cases = append(cases, commandAPDUFixture{name: fmt.Sprintf("case4e-%d-%d", nc, le), wire: frame(lc, data, []byte{byte(le >> 8), byte(le)}), form: 7, at: 7, count: uint32(nc), want: want})
		}
	}
	for n := 0; n < 4; n++ {
		cases = append(cases, commandAPDUFixture{name: fmt.Sprintf("header-%d", n), wire: append([]byte(nil), header[:n]...), err: 2})
	}
	cases = append(cases,
		commandAPDUFixture{name: "extended-length-one-byte", wire: frame([]byte{0, 1}), err: 3},
		commandAPDUFixture{name: "short-data-deficit", wire: frame([]byte{2, 0xa5}), err: 5},
		commandAPDUFixture{name: "short-lc-two-byte-le", wire: frame([]byte{1, 0xa5, 0, 1}), err: 6},
		commandAPDUFixture{name: "extended-zero-lc", wire: frame([]byte{0, 0, 0, 0xa5}), err: 4},
		commandAPDUFixture{name: "extended-data-deficit", wire: frame([]byte{0, 0, 2, 0xa5}), err: 5},
		commandAPDUFixture{name: "extended-lc-one-byte-le", wire: frame([]byte{0, 0, 1, 0xa5, 0}), err: 3},
		commandAPDUFixture{name: "extended-lc-three-byte-le", wire: frame([]byte{0, 0, 1, 0xa5, 0, 0, 1}), err: 6},
	)
	return cases
}

func commandAPDUFixtureProgram(cases []commandAPDUFixture) string {
	var src strings.Builder
	src.WriteString("package main\nimport(\"smartcard/apdu\")\nimport(\"bytes\")\n")
	src.WriteString(apduAssertions)
	src.WriteString("main: (): i32 {\n")
	for _, c := range cases {
		fmt.Fprintf(&src, "// %s\ntrue ? {\nwire: [%d]u8\nwire[0] = u8(91)\nwire[%d] = u8(92)\n", c.name, len(c.wire)+2, len(c.wire)+1)
		for i, value := range c.wire {
			fmt.Fprintf(&src, "wire[%d] = u8(%d)\n", i+1, value)
		}
		fmt.Fprintf(&src, "before: [%d]u8 = wire\nwhole: []u8 = view(&wire)\nframe: []u8 = whole[u32(1):u32(%d)]\n", len(c.wire)+2, len(c.wire)+1)
		if c.err != 0 {
			fmt.Fprintf(&src, "assert(expect_error(frame, u32(%d)))\n", c.err)
		} else {
			fmt.Fprintf(&src, "assert(expect_command(frame, u32(%d), u32(%d), u32(%d), u32(%d)))\n", c.form, c.at, c.count, c.want)
		}
		fmt.Fprintf(&src, "i: u32 = 0\nwhile i < u32(%d) { assert(wire[i] == before[i])\ni = i + u32(1) }\n}\n", len(c.wire)+2)
	}
	src.WriteString("42\n}\n")
	return src.String()
}

func TestE2EStdlibCommandAPDUMatrix(t *testing.T) {
	cases := commandAPDUSmallFixtures()
	if len(cases) != 54 {
		t.Fatalf("exact small fixture inventory: got %d, want 54", len(cases))
	}
	runBoundedReaderAPDUProgram(t, "apdu-matrix", commandAPDUFixtureProgram(cases))
}

func TestE2EStdlibCommandAPDUMaximumAndPayloads(t *testing.T) {
	var src strings.Builder
	src.WriteString("package main\nimport(\"smartcard/apdu\")\nimport(\"bytes\")\n")
	src.WriteString(apduAssertions)
	src.WriteString(`main: (): i32 {
  wire: [65547]u8
  wire[0] = u8(91)
  wire[65546] = u8(92)
  i: u32 = 1
  while i < u32(65546) { wire[i] = u8(165)
    i = i + u32(1)
  }
  wire[1] = u8(225)
  wire[2] = u8(242)
  wire[3] = u8(195)
  wire[4] = u8(212)
  wire[5] = u8(0)
  wire[6] = u8(255)
  wire[7] = u8(255)
  true ? {
    whole: []u8 = view(&wire)
    assert(expect_command(whole[u32(1):u32(65543)], u32(6), u32(7), u32(65535), u32(0)))
  }
  wire[65543] = u8(255)
  wire[65544] = u8(255)
  true ? {
    whole: []u8 = view(&wire)
    assert(expect_command(whole[u32(1):u32(65545)], u32(7), u32(7), u32(65535), u32(65535)))
  }
  wire[65543] = u8(0)
  wire[65544] = u8(0)
  true ? {
    whole: []u8 = view(&wire)
    assert(expect_command(whole[u32(1):u32(65545)], u32(7), u32(7), u32(65535), u32(65536)))
    assert(expect_error(whole[u32(1):u32(65546)], u32(1)))
  }
  // Alter only payload, including bytes that resemble length markers. The
  // parser observes header/length/trailer fields and preserves these bytes.
  pass: u32 = 0
  while pass < u32(3) {
    i = u32(8)
    while i < u32(65543) {
      wire[i] = pass == u32(0) ? u8(0) | pass == u32(1) ? u8(255) | u8_trunc_u32(i % u32(2))
      i = i + u32(1)
    }
    true ? {
      whole: []u8 = view(&wire)
      assert(expect_command(whole[u32(1):u32(65545)], u32(7), u32(7), u32(65535), u32(65536)))
      assert(expect_command(whole[u32(1):u32(65545)], u32(7), u32(7), u32(65535), u32(65536)))
    }
    i = u32(8)
    while i < u32(65543) {
      expected: u8 = pass == u32(0) ? u8(0) | pass == u32(1) ? u8(255) | u8_trunc_u32(i % u32(2))
      assert(wire[i] == expected)
      i = i + u32(1)
    }
    assert(wire[0] == u8(91) && wire[65546] == u8(92))
    assert(wire[1] == u8(225) && wire[2] == u8(242) && wire[3] == u8(195) && wire[4] == u8(212))
    assert(wire[5] == u8(0) && wire[6] == u8(255) && wire[7] == u8(255))
    assert(wire[65543] == u8(0) && wire[65544] == u8(0) && wire[65545] == u8(165))
    pass = pass + u32(1)
  }
  42
}
`)
	runBoundedReaderAPDUProgram(t, "apdu-maximum", src.String())
}

func TestE2EStdlibCommandAPDUBufferNonMutation(t *testing.T) {
	source := "package main\nimport(\"smartcard/apdu\")\nimport(\"bytes\")\nimport(\"buffer\")\n" + apduAssertions + `
main: (): i32 {
  states: [1]buffer.Cursor
  cursor: [*]buffer.Cursor = span(&states)
  cursor[0] = buffer.Cursor { start: u32(1), end: u32(7) }
  storage: [8]u8 = [8]u8{ u8(91), u8(225), u8(242), u8(195), u8(212), u8(0), u8(1), u8(92) }
  before: [8]u8 = storage
  true ? {
    live: []u8 = buffer.peek(cursor, view(&storage))
    assert(expect_error(live, u32(3)))
    assert(expect_error(live, u32(3)))
  }
  assert(cursor[0].start == u32(1) && cursor[0].end == u32(7))
  i: u32 = 0
  while i < u32(8) { assert(storage[i] == before[i])
    i = i + u32(1)
  }
  // The caller supplies a different complete frame explicitly. Decoding a
  // five-byte prefix succeeds structurally but still commits no queue state.
  true ? {
    live: []u8 = buffer.peek(cursor, view(&storage))
    frame: []u8 = live[u32(0):u32(5)]
    assert(expect_command(frame, u32(2), u32(5), u32(0), u32(256)))
  }
  assert(cursor[0].start == u32(1) && cursor[0].end == u32(7))
  42
}
`
	runBoundedReaderAPDUProgram(t, "apdu-buffer", source)
}
