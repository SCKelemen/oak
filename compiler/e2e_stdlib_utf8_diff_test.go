package compiler

import (
	"fmt"
	"math/rand"
	"strings"
	"testing"
	"unicode/utf8"
)

// The table-driven UTF-8 validator and decoder against Go's unicode/utf8 on
// random inputs: well-formed text mixing every sequence width at every
// alignment modulo eight (the ASCII word fast path), and the same text with
// one damage applied — a truncated tail, an over-long lead (C0/C1), a
// surrogate (ED A0..BF), a value above U+10FFFF (F4 90.., F5..FF), a stray
// continuation byte, a lead byte followed by ASCII. For every input the Oak
// program must agree with Go on validity, on the number of scalars when
// valid, on the offset of the first ill-formed byte when not, and on every
// decoded scalar value and width along the way.
func TestE2EStdlibUtf8Differential(t *testing.T) {
	skipInShort(t)
	random := rand.New(rand.NewSource(0x0f8))
	scalar := func() rune {
		switch c := random.Intn(100); {
		case c < 45:
			return rune(random.Intn(0x80))
		case c < 70:
			return rune(0x80 + random.Intn(0x800-0x80))
		case c < 88:
			r := rune(0x800 + random.Intn(0x10000-0x800))
			if r >= 0xD800 && r <= 0xDFFF {
				r -= 0x800
			}
			return r
		default:
			return rune(0x10000 + random.Intn(0x110000-0x10000))
		}
	}
	valid := func(n int, asciiPrefix int) []byte {
		var b []byte
		for i := 0; i < asciiPrefix; i++ {
			b = append(b, byte(random.Intn(0x80)))
		}
		for len(b) < n {
			b = utf8.AppendRune(b, scalar())
		}
		return b
	}
	damage := func(b []byte, kind int) []byte {
		out := append([]byte(nil), b...)
		if len(out) == 0 {
			return []byte{0x80}
		}
		at := random.Intn(len(out))
		switch kind {
		case 0:
			return out[:len(out)-1] // truncated tail (harmless when the last scalar is ASCII)
		case 1:
			return append(out[:at:at], append([]byte{0xC0, 0x80}, out[at:]...)...)
		case 2:
			return append(out[:at:at], append([]byte{0xED, 0xA0, 0x80}, out[at:]...)...)
		case 3:
			return append(out[:at:at], append([]byte{0xF4, 0x90, 0x80, 0x80}, out[at:]...)...)
		case 4:
			return append(out[:at:at], append([]byte{0xF5, 0x80, 0x80, 0x80}, out[at:]...)...)
		case 5:
			return append(out[:at:at], append([]byte{0xBF}, out[at:]...)...)
		case 6:
			return append(out[:at:at], append([]byte{0xE2, 0x41}, out[at:]...)...)
		case 7:
			return append(out[:at:at], append([]byte{0xE0, 0x9F, 0xBF}, out[at:]...)...) // over-long three-byte form
		default:
			return append(out[:at:at], append([]byte{0xF0, 0x8F, 0xBF, 0xBF}, out[at:]...)...) // over-long four-byte form
		}
	}
	var inputs [][]byte
	for _, n := range []int{0, 1, 2, 3, 7, 8, 9, 15, 16, 17, 24, 31, 33, 64, 100, 257} {
		for prefix := 0; prefix < 9; prefix++ {
			inputs = append(inputs, valid(n, prefix))
		}
	}
	base := len(inputs)
	for i := 0; i < base; i++ {
		for kind := 0; kind < 9; kind++ {
			inputs = append(inputs, damage(inputs[i], kind))
		}
	}
	var src strings.Builder
	src.WriteString("import(std)\n")
	// walk: decode from the start; returns the scalar count in the low 32 bits
	// and the offset of the first ill-formed byte (or len) in the high 32 bits,
	// summing every scalar value into a checksum the caller compares.
	src.WriteString(`
Walk: type = struct { count: u32, stop: u32, sum: u64 }
walk: (src: []u8): Walk {
  at: u32 = 0
  count: u32 = 0
  sum: u64 = u64(0)
  failed: Bool = false
  while at < len(src) && !failed {
    decoded: Result[TextScalar, TextError] = utf8_decode(src, at)
    text_decode_ok(decoded) ? {
      item: TextScalar = text_decoded(decoded)
      sum = sum * u64(31) + u64(item.value) + u64(item.next - at)
      at = item.next
      count = count + u32(1)
    } | { failed = true }
  }
  Walk { count: count, stop: at, sum: sum }
}
`)
	for i, input := range inputs {
		count, stop, sum := uint32(0), uint32(0), uint64(0)
		for at := 0; at < len(input); {
			r, width := utf8.DecodeRune(input[at:])
			if r == utf8.RuneError && width == 1 {
				break
			}
			sum = sum*31 + uint64(r) + uint64(width)
			at += width
			count++
			stop = uint32(at)
		}
		fmt.Fprintf(&src, "case_%d: (): Bool {\n", i)
		writeBytes(&src, "input", input)
		fmt.Fprintf(&src, "  w: Walk = walk(input)\n")
		fmt.Fprintf(&src, "  ok: Bool = w.count == u32(%d) && w.stop == u32(%d) && w.sum == u64(%d)\n", count, stop, sum)
		firstError := uint32(len(input))
		if !utf8.Valid(input) {
			firstError = stop
		}
		fmt.Fprintf(&src, "  ok && utf8_validate(input) == %t && text_result_value(utf8_count(input)) == u32(%d) && utf8_first_error(input) == u32(%d)\n}\n", utf8.Valid(input), func() uint32 {
			if utf8.Valid(input) {
				return count
			}
			return 4294967295
		}(), firstError)
	}
	src.WriteString("main: (): i32 {\n")
	for i := range inputs {
		fmt.Fprintf(&src, "  assert(case_%d())\n", i)
	}
	src.WriteString("  42\n}\n")
	code, abnormal := buildAndRun(t, "utf8_differential", src.String())
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
