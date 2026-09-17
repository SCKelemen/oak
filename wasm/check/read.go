package check

import "fmt"

// reader is restricted to its section/body slice. Errors are sticky; no
// length is converted to int or used for allocation before checking bounds.
type reader struct {
	data      []byte
	pos, base int
	err       error
}

func (r *reader) fail(format string, args ...any) {
	if r.err == nil {
		r.err = fmt.Errorf("wasm check: byte %d: %s", r.base+r.pos, fmt.Sprintf(format, args...))
	}
}

func (r *reader) byte() byte {
	if r.err != nil {
		return 0
	}
	if r.pos == len(r.data) {
		r.fail("unexpected end of input")
		return 0
	}
	b := r.data[r.pos]
	r.pos++
	return b
}

func (r *reader) take(n uint32) []byte {
	if r.err != nil {
		return nil
	}
	if uint64(n) > uint64(len(r.data)-r.pos) {
		r.fail("length %d exceeds remaining bytes", n)
		return nil
	}
	b := r.data[r.pos : r.pos+int(n)]
	r.pos += int(n)
	return b
}

func (r *reader) sub(n uint32) reader {
	base := r.base + r.pos
	data := r.take(n)
	return reader{data: data, base: base, err: r.err}
}

func (r *reader) done() error {
	if r.pos != len(r.data) {
		r.fail("trailing bytes")
	}
	return r.err
}

// Wasm permits padded encodings within ceil(width/7) bytes, but the final
// byte's unused bits must be zero (unsigned) or sign extension (signed).
// Do not use Go's varint encoding: signed Wasm LEB is not zig-zag encoded.
func (r *reader) integer(width uint, signed bool) uint64 {
	var value uint64
	for shift := uint(0); shift < width && r.err == nil; shift += 7 {
		b := r.byte()
		payload := uint64(b & 0x7f)
		remaining := width - shift
		if remaining < 7 {
			mask := uint64(1)<<remaining - 1
			unused := uint64(0x7f) &^ mask
			want := uint64(0)
			if signed && payload&(uint64(1)<<(remaining-1)) != 0 {
				want = unused
			}
			if payload&unused != want {
				r.fail("invalid unused LEB bits for %d-bit integer", width)
				return 0
			}
		}
		value |= payload << shift
		if b&0x80 == 0 {
			if signed && b&0x40 != 0 && shift+7 < 64 {
				value |= ^uint64(0) << (shift + 7)
			}
			return value
		}
	}
	r.fail("unterminated or overlong %d-bit LEB", width)
	return 0
}

func (r *reader) u32() uint32 { return uint32(r.integer(32, false)) }

func (r *reader) count(max uint32) int {
	n := r.u32()
	if n > max {
		r.fail("count %d exceeds limit %d", n, max)
		return 0
	}
	return int(n)
}

func (r *reader) valueType() ValueType {
	switch r.byte() {
	case 0x7f:
		return I32
	case 0x7e:
		return I64
	default:
		r.fail("only i32/i64 value types are admitted")
		return ""
	}
}
