package main

import "strconv"

// The corpus generators, byte for byte the twins of the static functions in
// ../runner.h. A change on one side must be mirrored on the other; the
// driver compares the Oak and Go preflight checksums and refuses to time a
// workload whose corpora or results have drifted apart.

type splitMix struct{ state uint64 }

func (s *splitMix) next() uint64 {
	s.state += 0x9e3779b97f4a7c15
	z := s.state
	z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9
	z = (z ^ (z >> 27)) * 0x94d049bb133111eb
	return z ^ (z >> 31)
}

const (
	fnvOffset = 14695981039346656037
	fnvPrime  = 1099511628211
)

func fnvBytes(data []byte) uint64 {
	acc := uint64(fnvOffset)
	for _, b := range data {
		acc = (acc ^ uint64(b)) * fnvPrime
	}
	return acc
}

func fnvU64(values []uint64) uint64 {
	acc := uint64(fnvOffset)
	for _, v := range values {
		acc = (acc ^ v) * fnvPrime
	}
	return acc
}

func fnvU32(values []uint32) uint64 {
	acc := uint64(fnvOffset)
	for _, v := range values {
		acc = (acc ^ uint64(v)) * fnvPrime
	}
	return acc
}

func scaled(scale float64, base int) int {
	n := int(float64(base) * scale)
	if n < 1 {
		return 1
	}
	return n
}

func fillBytes(count int, seed uint64) []byte {
	s := splitMix{seed}
	out := make([]byte, count)
	var word uint64
	for i := range out {
		if i%8 == 0 {
			word = s.next()
		}
		out[i] = byte(word >> ((i % 8) * 8))
	}
	return out
}

func fillU32(count int, seed uint64) []uint32 {
	s := splitMix{seed}
	out := make([]uint32, count)
	for i := range out {
		out[i] = uint32(s.next())
	}
	return out
}

func fillVarints(count int, seed uint64) []uint64 {
	s := splitMix{seed}
	out := make([]uint64, count)
	for i := range out {
		r := s.next()
		k := 1 + uint(r%10)
		v := s.next()
		if k == 10 {
			v |= 1 << 63
		} else {
			v >>= 64 - 7*k
		}
		out[i] = v
	}
	return out
}

const (
	unreserved = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-._~"
	reserved   = "!*'();:@&=+$,/?#[]%{}|^<>\"`\\"
)

func fillPercent(count int, seed uint64) []byte {
	s := splitMix{seed}
	out := make([]byte, count)
	for i := range out {
		r := s.next()
		switch {
		case r%10 < 7:
			out[i] = unreserved[(r>>8)%uint64(len(unreserved))]
		case (r>>4)%4 == 0:
			out[i] = byte(0x80 + (r>>16)%128)
		default:
			out[i] = reserved[(r>>16)%uint64(len(reserved))]
		}
	}
	return out
}

func fillUTF8(capacity int, seed uint64) []byte {
	s := splitMix{seed}
	out := make([]byte, 0, capacity)
	for {
		r := s.next()
		c, bits := r%100, r>>8
		var scalar uint32
		switch {
		case c < 60:
			scalar = uint32(bits % 128)
		case c < 85:
			scalar = uint32(0x80 + bits%(0x800-0x80))
		case c < 95:
			scalar = uint32(0x800 + bits%(0x10000-0x800))
			if scalar >= 0xD800 && scalar <= 0xDFFF {
				scalar -= 0x800
			}
		default:
			scalar = uint32(0x10000 + bits%(0x110000-0x10000))
		}
		width := 1
		switch {
		case scalar >= 0x10000:
			width = 4
		case scalar >= 0x800:
			width = 3
		case scalar >= 0x80:
			width = 2
		}
		if len(out)+width > capacity {
			return out
		}
		switch width {
		case 1:
			out = append(out, byte(scalar))
		case 2:
			out = append(out, byte(0xC0|(scalar>>6)), byte(0x80|(scalar&0x3F)))
		case 3:
			out = append(out, byte(0xE0|(scalar>>12)), byte(0x80|((scalar>>6)&0x3F)), byte(0x80|(scalar&0x3F)))
		default:
			out = append(out, byte(0xF0|(scalar>>18)), byte(0x80|((scalar>>12)&0x3F)), byte(0x80|((scalar>>6)&0x3F)), byte(0x80|(scalar&0x3F)))
		}
	}
}

func fillDecimals(count int, seed uint64) []uint64 {
	s := splitMix{seed}
	out := make([]uint64, count)
	for i := range out {
		r := s.next()
		k := 1 + uint(r%20)
		v := s.next()
		if k < 20 {
			limit := uint64(1)
			for j := uint(0); j < k; j++ {
				limit *= 10
			}
			v %= limit
		}
		out[i] = v
	}
	return out
}

func writeDecimals(values []uint64) []byte {
	out := make([]byte, 0, len(values)*21)
	for _, v := range values {
		out = strconv.AppendUint(out, v, 10)
		out = append(out, '\n')
	}
	return out
}

func fillInstants(count int, seed uint64) []int64 {
	s := splitMix{seed}
	out := make([]int64, count)
	for i := range out {
		nanos := int64(s.next()>>2) - (1 << 61)
		if nanos == 0 {
			nanos = 1
		}
		out[i] = nanos
	}
	return out
}
