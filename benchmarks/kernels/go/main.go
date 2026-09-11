// The Go side of the kernel comparison (benchmarks/kernels/README.md): the
// same command line, data, and output as the Oak runner. "go-stdlib" uses
// the standard library, which is hardware-accelerated for SHA-256 and
// CRC-32C on this class of machine; "go-generic" is the straightforward
// pure-Go implementation of the same algorithm, the shape Oak's stdlib has.
package main

import (
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"hash/crc32"
	"math"
	"math/bits"
	"os"
	"sort"
	"strconv"
	"time"
)

var rng uint64 = 0x9E3779B97F4A7C15

func next() uint64 {
	rng ^= rng << 13
	rng ^= rng >> 7
	rng ^= rng << 17
	return rng
}

var k = [64]uint32{
	0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
	0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
	0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
	0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
	0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
	0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
	0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
	0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
}

// genericSHA256 is a plain one-shot SHA-256 in Go, no assembly, byte loop
// into a block, word-at-a-time schedule.
func genericSHA256(data []byte, out *[32]byte) {
	h := [8]uint32{0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19}
	var w [64]uint32
	compress := func(block []byte) {
		for i := 0; i < 16; i++ {
			w[i] = binary.BigEndian.Uint32(block[4*i:])
		}
		for i := 16; i < 64; i++ {
			s0 := bits.RotateLeft32(w[i-15], -7) ^ bits.RotateLeft32(w[i-15], -18) ^ (w[i-15] >> 3)
			s1 := bits.RotateLeft32(w[i-2], -17) ^ bits.RotateLeft32(w[i-2], -19) ^ (w[i-2] >> 10)
			w[i] = w[i-16] + s0 + w[i-7] + s1
		}
		a, b, c, d, e, f, g, hh := h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7]
		for i := 0; i < 64; i++ {
			s1 := bits.RotateLeft32(e, -6) ^ bits.RotateLeft32(e, -11) ^ bits.RotateLeft32(e, -25)
			ch := (e & f) ^ (^e & g)
			t1 := hh + s1 + ch + k[i] + w[i]
			s0 := bits.RotateLeft32(a, -2) ^ bits.RotateLeft32(a, -13) ^ bits.RotateLeft32(a, -22)
			maj := (a & b) ^ (a & c) ^ (b & c)
			t2 := s0 + maj
			hh, g, f, e, d, c, b, a = g, f, e, d+t1, c, b, a, t1+t2
		}
		h[0] += a
		h[1] += b
		h[2] += c
		h[3] += d
		h[4] += e
		h[5] += f
		h[6] += g
		h[7] += hh
	}
	n := len(data)
	i := 0
	for ; i+64 <= n; i += 64 {
		compress(data[i : i+64])
	}
	var tail [128]byte
	rest := copy(tail[:], data[i:])
	tail[rest] = 0x80
	padded := 64
	if rest+1 > 56 {
		padded = 128
	}
	binary.BigEndian.PutUint64(tail[padded-8:], uint64(n)*8)
	for j := 0; j < padded; j += 64 {
		compress(tail[j : j+64])
	}
	for j := 0; j < 8; j++ {
		binary.BigEndian.PutUint32(out[4*j:], h[j])
	}
}

var crcTable [256]uint32

func init() {
	for i := 0; i < 256; i++ {
		c := uint32(i)
		for b := 0; b < 8; b++ {
			if c&1 != 0 {
				c = (c >> 1) ^ 0x82f63b78
			} else {
				c >>= 1
			}
		}
		crcTable[i] = c
	}
}

// genericCRC32C is the byte-at-a-time table form.
func genericCRC32C(data []byte) uint32 {
	c := ^uint32(0)
	for _, b := range data {
		c = crcTable[byte(c)^b] ^ (c >> 8)
	}
	return ^c
}

func dot(a, b []float32) float32 {
	var total float32
	for i := range a {
		total += a[i] * b[i]
	}
	return total
}

func sum(v []uint64) uint64 {
	var total uint64
	for _, x := range v {
		total += x
	}
	return total
}

func search(keys, probes []uint64) uint32 {
	var hits uint32
	for _, target := range probes {
		lo, hi := 0, len(keys)
		for lo < hi {
			mid := lo + (hi-lo)/2
			if keys[mid] == target {
				hits++
				break
			} else if keys[mid] < target {
				lo = mid + 1
			} else {
				hi = mid
			}
		}
	}
	return hits
}

func main() {
	if len(os.Args) != 6 {
		fmt.Fprintln(os.Stderr, "usage: kernels IMPL KERNEL SIZE ROUNDS SAMPLES")
		os.Exit(2)
	}
	impl, kernel := os.Args[1], os.Args[2]
	size, _ := strconv.Atoi(os.Args[3])
	rounds, _ := strconv.Atoi(os.Args[4])
	samples, _ := strconv.Atoi(os.Args[5])
	bytesBuf := make([]byte, size)
	fa := make([]float32, size)
	fb := make([]float32, size)
	words := make([]uint64, size)
	probeCount := size / 16
	if probeCount == 0 {
		probeCount = 1
	}
	probes := make([]uint64, probeCount)
	for i := 0; i < size; i++ {
		r := next()
		bytesBuf[i] = byte(r)
		fa[i] = float32(r&0xFFFF) / 65536.0
		fb[i] = float32((r>>16)&0xFFFF) / 65536.0
		words[i] = uint64(i) * 3
	}
	for i := range probes {
		probes[i] = next() % (uint64(size)*3 + 3)
	}
	castagnoli := crc32.MakeTable(crc32.Castagnoli)
	var out [32]byte
	width := 4
	ns := make([]float64, samples)
	for s := 0; s < samples; s++ {
		start := time.Now()
		var sink uint64
		for r := 0; r < rounds; r++ {
			switch kernel {
			case "sha256":
				width = 32
				if impl == "go-stdlib" {
					out = sha256.Sum256(bytesBuf)
				} else {
					genericSHA256(bytesBuf, &out)
				}
				sink += uint64(out[0])
			case "crc32c":
				var c uint32
				if impl == "go-stdlib" {
					c = crc32.Checksum(bytesBuf, castagnoli)
				} else {
					c = genericCRC32C(bytesBuf)
				}
				binary.LittleEndian.PutUint32(out[:], c)
				sink += uint64(c)
			case "dot":
				d := dot(fa, fb)
				binary.LittleEndian.PutUint32(out[:], math.Float32bits(d))
				sink += uint64(out[0])
			case "sum":
				width = 8
				t := sum(words)
				binary.LittleEndian.PutUint64(out[:], t)
				sink += t
			case "search":
				h := search(words, probes)
				binary.LittleEndian.PutUint32(out[:], h)
				sink += uint64(h)
			default:
				fmt.Fprintln(os.Stderr, "unknown kernel", kernel)
				os.Exit(2)
			}
		}
		ns[s] = float64(time.Since(start).Nanoseconds()) / float64(rounds)
		if sink == math.MaxUint64 {
			fmt.Fprintln(os.Stderr, "sink")
		}
	}
	sort.Float64s(ns)
	fmt.Printf("{\"impl\":\"%s\",\"kernel\":\"%s\",\"size\":%d,\"checksum\":\"%s\",\"ns_per_op_median\":%.1f,\"samples\":[", impl, kernel, size, hex.EncodeToString(out[:width]), ns[samples/2])
	for i, v := range ns {
		if i > 0 {
			fmt.Print(",")
		}
		fmt.Printf("%.1f", v)
	}
	fmt.Println("]}")
}
