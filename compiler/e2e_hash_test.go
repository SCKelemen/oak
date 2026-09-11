package compiler

import (
	"crypto/sha256"
	"fmt"
	"hash/crc32"
	"math/rand"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

// runHashProgram compiles and runs a program importing a library package
// (library packages resolve through the module loader, so the program is
// a module root), then interprets the same checked program — or, when a
// second source is given, that variant (for programs whose compiled form
// uses compile-time-only builtins).
func runHashProgram(t *testing.T, name, src string, interpreted ...string) {
	t.Helper()
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/" + name + "\noak 0.1.0\n",
		"main.oak": "package main\n" + src,
	})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("compiled hash program exited (%d, abnormal=%v)", code, abnormal)
	}
	if len(interpreted) > 0 {
		root = writeModule(t, map[string]string{
			"oak.mod":  "module example.com/" + name + "\noak 0.1.0\n",
			"main.oak": "package main\n" + interpreted[0],
		})
	}
	model, err := New().WithPackageDir(root).Check().Get()
	if err != nil {
		t.Fatalf("check failed: %v", err)
	}
	env := object.NewEnvironment()
	env.SetArithmeticWidths(model.TypeChecker.ArithmeticType)
	if result := evaluator.Eval(model.Tree.Root, env); result != nil {
		if e, isErr := result.(*object.Error); isErr {
			t.Fatalf("interpreter error evaluating program: %s", e.Message)
		}
	}
	call := parser.New(layout.New(scanner.New("main()"))).ParseProgram()
	result := evaluator.Eval(call, env)
	if e, isErr := result.(*object.Error); isErr {
		t.Fatalf("interpreter error in main(): %s", e.Message)
	}
	integer, ok := result.(*object.Integer)
	if !ok || integer.Value != 42 {
		t.Fatalf("interpreter returned %s", result.Inspect())
	}
}

// The hash package (stdlib/hash.oak): SHA-256 and CRC-32C written in Oak,
// checked against the standards' known-answer vectors and, over random
// inputs of every length class around the block size, against Go's
// crypto/sha256 and hash/crc32 (Castagnoli). The same program runs compiled
// and interpreted and must agree with both.
func hashProgram(cases []hashCase) string {
	var src strings.Builder
	src.WriteString("import(\"hash\")\n")
	src.WriteString(`
same32: (digest: []u8, expected: []u8): Bool {
  ok: Bool = len(digest) == u32(32) && len(expected) == u32(32)
  i: u32 = 0
  while ok && i < u32(32) {
    ok = digest[i] == expected[i]
    i = i + u32(1)
  }
  ok
}
`)
	for i, c := range cases {
		fmt.Fprintf(&src, "case_%d: (): Bool {\n", i)
		writeBytes(&src, "input", c.input)
		writeBytes(&src, "want", c.sha[:])
		src.WriteString(`  digest: [32]u8
  ok: Bool = hash.sha256(input, span(&digest))
  ok = ok && same32(view(&digest), want)
`)
		// Incremental: split at a byte position that straddles blocks.
		split := len(c.input) / 3
		fmt.Fprintf(&src, "  st: hash.Sha256State = hash.sha256_init()\n  st = hash.sha256_update(st, subslice(input, u32(0), u32(%d)))\n  st = hash.sha256_update(st, subslice(input, u32(%d), u32(%d)))\n", split, split, len(c.input)-split)
		src.WriteString(`  chunked: [32]u8
  ok = ok && hash.sha256_final(st, span(&chunked))
  ok = ok && same32(view(&chunked), want)
`)
		fmt.Fprintf(&src, "  ok = ok && hash.crc32c(input) == u32(%d)\n", c.crc)
		fmt.Fprintf(&src, "  ok = ok && hash.crc32c_update(hash.crc32c(subslice(input, u32(0), u32(%d))), subslice(input, u32(%d), u32(%d))) == u32(%d)\n", split, split, len(c.input)-split, c.crc)
		src.WriteString("  ok\n}\n")
	}
	src.WriteString("main: (): i32 {\n")
	for i := range cases {
		fmt.Fprintf(&src, "  assert(case_%d())\n", i)
	}
	src.WriteString("  small: [16]u8\n  empty: [1]u8\n  empty_view: []u8 = view(&empty)\n  assert(!hash.sha256(subslice(empty_view, u32(0), u32(0)), span(&small)))\n  42\n}\n")
	return src.String()
}

type hashCase struct {
	input []byte
	sha   [32]byte
	crc   uint32
}

func writeBytes(src *strings.Builder, name string, data []byte) {
	capacity := len(data)
	if capacity == 0 {
		capacity = 1
	}
	fmt.Fprintf(src, "  %s_data: [%d]u8\n", name, capacity)
	for i, b := range data {
		fmt.Fprintf(src, "  %s_data[%d] = u8(%d)\n", name, i, b)
	}
	fmt.Fprintf(src, "  %s_view: []u8 = view(&%s_data)\n", name, name)
	fmt.Fprintf(src, "  %s: []u8 = subslice(%s_view, u32(0), u32(%d))\n", name, name, len(data))
}

func hashCases(inputs [][]byte) []hashCase {
	castagnoli := crc32.MakeTable(crc32.Castagnoli)
	cases := make([]hashCase, 0, len(inputs))
	for _, input := range inputs {
		cases = append(cases, hashCase{input: input, sha: sha256.Sum256(input), crc: crc32.Checksum(input, castagnoli)})
	}
	return cases
}

func TestE2EHashKnownAnswers(t *testing.T) {
	// FIPS 180-4 / NIST examples and the RFC 3720 CRC-32C check value.
	cases := hashCases([][]byte{
		[]byte(""),
		[]byte("abc"),
		[]byte("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"),
		[]byte("123456789"),
	})
	if fmt.Sprintf("%x", cases[1].sha) != "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" {
		t.Fatal("reference digest mismatch")
	}
	if cases[3].crc != 0xE3069283 {
		t.Fatalf("reference CRC-32C check value mismatch: %08x", cases[3].crc)
	}
	runHashProgram(t, "hashknown", hashProgram(cases))
}

// Random inputs at every length class around the 64-byte block and the
// 56-byte padding boundary, compared with Go's implementations in both
// realizations.
func TestE2EHashDifferential(t *testing.T) {
	random := rand.New(rand.NewSource(0x5ea))
	var inputs [][]byte
	for _, n := range []int{1, 31, 55, 56, 57, 63, 64, 65, 119, 120, 128, 200} {
		data := make([]byte, n)
		random.Read(data)
		inputs = append(inputs, data)
	}
	runHashProgram(t, "hashdiff", hashProgram(hashCases(inputs)))
}

// A compact BLAKE3 reference (hash mode, 32-byte output) written from the
// specification independently of the Oak source, plus the official
// test-vector anchors for the empty input and the one-byte input.
func blake3Reference(input []byte) [32]byte {
	iv := [8]uint32{0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19}
	const chunkStart, chunkEnd, parent, root = 1, 2, 4, 8
	rotr := func(x uint32, n uint) uint32 { return x>>n | x<<(32-n) }
	g := func(v *[16]uint32, a, b, c, d int, mx, my uint32) {
		v[a] = v[a] + v[b] + mx
		v[d] = rotr(v[d]^v[a], 16)
		v[c] = v[c] + v[d]
		v[b] = rotr(v[b]^v[c], 12)
		v[a] = v[a] + v[b] + my
		v[d] = rotr(v[d]^v[a], 8)
		v[c] = v[c] + v[d]
		v[b] = rotr(v[b]^v[c], 7)
	}
	perm := [16]int{2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8}
	compress := func(cv [8]uint32, block [16]uint32, counter uint64, blockLen uint32, flags uint32) [16]uint32 {
		v := [16]uint32{cv[0], cv[1], cv[2], cv[3], cv[4], cv[5], cv[6], cv[7], iv[0], iv[1], iv[2], iv[3], uint32(counter), uint32(counter >> 32), blockLen, flags}
		m := block
		for r := 0; r < 7; r++ {
			g(&v, 0, 4, 8, 12, m[0], m[1])
			g(&v, 1, 5, 9, 13, m[2], m[3])
			g(&v, 2, 6, 10, 14, m[4], m[5])
			g(&v, 3, 7, 11, 15, m[6], m[7])
			g(&v, 0, 5, 10, 15, m[8], m[9])
			g(&v, 1, 6, 11, 12, m[10], m[11])
			g(&v, 2, 7, 8, 13, m[12], m[13])
			g(&v, 3, 4, 9, 14, m[14], m[15])
			if r < 6 {
				var next [16]uint32
				for i := range perm {
					next[i] = m[perm[i]]
				}
				m = next
			}
		}
		for i := 0; i < 8; i++ {
			v[i] ^= v[i+8]
			v[i+8] ^= cv[i]
		}
		return v
	}
	words := func(block []byte) [16]uint32 {
		var m [16]uint32
		for i := 0; i < 16; i++ {
			m[i] = uint32(block[4*i]) | uint32(block[4*i+1])<<8 | uint32(block[4*i+2])<<16 | uint32(block[4*i+3])<<24
		}
		return m
	}
	first8 := func(v [16]uint32) [8]uint32 { var cv [8]uint32; copy(cv[:], v[:8]); return cv }
	// Chunk chaining values, then the tree.
	type output struct {
		cv       [8]uint32
		block    [16]uint32
		counter  uint64
		blockLen uint32
		flags    uint32
	}
	chunkOutput := func(chunk []byte, counter uint64) output {
		cv := iv
		blocks := 0
		for len(chunk) > 64 {
			flags := uint32(0)
			if blocks == 0 {
				flags = chunkStart
			}
			cv = first8(compress(cv, words(chunk[:64]), counter, 64, flags))
			chunk = chunk[64:]
			blocks++
		}
		var last [64]byte
		copy(last[:], chunk)
		flags := uint32(chunkEnd)
		if blocks == 0 {
			flags |= chunkStart
		}
		return output{cv, words(last[:]), counter, uint32(len(chunk)), flags}
	}
	parentOutput := func(left, right [8]uint32) output {
		var block [16]uint32
		copy(block[:8], left[:])
		copy(block[8:], right[:])
		return output{iv, block, 0, 64, parent}
	}
	chainingValue := func(o output) [8]uint32 { return first8(compress(o.cv, o.block, o.counter, o.blockLen, o.flags)) }
	var stack [][8]uint32
	var counter uint64
	rest := input
	for len(rest) > 1024 {
		cv := chainingValue(chunkOutput(rest[:1024], counter))
		rest = rest[1024:]
		counter++
		total := counter
		for total&1 == 0 && len(stack) > 0 {
			cv = chainingValue(parentOutput(stack[len(stack)-1], cv))
			stack = stack[:len(stack)-1]
			total >>= 1
		}
		stack = append(stack, cv)
	}
	out := chunkOutput(rest, counter)
	for len(stack) > 0 {
		out = parentOutput(stack[len(stack)-1], chainingValue(out))
		stack = stack[:len(stack)-1]
	}
	rootWords := compress(out.cv, out.block, out.counter, out.blockLen, out.flags|root)
	var digest [32]byte
	for i := 0; i < 8; i++ {
		digest[4*i] = byte(rootWords[i])
		digest[4*i+1] = byte(rootWords[i] >> 8)
		digest[4*i+2] = byte(rootWords[i] >> 16)
		digest[4*i+3] = byte(rootWords[i] >> 24)
	}
	return digest
}

func blake3Program(inputs [][]byte) string {
	var src strings.Builder
	src.WriteString("import(\"hash\")\n")
	src.WriteString(`
same32: (digest: []u8, expected: []u8): Bool {
  ok: Bool = len(digest) == u32(32) && len(expected) == u32(32)
  i: u32 = 0
  while ok && i < u32(32) {
    ok = digest[i] == expected[i]
    i = i + u32(1)
  }
  ok
}
`)
	for i, input := range inputs {
		want := blake3Reference(input)
		fmt.Fprintf(&src, "case_%d: (): Bool {\n", i)
		writeBytes(&src, "input", input)
		writeBytes(&src, "want", want[:])
		src.WriteString("  digest: [32]u8\n  ok: Bool = hash.blake3(input, span(&digest))\n  ok = ok && same32(view(&digest), want)\n")
		split := len(input) * 2 / 3
		fmt.Fprintf(&src, "  st: hash.Blake3State = hash.blake3_init()\n  st = hash.blake3_update(st, subslice(input, u32(0), u32(%d)))\n  st = hash.blake3_update(st, subslice(input, u32(%d), u32(%d)))\n", split, split, len(input)-split)
		src.WriteString("  chunked: [32]u8\n  ok = ok && hash.blake3_final(st, span(&chunked))\n  ok = ok && same32(view(&chunked), want)\n  ok\n}\n")
	}
	src.WriteString("main: (): i32 {\n")
	for i := range inputs {
		fmt.Fprintf(&src, "  assert(case_%d())\n", i)
	}
	src.WriteString("  42\n}\n")
	return src.String()
}

// The official BLAKE3 test vectors anchor the reference: the empty input,
// and the one-byte input of the specification's byte pattern.
func TestBlake3ReferenceAnchors(t *testing.T) {
	if got := fmt.Sprintf("%x", blake3Reference(nil)); got != "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262" {
		t.Fatalf("empty input: %s", got)
	}
	if got := fmt.Sprintf("%x", blake3Reference([]byte{0})); got != "2d3adedff11b61f14c886e35afa036736dcd87a74d27b5c1510225d0f592e213" {
		t.Fatalf("one byte: %s", got)
	}
}

// BLAKE3 in Oak against the reference at every tree shape that matters:
// partial and full blocks, one chunk, the first parent, an odd number of
// chunks, a full power-of-two tree, and the specification's byte pattern.
func TestE2EHashBlake3(t *testing.T) {
	pattern := func(n int) []byte {
		data := make([]byte, n)
		for i := range data {
			data[i] = byte(i % 251)
		}
		return data
	}
	random := rand.New(rand.NewSource(0xb1a3e3))
	randomBytes := func(n int) []byte {
		data := make([]byte, n)
		random.Read(data)
		return data
	}
	inputs := [][]byte{
		{}, {0}, pattern(63), pattern(64), pattern(65), pattern(1023), pattern(1024), pattern(1025),
		pattern(2048), pattern(2049), pattern(3072), randomBytes(4096), randomBytes(5000),
	}
	runHashProgram(t, "hashblake3", blake3Program(inputs))
}
