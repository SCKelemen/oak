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

// runHashProgram compiles and runs a program importing the hash library
// package (library packages resolve through the module loader, so the
// program is a module root), then interprets the same checked program.
func runHashProgram(t *testing.T, name, src string) {
	t.Helper()
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/" + name + "\noak 0.1.0\n",
		"main.oak": "package main\n" + src,
	})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("compiled hash program exited (%d, abnormal=%v)", code, abnormal)
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
