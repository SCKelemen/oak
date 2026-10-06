package compiler

import (
	"fmt"
	"math/rand"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/internal/lrat"
)

func lratKernelSource(t *testing.T) string {
	t.Helper()
	source, err := os.ReadFile(filepath.Join("..", "prove", "solver", "lrat.oak"))
	if err != nil {
		t.Fatal(err)
	}
	return string(source)
}

// This exercises the actual Oak checker with raw words and independently
// bounded scratch. The Go encoder and the allocating solver driver are not
// involved: they would filter out precisely the hostile inputs under test.
func TestLRATKernelRawWords(t *testing.T) {
	type testCase struct {
		name  string
		words []uint32
		out   uint32
		want  int // -1: rejection required; -2: acceptance must agree with Go
	}
	var cases []testCase
	add := func(name string, words []uint32, want int) {
		cases = append(cases, testCase{name, words, 3, want})
	}
	record := func(vars uint32, initial, steps []uint32, clauses uint32) []uint32 {
		words := []uint32{lrat.Magic, vars, clauses, uint32(len(initial)), uint32(len(steps)), 31, 128, 0}
		words = append(words, initial...)
		return append(words, steps...)
	}
	// (x) / (!x), followed by the empty-clause derivation.
	valid := record(1, []uint32{1, 1, 1, 0}, []uint32{0, 3, 0, 2, 1, 2}, 2)
	add("unit conflict", valid, 0)
	add("initial empty", record(0, []uint32{0}, nil, 1), 0)
	add("empty deleted after derivation", record(1, []uint32{1, 1, 1, 0}, []uint32{0, 3, 0, 2, 1, 2, 1, 3, 1, 3}, 2), 0)
	add("no empty", record(1, []uint32{1, 1}, nil, 1), -1)
	add("non-unit hint", record(2, []uint32{2, 1, 3}, []uint32{0, 2, 0, 1, 1}, 1), -1)
	add("missing hint", record(1, []uint32{1, 1, 1, 0}, []uint32{0, 3, 0, 1, 3}, 2), -1)
	add("suffix after conflict", record(1, []uint32{1, 1, 1, 0}, []uint32{0, 3, 0, 3, 1, 2, 1}, 2), -1)
	add("dead hint", record(1, []uint32{1, 1, 1, 0}, []uint32{1, 2, 1, 1, 0, 3, 0, 2, 1, 2}, 2), -1)
	add("duplicate unit literals", record(1, []uint32{2, 1, 1, 1, 0}, []uint32{0, 3, 0, 2, 1, 2}, 2), 0)
	add("tautology", record(1, []uint32{0}, []uint32{0, 2, 2, 1, 0, 0}, 1), 0)
	add("tautology invalid suffix", record(1, []uint32{0}, []uint32{0, 2, 3, 1, 0, 2, 0}, 1), -1)
	add("trailing word", append(append([]uint32(nil), valid...), 42), -1)
	for n := 0; n < len(valid); n++ {
		add(fmt.Sprintf("truncated/%d", n), append([]uint32(nil), valid[:n]...), -1)
	}
	for _, field := range []int{3, 4, 8, 14, 15} {
		for _, count := range []uint32{0xfffffff0, 0xfffffff8, 0xfffffffc, 0xfffffffe, 0xffffffff} {
			words := append([]uint32(nil), valid...)
			words[field] = count
			add(fmt.Sprintf("overflow/%d/%x", field, count), words, -1)
		}
	}
	add("deletion count wraps", record(0, []uint32{0}, []uint32{1, 1, 0xfffffff8}, 1), -1)
	add("addition literals wrap", record(0, []uint32{0}, []uint32{0, 2, 0xfffffff8, 0}, 1), -1)
	add("hint count wraps", record(0, []uint32{0}, []uint32{0, 2, 0, 0xfffffff8}, 1), -1)
	for _, field := range []int{1, 2, 5, 6} {
		words := append([]uint32(nil), valid...)
		words[field] = 0xffffffff
		add(fmt.Sprintf("scratch capacity/%d", field), words, -1)
	}
	for n := uint32(0); n < 3; n++ {
		cases = append(cases, testCase{fmt.Sprintf("short output/%d", n), valid, n, 7})
	}
	// Deterministic mutation checks against the independent Go acceptance
	// kernel. Keep scratch metadata valid: Go does not use those hints.
	rng := rand.New(rand.NewSource(20261006))
	for i := 0; i < 512; i++ {
		words := append([]uint32(nil), valid...)
		index := []int{0, 2, 3, 4, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17}[rng.Intn(14)]
		words[index] = uint32(rng.Intn(24))
		add(fmt.Sprintf("mutation/%d", i), words, -2)
	}
	var data, offsets, sizes, outs []uint32
	for _, tc := range cases {
		offsets = append(offsets, uint32(len(data)))
		sizes = append(sizes, uint32(len(tc.words)))
		outs = append(outs, tc.out)
		data = append(data, tc.words...)
	}
	source := `import(std)
putchar: (ch: c.Int): c.Int = c.extern("putchar")
` + lratKernelSource(t) + `
check_case: (words: []u32, out_n: u32): u32 {
  starts: [32]u32
  lengths: [32]u32
  alive: [32]u8
  store: [128]u32
  assign: [8]u8
  trail: [8]u32
  out: [4]u32 = [4]u32{99, 99, 99, 99}
  status: u32 = 0
  true ? {
    dest: [*]u32 = span(&out)
    status = lrat_check(words, span(&starts), span(&lengths), span(&alive), span(&store), span(&assign), span(&trail), dest[0:out_n])
  } | { }
  assert(out[3] == 99)
  out_n < 3 ? { assert(out[0] == 99 && out[1] == 99 && out[2] == 99) } | { assert(out[0] == status) }
  status
}
main: (): i32 {
` + fmt.Sprintf("data: [%d]u32 = %s\noffsets: [%d]u32 = %s\nsizes: [%d]u32 = %s\nouts: [%d]u32 = %s\n", len(data), oakU32Array(data), len(offsets), oakU32Array(offsets), len(sizes), oakU32Array(sizes), len(outs), oakU32Array(outs)) + `
  all: []u32 = view(&data)
  i: u32 = 0
  while i < len(offsets) {
    status: u32 = check_case(subslice(all, offsets[i], sizes[i]), outs[i])
    _ = putchar(c.Int(i32_bits_u32(status + 65)))
    i = i + 1
  }
  0
}
`
	output, code, abnormal := buildAndRunOutput(t, "lrat_kernel", source)
	if abnormal || code != 0 || len(output) != len(cases) {
		t.Fatalf("raw kernel exit (%d, %v), %d/%d results: %q", code, abnormal, len(output), len(cases), output)
	}
	for i, tc := range cases {
		got := int(output[i]) - 65
		_, err := lrat.CheckWords(tc.words)
		switch {
		case tc.want >= 0 && got != tc.want:
			t.Errorf("%s: status %d, want %d", tc.name, got, tc.want)
		case tc.want == -1 && got == 0:
			t.Errorf("%s: malformed record accepted", tc.name)
		case tc.want == -2 && (got == 0) != (err == nil):
			t.Errorf("%s: Oak status %d, Go error %v; words %v", tc.name, got, err, tc.words)
		}
	}
	t.Logf("checked %d raw records, including short output spans", len(cases))
}

// Tie the proof to the production guard, not a handwritten equivalent.
func TestLRATKernelBoundsExtract(t *testing.T) {
	lratKernelExtract(t, "LRATBounds", []string{"lrat_fits", "lrat_alloc_fits"})
}

func TestLRATKernelRUPExtract(t *testing.T) {
	lratKernelExtract(t, "LRATRUP", []string{"lrat_rup"})
}

func TestLRATKernelCheckerExtract(t *testing.T) {
	lratKernelExtract(t, "LRATChecker", []string{"lrat_check"})
}

func lratKernelExtract(t *testing.T, module string, roots []string) {
	t.Helper()
	extracted, err := New().WithSource("lrat.oak", lratKernelSource(t)).EmitLeanRoots("Oak."+module, roots).Get()
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(extracted, "sorry") {
		t.Fatal("extraction contains sorry")
	}
	path := filepath.Join("..", "spec", "lean", "Oak", module+"Extracted.lean")
	if os.Getenv("OAK_LEAN_EXTRACT_UPDATE") == "1" {
		if err := os.WriteFile(path, []byte(extracted), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	committed, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	if string(committed) != extracted {
		t.Fatalf("%s extraction drift; regenerate with OAK_LEAN_EXTRACT_UPDATE=1", module)
	}
}
