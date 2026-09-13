package compiler

import (
	"fmt"
	"math"
	"math/rand"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// The bit-level binary32 operations of Oak.FloatOps (docs/spec/95-extraction.md
// section 3; the ml pilot's E4) against the host's binary32: add32, sub32,
// and mul32 must give the bits the hardware gives on edge operands and on
// random ones, so a theorem over them is a theorem about what the C and the
// interpreter compute. Needs the Lean toolchain and the spec/lean library.
func TestLeanFloatBitsAgreeWithHost(t *testing.T) {
	lake := findLake()
	if lake == "" {
		t.Skip("lake not found (PATH or ~/.elan/bin)")
	}
	root, err := filepath.Abs(filepath.Join("..", "spec", "lean"))
	if err != nil {
		t.Fatal(err)
	}
	edges := []float32{0, float32(math.Copysign(0, -1)), 1, -1, 2, 0.5, 3, 16777216, 16777217, 16777218, 1.5, 0.1,
		float32(math.Inf(1)), float32(math.Inf(-1)), math.MaxFloat32, -math.MaxFloat32,
		math.SmallestNonzeroFloat32, -math.SmallestNonzeroFloat32, 1.1754944e-38, 3.4e38, 1e-40, 2.5, 4.5, 1e-20, 1e20}
	rng := rand.New(rand.NewSource(0x0a4))
	var ops [][2]float32
	for _, a := range edges {
		for _, b := range edges {
			ops = append(ops, [2]float32{a, b})
		}
	}
	for i := 0; i < 400; i++ {
		ops = append(ops, [2]float32{math.Float32frombits(rng.Uint32()), math.Float32frombits(rng.Uint32())})
	}
	// The driver prints one result per line, in chunks of a hundred so no
	// do-block outgrows the elaborator's recursion depth.
	var driver, want strings.Builder
	driver.WriteString("import Oak.FloatOps\n\n")
	lines, parts := 0, 0
	line := func(op string, a, b uint32) {
		if lines%100 == 0 {
			parts++
			fmt.Fprintf(&driver, "def part%d : IO Unit := do\n", parts)
		}
		lines++
		fmt.Fprintf(&driver, "  IO.println (Oak.FloatOps.%s (Float32.ofBits (0x%08X : UInt32)) (Float32.ofBits (0x%08X : UInt32))).toBits\n", op, a, b)
	}
	canon := func(v float32) uint32 {
		if v != v {
			return 0x7FC00000 // the canonical quiet NaN the model yields
		}
		return math.Float32bits(v)
	}
	for _, p := range ops {
		a, b := p[0], p[1]
		ab, bb := math.Float32bits(a), math.Float32bits(b)
		line("add32", ab, bb)
		fmt.Fprintf(&want, "%d\n", canon(a+b))
		line("sub32", ab, bb)
		fmt.Fprintf(&want, "%d\n", canon(a-b))
		line("mul32", ab, bb)
		fmt.Fprintf(&want, "%d\n", canon(a*b))
	}
	driver.WriteString("\ndef main : IO Unit := do\n")
	for i := 1; i <= parts; i++ {
		fmt.Fprintf(&driver, "  part%d\n", i)
	}
	build := exec.Command(lake, "build", "Oak.FloatOps")
	build.Dir = root
	if out, err := build.CombinedOutput(); err != nil {
		t.Fatalf("lake build: %v\n%s", err, out)
	}
	path := filepath.Join(t.TempDir(), "floatbits.lean")
	if err := os.WriteFile(path, []byte(driver.String()), 0o644); err != nil {
		t.Fatal(err)
	}
	run := exec.Command(lake, "env", "lean", "--run", path)
	run.Dir = root
	out, err := run.CombinedOutput()
	if err != nil {
		t.Fatalf("lake env lean --run: %v\n%s", err, out)
	}
	got := strings.Split(strings.TrimRight(string(out), "\n"), "\n")
	wantLines := strings.Split(strings.TrimRight(want.String(), "\n"), "\n")
	if len(got) != len(wantLines) {
		t.Fatalf("%d lines from Lean, want %d\n%s", len(got), len(wantLines), out)
	}
	mismatches := 0
	for i := range wantLines {
		if got[i] != wantLines[i] {
			mismatches++
			if mismatches <= 10 {
				p := ops[i/3]
				t.Errorf("case %d (%v, %v) op %d: lean %s, host %s", i, p[0], p[1], i%3, got[i], wantLines[i])
			}
		}
	}
	if mismatches > 0 {
		t.Fatalf("%d of %d results differ from the host's binary32", mismatches, len(wantLines))
	}
}
