package asm

import (
	"bytes"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// Exact production streams for the narrow Lean leaf theorem. This pins three
// concrete assembler outputs; it does not assert universal Go refinement,
// source provenance, or external Sail execution of the function.
func rv64BitwiseFunctionPins(t *testing.T) []string {
	t.Helper()
	reg := func(n int) Register { return Register{Class: ClassRV64X, Num: n, Lane: -1} }
	var pins []string
	for _, tc := range []struct {
		name   string
		middle byte
	}{{"and", 0x75}, {"or", 0x65}, {"xor", 0x45}} {
		fn := &Function{Name: "bitwise", Arch: ArchRV64, Compressed: false, Items: []Item{
			Instruction{Mnemonic: tc.name, Operands: []Operand{reg(10), reg(10), reg(11)}},
			Instruction{Mnemonic: "ret"},
		}}
		got, relocs, err := encodeRV64Function(fn)
		want := []byte{0x33, tc.middle, 0xb5, 0, 0x67, 0x80, 0, 0}
		if err != nil || len(relocs) != 0 || !bytes.Equal(got, want) {
			t.Fatalf("%s: bytes %x, relocations %v, error %v; want %x", tc.name, got, relocs, err, want)
		}
		parts := make([]string, len(got))
		for i, b := range got {
			parts[i] = fmt.Sprint(b)
		}
		pins = append(pins, fmt.Sprintf("example : functionBytes .%s = [%s] := by decide +kernel", tc.name, strings.Join(parts, ", ")))
		// ABI sign extension is important on values with bit 31 set. These are
		// bounded differential checks; the Lean theorem quantifies over all pairs.
		values := []uint32{0, 1, 0x7fffffff, 0x80000000, 0xffffffff, 0xaaaaaaaa, 0x55555555}
		for _, a := range values {
			for _, b := range values {
				x, y := uint64(int64(int32(a))), uint64(int64(int32(b)))
				var result uint64
				var expected uint32
				switch tc.name {
				case "and":
					result, expected = x&y, a&b
				case "or":
					result, expected = x|y, a|b
				case "xor":
					result, expected = x^y, a^b
				}
				if result != uint64(int64(int32(expected))) {
					t.Fatalf("%s ABI mismatch for %x, %x", tc.name, a, b)
				}
			}
		}
	}
	return pins
}
func TestRV64BitwiseFunctionBytes(t *testing.T) { rv64BitwiseFunctionPins(t) }
func TestRV64BitwiseFunctionMatchesLean(t *testing.T) {
	pins := rv64BitwiseFunctionPins(t)
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_RV64_LEAN") != "" {
			t.Fatal("lake required for RV64 bitwise function")
		}
		t.Skip("lake unavailable; formal CI requires this oracle")
	}
	path := filepath.Join(t.TempDir(), "RV64BitwiseFunctionPins.lean")
	source := "import Oak.RiscVBitwiseFunction\nopen Oak.RiscVBitwiseFunction\n" + strings.Join(pins, "\n") + "\n"
	if err := os.WriteFile(path, []byte(source), 0600); err != nil {
		t.Fatal(err)
	}
	buildLeanImports(t, lake, path)
	cmd := exec.Command(lake, "env", "lean", path)
	cmd.Dir = filepath.Join("..", "spec", "lean")
	if output, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("Lean production-byte pins: %v\n%s", err, output)
	}
}
