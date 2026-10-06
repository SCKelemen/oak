package asm

import (
	"encoding/binary"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// Concatenate fields in ISA significance order, independently of rvcForm's
// permutation of byte-offset bits into table operands.
func rv64ProofCompressedDisplacement(jump bool, word uint16) int64 {
	w := uint32(word)
	var half uint32
	var bits uint
	if jump {
		half = ((w>>12)&1)<<10 | ((w>>8)&1)<<9 | ((w>>9)&3)<<7 |
			((w>>6)&1)<<6 | ((w>>7)&1)<<5 | ((w>>2)&1)<<4 |
			((w>>11)&1)<<3 | ((w >> 3) & 7)
		bits = 11
	} else {
		half = ((w>>12)&1)<<7 | ((w>>5)&3)<<5 | ((w>>2)&1)<<4 |
			((w>>10)&3)<<2 | ((w >> 3) & 3)
		bits = 8
	}
	return (int64(half) << (64 - bits) >> (64 - bits)) * 2
}

func TestRV64CompressedBranchLeanEncodingsMatchTable(t *testing.T) {
	contents, err := os.ReadFile(filepath.Join("..", "spec", "lean", "Oak", "RiscVCompressedBranchEncoding.lean"))
	if err != nil {
		t.Fatal(err)
	}
	start := strings.Index(string(contents), "-- OAK-RV64-CONTROL-C-ENC-BEGIN")
	end := strings.Index(string(contents), "-- OAK-RV64-CONTROL-C-ENC-END")
	if start < 0 || end <= start {
		t.Fatal("missing compressed control encoding block")
	}
	var got, want []string
	for _, line := range strings.Split(string(contents)[start:end], "\n") {
		if strings.HasPrefix(line, "def ") {
			got = append(got, line)
		}
	}
	for _, name := range []string{"c.beqz", "c.bnez", "c.j"} {
		line := leanEncodingLine(*rv64Table[name])
		want = append(want, strings.Replace(line, "def "+name+" :", "def "+strings.ReplaceAll(name, ".", "")+" :", 1))
	}
	if strings.Join(got, "\n") != strings.Join(want, "\n") {
		t.Fatalf("compressed control rows drifted:\ngot %v\nwant %v", got, want)
	}
}

// All 6,144 combinations of representable offsets, compressed source
// registers, and control opcodes go through the production encoder.
func TestRV64CompressedBranchEncodingRoundTrip(t *testing.T) {
	for _, mnemonic := range []string{"beq", "bne", "jal"} {
		jump := mnemonic == "jal"
		limit, first, last, row := int64(256), 8, 15, "c.beqz"
		if mnemonic == "bne" {
			row = "c.bnez"
		}
		if jump {
			limit, first, last, row = 2048, 0, 0, "c.j"
		}
		for rs := first; rs <= last; rs++ {
			instr := rv64ProofBranch(mnemonic, rs, 0)
			labels := map[string]int64{"target": 0}
			for delta := -limit; delta < limit; delta += 2 {
				labels["target"] = limit + delta
				word, ok := rvcEncode(instr, limit, labels)
				if !ok || rv64ProofCompressedDisplacement(jump, word) != delta {
					t.Fatalf("%s x%d offset %d: %#04x, accepted=%v", mnemonic, rs, delta, word, ok)
				}
				enc := rv64Table[row]
				if uint32(word)&enc.Mask != enc.Value || (!jump && int(word>>7&7)+8 != rs) {
					t.Fatalf("%s x%d changed opcode/register: %#04x", mnemonic, rs, word)
				}
			}
		}
		// Every architectural register combination, including swapped zero
		// operands and link destinations, checks the compression admission rule.
		for a := 0; a < 32; a++ {
			for b := 0; b < 32; b++ {
				if jump && b != 0 {
					continue
				}
				want := a >= 8 && a <= 15 && b == 0
				if jump {
					want = a == 0
				}
				word, ok := rvcEncode(rv64ProofBranch(mnemonic, a, b), 0, map[string]int64{"target": 2})
				if ok != want || (!ok && word != 0) {
					t.Fatalf("%s x%d x%d: %#x accepted=%v want=%v", mnemonic, a, b, word, ok, want)
				}
			}
		}
	}
}

// Return Lean claims for bytes from the actual mixed-width function writer.
// The first branch initially sees +256 (too far). Shrinking the following
// jump makes it +254, so a second relaxation pass can compress that branch.
// Its final displacement is +252; backward references must also be updated.
func rv64CompressedLayoutClaims(t *testing.T) []string {
	t.Helper()
	branch := func(mnemonic string, a, b int, label string) Instruction {
		instr := rv64ProofBranch(mnemonic, a, b)
		instr.Operands[len(instr.Operands)-1] = Symbol{Name: label}
		return instr
	}
	reg := func(n int) Register { return Register{Class: ClassRV64X, Num: n, Lane: -1} }
	fn := &Function{Name: "cascade", Arch: ArchRV64, Compressed: true, Items: []Item{
		Label{Name: "start"}, branch("beq", 8, 0, "target"), branch("jal", 0, 0, "target"),
	}}
	for i := 0; i < 62; i++ {
		fn.Items = append(fn.Items, Instruction{Mnemonic: "mul", Operands: []Operand{reg(5), reg(6), reg(7)}})
	}
	fn.Items = append(fn.Items, Label{Name: "target"}, branch("bne", 15, 0, "start"),
		branch("jal", 0, 0, "start"), branch("jal", 1, 0, "start"),
		Instruction{Mnemonic: "addi", Operands: []Operand{reg(8), reg(8), Immediate{Value: 1}}})
	code, relocs, err := encodeRV64Function(fn)
	if err != nil || len(relocs) != 0 || len(code) != 262 {
		t.Fatalf("cascade layout: %d bytes, %v, %v", len(code), relocs, err)
	}
	var claims []string
	for _, tc := range []struct {
		pc, target int
		jump       bool
		model      string
	}{
		{0, 252, false, "encodeCB false 0 (BitVec.ofInt 8 126)"},
		{2, 252, true, "encodeCJ (BitVec.ofInt 11 125)"},
		{252, 0, false, "encodeCB true 7 (BitVec.ofInt 8 (-126))"},
		{254, 0, true, "encodeCJ (BitVec.ofInt 11 (-127))"},
	} {
		word := binary.LittleEndian.Uint16(code[tc.pc:])
		if word&3 == 3 || int64(tc.pc)+rv64ProofCompressedDisplacement(tc.jump, word) != int64(tc.target) {
			t.Fatalf("cascade at %d missed %d: %#x", tc.pc, tc.target, word)
		}
		claims = append(claims, fmt.Sprintf("example : wordBytes (%s) = [%d#8, %d#8] := by decide", tc.model, code[tc.pc], code[tc.pc+1]))
	}
	// Inspect the intervening instruction widths and the uncompressed link.
	for pc := 4; pc < 252; pc += 4 {
		if word := binary.LittleEndian.Uint32(code[pc:]); word&0xfe00707f != 0x02000033 {
			t.Fatalf("mul at %d: %#x", pc, word)
		}
	}
	link := binary.LittleEndian.Uint32(code[256:])
	if link&0xfff != 0x0ef || 256+rv64ProofDisplacement("jal", link) != 0 {
		t.Fatalf("RV64 link jump must remain JAL x1: %#x", link)
	}
	if tail := binary.LittleEndian.Uint16(code[260:]); tail != 0x0405 {
		t.Fatalf("compressed addi tail: %#x", tail)
	}
	return claims
}

func TestRV64CompressedBranchRelaxationCascade(t *testing.T) {
	rv64CompressedLayoutClaims(t)
}

func TestRV64CompressedBranchesMatchLean(t *testing.T) {
	const max = int64(^uint64(0) >> 1)
	const min = -max - 1
	var examples []string
	for _, mnemonic := range []string{"beq", "bne", "jal"} {
		limit := int64(256)
		regs := [][2]int{{0, 0}, {7, 0}, {8, 0}, {10, 0}, {15, 0}, {16, 0}, {31, 0}, {8, 1}, {15, 31}, {0, 8}}
		if mnemonic == "jal" {
			limit, regs = 2048, [][2]int{{0, 0}, {1, 0}, {31, 0}}
		}
		cases := []struct {
			pc, target int64
			fits       bool
		}{
			{0, 0, true}, {8192, 8200, true}, {8192, 8186, true}, {0, 2, true},
			{limit, 0, true}, {0, limit - 2, true}, {limit + 2, 0, false}, {0, limit, false},
			{0, 1, false}, {1, 0, false}, {1, 3, true},
			{max - 3, max - 1, true}, {min + 2, min, true},
			{min + 2, max - 1, false}, {max - 1, min + 2, false},
		}
		for _, tc := range cases {
			for _, rs := range regs {
				word, ok := rvcEncode(rv64ProofBranch(mnemonic, rs[0], rs[1]), tc.pc, map[string]int64{"target": tc.target})
				want := tc.fits && rs[0] >= 8 && rs[0] < 16 && rs[1] == 0
				call := fmt.Sprintf("localCB %v %d %d", mnemonic == "bne", rs[0], rs[1])
				if mnemonic == "jal" {
					want = tc.fits && rs[0] == 0
					call = fmt.Sprintf("localCJ %d", rs[0])
				}
				if ok != want || (!ok && word != 0) {
					t.Fatalf("%s x%d x%d pc=%d target=%d: %#x accepted=%v want=%v", mnemonic, rs[0], rs[1], tc.pc, tc.target, word, ok, want)
				}
				result := "none"
				if ok {
					result = fmt.Sprintf("some 0x%04x#16", word)
				}
				examples = append(examples, fmt.Sprintf("example : %s (%d : Int) (%d : Int) = %s := by decide", call, tc.pc, tc.target, result))
			}
		}
		a := 8
		if mnemonic == "jal" {
			a = 0
		}
		if word, ok := rvcEncode(rv64ProofBranch(mnemonic, a, 0), 0, nil); ok || word != 0 {
			t.Fatalf("%s compressed missing label: %#x", mnemonic, word)
		}
	}
	examples = append(examples, rv64CompressedLayoutClaims(t)...)
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_RV64_LEAN") != "" {
			t.Fatal("lake required for RV64 compressed production correspondence")
		}
		t.Skip("lake not on PATH; formal workflow requires this oracle")
	}
	source := "import Oak.RiscVCompressedBranchEncoding\nopen Oak.RiscVCompressedBranchEncoding\n" + strings.Join(examples, "\n") + "\n"
	path := filepath.Join(t.TempDir(), "RV64CompressedProductionPins.lean")
	if err := os.WriteFile(path, []byte(source), 0600); err != nil {
		t.Fatal(err)
	}
	buildLeanImports(t, lake, path)
	cmd := exec.Command(lake, "env", "lean", path)
	cmd.Dir = filepath.Join("..", "spec", "lean")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("RV64 compressed production correspondence: %v\n%s", err, out)
	}
}
