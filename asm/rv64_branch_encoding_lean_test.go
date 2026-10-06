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

var rv64BranchProofMnemonics = []string{"beq", "bne", "blt", "bge", "bltu", "bgeu", "jal"}

func rv64ProofBranch(mnemonic string, a, b int) Instruction {
	reg := func(n int) Register { return Register{Class: ClassRV64X, Num: n, Lane: -1} }
	ops := []Operand{reg(a), reg(b), Symbol{Name: "target"}}
	if mnemonic == "jal" {
		ops = []Operand{reg(a), Symbol{Name: "target"}}
	}
	return Instruction{Mnemonic: mnemonic, Operands: ops}
}

// Independent decoder: concatenate fields in significance order, sign-extend,
// then scale. The production encoder splits a byte displacement instead.
func rv64ProofDisplacement(mnemonic string, word uint32) int64 {
	var half uint32
	var bits uint
	if mnemonic == "jal" {
		half = (word>>31)<<19 | ((word>>12)&255)<<11 | ((word>>20)&1)<<10 | ((word >> 21) & 1023)
		bits = 20
	} else {
		half = (word>>31)<<11 | ((word>>7)&1)<<10 | ((word>>25)&63)<<4 | ((word >> 8) & 15)
		bits = 12
	}
	return (int64(half) << (64 - bits) >> (64 - bits)) * 2
}

func TestRV64JumpLeanEncodingMatchesTable(t *testing.T) {
	contents, err := os.ReadFile(filepath.Join("..", "spec", "lean", "Oak", "RiscVBranchEncoding.lean"))
	if err != nil {
		t.Fatal(err)
	}
	start := strings.Index(string(contents), "-- OAK-RV64-J-ENC-BEGIN")
	end := strings.Index(string(contents), "-- OAK-RV64-J-ENC-END")
	if start < 0 || end <= start {
		t.Fatal("missing J encoding block")
	}
	lines := strings.Split(string(contents)[start:end], "\n")
	var got []string
	for _, line := range lines {
		if strings.HasPrefix(line, "def ") {
			got = append(got, line)
		}
	}
	want := leanEncodingLine(*rv64Table["jal"])
	if len(got) != 1 || got[0] != want {
		t.Fatalf("J row drifted: %v; want %s", got, want)
	}
}

// Every representable B and J displacement is decoded from actual encoder
// output. All register numbers and all B conditions also get a full offset
// sweep. This is exhaustive over offsets, not a proof of the Go program.
func TestRV64BranchEncodingRoundTrip(t *testing.T) {
	for _, mnemonic := range rv64BranchProofMnemonics {
		t.Run(mnemonic, func(t *testing.T) {
			limit, registers := int64(4096), 32
			if mnemonic == "jal" {
				limit, registers = 1048576, 1
			}
			for n := 0; n < registers; n++ {
				instr := rv64ProofBranch(mnemonic, n, 31-n)
				labels := map[string]int64{"target": 0}
				for delta := -limit; delta < limit; delta += 2 {
					labels["target"] = limit + delta
					word, err := encodeRV64Instruction(instr, limit, labels)
					if err != nil {
						t.Fatal(err)
					}
					if got := rv64ProofDisplacement(mnemonic, word); got != delta {
						t.Fatalf("n=%d offset %d decoded as %d (%#08x)", n, delta, got, word)
					}
					enc := rv64Table[mnemonic]
					if word&enc.Mask != enc.Value {
						t.Fatalf("changed opcode: %#08x", word)
					}
					if mnemonic == "jal" {
						if int(word>>7&31) != n {
							t.Fatalf("changed rd: %#08x", word)
						}
					} else if int(word>>15&31) != n || int(word>>20&31) != 31-n {
						t.Fatalf("changed source registers: %#08x", word)
					}
				}
			}
		})
	}
}

// Kernel-check accepted and refused production decisions against the model.
// CI requires Lake, so this test cannot silently skip the formal oracle there.
func TestRV64LocalBranchesMatchLean(t *testing.T) {
	const max = int64(^uint64(0) >> 1)
	const min = -max - 1
	var examples []string
	for _, mnemonic := range rv64BranchProofMnemonics {
		limit := int64(4096)
		if mnemonic == "jal" {
			limit = 1048576
		}
		cases := []struct {
			name       string
			pc, target int64
			accept     bool
		}{
			{"zero", 0, 0, true}, {"forward", 8192, 8200, true}, {"backward", 8192, 8186, true},
			{"halfword", 0, 2, true}, {"negative endpoint", limit, 0, true}, {"positive endpoint", 0, limit - 2, true},
			{"below range", limit + 2, 0, false}, {"above range", 0, limit, false}, {"odd delta", 0, 1, false},
			{"odd negative", 1, 0, false}, {"jointly odd offsets", 1, 3, true},
			{"near max", max - 3, max - 1, true}, {"near min", min + 2, min, true},
			{"positive overflow", min + 2, max - 1, false}, {"negative overflow", max - 1, min + 2, false},
		}
		for _, tc := range cases {
			for _, n := range []int{0, 1, 10, 31} {
				t.Run(fmt.Sprintf("%s/%s/x%d", mnemonic, tc.name, n), func(t *testing.T) {
					word, err := encodeRV64Instruction(rv64ProofBranch(mnemonic, n, 31-n), tc.pc, map[string]int64{"target": tc.target})
					if (err == nil) != tc.accept {
						t.Fatalf("word=%#08x error=%v; accept=%v", word, err, tc.accept)
					}
					if err != nil && word != 0 {
						t.Fatalf("refused encoding returned %#08x", word)
					}
					result := "none"
					if err == nil {
						result = fmt.Sprintf("some 0x%08x#32", word)
					}
					call := fmt.Sprintf("localB .%s %d#5 %d#5", mnemonic, n, 31-n)
					if mnemonic == "jal" {
						call = fmt.Sprintf("localJ %d#5", n)
					}
					examples = append(examples, fmt.Sprintf("example : %s (%d : Int) (%d : Int) = %s := by decide", call, tc.pc, tc.target, result))
				})
			}
		}
		if _, err := encodeRV64Instruction(rv64ProofBranch(mnemonic, 1, 2), 0, nil); err == nil {
			t.Fatalf("%s accepted missing label", mnemonic)
		}
	}
	// Include the actual function writer's byte stream, not just instruction words.
	fn := &Function{Name: "bytes", Arch: ArchRV64, Items: []Item{
		Label{Name: "target"}, rv64ProofBranch("beq", 10, 11), rv64ProofBranch("jal", 1, 0),
	}}
	code, relocs, err := encodeRV64Function(fn)
	if err != nil || len(relocs) != 0 || len(code) != 8 {
		t.Fatalf("function: %x %v %v", code, relocs, err)
	}
	for i, kind := range []string{"beq", "jal"} {
		word := binary.LittleEndian.Uint32(code[i*4:])
		if rv64ProofDisplacement(kind, word) != int64(-i*4) {
			t.Fatalf("incorrect function target at %d: %#x", i*4, word)
		}
		bytes := code[i*4 : i*4+4]
		call := "encodeB .beq 10 11 0"
		if kind == "jal" {
			call = "encodeJ 1 (BitVec.ofInt 20 (-2))"
		}
		examples = append(examples, fmt.Sprintf("example : wordBytes (%s) = [%d#8, %d#8, %d#8, %d#8] := by decide", call, bytes[0], bytes[1], bytes[2], bytes[3]))
	}
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_RV64_LEAN") != "" {
			t.Fatal("lake required for RV64 production correspondence")
		}
		t.Skip("lake not on PATH; formal workflow requires this oracle")
	}
	source := "import Oak.RiscVBranchEncoding\nopen Oak.RiscVBranchEncoding\n" + strings.Join(examples, "\n") + "\n"
	path := filepath.Join(t.TempDir(), "RV64BranchProductionPins.lean")
	if err := os.WriteFile(path, []byte(source), 0600); err != nil {
		t.Fatal(err)
	}
	buildLeanImports(t, lake, path)
	cmd := exec.Command(lake, "env", "lean", path)
	cmd.Dir = filepath.Join("..", "spec", "lean")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("RV64 production correspondence: %v\n%s", err, out)
	}
}

func TestRV64CompressedBranchesRejectOverflow(t *testing.T) {
	const max = int64(^uint64(0) >> 1)
	const min = -max - 1
	for _, mnemonic := range []string{"beq", "bne", "jal"} {
		a := 8
		if mnemonic == "jal" {
			a = 0
		}
		instr := rv64ProofBranch(mnemonic, a, 0)
		if _, ok := rvcEncode(instr, 4, map[string]int64{"target": 0}); !ok {
			t.Fatalf("%s control did not compress", mnemonic)
		}
		for _, pair := range [][2]int64{{min + 2, max - 1}, {max - 1, min + 2}} {
			if word, ok := rvcEncode(instr, pair[0], map[string]int64{"target": pair[1]}); ok || word != 0 {
				t.Fatalf("%s compressed overflowing displacement: %#x", mnemonic, word)
			}
		}
	}
}
