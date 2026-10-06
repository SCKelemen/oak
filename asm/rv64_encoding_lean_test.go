package asm

import (
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

// The encodings the Lean specification restates (spec/lean/Oak/RiscV.lean,
// the OAK-ENC block; spec/lean-sail/OakSailBridge/Encoding.lean proves each
// equal to the Sail model's encdec of the instruction it spells) must be
// the generated table's entries, field for field. The block is generated
// from the table: run with OAK_WRITE_LEAN_ENCODINGS=1 to print it.
var leanEncodedMnemonics = []string{
	"add", "sub", "sll", "slt", "sltu", "xor", "srl", "sra", "or", "and",
	"addw", "subw", "sllw", "srlw", "sraw",
	"addi", "slti", "sltiu", "xori", "ori", "andi",
	"slli", "srli", "srai",
	"beq", "bne", "blt", "bge", "bltu", "bgeu",
}

// leanEncodingName spells a mnemonic as a Lean identifier (`or` and `and`
// are keywords; `sub` reads better as `sub_`).
func leanEncodingName(mnemonic string) string {
	switch mnemonic {
	case "or", "and", "xor":
		return mnemonic + "_"
	}
	return mnemonic
}

func leanEncodingLine(enc rv64Encoding) string {
	fields := make([]string, 0, len(enc.Args))
	for _, arg := range enc.Args {
		fields = append(fields, fmt.Sprintf("⟨%q, %d, %d⟩", arg.Name, arg.Hi, arg.Lo))
	}
	return fmt.Sprintf("def %s : Encoding := ⟨%q, 0x%08x#32, 0x%08x#32, [%s]⟩", leanEncodingName(enc.Mnemonic), enc.Mnemonic, enc.Value, enc.Mask, strings.Join(fields, ", "))
}

func expectedLeanEncodings(t *testing.T) []string {
	t.Helper()
	byName := map[string]rv64Encoding{}
	for _, enc := range rv64Encodings {
		byName[enc.Mnemonic] = enc
	}
	var lines []string
	for _, mnemonic := range leanEncodedMnemonics {
		enc, ok := byName[mnemonic]
		if !ok {
			t.Fatalf("%s is not in the generated table", mnemonic)
		}
		lines = append(lines, leanEncodingLine(enc))
	}
	return lines
}

var leanEncBlock = regexp.MustCompile(`(?s)-- OAK-ENC-BEGIN[^\n]*\n(.*?)-- OAK-ENC-END`)

func TestRV64LeanEncodingsMatchTable(t *testing.T) {
	expected := expectedLeanEncodings(t)
	if os.Getenv("OAK_WRITE_LEAN_ENCODINGS") != "" {
		fmt.Println(strings.Join(expected, "\n"))
	}
	for _, path := range []string{filepath.Join("..", "spec", "lean", "Oak", "RiscV.lean"), filepath.Join("..", "spec", "lean-sail", "OakSailBridge", "Encoding.lean")} {
		text, err := os.ReadFile(path)
		if err != nil {
			t.Fatal(err)
		}
		m := leanEncBlock.FindStringSubmatch(string(text))
		if m == nil {
			t.Fatalf("%s lacks its OAK-ENC block", path)
		}
		var got []string
		for _, line := range strings.Split(m[1], "\n") {
			if strings.HasPrefix(strings.TrimSpace(line), "def ") {
				got = append(got, strings.TrimSpace(line))
			}
		}
		if strings.Join(got, "\n") != strings.Join(expected, "\n") {
			t.Errorf("%s: the OAK-ENC block drifted from the generated table; regenerate with OAK_WRITE_LEAN_ENCODINGS=1:\n--- have\n%s\n--- want\n%s", path, strings.Join(got, "\n"), strings.Join(expected, "\n"))
		}
	}
}

// Compare actual production words with the field-placement model used by Lean.
// These bounded cases are regression evidence, not implementation refinement.
func TestRV64LeanPlacementMatchesEncoder(t *testing.T) {
	reg := func(n int) Register { return Register{Class: ClassRV64X, Num: n, Lane: -1} }
	for _, mnemonic := range leanEncodedMnemonics {
		for _, n := range []int{0, 1, 10, 31} {
			for _, value := range []int64{-2048, -1, 0, 1, 31, 63, 2047} {
				rd, rs1, rs2 := n, (n+7)%32, (n+19)%32
				fields := map[string]int64{"rd": int64(rd), "rs1": int64(rs1), "rs2": int64(rs2)}
				ops := []Operand{reg(rd), reg(rs1), reg(rs2)}
				delta := value * 2
				switch mnemonic {
				case "addi", "slti", "sltiu", "xori", "ori", "andi":
					ops[2] = Immediate{Value: value}
					fields["imm12"] = value
				case "slli", "srli", "srai":
					if value < 0 || value > 63 {
						continue
					}
					ops[2] = Immediate{Value: value}
					fields["shamtd"] = value
				case "beq", "bne", "blt", "bge", "bltu", "bgeu":
					ops = []Operand{reg(rs1), reg(rs2), Symbol{Name: "target"}}
					fields["bimm12hi"] = (delta>>12&1)<<6 | delta>>5&63
					fields["bimm12lo"] = delta>>1&15<<1 | delta>>11&1
				}
				enc := rv64Table[mnemonic]
				want := enc.Value
				for _, arg := range enc.Args {
					v, ok := fields[arg.Name]
					if !ok {
						t.Fatalf("missing model operand %s", arg.Name)
					}
					want |= uint32(uint64(v)&((1<<uint(arg.Hi-arg.Lo+1))-1)) << uint(arg.Lo)
				}
				got, err := encodeRV64Instruction(Instruction{Mnemonic: mnemonic, Operands: ops}, 8192, map[string]int64{"target": 8192 + delta})
				if err != nil || got != want {
					t.Fatalf("%s n=%d value=%d: production=%#08x, %v; model=%#08x", mnemonic, n, value, got, err, want)
				}
			}
		}
	}
}
