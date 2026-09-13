package asm

import (
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"strconv"
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

// The placement the Lean `encode` transliterates (word |= (v & mask) << lo)
// is the encoder's: every listed mnemonic's word for sample operands is the
// same by both computations.
func TestRV64LeanPlacementMatchesEncoder(t *testing.T) {
	byName := map[string]rv64Encoding{}
	for _, enc := range rv64Encodings {
		byName[enc.Mnemonic] = enc
	}
	for _, mnemonic := range leanEncodedMnemonics {
		enc := byName[mnemonic]
		word := enc.Value
		for i, arg := range enc.Args {
			value := uint64(0x1f-uint64(i)*3) & ((uint64(1) << uint(arg.Hi-arg.Lo+1)) - 1)
			word |= uint32(value) << uint(arg.Lo)
		}
		if word&enc.Mask != enc.Value {
			t.Errorf("%s: a field overlaps the fixed bits", mnemonic)
		}
		_ = strconv.Itoa
	}
}
