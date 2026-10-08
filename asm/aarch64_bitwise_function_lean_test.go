package asm

import (
	"bytes"
	"encoding/binary"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// This is executable assembler correspondence evidence, not a universal proof
// of Oak source lowering, register allocation, or the Go implementation.
func TestAArch64BitwiseFunctionLeanExactBytes(t *testing.T) {
	source, err := os.ReadFile(filepath.Join("..", "spec", "lean", "Oak", "AArch64BitwiseFunction.lean"))
	if err != nil {
		t.Fatal(err)
	}
	w := func(n int) Register { return Register{Text: fmt.Sprintf("w%d", n), Class: ClassW, Num: n, Lane: -1} }
	cases := []struct {
		mnemonic, op string
		word         uint32
		bytes        []byte
	}{
		{"and", "and", 0x0a010000, []byte{0, 0, 1, 0x0a, 0xc0, 3, 0x5f, 0xd6}},
		{"orr", "or", 0x2a010000, []byte{0, 0, 1, 0x2a, 0xc0, 3, 0x5f, 0xd6}},
		{"eor", "xor", 0x4a010000, []byte{0, 0, 1, 0x4a, 0xc0, 3, 0x5f, 0xd6}},
	}
	for _, tc := range cases {
		t.Run(tc.mnemonic, func(t *testing.T) {
			instruction := Instruction{Mnemonic: tc.mnemonic, Operands: []Operand{w(0), w(0), w(1)}}
			word, reloc, err := EncodeInstruction(instruction, 0, nil)
			if err != nil || reloc != nil || word != tc.word {
				t.Fatalf("logical word %#08x, relocation %v, error %v; want %#08x", word, reloc, err, tc.word)
			}
			ret, reloc, err := EncodeInstruction(Instruction{Mnemonic: "ret"}, 4, nil)
			if err != nil || reloc != nil || ret != 0xd65f03c0 {
				t.Fatalf("return word %#08x, relocation %v, error %v", ret, reloc, err)
			}
			emitted := make([]byte, 8)
			binary.LittleEndian.PutUint32(emitted, word)
			binary.LittleEndian.PutUint32(emitted[4:], ret)
			if !bytes.Equal(emitted, tc.bytes) {
				t.Fatalf("emitted %x, want %x", emitted, tc.bytes)
			}
			// Bind the theorem's complete literal to the actual emitter bytes.
			var literals []string
			for _, b := range emitted {
				literals = append(literals, fmt.Sprintf("0x%02x", b))
			}
			line := "| ." + tc.op + " => [" + strings.Join(literals, ", ") + "]"
			normalized := strings.Join(strings.Fields(string(source)), " ")
			if !strings.Contains(normalized, line) {
				t.Fatalf("Lean exact bytes missing/drifted: %s", line)
			}
		})
	}
}

func TestAArch64BitwiseFunctionLeanEncodingRows(t *testing.T) {
	fields := []isaField{{"sf", 31, 1}, {"opc", 30, 2}, {"shift", 23, 2}, {"N", 21, 1}, {"Rm", 20, 5}, {"imm6", 15, 6}, {"Rn", 9, 5}, {"Rd", 4, 5}}
	for _, tc := range []struct {
		name  string
		value uint32
	}{{"AND_32_log_shift", 0x0a000000}, {"ORR_32_log_shift", 0x2a000000}, {"EOR_32_log_shift", 0x4a000000}} {
		matches := 0
		for _, row := range isaEncodings {
			if row.Name != tc.name {
				continue
			}
			matches++
			if row.Value != tc.value || row.Mask != 0xff200000 {
				t.Fatalf("%s row value/mask drifted", tc.name)
			}
			if fmt.Sprint(row.Fields) != fmt.Sprint(fields) {
				t.Fatalf("%s fields drifted: %+v", tc.name, row.Fields)
			}
			found := false
			for _, form := range row.Forms {
				if len(form.Operands) != 3 {
					continue
				}
				if len(form.Defaults) != 2 || form.Defaults[0].Field != "shift" || form.Defaults[0].Value != 0 || form.Defaults[1].Field != "imm6" || form.Defaults[1].Value != 0 {
					t.Fatalf("%s no-shift defaults drifted", tc.name)
				}
				found = true
			}
			if !found {
				t.Fatalf("%s missing three-register form", tc.name)
			}
		}
		if matches != 1 {
			t.Fatalf("%s matched %d rows", tc.name, matches)
		}
	}
}
