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
			unit, diagnostics := ParseUnit("bitwise.arm64.oakasm", fmt.Sprintf("bitwise: (a: u32, b: u32) -> u32 = {\n %s w0, w0, w1\n ret\n}\n", tc.mnemonic))
			if len(diagnostics) != 0 || unit == nil || len(unit.Functions) != 1 {
				t.Fatalf("parse function: %v", diagnostics)
			}
			emitted, relocations, err := EncodeFunction(unit.Functions[0])
			if err != nil || len(relocations) != 0 {
				t.Fatalf("encode function: %v, relocations %v", err, relocations)
			}
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

// Mandatory in formal.yml; optional in Go-only developer environments.
func TestAArch64BitwiseFunctionMatchesLean(t *testing.T) {
	if _, err := exec.LookPath("lake"); err != nil {
		if os.Getenv("OAK_REQUIRE_ARM64_LEAN") == "1" {
			t.Fatal("lake is required: ", err)
		}
		t.Skip("lake unavailable; formal.yml requires this oracle")
	}
	var source strings.Builder
	source.WriteString("import Oak.AArch64BitwiseFunction\nopen Oak.AArch64BitwiseFunction\n")
	for _, tc := range []struct{ mnemonic, op string }{{"and", "and"}, {"orr", "or"}, {"eor", "xor"}} {
		unit, diagnostics := ParseUnit("bitwise.arm64.oakasm", fmt.Sprintf("bitwise: (a: u32, b: u32) -> u32 = {\n %s w0, w0, w1\n ret\n}\n", tc.mnemonic))
		if len(diagnostics) != 0 || unit == nil || len(unit.Functions) != 1 {
			t.Fatalf("parse: %v", diagnostics)
		}
		code, relocs, err := EncodeFunction(unit.Functions[0])
		if err != nil || len(relocs) != 0 {
			t.Fatalf("encode: %v, relocs %v", err, relocs)
		}
		var literals []string
		for _, b := range code {
			literals = append(literals, fmt.Sprint(b))
		}
		fmt.Fprintf(&source, "example : functionBytes .%s = [%s] := by decide +kernel\n", tc.op, strings.Join(literals, ","))
		fmt.Fprintf(&source, "example (s : State) : invoke [%s] s = some (returned .%s s) := by exact function_success .%s s\n", strings.Join(literals, ","), tc.op, tc.op)
	}
	path := filepath.Join(t.TempDir(), "Arm64BitwiseCorrespondence.lean")
	if err := os.WriteFile(path, []byte(source.String()), 0600); err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command("lake", "env", "lean", path)
	cmd.Dir = filepath.Join("..", "spec", "lean")
	if output, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("Lean byte/execution correspondence: %v\n%s\n%s", err, output, source.String())
	}
}
