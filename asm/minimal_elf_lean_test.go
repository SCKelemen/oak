package asm

import (
	"bytes"
	"debug/elf"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// Compress long padding runs in kernel-evaluated exact file literals. No
// payload or ELF metadata is omitted from the generated term.
func minimalELFLeanBytes(data []byte) string {
	var chunks []string
	for len(data) > 0 {
		n := 0
		for n < len(data) && data[n] == 0 {
			n++
		}
		if n >= 8 {
			chunks = append(chunks, fmt.Sprintf("List.replicate %d 0", n))
			data = data[n:]
			continue
		}
		end := 1
		for end < len(data) {
			run := 0
			for end+run < len(data) && data[end+run] == 0 {
				run++
			}
			if run >= 8 {
				break
			}
			if run > 0 {
				end += run
			} else {
				end++
			}
		}
		var vals []string
		for _, b := range data[:end] {
			vals = append(vals, fmt.Sprint(b))
		}
		chunks = append(chunks, "["+strings.Join(vals, ",")+"]")
		data = data[end:]
	}
	if len(chunks) == 0 {
		return "[]"
	}
	return "(" + strings.Join(chunks, " ++ ") + ")"
}

func TestRV64BitwiseELFMatchesLean(t *testing.T) {
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_RV64_LEAN") != "" {
			t.Fatal("lake required for RV64 ELF admission")
		}
		t.Skip("lake unavailable")
	}
	var claims []string
	reg := func(n int) Register { return Register{Class: ClassRV64X, Num: n, Lane: -1} }
	for _, op := range []string{"and", "or", "xor"} {
		fn := &Function{Name: "leaf", Arch: ArchRV64, Items: []Item{
			Instruction{Mnemonic: op, Operands: []Operand{reg(10), reg(10), reg(11)}}, Instruction{Mnemonic: "ret"}}}
		code, relocs, err := encodeRV64Function(fn)
		if err != nil || len(relocs) != 0 {
			t.Fatalf("encode: %v", err)
		}
		image, err := WriteExecutable([]EncodedFunction{{Symbol: "leaf", Bytes: code, Align: 4, Arch: ArchRV64}}, ExecutableOptions{OS: OSLinux, Arch: ArchRV64, Entry: "leaf", RV64FloatABI: "double"})
		if err != nil {
			t.Fatal(err)
		}
		parsed, err := elf.NewFile(bytes.NewReader(image))
		if err != nil {
			t.Fatal(err)
		}
		syms, err := parsed.Symbols()
		if err != nil {
			t.Fatal(err)
		}
		var address uint64
		for _, s := range syms {
			if s.Name == "leaf" {
				address = s.Value
			}
		}
		if address == 0 {
			t.Fatal("missing leaf")
		}
		name := "image_" + op
		claims = append(claims, fmt.Sprintf("def %s : Bytes := %s", name, minimalELFLeanBytes(image)))
		claims = append(claims, fmt.Sprintf("example : admittedBytes .rv64 %s %d (Oak.RiscVBitwiseFunction.functionBytes .%s) = true := by decide +kernel", name, address, op))
		claims = append(claims, fmt.Sprintf("example : admittedBytes .arm64 %s %d (Oak.RiscVBitwiseFunction.functionBytes .%s) = false := by decide +kernel", name, address, op))
		for _, badAddress := range []uint64{address + 1, address - 4, address + 4096} {
			claims = append(claims, fmt.Sprintf("example : admittedBytes .rv64 %s %d (Oak.RiscVBitwiseFunction.functionBytes .%s) = false := by decide +kernel", name, badAddress, op))
		}
		wrong := "and"
		if op == wrong {
			wrong = "or"
		}
		claims = append(claims, fmt.Sprintf("example : admittedBytes .rv64 %s %d (Oak.RiscVBitwiseFunction.functionBytes .%s) = false := by decide +kernel", name, address, wrong))
		if op == "and" {
			for _, at := range []int{0, 4, 5, 16, 18, 24, 32, 48, 52, 54, 56, 64, 68, 72, 80, 96, 104, 112} {
				claims = append(claims, fmt.Sprintf("example : admittedBytes .rv64 (%s.set %d 255) %d (Oak.RiscVBitwiseFunction.functionBytes .and) = false := by decide +kernel", name, at, address))
			}
			off := int(parsed.Progs[0].Off + address - parsed.Progs[0].Vaddr)
			claims = append(claims, fmt.Sprintf("example : admittedBytes .rv64 (%s.set %d 0) %d (Oak.RiscVBitwiseFunction.functionBytes .and) = false := by decide +kernel", name, off, address))
			claims = append(claims, fmt.Sprintf("example : admittedBytes .rv64 (%s.take %d) %d (Oak.RiscVBitwiseFunction.functionBytes .and) = false := by decide +kernel", name, off+7, address))
		}
	}
	source := "import Oak.RiscVBitwiseELF\nopen Oak.MinimalELF\nset_option maxRecDepth 20000\nset_option maxHeartbeats 2000000\n" + strings.Join(claims, "\n") + "\n"
	path := filepath.Join(t.TempDir(), "MinimalELFPins.lean")
	if err := os.WriteFile(path, []byte(source), 0600); err != nil {
		t.Fatal(err)
	}
	buildLeanImports(t, lake, path)
	cmd := exec.Command(lake, "env", "lean", path)
	cmd.Dir = filepath.Join("..", "spec", "lean")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("ELF admission pins: %v\n%s", err, out)
	}
	t.Logf("checked %d exact image/admission claims", len(claims))
}
