package compiler

import (
	"bytes"
	"debug/elf"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/target"
)

// This pins actual source-to-image output for one constant program. It does
// not prove parsing/lowering, ELF loader execution or Linux syscall behavior.
func TestAArch64MinimalStartupMatchesLean(t *testing.T) {
	image, err := New().WithSource("minimal.oak", "main: (): i32 { 42 }\n").WithTarget(target.Target{OS: target.OSLinux, Arch: target.ArchArm64}).EmitExecutable().Get()
	if err != nil {
		t.Fatal(err)
	}
	file, err := elf.NewFile(bytes.NewReader(image))
	if err != nil {
		t.Fatal(err)
	}
	if file.Machine != elf.EM_AARCH64 || file.Class != elf.ELFCLASS64 || file.Data != elf.ELFDATA2LSB || file.Type != elf.ET_EXEC || file.Entry != 0x10000 {
		t.Fatalf("unexpected ELF header: %+v", file.FileHeader)
	}
	text := file.Section(".text")
	if text == nil || text.Addr != 0x10000 {
		t.Fatal("missing/misplaced text")
	}
	code, err := text.Data()
	if err != nil {
		t.Fatal(err)
	}
	expected := []byte{3, 0, 0, 148, 168, 11, 128, 82, 1, 0, 0, 212, 64, 5, 128, 82, 192, 3, 95, 214}
	if !bytes.Equal(code, expected) {
		t.Fatalf("actual text %x, want %x", code, expected)
	}
	if len(file.Progs) != 1 {
		t.Fatal("expected one segment")
	}
	p := file.Progs[0]
	if p.Type != elf.PT_LOAD || p.Flags != elf.PF_R|elf.PF_X || p.Off != 4096 || p.Vaddr != 0x10000 || p.Filesz != 32 || p.Memsz != 32 || p.Align != 4096 {
		t.Fatalf("unexpected segment: %+v", p.ProgHeader)
	}
	if _, err := exec.LookPath("lake"); err != nil {
		if os.Getenv("OAK_REQUIRE_ARM64_LEAN") == "1" {
			t.Fatal(err)
		}
		t.Skip("lake unavailable; compiler ELF byte pin above passed")
	}
	var literals []string
	for _, b := range code {
		literals = append(literals, fmt.Sprint(b))
	}
	source := fmt.Sprintf("import Oak.AArch64MinimalStartup\nopen Oak.AArch64MinimalStartup\nexample : textBytes = [%s] := by decide +kernel\nexample (regs : Oak.AArch64BitwiseFunction.Registers) (sp : BitVec 64) (flags : BitVec 4) : run 5 %d [%s] ⟨regs, %d#64, sp, flags⟩ = some (93#64,42#64) := by exact startup_request regs sp flags\n", strings.Join(literals, ","), file.Entry, strings.Join(literals, ","), file.Entry)

	var imageLiterals []string
	for _, b := range image {
		imageLiterals = append(imageLiterals, fmt.Sprint(b))
	}
	source += fmt.Sprintf("set_option maxRecDepth 100000\nset_option maxHeartbeats 2000000\ndef emittedImage : Oak.MinimalELF.Bytes := [%s]\nexample : acceptsImage emittedImage = true := by decide +kernel\nexample (regs : Oak.AArch64BitwiseFunction.Registers) (sp : BitVec 64) (flags : BitVec 4) : (Oak.MinimalELF.loadBytes emittedImage 65536 fileText.length).bind (executeLoaded regs sp flags) = some (93#64,42#64) := (admitted_startup_request emittedImage (by decide +kernel) regs sp flags).2\n", strings.Join(imageLiterals, ","))
	path := filepath.Join(t.TempDir(), "Startup.lean")
	if err := os.WriteFile(path, []byte(source), 0600); err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command("lake", "env", "lean", "--tstack=400000", path)
	cmd.Dir = filepath.Join("..", "spec", "lean")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("Lean compiler/startup byte pin: %v\n%s", err, out)
	}
}
