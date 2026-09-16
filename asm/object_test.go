package asm

import (
	"bytes"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
	"testing"
)

// The relocatable objects are checked with the host LLVM binary tools
// (skipped without them): llvm-objdump must disassemble exactly the
// encoder's words under each function's symbol, and report the relocations
// the encoder recorded; llvm-nm must list the defined and undefined symbols.
func TestObjectsAgainstLLVMTools(t *testing.T) {
	llvmMC := findLLVMMC(t)
	bin := strings.TrimSuffix(llvmMC, "llvm-mc")
	objdump, nm := bin+"llvm-objdump", bin+"llvm-nm"
	for _, tool := range []string{objdump, nm} {
		if _, err := os.Stat(tool); err != nil {
			t.Skipf("%s not present", tool)
		}
	}
	source, err := os.ReadFile("../examples/asm/kernels.arm64.oakasm")
	if err != nil {
		t.Fatal(err)
	}
	// A caller of another Oak function: a `bl` that becomes a relocation.
	source = append(source, []byte(`
caller: (a: u64) -> u64 = {
  bind x0 = a
  clobber x30
  frame 16
  str x30, [sp, #-16]!
  bl helper
  ldr x30, [sp], #16
  ret
}
`)...)
	unit, errs := ParseUnit("kernels.arm64.oakasm", string(source))
	if len(errs) != 0 {
		t.Fatalf("parse: %v", errs)
	}
	symbolFor := func(name string) string { return "oak_" + name }
	encoded, err := EncodeFunctions(unit.Functions, symbolFor)
	if err != nil {
		t.Fatal(err)
	}
	for _, format := range []struct {
		name   string
		format ObjectFormat
		prefix string
	}{{"macho", MachO, "_"}, {"elf", ELF, ""}} {
		t.Run(format.name, func(t *testing.T) {
			object, err := WriteObject(format.format, encoded)
			if err != nil {
				t.Fatal(err)
			}
			path := filepath.Join(t.TempDir(), "asm.o")
			if err := os.WriteFile(path, object, 0o644); err != nil {
				t.Fatal(err)
			}
			dis, err := exec.Command(objdump, "-d", "-r", path).CombinedOutput()
			if err != nil {
				t.Fatalf("llvm-objdump: %v\n%s", err, dis)
			}
			// Words per symbol, and relocation lines.
			words := map[string][]byte{}
			var relocLines []string
			current := ""
			symbolRe := regexp.MustCompile(`^[0-9a-f]+ <([^>]+)>:`)
			wordRe := regexp.MustCompile(`^\s*[0-9a-f]+:\s+([0-9a-f]{8})\s`)
			for _, line := range strings.Split(string(dis), "\n") {
				if m := symbolRe.FindStringSubmatch(line); m != nil {
					current = m[1]
					continue
				}
				if m := wordRe.FindStringSubmatch(line); m != nil && current != "" {
					v, _ := strconv.ParseUint(m[1], 16, 32)
					words[current] = append(words[current], wordBytes(uint32(v))...)
					continue
				}
				if strings.Contains(line, "R_AARCH64_") || strings.Contains(line, "ARM64_RELOC_") {
					relocLines = append(relocLines, strings.TrimSpace(line))
				}
			}
			for _, fn := range encoded {
				got := words[format.prefix+fn.Symbol]
				if !bytes.Equal(got, fn.Bytes) {
					t.Errorf("%s: objdump words %x, encoder %x", fn.Symbol, got, fn.Bytes)
				}
			}
			if len(relocLines) != 1 || !strings.Contains(relocLines[0], format.prefix+"oak_helper") {
				t.Errorf("expected one relocation against %soak_helper, got %v\n%s", format.prefix, relocLines, dis)
			}
			symbols, err := exec.Command(nm, path).CombinedOutput()
			if err != nil {
				t.Fatalf("llvm-nm: %v\n%s", err, symbols)
			}
			for _, fn := range encoded {
				if !strings.Contains(string(symbols), " T "+format.prefix+fn.Symbol) {
					t.Errorf("%s not listed as a defined text symbol:\n%s", fn.Symbol, symbols)
				}
			}
			if !strings.Contains(string(symbols), " U "+format.prefix+"oak_helper") {
				t.Errorf("oak_helper not listed as undefined:\n%s", symbols)
			}
		})
	}
}

// Layout failures are errors, never truncated objects.
func TestObjectLayoutErrors(t *testing.T) {
	if _, err := WriteObject(MachO, []EncodedFunction{{Symbol: "f", Bytes: []byte{0, 0, 0, 0}, Align: 6}}); err == nil {
		t.Error("alignment 6 must be rejected")
	}
	if _, err := WriteObject(ELF, []EncodedFunction{{Symbol: "f", Bytes: []byte{0, 0, 0, 0}}, {Symbol: "f", Bytes: []byte{0, 0, 0, 0}}}); err == nil {
		t.Error("a duplicate symbol must be rejected")
	}
	if _, err := WriteObject(MachO, []EncodedFunction{{Symbol: "f", Bytes: []byte{0, 0, 0, 0}, Relocs: []Relocation{{Offset: 0, Kind: "condbr19", Symbol: "g"}}}}); err == nil {
		t.Error("a conditional branch to an external symbol has no Mach-O relocation and must be rejected")
	}
	if _, err := WriteObject(ELF, []EncodedFunction{{Symbol: "f", Bytes: []byte{0, 0, 0, 0}, Relocs: []Relocation{{Offset: 0, Kind: "condbr19", Symbol: "g"}}}}); err != nil {
		t.Errorf("ELF carries R_AARCH64_CONDBR19: %v", err)
	}
	if _, err := WriteObject(ELF, []EncodedFunction{{Symbol: "f", Bytes: []byte{0, 0, 0, 0}, Relocs: []Relocation{{Offset: 0, Kind: "call26"}}}}); err == nil || !strings.Contains(err.Error(), "has no symbol") {
		t.Errorf("nameless relocation error = %v", err)
	}
	if _, err := WriteObject(ELF, []EncodedFunction{{Symbol: "f", Bytes: []byte{0, 0, 0, 0}, Relocs: []Relocation{{Offset: 0, Kind: "future_pair", Symbol: "g"}}}}); err == nil || !strings.Contains(err.Error(), "relocation kind") {
		t.Errorf("unclassified relocation error = %v", err)
	}
}

func TestObjectLayoutChecksCompletePairedRelocationFootprints(t *testing.T) {
	for _, test := range []struct {
		name, arch, kind string
	}{
		{name: "AArch64 adrl", arch: ArchArm64, kind: "adrl21"},
		{name: "RV64 address", arch: ArchRV64, kind: "riscv_pcrel"},
		{name: "RV64 call", arch: ArchRV64, kind: "riscv_call_plt"},
	} {
		t.Run(test.name, func(t *testing.T) {
			function := func(size, offset int) EncodedFunction {
				return EncodedFunction{
					Symbol: "f", Arch: test.arch, Bytes: make([]byte, size),
					Relocs: []Relocation{{Offset: offset, Kind: test.kind, Symbol: "target"}},
				}
			}
			if _, err := WriteObject(ELF, []EncodedFunction{function(4, 0)}); err == nil || !strings.Contains(err.Error(), "outside the function") {
				t.Fatalf("four-byte pair error = %v", err)
			}
			if _, err := WriteObject(ELF, []EncodedFunction{function(8, 4)}); err == nil || !strings.Contains(err.Error(), "outside the function") {
				t.Fatalf("pair beginning at final word error = %v", err)
			}
			if _, err := WriteObject(ELF, []EncodedFunction{function(8, 0)}); err != nil {
				t.Fatalf("exact eight-byte pair: %v", err)
			}
		})
	}
}

// TestObjectLayoutPadsRVCHalfWords: an RV64 function under RVC may end on
// a half word, and the next entry still lands on its boundary — the gap
// is filled with the lane's no-ops, closed by one c.nop, rather than
// looping on a word-sized pad that never reaches it.
func TestObjectLayoutPadsRVCHalfWords(t *testing.T) {
	first := []byte{0x01, 0x00, 0x01, 0x00, 0x82, 0x80} // c.nop; c.nop; c.ret
	second := []byte{0x67, 0x80, 0x00, 0x00}            // ret
	layout, err := layOut([]EncodedFunction{
		{Symbol: "f", Bytes: first, Arch: ArchRV64, Compressed: true},
		{Symbol: "g", Bytes: second, Arch: ArchRV64, Align: 8},
	})
	if err != nil {
		t.Fatal(err)
	}
	if got := layout.defined[1].offset; got != 8 {
		t.Fatalf("g at %d, want 8", got)
	}
	want := append(append(append([]byte{}, first...), 0x01, 0x00), second...)
	if !bytes.Equal(layout.text, want) {
		t.Fatalf("text % x, want % x", layout.text, want)
	}
	layout, err = layOut([]EncodedFunction{
		{Symbol: "f", Bytes: first, Arch: ArchRV64, Compressed: true},
		{Symbol: "g", Bytes: second, Arch: ArchRV64, Align: 16},
	})
	if err != nil {
		t.Fatal(err)
	}
	want = append(append(append([]byte{}, first...), 0x13, 0x00, 0x00, 0x00, 0x13, 0x00, 0x00, 0x00, 0x01, 0x00), second...)
	if !bytes.Equal(layout.text, want) {
		t.Fatalf("text % x, want % x", layout.text, want)
	}
	if _, err := layOut([]EncodedFunction{{Symbol: "f", Bytes: []byte{0, 0}, Arch: ArchArm64}, {Symbol: "g", Bytes: second, Arch: ArchArm64}}); err == nil {
		t.Error("an AArch64 entry after a half word must be refused, not padded forever")
	}
}
