package compiler

import (
	"bytes"
	"debug/elf"
	"encoding/binary"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/target"
)

// Compile actual Oak source through production lowering/selection/assembly,
// extract oak_mix from the emitted ELF object, and bind its complete bytes to
// the universal framed execution theorem. This is not a universal theorem of
// the Go parser/compiler or a source-identity certificate consumer.
func TestRV64FramedBitwiseCompilerMatchesLean(t *testing.T) {
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_RV64_LEAN") != "" {
			t.Fatal("lake required for RV64 compiler correspondence")
		}
		t.Skip("lake unavailable")
	}
	var pins []string
	for _, tc := range []struct{ name, operator string }{{"and", "&"}, {"or", "|"}, {"xor", "^"}} {
		source := fmt.Sprintf("mix: (a: u32, b: u32) -> u32 = a %s b\nmain: () -> i32 = i32(0)\n", tc.operator)
		out, err := New().WithSource("framed_bitwise.oak", source).WithTarget(target.Target{OS: target.OSLinux, Arch: target.ArchRiscv64}).WithNativeBodies().EmitNative(asm.ELF).Get()
		if err != nil {
			t.Fatal(err)
		}
		f, err := elf.NewFile(bytes.NewReader(out.Object))
		if err != nil {
			t.Fatal(err)
		}
		if f.Machine != elf.EM_RISCV || f.Class != elf.ELFCLASS64 || f.Data != elf.ELFDATA2LSB || f.Type != elf.ET_REL {
			t.Fatalf("wrong object target: %+v", f.FileHeader)
		}
		if binary.LittleEndian.Uint32(out.Object[48:52]) != 4 {
			t.Fatal("expected uncompressed LP64D object flags")
		}
		syms, err := f.Symbols()
		if err != nil {
			t.Fatal(err)
		}
		var code []byte
		for _, s := range syms {
			if s.Name == "oak_mix" {
				if elf.ST_TYPE(s.Info) != elf.STT_FUNC || s.Section == elf.SHN_UNDEF || int(s.Section) >= len(f.Sections) {
					t.Fatalf("bad function symbol: %+v", s)
				}
				section, err := f.Sections[s.Section].Data()
				if err != nil {
					t.Fatal(err)
				}
				if s.Value > uint64(len(section)) || s.Size > uint64(len(section))-s.Value {
					t.Fatal("symbol extent outside section")
				}
				code = section[s.Value : s.Value+s.Size]
				for _, rel := range f.Sections {
					if rel.Type == elf.SHT_RELA && rel.Info == uint32(s.Section) {
						data, err := rel.Data()
						if err != nil {
							t.Fatal(err)
						}
						if len(data)%24 != 0 {
							t.Fatal("bad ELF64 relocation size")
						}
						for at := 0; at < len(data); at += 24 {
							offset := binary.LittleEndian.Uint64(data[at : at+8])
							if offset >= s.Value && offset < s.Value+s.Size {
								t.Fatal("framed function contains an unresolved relocation")
							}
						}
					}
				}
			}
		}
		if len(code) != 36 {
			t.Fatalf("%s complete compiler function is %d bytes, expected current36-byte framed profile", tc.name, len(code))
		}
		vals := make([]string, len(code))
		for i, b := range code {
			vals[i] = fmt.Sprint(b)
		}
		pins = append(pins, fmt.Sprintf("example : functionBytes .%s = [%s] := by rfl", tc.name, strings.Join(vals, ",")))
		t.Logf("%s source→oak_mix bytes %x", tc.name, code)
	}
	root := filepath.Join("..", "spec", "lean")
	build := exec.Command(lake, "build", "Oak.RiscVFramedBitwise")
	build.Dir = root
	if out, err := build.CombinedOutput(); err != nil {
		t.Fatalf("model build: %v\n%s", err, out)
	}
	source := "import Oak.RiscVFramedBitwise\nopen Oak.RiscVFramedBitwise\n" + strings.Join(pins, "\n") + "\n"
	file := filepath.Join(t.TempDir(), "RV64CompilerBitwisePins.lean")
	if err := os.WriteFile(file, []byte(source), 0600); err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command(lake, "env", "lean", file)
	cmd.Dir = root
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("compiler-byte Lean pins: %v\n%s", err, out)
	}
}
