package asm

import (
	"bytes"
	"debug/elf"
	"testing"
)

func TestExplicitObjectTargetEmptyAndData(t *testing.T) {
	for _, tc := range []struct {
		arch    string
		machine elf.Machine
	}{{ArchArm64, elf.EM_AARCH64}, {ArchRV64, elf.EM_RISCV}} {
		for _, data := range [][]DataSymbol{nil, {{Name: "value", Bytes: []byte{1, 2, 3}, Align: 1}}} {
			raw, err := WriteObjectFor(tc.arch, ELF, nil, ObjectOptions{Data: data})
			if err != nil {
				t.Fatal(err)
			}
			f, err := elf.NewFile(bytes.NewReader(raw))
			if err != nil {
				t.Fatal(err)
			}
			if f.Machine != tc.machine {
				t.Fatalf("%s: machine %v, want %v", tc.arch, f.Machine, tc.machine)
			}
			if len(data) > 0 {
				syms, err := f.Symbols()
				if err != nil {
					t.Fatal(err)
				}
				found := false
				for _, s := range syms {
					if s.Name == "value" {
						found = true
						b, err := f.Sections[s.Section].Data()
						if err != nil || !bytes.Equal(b[s.Value:s.Value+s.Size], data[0].Bytes) {
							t.Fatalf("data mismatch: %x %v", b, err)
						}
					}
				}
				if !found {
					t.Fatal("missing data symbol")
				}
			}
			f.Close()
		}
	}
}

func TestExplicitObjectTargetRefusals(t *testing.T) {
	for _, arch := range []string{"", "wasm32", "x86_64", "rv65"} {
		if b, err := WriteObjectFor(arch, ELF, nil, ObjectOptions{}); err == nil || b != nil {
			t.Fatalf("accepted %q", arch)
		}
	}
	for _, arch := range []string{"", ArchRV64, "wasm32"} {
		if b, err := WriteObjectFor(ArchArm64, ELF, []EncodedFunction{{Symbol: "f", Arch: arch}}, ObjectOptions{}); err == nil || b != nil {
			t.Fatalf("accepted mismatched function %q", arch)
		}
	}
	if b, err := WriteObjectFor(ArchRV64, MachO, nil, ObjectOptions{}); err == nil || b != nil {
		t.Fatal("accepted empty RV64 Mach-O")
	}
}

func TestExplicitObjectTargetParity(t *testing.T) {
	for _, arch := range []string{ArchArm64, ArchRV64} {
		code, relocs, err := EncodeFunction(&Function{Name: "f", Arch: arch, Items: []Item{Instruction{Mnemonic: "ret"}}})
		if err != nil {
			t.Fatal(err)
		}
		functions := []EncodedFunction{{Symbol: "f", Arch: arch, Bytes: code, Relocs: relocs}}
		for _, format := range []ObjectFormat{ELF, MachO} {
			if arch == ArchRV64 && format == MachO {
				continue
			}
			old, err := WriteObjectWith(format, functions, ObjectOptions{})
			if err != nil {
				t.Fatal(err)
			}
			got, err := WriteObjectFor(arch, format, functions, ObjectOptions{})
			if err != nil || !bytes.Equal(old, got) {
				t.Fatalf("%s format %d parity: %v", arch, format, err)
			}
		}
	}
}
