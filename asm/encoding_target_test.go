package asm

import (
	"bytes"
	"debug/elf"
	"encoding/binary"
	"testing"
)

func TestEncodingTargetRejectsUnknown(t *testing.T) {
	for _, arch := range []string{"wasm", "wasm32", "x86_64", "ARM64", " arm64", "rv65"} {
		t.Run(arch, func(t *testing.T) {
			fn := &Function{Name: "ret", Arch: arch, Items: []Item{Instruction{Mnemonic: "ret"}}}
			if code, relocs, err := EncodeFunction(fn); err == nil || code != nil || relocs != nil {
				t.Errorf("unsupported target returned code=%x relocs=%v err=%v", code, relocs, err)
			}
			for _, format := range []ObjectFormat{ELF, MachO} {
				functions := []EncodedFunction{{Symbol: "ret", Arch: arch, Bytes: []byte{0xc0, 0x03, 0x5f, 0xd6}}}
				if object, err := WriteObject(format, functions); err == nil || object != nil {
					t.Errorf("format %d accepted unsupported target: bytes=%d err=%v", format, len(object), err)
				}
			}
		})
	}
}

func TestEncodingTargetNilFunction(t *testing.T) {
	if code, relocs, err := EncodeFunction(nil); err == nil || code != nil || relocs != nil {
		t.Fatalf("nil function returned code=%x relocs=%v err=%v", code, relocs, err)
	}
}

func TestEncodingTargetPreservesNativeBytes(t *testing.T) {
	for _, tc := range []struct {
		arch    string
		word    uint32
		machine elf.Machine
	}{{"", 0xd65f03c0, elf.EM_AARCH64}, {ArchArm64, 0xd65f03c0, elf.EM_AARCH64}, {ArchRV64, 0x00008067, elf.EM_RISCV}} {
		t.Run(tc.arch, func(t *testing.T) {
			fn := &Function{Name: "ret", Arch: tc.arch, Items: []Item{Instruction{Mnemonic: "ret"}}}
			code, relocs, err := EncodeFunction(fn)
			if err != nil || len(code) != 4 || binary.LittleEndian.Uint32(code) != tc.word || len(relocs) != 0 {
				t.Fatalf("ret encoding=%x relocs=%v err=%v", code, relocs, err)
			}
			object, err := WriteObject(ELF, []EncodedFunction{{Symbol: "ret", Arch: tc.arch, Bytes: code}})
			if err != nil {
				t.Fatal(err)
			}
			f, err := elf.NewFile(bytes.NewReader(object))
			if err != nil {
				t.Fatal(err)
			}
			defer f.Close()
			if f.Machine != tc.machine {
				t.Fatalf("machine=%v, want %v", f.Machine, tc.machine)
			}
			text, err := f.Section(".text").Data()
			if err != nil || !bytes.Equal(text, code) {
				t.Fatalf("text=%x err=%v", text, err)
			}
		})
	}
}

func TestEncodingTargetLegacyObjectParity(t *testing.T) {
	for _, format := range []ObjectFormat{ELF, MachO} {
		functions := []EncodedFunction{{Symbol: "ret", Bytes: []byte{0xc0, 0x03, 0x5f, 0xd6}}}
		legacy, err := WriteObject(format, functions)
		if err != nil {
			t.Fatal(err)
		}
		functions[0].Arch = ArchArm64
		explicit, err := WriteObject(format, functions)
		if err != nil || !bytes.Equal(legacy, explicit) {
			t.Fatalf("format %d legacy parity: %v", format, err)
		}
	}
}
