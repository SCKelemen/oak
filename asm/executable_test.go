package asm

import (
	"bytes"
	"debug/elf"
	"encoding/binary"
	"testing"
)

// The executable writer (docs/spec/94-assembler.md §9): a static ELF64
// with the start stub at the entry, every function a symbol, one
// read-and-execute segment, and the calls between functions resolved.
func TestWriteExecutableRV64(t *testing.T) {
	main, errs := rv64Unit(t, "oak_main: () -> i32", "  li a0, 42\n  ret")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	helper, errs := rv64Unit(t, "oak_twice: (x: u32) -> u32", "  bind a0 = x\n  frame 16\n  addi sp, sp, -16\n  sd ra, 8(sp)\n  call oak_main\n  addw a0, a0, a0\n  ld ra, 8(sp)\n  addi sp, sp, 16\n  ret")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	encoded, err := EncodeFunctions([]*Function{main, helper}, func(s string) string { return s })
	if err != nil {
		t.Fatal(err)
	}
	for _, o := range []ExecutableOptions{
		{OS: OSLinux, Arch: ArchRV64, Entry: "oak_main", RV64FloatABI: "double"},
		{OS: OSFreestanding, Arch: ArchRV64, Entry: "oak_main"},
	} {
		image, err := WriteExecutable(encoded, o)
		if err != nil {
			t.Fatalf("%s: %v", o.OS, err)
		}
		file, err := elf.NewFile(bytes.NewReader(image))
		if err != nil {
			t.Fatalf("%s: %v", o.OS, err)
		}
		if file.Machine != elf.EM_RISCV || file.Type != elf.ET_EXEC {
			t.Fatalf("%s: machine %v type %v", o.OS, file.Machine, file.Type)
		}
		if len(file.Progs) != 1 || file.Progs[0].Type != elf.PT_LOAD || file.Progs[0].Flags != elf.PF_R|elf.PF_X || file.Progs[0].Vaddr != o.base() {
			t.Fatalf("%s: program headers %+v", o.OS, file.Progs)
		}
		symbols, err := file.Symbols()
		if err != nil {
			t.Fatal(err)
		}
		addr := map[string]uint64{}
		for _, s := range symbols {
			addr[s.Name] = s.Value
		}
		if addr["_start"] != file.Entry || addr["oak_main"] == 0 || addr["oak_twice"] == 0 {
			t.Fatalf("%s: symbols %v, entry %#x", o.OS, addr, file.Entry)
		}
		// The stub's call reaches oak_main: decode the auipc/jalr pair (the
		// first auipc into ra in the text).
		text := file.Section(".text")
		data, err := text.Data()
		if err != nil {
			t.Fatal(err)
		}
		callAt := -1
		for i := 0; i+8 <= len(data); i += 4 {
			if word := binary.LittleEndian.Uint32(data[i : i+4]); word&0xfff == 0x097 {
				callAt = i
				break
			}
		}
		if callAt < 0 {
			t.Fatalf("%s: no auipc ra in the stub", o.OS)
		}
		auipc, jalr := binary.LittleEndian.Uint32(data[callAt:callAt+4]), binary.LittleEndian.Uint32(data[callAt+4:callAt+8])
		hi := int64(int32(auipc&0xfffff000)) >> 12
		lo := int64(int32(jalr) >> 20)
		if got := int64(file.Entry) + int64(callAt) + hi<<12 + lo; got != int64(addr["oak_main"]) {
			t.Fatalf("%s: the start stub calls %#x, oak_main is at %#x", o.OS, got, addr["oak_main"])
		}
		if file.Entry != o.base() {
			t.Fatalf("%s: entry %#x is not the load address %#x", o.OS, file.Entry, o.base())
		}
		if eflags := binary.LittleEndian.Uint32(image[48:52]); o.OS == OSLinux && eflags&0x6 != 0x4 {
			t.Fatalf("linux executable e_flags %#x, want lp64d", eflags)
		}
	}
	// An undefined callee is refused.
	if _, err := WriteExecutable(encoded[1:], ExecutableOptions{OS: OSLinux, Arch: ArchRV64, Entry: "oak_main"}); err == nil {
		t.Fatal("an executable with an undefined symbol was written")
	}
}

func TestWriteExecutableArm64(t *testing.T) {
	unit, errs := ParseUnit("main.arm64.oakasm", "oak_main: () -> i32 = {\n  movz w0, #42\n  ret\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	encoded, err := EncodeFunctions(unit.Functions, func(s string) string { return s })
	if err != nil {
		t.Fatal(err)
	}
	for _, o := range []ExecutableOptions{{OS: OSLinux, Arch: ArchArm64, Entry: "oak_main"}, {OS: OSFreestanding, Arch: ArchArm64, Entry: "oak_main"}} {
		image, err := WriteExecutable(encoded, o)
		if err != nil {
			t.Fatalf("%s: %v", o.OS, err)
		}
		file, err := elf.NewFile(bytes.NewReader(image))
		if err != nil {
			t.Fatal(err)
		}
		if file.Machine != elf.EM_AARCH64 || file.Type != elf.ET_EXEC {
			t.Fatalf("%s: machine %v type %v", o.OS, file.Machine, file.Type)
		}
		symbols, _ := file.Symbols()
		addr := map[string]uint64{}
		for _, s := range symbols {
			addr[s.Name] = s.Value
		}
		text, _ := file.Section(".text").Data()
		// The stub's bl: the first word on Linux; after the FP/SIMD enable
		// (mrs, orr, msr, isb) and the stack setup on the freestanding board.
		blAt := 0
		if o.OS == OSFreestanding {
			blAt = 24
		}
		bl := binary.LittleEndian.Uint32(text[blAt : blAt+4])
		if bl>>26 != 0x25 {
			t.Fatalf("%s: word %#x at %d is not bl", o.OS, bl, blAt)
		}
		delta := int64(int32(bl<<6)>>6) * 4
		if got := int64(file.Entry) + int64(blAt) + delta; got != int64(addr["oak_main"]) {
			t.Fatalf("%s: the start stub calls %#x, oak_main is at %#x", o.OS, got, addr["oak_main"])
		}
	}
}
