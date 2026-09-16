package asm

import (
	"encoding/binary"
	"fmt"
	"sort"
)

// Executable emission (docs/spec/94-assembler.md §9): a program whose every
// body the native backend lowered links into a final ELF64 executable
// here, with no system linker and no C toolchain. The encoded functions
// are laid out after a `_start` stub — assembled from `.oakasm` text by
// this package's own parser and encoder — at the target's load address;
// the calls between them, which the object writer would have handed to a
// linker as relocations, are resolved by patching the branch words with
// range checks; one read-and-execute segment carries the headers and the
// text; the entry is the stub. Every offset and count is computed from the
// bytes and checked against the field that carries it, and a relocation
// the writer cannot resolve is an error, never a silently wrong word.
//
// The stub is the program's whole runtime: on Linux it calls the entry
// symbol and leaves through the exit system call with its result; on the
// freestanding targets it sets the stack pointer, calls the entry symbol,
// and reports the result to the machine — the sifive_test finisher on
// RISC-V's virt board, semihosting SYS_EXIT on AArch64's — so an emulator
// exits with the program's code. A trap (`brk`/`ebreak` from a failed
// guard) has no handler: the machine stops there.

// ExecutableOptions are the target facts the executable records.
type ExecutableOptions struct {
	// OS is "linux" or "freestanding"; Arch the lane (ArchArm64, ArchRV64).
	OS, Arch string
	// Entry is the C symbol the stub calls: the program's main.
	Entry string
	// Base is the load address; 0 takes the target's default (0x10000 on
	// Linux, RAM's start on the freestanding boards: 0x80000000 for the
	// RISC-V virt machine, 0x40000000 for the AArch64 one).
	Base uint64
	// StackTop is the freestanding stub's initial sp, a multiple of
	// 65536; 0 takes Base + 1 MiB.
	StackTop uint64
	// Data are the program's constant data symbols, placed read-only after
	// the text in the one loaded segment (ObjectOptions.Data).
	Data []DataSymbol
	// RV64FloatABI is the e_flags float ABI, as ObjectOptions spells it.
	RV64FloatABI string
}

const (
	OSLinux        = "linux"
	OSFreestanding = "freestanding"
)

func (o ExecutableOptions) base() uint64 {
	if o.Base != 0 {
		return o.Base
	}
	switch {
	case o.OS == OSLinux:
		return 0x10000
	case o.Arch == ArchRV64:
		return 0x80000000
	default:
		return 0x40000000
	}
}

func (o ExecutableOptions) stackTop() uint64 {
	if o.StackTop != 0 {
		return o.StackTop
	}
	return o.base() + 1<<20
}

// startStub is the `_start` of a target, as `.oakasm` text.
func startStub(o ExecutableOptions) (string, error) {
	entry := o.Entry
	switch {
	case o.OS == OSLinux && o.Arch == ArchRV64:
		// exit(a0): the result is already in a0.
		return fmt.Sprintf("start: () -> () = {\n  call %s\n  li a7, 93\n  ecall\n}\n", entry), nil
	case o.OS == OSLinux && o.Arch == ArchArm64:
		return fmt.Sprintf("start: () -> () = {\n  bl %s\n  movz w8, #93\n  svc #0\n}\n", entry), nil
	case o.OS == OSFreestanding && o.Arch == ArchRV64:
		top := o.stackTop()
		if top%65536 != 0 || top>>16 > 0x7fff_ffff {
			return "", fmt.Errorf("executable: the stack top %#x is not a multiple of 65536 below 2^47", top)
		}
		// The sifive_test finisher at 0x100000: PASS (0x5555) exits 0,
		// FAIL (0x3333 with the code above bit 16) exits with the code.
		return fmt.Sprintf(`start: () -> () = {
  li t0, %d
  slli sp, t0, 16
  call %s
  lui t1, 256
  beqz a0, pass
  slli t0, a0, 16
  lui t2, 3
  addi t2, t2, 819
  or t0, t0, t2
  sw t0, 0(t1)
  j spin
pass:
  lui t0, 5
  addi t0, t0, 1365
  sw t0, 0(t1)
spin:
  j spin
}
`, top>>16, entry), nil
	case o.OS == OSFreestanding && o.Arch == ArchArm64:
		top := o.stackTop()
		if top%65536 != 0 || top>>16 > 0xffff {
			return "", fmt.Errorf("executable: the stack top %#x is not a multiple of 65536 below 2^32", top)
		}
		// The FP/SIMD unit is off at reset (CPACR_EL1.FPEN = 0b00): a
		// program whose reductions run in vector lanes (§9 "Reduction
		// vectorization") would take an undefined-instruction trap the
		// stub has no handler for. FPEN = 0b11 (bits 20–21) enables it at
		// EL1 and EL0; the `isb` makes the write visible to what follows.
		// Semihosting SYS_EXIT (0x18) with the parameter block
		// {ADP_Stopped_ApplicationExit, code} on the stack: the emulator
		// exits with the code.
		return fmt.Sprintf(`start: () -> () = {
  system
  mrs x9, cpacr_el1
  orr x9, x9, #3145728
  msr cpacr_el1, x9
  isb
  movz x9, #%d, lsl #16
  add sp, x9, #0
  bl %s
  sub sp, sp, #16
  movz x2, #38
  movk x2, #2, lsl #16
  str x2, [sp]
  str x0, [sp, #8]
  add x1, sp, #0
  movz w0, #24
  hlt #61440
}
`, top>>16, entry), nil
	}
	return "", fmt.Errorf("executable: no start stub for %s/%s", o.OS, o.Arch)
}

// encodeStart assembles the start stub of a target into an encoded
// function named _start.
func encodeStart(o ExecutableOptions) (EncodedFunction, error) {
	text, err := startStub(o)
	if err != nil {
		return EncodedFunction{}, err
	}
	unit, errs := ParseUnit("_start."+o.Arch+".oakasm", text)
	if len(errs) != 0 || unit == nil || len(unit.Functions) != 1 {
		return EncodedFunction{}, fmt.Errorf("executable: the start stub does not parse: %v", errs)
	}
	fn := unit.Functions[0]
	code, relocs, err := EncodeFunction(fn)
	if err != nil {
		return EncodedFunction{}, fmt.Errorf("executable: the start stub does not encode: %v", err)
	}
	return EncodedFunction{Symbol: "_start", Bytes: code, Relocs: relocs, Align: 4, Arch: o.Arch}, nil
}

// WriteExecutable links the encoded functions of a compilation with the
// target's start stub into a static ELF64 executable.
func WriteExecutable(functions []EncodedFunction, o ExecutableOptions) ([]byte, error) {
	if o.Arch != ArchArm64 && o.Arch != ArchRV64 {
		return nil, fmt.Errorf("executable: no lane %q", o.Arch)
	}
	if o.Entry == "" {
		return nil, fmt.Errorf("executable: no entry symbol")
	}
	start, err := encodeStart(o)
	if err != nil {
		return nil, err
	}
	all := append([]EncodedFunction{start}, functions...)
	for _, fn := range functions {
		if fn.Arch != o.Arch && !(fn.Arch == "" && o.Arch == ArchArm64) {
			return nil, fmt.Errorf("executable: %s is %s code in a %s executable", fn.Symbol, fn.Arch, o.Arch)
		}
	}
	layout, err := layOut(all)
	if err != nil {
		return nil, err
	}
	if err := layout.addData(o.Data); err != nil {
		return nil, err
	}
	if len(layout.undefined) != 0 {
		return nil, fmt.Errorf("executable: undefined symbols %v (every function the program reaches must be lowered natively)", layout.undefined)
	}
	// Layout: the ELF header (64) and one program header (56), the text on
	// the next page — loaded at the base address itself, so the entry stub
	// is the first word at the load address (the RISC-V virt board's reset
	// vector jumps to the start of RAM, not to the ELF entry) and the
	// segment's file offset is congruent to its address modulo the page —
	// then the symbol tables and section headers for tools.
	const page = 0x1000
	textOff := int64(page)
	if layout.align > page {
		return nil, fmt.Errorf("executable: a function alignment of %d exceeds the page", layout.align)
	}
	base := o.base()
	if base%page != 0 {
		return nil, fmt.Errorf("executable: the load address %#x is not page aligned", base)
	}
	textAddr := base
	symbolAddr := map[string]uint64{}
	for _, d := range layout.defined {
		symbolAddr[d.name] = textAddr + uint64(d.offset)
	}
	// The data follows the text in the segment, at its alignment (16 at
	// least, so the file offset and the address stay congruent).
	dataAlign := int64(16)
	if layout.dataAlign > dataAlign {
		dataAlign = layout.dataAlign
	}
	dataOff := textOff + int64(len(layout.text))
	for dataOff%dataAlign != 0 {
		dataOff++
	}
	dataAddr := textAddr + uint64(dataOff-textOff)
	for _, d := range layout.dataSyms {
		symbolAddr[d.name] = dataAddr + uint64(d.offset)
	}
	if err := resolveRelocations(layout, textAddr, symbolAddr); err != nil {
		return nil, err
	}
	entry, ok := symbolAddr["_start"]
	if !ok {
		return nil, fmt.Errorf("executable: no _start")
	}
	// Symbols: every function, STT_FUNC GLOBAL, sorted by address.
	defined := append([]definedSymbol(nil), layout.defined...)
	sort.Slice(defined, func(i, j int) bool { return defined[i].offset < defined[j].offset })
	strtab := []byte{0}
	type sym struct {
		name  uint32
		info  uint8
		shndx uint16
		value uint64
		size  uint64
	}
	symbols := []sym{{}}
	for _, d := range defined {
		symbols = append(symbols, sym{name: uint32(len(strtab)), info: 0x12 /* GLOBAL FUNC */, shndx: 1, value: textAddr + uint64(d.offset), size: uint64(d.size)})
		strtab = append(strtab, d.name...)
		strtab = append(strtab, 0)
	}
	for _, d := range layout.dataSyms {
		symbols = append(symbols, sym{name: uint32(len(strtab)), info: 0x11 /* GLOBAL OBJECT */, shndx: 2, value: dataAddr + uint64(d.offset), size: uint64(d.size)})
		strtab = append(strtab, d.name...)
		strtab = append(strtab, 0)
	}
	shstrtab := []byte("\x00.text\x00.rodata\x00.symtab\x00.strtab\x00.shstrtab\x00")
	nameOff := func(name string) uint32 {
		if name == "" {
			return 0
		}
		for i := 0; i+len(name)+1 < len(shstrtab); i++ {
			if shstrtab[i] == 0 && string(shstrtab[i+1:i+1+len(name)]) == name && shstrtab[i+1+len(name)] == 0 {
				return uint32(i + 1)
			}
		}
		return 0
	}
	align := func(n, to int64) int64 {
		for n%to != 0 {
			n++
		}
		return n
	}
	dataEnd := dataOff + int64(len(layout.data))
	symOff := align(dataEnd, 8)
	strOff := symOff + 24*int64(len(symbols))
	shstrOff := strOff + int64(len(strtab))
	shOff := align(shstrOff+int64(len(shstrtab)), 8)
	total := shOff + 64*6
	if total > 1<<31 {
		return nil, fmt.Errorf("executable: %d bytes exceed the writer's reach", total)
	}
	out := make([]byte, 0, total)
	le := binary.LittleEndian
	put8 := func(v uint8) { out = append(out, v) }
	put16 := func(v uint16) { out = le.AppendUint16(out, v) }
	put32 := func(v uint32) { out = le.AppendUint32(out, v) }
	put64 := func(v uint64) { out = le.AppendUint64(out, v) }
	pad := func(to int64) {
		for int64(len(out)) < to {
			out = append(out, 0)
		}
	}
	// ELF header.
	out = append(out, 0x7f, 'E', 'L', 'F', 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0)
	put16(2) // ET_EXEC
	machine, flags := uint16(183), uint32(0)
	if o.Arch == ArchRV64 {
		machine = 243
		switch o.RV64FloatABI {
		case "double":
			flags = 0x4
		case "soft", "":
		default:
			return nil, fmt.Errorf("executable: RISC-V float ABI %q", o.RV64FloatABI)
		}
	}
	put16(machine)
	put32(1)
	put64(entry)
	put64(64)            // phoff
	put64(uint64(shOff)) // shoff
	put32(flags)
	put16(64) // ehsize
	put16(56) // phentsize
	put16(1)  // phnum
	put16(64) // shentsize
	put16(6)  // shnum
	put16(5)  // shstrndx
	// The one PT_LOAD: the text and the data after it, read and execute,
	// at the load address.
	put32(1)                         // PT_LOAD
	put32(5)                         // PF_R | PF_X
	put64(uint64(textOff))           // offset
	put64(base)                      // vaddr
	put64(base)                      // paddr
	put64(uint64(dataEnd - textOff)) // filesz
	put64(uint64(dataEnd - textOff)) // memsz
	put64(page)                      // align
	pad(textOff)
	out = append(out, layout.text...)
	pad(dataOff)
	out = append(out, layout.data...)
	pad(symOff)
	for _, s := range symbols {
		put32(s.name)
		put8(s.info)
		put8(0)
		put16(s.shndx)
		put64(s.value)
		put64(s.size)
	}
	out = append(out, strtab...)
	out = append(out, shstrtab...)
	pad(shOff)
	section := func(name string, typ uint32, flags, addr, off, size uint64, link, info uint32, addralign, entsize uint64) {
		put32(nameOff(name))
		put32(typ)
		put64(flags)
		put64(addr)
		put64(off)
		put64(size)
		put32(link)
		put32(info)
		put64(addralign)
		put64(entsize)
	}
	section("", 0, 0, 0, 0, 0, 0, 0, 0, 0)
	section(".text", 1, 6 /* ALLOC|EXECINSTR */, textAddr, uint64(textOff), uint64(len(layout.text)), 0, 0, uint64(layout.align), 0)
	section(".rodata", 1, 2 /* ALLOC */, dataAddr, uint64(dataOff), uint64(len(layout.data)), 0, 0, uint64(dataAlign), 0)
	section(".symtab", 2, 0, 0, uint64(symOff), uint64(24*len(symbols)), 4, 1, 8, 24)
	section(".strtab", 3, 0, 0, uint64(strOff), uint64(len(strtab)), 0, 0, 1, 0)
	section(".shstrtab", 3, 0, 0, uint64(shstrOff), uint64(len(shstrtab)), 0, 0, 1, 0)
	if int64(len(out)) != total {
		return nil, fmt.Errorf("executable: wrote %d bytes, laid out %d", len(out), total)
	}
	return out, nil
}

// resolveRelocations patches every cross-function reference in the text
// with the displacement its symbol's address implies, checking the range
// each encoding reaches.
func resolveRelocations(l *textLayout, textAddr uint64, symbolAddr map[string]uint64) error {
	le := binary.LittleEndian
	for _, r := range l.relocs {
		target, defined := symbolAddr[r.symbol]
		if !defined {
			return fmt.Errorf("executable: undefined symbol %s", r.symbol)
		}
		if r.offset < 0 || len(l.text) < 4 || r.offset > int64(len(l.text)-4) {
			return fmt.Errorf("executable: relocation at %d outside the text", r.offset)
		}
		switch r.kind {
		case "call26", "jump26", "branch26":
			offset := uint64(r.offset)
			if textAddr > ^uint64(0)-offset {
				return fmt.Errorf("executable: relocation address %#x + %d overflows", textAddr, r.offset)
			}
			place := textAddr + offset
			original := le.Uint32(l.text[r.offset:])
			patched, err := patchAArch64Branch26(r.kind, original, place, target)
			if err != nil {
				return fmt.Errorf("executable: %s to %s: %w", r.kind, r.symbol, err)
			}
			le.PutUint32(l.text[r.offset:], patched)
		case "condbr19":
			place := textAddr + uint64(r.offset)
			delta := int64(target) - int64(place)
			if delta%4 != 0 || delta < -(1<<20) || delta >= 1<<20 {
				return fmt.Errorf("executable: %s to %s at %#x is %d bytes away, beyond the 19-bit branch", r.kind, r.symbol, place, delta)
			}
			word := le.Uint32(l.text[r.offset:])
			word = word&^(0x7ffff<<5) | (uint32(delta>>2)&0x7ffff)<<5
			le.PutUint32(l.text[r.offset:], word)
		case "adrl21":
			place := textAddr + uint64(r.offset)
			// adrp xR, page(sym) - page(place); add xR, xR, #lo12(sym).
			if len(l.text) < 8 || r.offset > int64(len(l.text)-8) {
				return fmt.Errorf("executable: an adrl at %d cut short", r.offset)
			}
			pageDelta := (int64(target) >> 12) - (int64(place) >> 12)
			if pageDelta < -(1<<20) || pageDelta >= 1<<20 {
				return fmt.Errorf("executable: adrl to %s at %#x is %d pages away, beyond adrp's reach", r.symbol, place, pageDelta)
			}
			adrp := le.Uint32(l.text[r.offset:])
			adrp = adrp&^(0x3<<29|0x7ffff<<5) | uint32(pageDelta&0x3)<<29 | uint32((pageDelta>>2)&0x7ffff)<<5
			add := le.Uint32(l.text[r.offset+4:])
			add = add&^(0xfff<<10) | uint32(target&0xfff)<<10
			le.PutUint32(l.text[r.offset:], adrp)
			le.PutUint32(l.text[r.offset+4:], add)
		case "riscv_pcrel":
			place := textAddr + uint64(r.offset)
			delta := int64(target) - int64(place)
			// auipc rd, hi20 then addi rd, rd, lo12: the same split as a call's.
			if len(l.text) < 8 || r.offset > int64(len(l.text)-8) {
				return fmt.Errorf("executable: an la at %d cut short", r.offset)
			}
			if delta < -(1<<31) || delta >= 1<<31 {
				return fmt.Errorf("executable: la of %s at %#x is %d bytes away, beyond auipc's reach", r.symbol, place, delta)
			}
			hi := (delta + 0x800) >> 12
			lo := delta - hi<<12
			auipc := le.Uint32(l.text[r.offset:])
			addi := le.Uint32(l.text[r.offset+4:])
			auipc = auipc&0xfff | uint32(hi&0xfffff)<<12
			addi = addi&0x000fffff | uint32(lo&0xfff)<<20
			le.PutUint32(l.text[r.offset:], auipc)
			le.PutUint32(l.text[r.offset+4:], addi)
		case "riscv_call_plt":
			place := textAddr + uint64(r.offset)
			delta := int64(target) - int64(place)
			// auipc ra, hi20 then jalr ra, lo12(ra): hi rounds so lo is a
			// signed 12-bit remainder.
			if len(l.text) < 8 || r.offset > int64(len(l.text)-8) {
				return fmt.Errorf("executable: a call at %d cut short", r.offset)
			}
			if delta < -(1<<31) || delta >= 1<<31 {
				return fmt.Errorf("executable: call to %s at %#x is %d bytes away, beyond auipc's reach", r.symbol, place, delta)
			}
			hi := (delta + 0x800) >> 12
			lo := delta - hi<<12
			auipc := le.Uint32(l.text[r.offset:])
			jalr := le.Uint32(l.text[r.offset+4:])
			auipc = auipc&0xfff | uint32(hi&0xfffff)<<12
			jalr = jalr&0x000fffff | uint32(lo&0xfff)<<20
			le.PutUint32(l.text[r.offset:], auipc)
			le.PutUint32(l.text[r.offset+4:], jalr)
		default:
			return fmt.Errorf("executable: relocation kind %q to %s cannot be resolved by the executable writer", r.kind, r.symbol)
		}
	}
	return nil
}
