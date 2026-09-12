package asm

import (
	"encoding/binary"
	"fmt"
	"sort"
	"strings"
)

// Relocatable object emission (docs/spec/94-assembler.md §9): the encoded
// functions of a compilation's asm units as a Mach-O (arm64) or ELF
// (AArch64) object the system linker joins with the compiled C. The
// object's bytes are the encoder's — no toolchain assembler is involved.
//
// Every offset and count is computed from the encoded bytes and checked
// against the fields that carry it; a function or table too large for a
// field is an error, never a truncated file.

// ObjectFormat selects the container.
type ObjectFormat int

const (
	// MachO is the macOS relocatable object (MH_OBJECT, CPU_TYPE_ARM64).
	MachO ObjectFormat = iota
	// ELF is the ELF64 relocatable object (ET_REL, EM_AARCH64).
	ELF
)

// EncodedFunction is one function's machine code under its C symbol
// (without the platform's user-label prefix), with the relocations that
// refer to other symbols.
type EncodedFunction struct {
	Symbol string
	Bytes  []byte
	Relocs []Relocation // Symbol fields already carry C symbol names
	Align  int64        // entry alignment in bytes (0 = 4)
	Arch   string       // the lane; every function of an object shares it
}

// EncodeFunctions encodes checked functions for an object; symbolFor maps
// an Oak function name to its C symbol (the emitter's mangling), for the
// functions themselves and for the symbols their calls reference.
func EncodeFunctions(functions []*Function, symbolFor func(string) string) ([]EncodedFunction, error) {
	var out []EncodedFunction
	for _, fn := range functions {
		code, relocs, err := EncodeFunction(fn)
		if err != nil {
			return nil, err
		}
		for i := range relocs {
			relocs[i].Symbol = symbolFor(relocs[i].Symbol)
		}
		out = append(out, EncodedFunction{Symbol: symbolFor(fn.Name), Bytes: code, Relocs: relocs, Align: fn.Align, Arch: fn.Arch})
	}
	return out, nil
}

// WriteObject lays the functions out in one text section, in order, each
// at its entry alignment, and writes the object in the given format.
func WriteObject(format ObjectFormat, functions []EncodedFunction) ([]byte, error) {
	layout, err := layOut(functions)
	if err != nil {
		return nil, err
	}
	switch format {
	case MachO:
		if layout.arch == ArchRV64 {
			return nil, fmt.Errorf("object: rv64 units are written as ELF (EM_RISCV), not Mach-O")
		}
		return writeMachO(layout)
	case ELF:
		return writeELF(layout)
	}
	return nil, fmt.Errorf("object format %d", format)
}

// textLayout is the text section with symbol offsets and relocations.
type textLayout struct {
	arch      string // ArchArm64 or ArchRV64
	text      []byte
	align     int64 // section alignment in bytes
	defined   []definedSymbol
	relocs    []placedReloc
	undefined []string // referenced symbols not defined here, sorted
}

type definedSymbol struct {
	name   string
	offset int64
	size   int64
}

type placedReloc struct {
	offset int64 // within the text section
	kind   string
	symbol string
}

func layOut(functions []EncodedFunction) (*textLayout, error) {
	l := &textLayout{align: 4, arch: ArchArm64}
	defined := map[string]bool{}
	referenced := map[string]bool{}
	for i, fn := range functions {
		if fn.Symbol == "" {
			return nil, fmt.Errorf("object: a function without a symbol")
		}
		arch := fn.Arch
		if arch == "" {
			arch = ArchArm64
		}
		if i == 0 {
			l.arch = arch
		} else if arch != l.arch {
			return nil, fmt.Errorf("object: function %s is %s, but the object is %s (one lane per object)", fn.Symbol, arch, l.arch)
		}
		if defined[fn.Symbol] {
			return nil, fmt.Errorf("object: symbol %s defined twice", fn.Symbol)
		}
		defined[fn.Symbol] = true
		align := fn.Align
		if align <= 0 {
			align = 4
		}
		if align&(align-1) != 0 {
			return nil, fmt.Errorf("object: %s: alignment %d is not a power of two", fn.Symbol, align)
		}
		if align > l.align {
			l.align = align
		}
		for int64(len(l.text))%align != 0 {
			l.text = append(l.text, 0x1f, 0x20, 0x03, 0xd5) // nop padding
		}
		start := int64(len(l.text))
		l.text = append(l.text, fn.Bytes...)
		l.defined = append(l.defined, definedSymbol{name: fn.Symbol, offset: start, size: int64(len(fn.Bytes))})
		for _, r := range fn.Relocs {
			if int64(r.Offset) < 0 || int64(r.Offset)+4 > int64(len(fn.Bytes)) {
				return nil, fmt.Errorf("object: %s: relocation at %d outside the function", fn.Symbol, r.Offset)
			}
			l.relocs = append(l.relocs, placedReloc{offset: start + int64(r.Offset), kind: r.Kind, symbol: r.Symbol})
			referenced[r.Symbol] = true
		}
	}
	for name := range referenced {
		if !defined[name] {
			l.undefined = append(l.undefined, name)
		}
	}
	sort.Strings(l.undefined)
	if int64(len(l.text)) > 1<<30 {
		return nil, fmt.Errorf("object: text section of %d bytes exceeds the format's reach", len(l.text))
	}
	return l, nil
}

func log2Align(n int64) uint32 {
	var v uint32
	for n > 1 {
		n >>= 1
		v++
	}
	return v
}

// ---- Mach-O ---------------------------------------------------------------------

func writeMachO(l *textLayout) ([]byte, error) {
	const (
		headerSize    = 32
		segmentSize   = 72 + 80 // LC_SEGMENT_64 with one section_64
		buildVersion  = 24
		symtabCmdSize = 24
	)
	// Symbols: the defined functions, then the undefined references; every
	// name carries the Mach-O user-label prefix.
	type nlist struct {
		name  string
		typ   uint8
		sect  uint8
		value uint64
	}
	var symbols []nlist
	index := map[string]uint32{}
	for _, d := range l.defined {
		index[d.name] = uint32(len(symbols))
		symbols = append(symbols, nlist{name: "_" + d.name, typ: 0x0f /* N_SECT|N_EXT */, sect: 1, value: uint64(d.offset)})
	}
	for _, u := range l.undefined {
		index[u] = uint32(len(symbols))
		symbols = append(symbols, nlist{name: "_" + u, typ: 0x01 /* N_UNDF|N_EXT */})
	}
	if len(symbols) >= 1<<24 {
		return nil, fmt.Errorf("object: %d symbols exceed the relocation index", len(symbols))
	}
	// String table: index 0 is the empty string.
	strtab := []byte{0}
	strIndex := make([]uint32, len(symbols))
	for i, s := range symbols {
		strIndex[i] = uint32(len(strtab))
		strtab = append(strtab, []byte(s.name)...)
		strtab = append(strtab, 0)
	}
	for len(strtab)%8 != 0 {
		strtab = append(strtab, 0)
	}
	// Relocation entries.
	type relocEntry struct {
		address uint32
		info    uint32
	}
	var relocs []relocEntry
	for _, r := range l.relocs {
		var typ, pcrel uint32 = 0, 1
		switch r.kind {
		case "call26", "jump26", "branch26":
			typ = 2 // ARM64_RELOC_BRANCH26
		case "adr21", "adrp21":
			typ = 3 // ARM64_RELOC_PAGE21 (adr uses the same page-relative form only for adrp; plain adr to an external symbol is not expressible)
			if r.kind == "adr21" {
				return nil, fmt.Errorf("object: adr to external symbol %s has no Mach-O relocation (use adrp/add)", r.symbol)
			}
		default:
			return nil, fmt.Errorf("object: %s to external symbol %s has no Mach-O relocation (conditional branches and bit tests reach only labels within the function)", r.kind, r.symbol)
		}
		if r.offset >= 1<<31 {
			return nil, fmt.Errorf("object: relocation offset %d exceeds the field", r.offset)
		}
		symbol := index[r.symbol]
		// r_symbolnum:24 | r_pcrel:1 | r_length:2 | r_extern:1 | r_type:4
		info := symbol | pcrel<<24 | 2<<25 | 1<<27 | typ<<28
		relocs = append(relocs, relocEntry{address: uint32(r.offset), info: info})
	}
	// File layout: header, load commands, text (padded), relocations,
	// symbol table, string table.
	ncmds := 3
	sizeofcmds := segmentSize + buildVersion + symtabCmdSize
	textOff := headerSize + sizeofcmds
	for textOff%int(l.align) != 0 {
		textOff++
	}
	text := append([]byte{}, l.text...)
	for len(text)%8 != 0 {
		text = append(text, 0)
	}
	relocOff := textOff + len(text)
	symOff := relocOff + 8*len(relocs)
	strOff := symOff + 16*len(symbols)
	total := strOff + len(strtab)
	out := make([]byte, 0, total)
	le := binary.LittleEndian
	put32 := func(v uint32) { out = le.AppendUint32(out, v) }
	put64 := func(v uint64) { out = le.AppendUint64(out, v) }
	putName := func(name string) {
		buf := make([]byte, 16)
		copy(buf, name)
		out = append(out, buf...)
	}
	// mach_header_64
	put32(0xfeedfacf)
	put32(0x0100000c) // CPU_TYPE_ARM64
	put32(0)          // CPU_SUBTYPE_ARM64_ALL
	put32(1)          // MH_OBJECT
	put32(uint32(ncmds))
	put32(uint32(sizeofcmds))
	put32(0x2000) // MH_SUBSECTIONS_VIA_SYMBOLS
	put32(0)
	// LC_SEGMENT_64
	put32(0x19)
	put32(uint32(segmentSize))
	putName("")
	put64(0)                   // vmaddr
	put64(uint64(len(l.text))) // vmsize
	put64(uint64(textOff))     // fileoff
	put64(uint64(len(l.text))) // filesize
	put32(7)                   // maxprot rwx
	put32(7)                   // initprot
	put32(1)                   // nsects
	put32(0)                   // flags
	putName("__text")          // section_64
	putName("__TEXT")          //
	put64(0)                   // addr
	put64(uint64(len(l.text))) // size
	put32(uint32(textOff))     // offset
	put32(log2Align(l.align))  // align (log2)
	put32(uint32(relocOff))    // reloff
	put32(uint32(len(relocs))) // nreloc
	put32(0x80000400)          // S_REGULAR | S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS
	put32(0)                   // reserved1
	put32(0)                   // reserved2
	put32(0)                   // reserved3
	// LC_BUILD_VERSION: macOS 11.0, no tools.
	put32(0x32)
	put32(uint32(buildVersion))
	put32(1)        // PLATFORM_MACOS
	put32(11 << 16) // minos 11.0.0
	put32(0)        // sdk
	put32(0)        // ntools
	// LC_SYMTAB
	put32(0x2)
	put32(uint32(symtabCmdSize))
	put32(uint32(symOff))
	put32(uint32(len(symbols)))
	put32(uint32(strOff))
	put32(uint32(len(strtab)))
	for len(out) < textOff {
		out = append(out, 0)
	}
	out = append(out, text...)
	for _, r := range relocs {
		put32(r.address)
		put32(r.info)
	}
	for i, s := range symbols {
		put32(strIndex[i])
		out = append(out, s.typ, s.sect)
		out = le.AppendUint16(out, 0) // n_desc
		put64(s.value)
	}
	out = append(out, strtab...)
	if len(out) != total {
		return nil, fmt.Errorf("object: Mach-O layout wrote %d bytes, planned %d", len(out), total)
	}
	return out, nil
}

// ---- ELF ------------------------------------------------------------------------

func writeELF(l *textLayout) ([]byte, error) {
	le := binary.LittleEndian
	// Symbols: null, the .text section symbol, the defined functions
	// (global), then the undefined references.
	type elfSym struct {
		name  string
		info  uint8
		shndx uint16
		value uint64
		size  uint64
	}
	symbols := []elfSym{{}, {info: 0x03 /* STT_SECTION, local */, shndx: 1}}
	index := map[string]uint32{}
	firstGlobal := uint32(len(symbols))
	for _, d := range l.defined {
		index[d.name] = uint32(len(symbols))
		symbols = append(symbols, elfSym{name: d.name, info: 0x12 /* GLOBAL FUNC */, shndx: 1, value: uint64(d.offset), size: uint64(d.size)})
	}
	for _, u := range l.undefined {
		index[u] = uint32(len(symbols))
		symbols = append(symbols, elfSym{name: u, info: 0x10 /* GLOBAL NOTYPE */})
	}
	strtab := []byte{0}
	strIndex := make([]uint32, len(symbols))
	for i, s := range symbols {
		if s.name == "" {
			continue
		}
		strIndex[i] = uint32(len(strtab))
		strtab = append(strtab, []byte(s.name)...)
		strtab = append(strtab, 0)
	}
	// Relocations.
	type rela struct {
		offset uint64
		info   uint64
	}
	var relas []rela
	for _, r := range l.relocs {
		var typ uint64
		switch r.kind {
		case "call26":
			typ = 283 // R_AARCH64_CALL26
		case "jump26", "branch26":
			typ = 282 // R_AARCH64_JUMP26
		case "condbr19":
			typ = 280 // R_AARCH64_CONDBR19
		case "tbz14":
			typ = 279 // R_AARCH64_TSTBR14
		case "adr21":
			typ = 274 // R_AARCH64_ADR_PREL_LO21
		case "adrp21":
			typ = 275 // R_AARCH64_ADR_PREL_PG_HI21
		case "riscv_call_plt":
			typ = 19 // R_RISCV_CALL_PLT: the auipc/jalr pair of `call`
		default:
			return nil, fmt.Errorf("object: relocation kind %q", r.kind)
		}
		if (l.arch == ArchRV64) != (r.kind == "riscv_call_plt") {
			return nil, fmt.Errorf("object: relocation kind %q in an %s object", r.kind, l.arch)
		}
		relas = append(relas, rela{offset: uint64(r.offset), info: uint64(index[r.symbol])<<32 | typ})
	}
	shstrtab := []byte("\x00.text\x00.rela.text\x00.symtab\x00.strtab\x00.shstrtab\x00")
	nameOff := func(name string) uint32 {
		return uint32(strings.Index(string(shstrtab), "\x00"+name+"\x00") + 1)
	}
	// Layout: header, .text, .rela.text, .symtab, .strtab, .shstrtab, section headers.
	off := 64
	align := func(n, to int) int {
		for n%to != 0 {
			n++
		}
		return n
	}
	textOff := align(off, int(l.align))
	relaOff := align(textOff+len(l.text), 8)
	symOff := align(relaOff+24*len(relas), 8)
	strOff := symOff + 24*len(symbols)
	shstrOff := strOff + len(strtab)
	shOff := align(shstrOff+len(shstrtab), 8)
	total := shOff + 64*6
	out := make([]byte, 0, total)
	put16 := func(v uint16) { out = le.AppendUint16(out, v) }
	put32 := func(v uint32) { out = le.AppendUint32(out, v) }
	put64 := func(v uint64) { out = le.AppendUint64(out, v) }
	// ELF header.
	out = append(out, 0x7f, 'E', 'L', 'F', 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0)
	put16(1) // ET_REL
	if l.arch == ArchRV64 {
		put16(243) // EM_RISCV; e_flags 0 below is the LP64 soft-float ABI without RVC
	} else {
		put16(183) // EM_AARCH64
	}
	put32(1)
	put64(0) // entry
	put64(0) // phoff
	put64(uint64(shOff))
	put32(0)  // flags
	put16(64) // ehsize
	put16(0)  // phentsize
	put16(0)  // phnum
	put16(64) // shentsize
	put16(6)  // shnum
	put16(5)  // shstrndx
	pad := func(to int) {
		for len(out) < to {
			out = append(out, 0)
		}
	}
	pad(textOff)
	out = append(out, l.text...)
	pad(relaOff)
	for _, r := range relas {
		put64(r.offset)
		put64(r.info)
		put64(0) // addend
	}
	pad(symOff)
	for i, s := range symbols {
		put32(strIndex[i])
		out = append(out, s.info, 0)
		put16(s.shndx)
		put64(s.value)
		put64(s.size)
	}
	out = append(out, strtab...)
	out = append(out, shstrtab...)
	pad(shOff)
	section := func(name uint32, typ, flags uint32, off, size, link, info, addralign, entsize uint64) {
		put32(name)
		put32(typ)
		put64(uint64(flags))
		put64(0) // addr
		put64(off)
		put64(size)
		put32(uint32(link))
		put32(uint32(info))
		put64(addralign)
		put64(entsize)
	}
	section(0, 0, 0, 0, 0, 0, 0, 0, 0)
	section(nameOff(".text"), 1, 0x6, uint64(textOff), uint64(len(l.text)), 0, 0, uint64(l.align), 0)
	section(nameOff(".rela.text"), 4, 0x40, uint64(relaOff), uint64(24*len(relas)), 3, 1, 8, 24)
	section(nameOff(".symtab"), 2, 0, uint64(symOff), uint64(24*len(symbols)), 4, uint64(firstGlobal), 8, 24)
	section(nameOff(".strtab"), 3, 0, uint64(strOff), uint64(len(strtab)), 0, 0, 1, 0)
	section(nameOff(".shstrtab"), 3, 0, uint64(shstrOff), uint64(len(shstrtab)), 0, 0, 1, 0)
	if len(out) != total {
		return nil, fmt.Errorf("object: ELF layout wrote %d bytes, planned %d", len(out), total)
	}
	return out, nil
}
