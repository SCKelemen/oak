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
	// Compressed marks an rv64 function encoded under option rvc: the ELF
	// header flags EF_RISCV_RVC so the linker and loader expect 16-bit
	// instructions.
	Compressed bool
	Arch       string // the lane; every function of an object shares it
}

// AddressedGlobals names every global the functions address
// (Function.Globals), for the symbol mapping of the object they encode to.
func AddressedGlobals(functions []*Function) map[string]bool {
	names := map[string]bool{}
	for _, fn := range functions {
		for name := range fn.Globals {
			names[name] = true
		}
	}
	return names
}

// DataSymbol is one constant data object of the program — a constant
// table the native backend reads through `adrl`/`la` — placed in the
// object's read-only data under its symbol (docs/spec/94-assembler.md §9).
type DataSymbol struct {
	Name  string
	Bytes []byte
	Align int64 // 0 = 1
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
		out = append(out, EncodedFunction{Symbol: symbolFor(fn.Name), Bytes: code, Relocs: relocs, Align: fn.Align, Arch: fn.Arch, Compressed: fn.Compressed})
	}
	return out, nil
}

// WriteObject lays the functions out in one text section, in order, each
// at its entry alignment, and writes the object in the given format.
func WriteObject(format ObjectFormat, functions []EncodedFunction) ([]byte, error) {
	return WriteObjectWith(format, functions, ObjectOptions{})
}

// ObjectOptions are the target facts an object records beyond its machine.
type ObjectOptions struct {
	// RV64FloatABI is the RISC-V floating-point calling convention the
	// object declares in e_flags: "" or "soft" (lp64: EF_RISCV_FLOAT_ABI_SOFT,
	// the bare-metal rv64im toolchains), "double" (lp64d: the Linux
	// distributions' and musl's rv64gc). The units carry no floating-point
	// arguments in this increment, so the declaration only has to agree
	// with what the object links against — a linker refuses to mix them.
	RV64FloatABI string
	// Data are the program's constant data symbols, placed in a read-only
	// data section after the text; relocations of kind adrl21 (AArch64)
	// and riscv_pcrel (RV64) reach them.
	Data []DataSymbol
}

// WriteObjectWith is WriteObject with the target facts.
func WriteObjectWith(format ObjectFormat, functions []EncodedFunction, options ObjectOptions) ([]byte, error) {
	layout, err := layOut(functions)
	if err != nil {
		return nil, err
	}
	if err := layout.addData(options.Data); err != nil {
		return nil, err
	}
	switch options.RV64FloatABI {
	case "", "soft":
	case "double":
		layout.elfFlags = 0x0004 // EF_RISCV_FLOAT_ABI_DOUBLE
	default:
		return nil, fmt.Errorf("object: RISC-V float ABI %q (soft or double)", options.RV64FloatABI)
	}
	for _, fn := range functions {
		if fn.Compressed && fn.Arch == ArchRV64 {
			layout.elfFlags |= 0x0001 // EF_RISCV_RVC
		}
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
	elfFlags  uint32 // e_flags: the RISC-V float ABI, 0 otherwise
	text      []byte
	align     int64 // section alignment in bytes
	defined   []definedSymbol
	relocs    []placedReloc
	undefined []string // referenced symbols not defined here, sorted
	// The read-only data section: the program's constant tables, each at
	// its offset within data (addData).
	data      []byte
	dataAlign int64
	dataSyms  []definedSymbol
}

// addData lays the constant data symbols out after the text, in order,
// each at its alignment, and takes their names off the undefined list.
func (l *textLayout) addData(data []DataSymbol) error {
	l.dataAlign = 1
	names := map[string]bool{}
	for _, d := range l.defined {
		names[d.name] = true
	}
	for _, d := range data {
		if d.Name == "" {
			return fmt.Errorf("object: a data symbol without a name")
		}
		if names[d.Name] {
			return fmt.Errorf("object: symbol %s defined twice", d.Name)
		}
		names[d.Name] = true
		align := d.Align
		if align <= 0 {
			align = 1
		}
		if align&(align-1) != 0 {
			return fmt.Errorf("object: %s: alignment %d is not a power of two", d.Name, align)
		}
		if align > l.dataAlign {
			l.dataAlign = align
		}
		for int64(len(l.data))%align != 0 {
			l.data = append(l.data, 0)
		}
		l.dataSyms = append(l.dataSyms, definedSymbol{name: d.Name, offset: int64(len(l.data)), size: int64(len(d.Bytes))})
		l.data = append(l.data, d.Bytes...)
	}
	var undefined []string
	for _, name := range l.undefined {
		if !names[name] {
			undefined = append(undefined, name)
		}
	}
	l.undefined = undefined
	if int64(len(l.data)) > 1<<30 {
		return fmt.Errorf("object: data section of %d bytes exceeds the format's reach", len(l.data))
	}
	return nil
}

// rv64Reloc reports a relocation kind of the RV64 lane.
func rv64Reloc(kind string) bool { return kind == "riscv_call_plt" || kind == "riscv_pcrel" }

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
		if err := l.pad(fn.Symbol, align); err != nil {
			return nil, err
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

// pad fills the gap before the next entry with the lane's no-ops, so a
// disassembler reads the section as instructions throughout. AArch64
// instructions are one word, so the gap is always whole words. An RV64
// function under RVC (docs/spec/94-assembler.md, "Compressed encodings")
// may end on a half word, so its gap is filled in words and closed with
// one c.nop; a fixed word-sized pad would never reach the boundary
// (spec/lean/Oak/Assembler.lean, `pad_halfwords_reaches`,
// `pad_words_misses`).
func (l *textLayout) pad(symbol string, align int64) error {
	gap := (align - int64(len(l.text))%align) % align
	switch l.arch {
	case ArchRV64:
		if gap%2 != 0 {
			return fmt.Errorf("object: %s: the text before it ends on an odd byte", symbol)
		}
		for ; gap >= 4; gap -= 4 {
			l.text = append(l.text, 0x13, 0x00, 0x00, 0x00) // nop (addi x0, x0, 0)
		}
		if gap == 2 {
			l.text = append(l.text, 0x01, 0x00) // c.nop
		}
	default:
		if gap%4 != 0 {
			return fmt.Errorf("object: %s: the text before it ends inside a word", symbol)
		}
		for ; gap > 0; gap -= 4 {
			l.text = append(l.text, 0x1f, 0x20, 0x03, 0xd5) // nop
		}
	}
	return nil
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
	nsects := 1
	if len(l.data) > 0 {
		nsects = 2 // __text, then __const for the data symbols
	}
	const (
		headerSize    = 32
		buildVersion  = 24
		symtabCmdSize = 24
	)
	segmentSize := 72 + 80*nsects // LC_SEGMENT_64 with its section_64s
	// The data follows the text in the segment, at its alignment.
	dataAddr := alignUp(int64(len(l.text)), max(l.dataAlign, 1))
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
	for _, d := range l.dataSyms {
		index[d.name] = uint32(len(symbols))
		symbols = append(symbols, nlist{name: "_" + d.name, typ: 0x0f /* N_SECT|N_EXT */, sect: 2, value: uint64(dataAddr + d.offset)})
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
		case "lo12":
			typ, pcrel = 4, 0 // ARM64_RELOC_PAGEOFF12: the low 12 bits of the symbol's address into the add's imm12
		case "adrl21":
			// adrp then add: ARM64_RELOC_PAGE21 on the first word,
			// ARM64_RELOC_PAGEOFF12 (not pc-relative) on the second.
			if r.offset+8 > int64(len(l.text)) || r.offset+4 >= 1<<31 {
				return nil, fmt.Errorf("object: adrl at %d cut short", r.offset)
			}
			symbol := index[r.symbol]
			relocs = append(relocs, relocEntry{address: uint32(r.offset), info: symbol | 1<<24 | 2<<25 | 1<<27 | 3<<28})
			relocs = append(relocs, relocEntry{address: uint32(r.offset + 4), info: symbol | 0<<24 | 2<<25 | 1<<27 | 4<<28})
			continue
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
	if nsects == 2 {
		for int64(len(text)) < dataAddr {
			text = append(text, 0)
		}
		text = append(text, l.data...)
	}
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
	put64(uint64(len(text)))   // vmsize
	put64(uint64(textOff))     // fileoff
	put64(uint64(len(text)))   // filesize
	put32(7)                   // maxprot rwx
	put32(7)                   // initprot
	put32(uint32(nsects))      // nsects
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
	if nsects == 2 {
		putName("__const")                        // section_64: the constant tables
		putName("__TEXT")                         //
		put64(uint64(dataAddr))                   // addr
		put64(uint64(len(l.data)))                // size
		put32(uint32(textOff) + uint32(dataAddr)) // offset
		put32(log2Align(max(l.dataAlign, 1)))     // align (log2)
		put32(0)                                  // reloff: relocations are on __text
		put32(0)                                  // nreloc
		put32(0)                                  // S_REGULAR
		put32(0)                                  // reserved1
		put32(0)                                  // reserved2
		put32(0)                                  // reserved3
	}
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
	// Sections: 1 .text, 2 .rodata, 3 .rela.text, 4 .symtab, 5 .strtab,
	// 6 .shstrtab. Local symbols first: the two section symbols and one
	// label per `la` (its auipc), which R_RISCV_PCREL_LO12_I must name.
	symbols := []elfSym{{}, {info: 0x03 /* STT_SECTION, local */, shndx: 1}, {info: 0x03, shndx: 2}}
	index := map[string]uint32{}
	pcrelLabel := map[int64]uint32{}
	for _, r := range l.relocs {
		if r.kind == "riscv_pcrel" {
			pcrelLabel[r.offset] = uint32(len(symbols))
			symbols = append(symbols, elfSym{name: fmt.Sprintf(".Lpcrel_hi%d", r.offset), info: 0x00 /* LOCAL NOTYPE */, shndx: 1, value: uint64(r.offset)})
		}
	}
	firstGlobal := uint32(len(symbols))
	for _, d := range l.defined {
		index[d.name] = uint32(len(symbols))
		symbols = append(symbols, elfSym{name: d.name, info: 0x12 /* GLOBAL FUNC */, shndx: 1, value: uint64(d.offset), size: uint64(d.size)})
	}
	for _, d := range l.dataSyms {
		index[d.name] = uint32(len(symbols))
		symbols = append(symbols, elfSym{name: d.name, info: 0x11 /* GLOBAL OBJECT */, shndx: 2, value: uint64(d.offset), size: uint64(d.size)})
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
		case "lo12":
			typ = 277 // R_AARCH64_ADD_ABS_LO12_NC
		case "riscv_call_plt":
			typ = 19 // R_RISCV_CALL_PLT: the auipc/jalr pair of `call`
		case "adrl21":
			// adrp then add: R_AARCH64_ADR_PREL_PG_HI21 on the first word,
			// R_AARCH64_ADD_ABS_LO12_NC on the second.
			if l.arch == ArchRV64 {
				return nil, fmt.Errorf("object: relocation kind %q in an %s object", r.kind, l.arch)
			}
			relas = append(relas, rela{offset: uint64(r.offset), info: uint64(index[r.symbol])<<32 | 275})
			relas = append(relas, rela{offset: uint64(r.offset + 4), info: uint64(index[r.symbol])<<32 | 277})
			continue
		case "riscv_pcrel":
			// auipc then addi: R_RISCV_PCREL_HI20 on the auipc against the
			// symbol, R_RISCV_PCREL_LO12_I on the addi against the label
			// of the auipc, as the psABI spells the pair.
			if l.arch != ArchRV64 {
				return nil, fmt.Errorf("object: relocation kind %q in an %s object", r.kind, l.arch)
			}
			relas = append(relas, rela{offset: uint64(r.offset), info: uint64(index[r.symbol])<<32 | 23})
			relas = append(relas, rela{offset: uint64(r.offset + 4), info: uint64(pcrelLabel[r.offset])<<32 | 24})
			continue
		default:
			return nil, fmt.Errorf("object: relocation kind %q", r.kind)
		}
		if (l.arch == ArchRV64) != rv64Reloc(r.kind) {
			return nil, fmt.Errorf("object: relocation kind %q in an %s object", r.kind, l.arch)
		}
		relas = append(relas, rela{offset: uint64(r.offset), info: uint64(index[r.symbol])<<32 | typ})
	}
	shstrtab := []byte("\x00.text\x00.rodata\x00.rela.text\x00.symtab\x00.strtab\x00.shstrtab\x00")
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
	dataOff := align(textOff+len(l.text), int(max(l.dataAlign, 8)))
	relaOff := align(dataOff+len(l.data), 8)
	symOff := align(relaOff+24*len(relas), 8)
	strOff := symOff + 24*len(symbols)
	shstrOff := strOff + len(strtab)
	shOff := align(shstrOff+len(shstrtab), 8)
	total := shOff + 64*7
	out := make([]byte, 0, total)
	put16 := func(v uint16) { out = le.AppendUint16(out, v) }
	put32 := func(v uint32) { out = le.AppendUint32(out, v) }
	put64 := func(v uint64) { out = le.AppendUint64(out, v) }
	// ELF header.
	out = append(out, 0x7f, 'E', 'L', 'F', 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0)
	put16(1) // ET_REL
	if l.arch == ArchRV64 {
		put16(243) // EM_RISCV; e_flags below carries the float ABI, never RVC
	} else {
		put16(183) // EM_AARCH64
	}
	put32(1)
	put64(0) // entry
	put64(0) // phoff
	put64(uint64(shOff))
	put32(l.elfFlags) // flags: the RISC-V float ABI (ObjectOptions), 0 for AArch64
	put16(64)         // ehsize
	put16(0)          // phentsize
	put16(0)          // phnum
	put16(64)         // shentsize
	put16(7)          // shnum
	put16(6)          // shstrndx
	pad := func(to int) {
		for len(out) < to {
			out = append(out, 0)
		}
	}
	pad(textOff)
	out = append(out, l.text...)
	pad(dataOff)
	out = append(out, l.data...)
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
	section(nameOff(".rodata"), 1, 0x2, uint64(dataOff), uint64(len(l.data)), 0, 0, uint64(max(l.dataAlign, 1)), 0)
	section(nameOff(".rela.text"), 4, 0x40, uint64(relaOff), uint64(24*len(relas)), 4, 1, 8, 24)
	section(nameOff(".symtab"), 2, 0, uint64(symOff), uint64(24*len(symbols)), 5, uint64(firstGlobal), 8, 24)
	section(nameOff(".strtab"), 3, 0, uint64(strOff), uint64(len(strtab)), 0, 0, 1, 0)
	section(nameOff(".shstrtab"), 3, 0, uint64(shstrOff), uint64(len(shstrtab)), 0, 0, 1, 0)
	if len(out) != total {
		return nil, fmt.Errorf("object: ELF layout wrote %d bytes, planned %d", len(out), total)
	}
	return out, nil
}
