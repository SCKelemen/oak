package compiler

import (
	"bytes"
	"context"
	"encoding/binary"
	"fmt"
	"strings"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/bitwisecheck"
	"github.com/SCKelemen/oak/target"
)

// EmitKernelCheckedBitwiseImageBundle compiles one unchanged source snapshot to
// a complete core/wasm32 module and Linux ARM64 and RV64 executable images, then
// admits those exact four byte strings together with the independent Lean
// checker. The narrow canonical two-u32 AND/OR/XOR profile is defined by
// bitwisecheck. Compilation and intermediate object parsing confer no authority.
//
// Each target uses a fresh default Compilation. Native objects only propose a
// complete named body to the unchanged assembler executable writer: no main is
// appended, no companion C is generated, and no overlay, ABI, compression,
// assembly, rewrite, or proof-claim option can enter this API. The final images,
// including the startup stub, metadata, and padding, are independently checked.
// This separate capability does not promote legacy verdicts, verified-profile
// results, Wasm TranslationVerified, or the existing checked-object API.
//
// The caller owns installation and must Close it. Cancellation is cooperative
// between synchronous compilation, extraction, and writing stages, and is passed
// to the independent checker; emitter internals are not interruptible.
func EmitKernelCheckedBitwiseImageBundle(ctx context.Context, installation *bitwisecheck.ImageInstallation, original SourceText) Stage[*bitwisecheck.CheckedImageBundle] {
	fail := func(stage string, err error) Stage[*bitwisecheck.CheckedImageBundle] {
		return Failure[*bitwisecheck.CheckedImageBundle](fmt.Errorf("checked bitwise image bundle: %s: %w", stage, err))
	}
	if ctx == nil {
		return fail("context", fmt.Errorf("nil context"))
	}
	if err := ctx.Err(); err != nil {
		return fail("context", err)
	}
	if !installation.Valid() {
		return fail("checker", bitwisecheck.ErrInvalidInstallation)
	}
	if len(original.Text) == 0 || len(original.Text) > bitwisecheck.MaxSourceBytes {
		return fail("source", bitwisecheck.ErrBounds)
	}
	// SourceText contains immutable Go strings. Own one byte snapshot and use
	// its exact contents for every emitter and the final independent request.
	source := []byte(original.Text)
	text := string(source)
	symbol, err := checkedImageProposedSymbol(text)
	if err != nil {
		return fail("source symbol proposal", err)
	}
	wasm, err := New().WithSource(original.Path, text).
		WithTarget(target.Target{OS: target.OSCore, Arch: target.ArchWasm32}).EmitWasm().Get()
	if err != nil {
		return fail("core/wasm32 emission", err)
	}
	wasmBytes := append([]byte(nil), wasm.Bytes...)
	if err := ctx.Err(); err != nil {
		return fail("after core/wasm32 emission", err)
	}
	var images [2][]byte
	for i, arch := range []string{target.ArchArm64, target.ArchRiscv64} {
		stage := "linux/" + arch
		object, err := New().WithSource(original.Path, text).
			WithTarget(target.Target{OS: target.OSLinux, Arch: arch}).EmitNativeObject(asm.ELF).Get()
		if err != nil {
			return fail(stage+" object emission", err)
		}
		if err := ctx.Err(); err != nil {
			return fail("after "+stage+" object emission", err)
		}
		body, err := checkedImageProposeBody(object, symbol, arch)
		if err != nil {
			return fail(stage+" body proposal", err)
		}
		if err := ctx.Err(); err != nil {
			return fail("after "+stage+" body proposal", err)
		}
		image, err := asm.WriteExecutable([]asm.EncodedFunction{body}, asm.ExecutableOptions{
			OS: asm.OSLinux, Arch: body.Arch, Entry: symbol, Base: 0, RV64FloatABI: "double",
		})
		if err != nil {
			return fail(stage+" image emission", err)
		}
		images[i] = append([]byte(nil), image...)
		if err := ctx.Err(); err != nil {
			return fail("after "+stage+" image emission", err)
		}
	}
	bundle, err := installation.CheckImageBundle(ctx, source, wasmBytes, images[0], images[1])
	if err != nil {
		return fail("kernel admission", err)
	}
	if err := ctx.Err(); err != nil {
		return fail("after kernel admission", err)
	}
	if !bundle.Valid() {
		return fail("kernel admission", bitwisecheck.ErrInvalidBundle)
	}
	return Value(bundle)
}

// checkedImageProposedSymbol is intentionally not an authority-bearing source
// parser. It only proposes the initial declaration's native symbol. The Lean
// checker independently parses every byte of the unchanged original source.
func checkedImageProposedSymbol(source string) (string, error) {
	n := strings.IndexByte(source, ':')
	if n < 1 || n > 256 {
		return "", fmt.Errorf("missing or oversized initial declaration name")
	}
	for i := 0; i < n; i++ {
		c := source[i]
		if !(c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c == '_' || i != 0 && c >= '0' && c <= '9') {
			return "", fmt.Errorf("unsupported initial declaration name")
		}
	}
	return "oak_" + source[:n], nil
}

// checkedImageProposeBody is a bounded, untrusted proposal extractor for the
// production writer's narrow ET_REL shape. It deliberately does not use an ELF
// reader that can allocate or decompress from untrusted section metadata. All
// offsets are checked against the already bounded file before indexing, and no
// attacker-controlled count determines an allocation. A strict final-image
// checker remains the sole admission authority, including for these body bytes.
func checkedImageProposeBody(object []byte, symbol, arch string) (asm.EncodedFunction, error) {
	refuse := func(reason string) (asm.EncodedFunction, error) {
		return asm.EncodedFunction{}, fmt.Errorf("untrusted object proposal: %s", reason)
	}
	if len(object) < 64 || len(object) > bitwisecheck.MaxObjectBytes {
		return refuse("object bounds")
	}
	machine, flags, extent, lane := uint16(183), uint32(0), uint64(8), asm.ArchArm64
	switch arch {
	case target.ArchArm64:
	case target.ArchRiscv64:
		machine, flags, extent, lane = 243, 4, 36, asm.ArchRV64
	default:
		return refuse("unsupported target")
	}
	le := binary.LittleEndian
	if !bytes.Equal(object[:16], []byte{0x7f, 'E', 'L', 'F', 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}) ||
		le.Uint16(object[16:18]) != 1 || le.Uint16(object[18:20]) != machine || le.Uint32(object[20:24]) != 1 ||
		le.Uint64(object[24:32]) != 0 || le.Uint64(object[32:40]) != 0 || le.Uint32(object[48:52]) != flags ||
		le.Uint16(object[52:54]) != 64 || le.Uint16(object[54:56]) != 0 || le.Uint16(object[56:58]) != 0 ||
		le.Uint16(object[58:60]) != 64 || le.Uint16(object[60:62]) != 7 || le.Uint16(object[62:64]) != 6 {
		return refuse("ELF target, ABI, compression, or header mismatch")
	}
	shoff := le.Uint64(object[40:48])
	if shoff < 64 || shoff%8 != 0 || shoff > uint64(len(object)) || uint64(len(object))-shoff != 7*64 {
		return refuse("section table bounds")
	}
	type section struct {
		header []byte
		data   []byte
	}
	var sections [7]section
	end := uint64(64)
	for i := range sections {
		h := object[shoff+uint64(i)*64 : shoff+uint64(i+1)*64]
		off, size := le.Uint64(h[24:32]), le.Uint64(h[32:40])
		if i == 0 {
			if !bytes.Equal(h, make([]byte, 64)) {
				return refuse("nonempty null section")
			}
		} else {
			if off < end || off > shoff || size > shoff-off {
				return refuse("section extent or ownership")
			}
			end = off + size
		}
		sections[i] = section{h, object[off : off+size]}
	}
	// No compression, allocated data, dynamic table, additional text section,
	// or unresolved relocation is part of this proposal profile. Check flags
	// and raw extents before using any section contents.
	for i, want := range []struct {
		name                string
		typ, link, info     uint32
		flags, align, entry uint64
	}{
		{"", 0, 0, 0, 0, 0, 0},
		{".text", 1, 0, 0, 6, 4, 0},
		{".rodata", 1, 0, 0, 2, 1, 0},
		{".rela.text", 4, 4, 1, 0x40, 8, 24},
		{".symtab", 2, 5, 3, 0, 8, 24},
		{".strtab", 3, 0, 0, 0, 1, 0},
		{".shstrtab", 3, 0, 0, 0, 1, 0},
	} {
		h := sections[i].header
		name, ok := checkedImageELFString(sections[6].data, le.Uint32(h[:4]))
		if !ok || name != want.name || le.Uint32(h[4:8]) != want.typ || le.Uint64(h[8:16]) != want.flags ||
			le.Uint64(h[16:24]) != 0 || le.Uint32(h[40:44]) != want.link || le.Uint32(h[44:48]) != want.info ||
			le.Uint64(h[48:56]) != want.align || le.Uint64(h[56:64]) != want.entry {
			return refuse("section type, flags, name, or ownership mismatch")
		}
	}
	if uint64(len(sections[1].data)) != extent || len(sections[2].data) != 0 || len(sections[3].data) != 0 {
		return refuse("body extent, data, or unresolved body relocation")
	}
	syms, strtab := sections[4].data, sections[5].data
	if len(syms) != 4*24 || len(strtab) == 0 || strtab[0] != 0 {
		return refuse("missing or duplicate function symbols")
	}
	for i := 0; i < 4; i++ {
		s := syms[i*24 : (i+1)*24]
		name, ok := checkedImageELFString(strtab, le.Uint32(s[:4]))
		wantName, info, owner, size := "", byte(0), uint16(0), uint64(0)
		switch i {
		case 1, 2:
			info, owner = 3, uint16(i)
		case 3:
			wantName, info, owner, size = symbol, 18, 1, extent
		}
		if !ok || name != wantName || s[4] != info || s[5] != 0 || le.Uint16(s[6:8]) != owner ||
			le.Uint64(s[8:16]) != 0 || le.Uint64(s[16:24]) != size {
			return refuse("missing, duplicate, misowned, or invalid function symbol")
		}
	}
	return asm.EncodedFunction{Symbol: symbol, Bytes: append([]byte(nil), sections[1].data...), Align: 4, Arch: lane}, nil
}

func checkedImageELFString(table []byte, offset uint32) (string, bool) {
	if uint64(offset) >= uint64(len(table)) {
		return "", false
	}
	end := bytes.IndexByte(table[offset:], 0)
	if end < 0 {
		return "", false
	}
	return string(table[offset : uint64(offset)+uint64(end)]), true
}
