package compiler

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/stdlib"
	"github.com/SCKelemen/oak/target"
)

func selfhostBitwiseELFSource(t *testing.T) string {
	t.Helper()
	source, err := os.ReadFile(filepath.Join("..", "asm", "selfhost", "bitwise_elf.oak"))
	if err != nil {
		t.Fatal(err)
	}
	return string(source)
}

// These independently specified proposal words are not read from the fresh
// production artifact. The writer is responsible for the complete envelope;
// neither these proposals nor the Oak writer grant checker authority.
func selfhostBitwiseLinkedText(arch uint32, op int) []byte {
	armOps := []uint32{0, 0x0a010000, 0x2a010000, 0x4a010000}
	rvOps := []uint32{0, 0x00b57533, 0x00b56533, 0x00b54533}
	words := []uint32{0x94000003, 0x52800ba8, 0xd4000001, armOps[op], 0xd65f03c0}
	if arch == 2 {
		words = []uint32{0x00000097, 0x010080e7, 0x05d00893, 0x00000073,
			0xfa010113, 0x00913023, 0x01213423, 0x00058913, rvOps[op],
			0x00013483, 0x00813903, 0x06010113, 0x00008067}
	}
	var out bytes.Buffer
	if err := binary.Write(&out, binary.LittleEndian, words); err != nil {
		panic(err)
	}
	return out.Bytes()
}

// Compile the original canonical source afresh, then invoke the existing
// production object proposal reader and executable writer without any checker
// capability. Complete byte equality is tested separately from admission.
func selfhostBitwiseELFReference(t *testing.T, name string, op int, arch uint32) []byte {
	t.Helper()
	operator := []string{"", "&", "|", "^"}[op]
	first, second := "x", "y"
	if name == "Mix9" {
		first, second = "left", "right"
	}
	source := fmt.Sprintf("%s: (%s: u32, %s: u32): u32 = %s %s %s\n", name, first, second, first, operator, second)
	lane := target.ArchArm64
	if arch == 2 {
		lane = target.ArchRiscv64
	}
	object, err := New().WithSource("strict-bitwise.oak", source).
		WithTarget(target.Target{OS: target.OSLinux, Arch: lane}).EmitNativeObject(asm.ELF).Get()
	if err != nil {
		t.Fatal(err)
	}
	body, err := checkedImageProposeBody(object, "oak_"+name, lane)
	if err != nil {
		t.Fatal(err)
	}
	image, err := asm.WriteExecutable([]asm.EncodedFunction{body}, asm.ExecutableOptions{
		OS: asm.OSLinux, Arch: body.Arch, Entry: "oak_" + name, RV64FloatABI: "double",
	})
	if err != nil {
		t.Fatal(err)
	}
	return image
}

// Struct serialization is an independent byte-layout oracle, distinct from
// both Oak's packed-word writes and production asm.WriteExecutable.
func selfhostBitwiseELFOracle(t *testing.T, text, name []byte, arch uint32) []byte {
	t.Helper()
	stub, body, load, machine, flags := uint64(12), uint64(8), uint64(32), uint16(183), uint32(0)
	if arch == 2 {
		stub, body, load, machine, flags = 16, 36, 64, 243, 4
	}
	sym := uint64(4096) + load
	str := sym + 72
	shstr := str + uint64(len(name)) + 13
	sections := (shstr + 41 + 7) &^ uint64(7)
	image := make([]byte, sections+384)
	put := func(offset uint64, value any) {
		var out bytes.Buffer
		if err := binary.Write(&out, binary.LittleEndian, value); err != nil {
			t.Fatal(err)
		}
		copy(image[offset:], out.Bytes())
	}
	put(0, struct {
		Ident                                                [16]byte
		Type, Machine                                        uint16
		Version                                              uint32
		Entry, Phoff, Shoff                                  uint64
		Flags                                                uint32
		Ehsize, Phentsize, Phnum, Shentsize, Shnum, Shstrndx uint16
	}{[16]byte{127, 'E', 'L', 'F', 2, 1, 1}, 2, machine, 1, 65536, 64, sections, flags, 64, 56, 1, 64, 6, 5})
	put(64, struct {
		Type, Flags                                uint32
		Offset, Vaddr, Paddr, Filesz, Memsz, Align uint64
	}{1, 5, 4096, 65536, 65536, load, load, 4096})
	copy(image[4096:], text)
	type symbol struct {
		Name        uint32
		Info, Other uint8
		Shndx       uint16
		Value, Size uint64
	}
	put(sym, []symbol{{}, {1, 18, 0, 1, 65536, stub}, {8, 18, 0, 1, 65536 + stub, body}})
	copy(image[str:], append(append([]byte("\x00_start\x00oak_"), name...), 0))
	copy(image[shstr:], []byte("\x00.text\x00.rodata\x00.symtab\x00.strtab\x00.shstrtab\x00"))
	type section struct {
		Name, Type                   uint32
		Flags, Address, Offset, Size uint64
		Link, Info                   uint32
		Align, Entsize               uint64
	}
	put(sections, []section{
		{}, {1, 1, 6, 65536, 4096, stub + body, 0, 0, 4, 0},
		{7, 1, 2, 65536 + load, sym, 0, 0, 0, 16, 0},
		{15, 2, 0, 0, sym, 72, 4, 1, 8, 24},
		{23, 3, 0, 0, str, uint64(len(name)) + 13, 0, 0, 1, 0},
		{31, 3, 0, 0, shstr, 41, 0, 0, 1, 0},
	})
	return image
}

type selfhostBitwiseELFCase struct {
	label             string
	name, text        []byte
	arch              uint32
	op, capacity      int
	accept, canonical bool
}

func selfhostBitwiseELFCases(t *testing.T) []selfhostBitwiseELFCase {
	t.Helper()
	var cases []selfhostBitwiseELFCase
	for _, arch := range []uint32{1, 2} {
		add := func(label string, name, text []byte, capacity int, accept, canonical bool, op int) {
			cases = append(cases, selfhostBitwiseELFCase{
				fmt.Sprintf("arch%d/%s", arch, label), bytes.Clone(name), bytes.Clone(text), arch, op, capacity, accept, canonical,
			})
		}
		for _, name := range []string{"bitwise", "Mix9"} {
			for op := 1; op <= 3; op++ {
				add(fmt.Sprintf("%s/op%d", name, op), []byte(name), selfhostBitwiseLinkedText(arch, op), 5120, true, true, op)
			}
		}
		text := selfhostBitwiseLinkedText(arch, 1)
		name := []byte("bitwise")
		for _, n := range []int{1, 2, 3, 4, 5, 6, 8, 9, 123, 124, 127, 128, 255, 256} {
			boundaryName := bytes.Repeat([]byte{'N'}, n)
			size := len(selfhostBitwiseELFOracle(t, text, boundaryName, arch))
			add(fmt.Sprintf("name%d/exact", n), boundaryName, text, size, true, true, 1)
			add(fmt.Sprintf("name%d/suffix", n), boundaryName, text, size+19, true, false, 1)
		}
		// These succeed only as image-format proposals. They are NOT canonical
		// source identifiers; complete original-source checking remains required.
		for i, profileName := range [][]byte{[]byte("main"), []byte("A_B"), []byte("9A"), {1, 127}, []byte("two words")} {
			add(fmt.Sprintf("profile-not-source%d", i), profileName, text, 5120, true, false, 1)
		}
		untrusted := bytes.Clone(text)
		untrusted[len(untrusted)-1] ^= 255
		add("untrusted-body", name, untrusted, 5120, true, false, 1)
		for _, capacity := range []int{0, 1, 4096, len(selfhostBitwiseELFOracle(t, text, name, arch)) - 1} {
			add(fmt.Sprintf("short-capacity%d", capacity), name, text, capacity, false, false, 1)
		}
		for _, badName := range [][]byte{nil, bytes.Repeat([]byte{'N'}, 257), {0}, {128}, {255}, {'A', 0}, {'A', 128}, append(bytes.Repeat([]byte{'N'}, 255), 0)} {
			add(fmt.Sprintf("invalid-name%d", len(cases)), badName, text, 5120, false, false, 1)
		}
		for _, badText := range [][]byte{nil, text[:1], text[:len(text)-1], append(bytes.Clone(text), 0), selfhostBitwiseLinkedText(3-arch, 1)} {
			add(fmt.Sprintf("invalid-length%d", len(badText)), name, badText, 5120, false, false, 1)
		}
		stub := 12
		if arch == 2 {
			stub = 16
		}
		for i := 0; i < stub; i++ {
			badText := bytes.Clone(text)
			badText[i] ^= 1
			add(fmt.Sprintf("startup-byte%d", i), name, badText, 5120, false, false, 1)
		}
	}
	for _, arch := range []uint32{0, 3, ^uint32(0)} {
		cases = append(cases, selfhostBitwiseELFCase{fmt.Sprintf("invalid-arch%d", arch), []byte("bitwise"), selfhostBitwiseLinkedText(1, 1), arch, 1, 5120, false, false})
	}
	return cases
}

func selfhostBitwiseELFArray(s *strings.Builder, name string, data []byte) {
	fmt.Fprintf(s, "    %s: [%d]u8", name, len(data))
	if len(data) != 0 {
		s.WriteString(" = [")
		for i, b := range data {
			if i != 0 {
				s.WriteString(", ")
			}
			fmt.Fprintf(s, "u8(%d)", b)
		}
		s.WriteByte(']')
	}
	s.WriteByte('\n')
}

// Capture binary stdout without trimming, reconstruction, or Go-built metadata
// in the image. Returned lengths delimit each complete caller-owned buffer.
// Execution is still bootstrapped by the Go EmitC compiler and system cc.
func selfhostBitwiseELFRun(t *testing.T, cases []selfhostBitwiseELFCase) ([][]byte, []uint32) {
	t.Helper()
	requireSelfhostImageCC(t)
	var s strings.Builder
	s.WriteString(selfhostBitwiseELFSource(t))
	s.WriteString(`
putchar: (ch: c.Int): c.Int = c.extern("putchar")
main: (): i32 {
`)
	for _, tc := range cases {
		s.WriteString("  true ? {\n")
		selfhostBitwiseELFArray(&s, "text", tc.text)
		selfhostBitwiseELFArray(&s, "name", tc.name)
		fmt.Fprintf(&s, "    image: [%d]u8\n    size: u32 = 0\n", tc.capacity)
		s.WriteString("    true ? { dst: [*]u8 = span(&image)\n      i: u32 = 0\n      while i < len(dst) { dst[i] = u8_trunc_u32(i % u32(251) + u32(1))\n        i = i + u32(1) }\n")
		fmt.Fprintf(&s, "      size = native_bitwise_elf_image(dst, view(&text), u32(%d), view(&name))\n    }\n", tc.arch)
		s.WriteString("    i: u32 = 0\n    while i < u32(4) { putchar(c.Int(i32_bits_u32((size >> (i * u32(8))) & u32(255))))\n      i = i + u32(1) }\n    i = u32(0)\n    while i < len(image) { putchar(c.Int(i32_bits_u32(u32(image[i]))))\n      i = i + u32(1) }\n  }\n")
	}
	s.WriteString("  0\n}\n")
	out, code, abnormal := buildAndRunOutput(t, "strict_bitwise_elf", s.String())
	if code != 0 || abnormal {
		t.Fatalf("Oak ELF producer exit (%d,%v)", code, abnormal)
	}
	var buffers [][]byte
	var sizes []uint32
	data := []byte(out)
	for _, tc := range cases {
		if len(data) < 4+tc.capacity {
			t.Fatalf("%s: truncated captured buffer", tc.label)
		}
		sizes = append(sizes, binary.LittleEndian.Uint32(data[:4]))
		buffers = append(buffers, bytes.Clone(data[4:4+tc.capacity]))
		data = data[4+tc.capacity:]
	}
	if len(data) != 0 {
		t.Fatalf("unexpected %d trailing generator bytes", len(data))
	}
	return buffers, sizes
}

func selfhostBitwiseELFEqual(t *testing.T, label string, got, want []byte) {
	t.Helper()
	if bytes.Equal(got, want) {
		return
	}
	offset := 0
	for offset < len(got) && offset < len(want) && got[offset] == want[offset] {
		offset++
	}
	t.Fatalf("%s: first differing offset %d; length got/want %d/%d; sha256 got/want %x/%x", label, offset, len(got), len(want), sha256.Sum256(got), sha256.Sum256(want))
}

func TestE2ESelfHostedBitwiseELF(t *testing.T) {
	cases := selfhostBitwiseELFCases(t)
	buffers, sizes := selfhostBitwiseELFRun(t, cases)
	for i, tc := range cases {
		t.Run(tc.label, func(t *testing.T) {
			want := make([]byte, tc.capacity)
			for j := range want {
				want[j] = byte(j%251 + 1)
			}
			var image []byte
			if tc.accept {
				image = selfhostBitwiseELFOracle(t, tc.text, tc.name, tc.arch)
				copy(want, image)
			}
			if sizes[i] != uint32(len(image)) {
				t.Fatalf("reported length %d, want %d", sizes[i], len(image))
			}
			selfhostBitwiseELFEqual(t, "complete sentinel buffer", buffers[i], want)
			if tc.canonical {
				reference := selfhostBitwiseELFReference(t, string(tc.name), tc.op, tc.arch)
				selfhostBitwiseELFEqual(t, "fresh complete production ELF", buffers[i][:sizes[i]], reference)
			}
		})
	}
	t.Logf("checked %d actual Oak full-buffer results (including complete fresh-production parity)", len(cases))
}

// A source-extraction feasibility check, not a refinement or totality theorem.
// The same standalone source is compiled and executed by the byte tests below.
func TestE2ESelfHostedBitwiseELFExtract(t *testing.T) {
	source := selfhostBitwiseELFSource(t)
	extracted, err := New().WithSource("bitwise_elf.oak", stdlib.Prelude+"\n"+source).
		EmitLeanRoots("Oak.BitwiseELFProducer", topLevelNames(t, source)).Get()
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(extracted, "sorry") || !strings.Contains(extracted, "def native_bitwise_elf_image") {
		t.Fatal("incomplete strict ELF writer extraction")
	}
	if path := os.Getenv("OAK_BITWISE_ELF_EXTRACT_OUTPUT"); path != "" {
		if err := os.WriteFile(path, []byte(extracted), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	t.Logf("extracted %d bytes of fuel-indexed definitions; no universal writer theorem is asserted", len(extracted))
}
