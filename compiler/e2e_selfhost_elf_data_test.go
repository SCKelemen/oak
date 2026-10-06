package compiler

import (
	"bytes"
	"debug/elf"
	"encoding/binary"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/target"
)

func selfhostDataCore(t *testing.T) string {
	t.Helper()
	var s strings.Builder
	for _, name := range []string{"native.oak", "objects.oak", "elf.oak", "elf_data.oak"} {
		data, err := os.ReadFile(filepath.Join("..", "asm", "selfhost", name))
		if err != nil {
			t.Fatal(err)
		}
		s.Write(data)
		s.WriteByte('\n')
	}
	return s.String()
}

// The produced programs read initialized data, read zero-initialized BSS on
// a page beyond EOF, write/read that BSS cell, then exit with 42. The BSS-only
// variant checks a segment with zero file bytes. QEMU execution is mandatory
// in cross-target CI; ELF/relocation byte checks run on every C-capable host.
func TestE2ESelfHostedELFData(t *testing.T) {
	core := selfhostDataCore(t)
	for _, arch := range []string{target.ArchArm64, target.ArchRiscv64} {
		for _, bssOnly := range []bool{false, true} {
			t.Run(fmt.Sprintf("%s/bssOnly_%v", arch, bssOnly), func(t *testing.T) {
				dataSize, increment, dataOwner := 4, 22, uint32(0xffffffff)
				if bssOnly {
					dataSize, increment, dataOwner = 0, 42, 0xfffffffe
				}
				archID, kind := 1, 3
				words := []uint32{0x90000009, 0x91000129, 0xb9400120,
					0x9000000a, 0x9100014a, 0xb9400141, 0x0b010000,
					0x11000000 | uint32(increment)<<10, 0xb9000140, 0xb9400140, 0x52800ba8, 0xd4000001}
				if arch == target.ArchRiscv64 {
					archID, kind = 2, 5
					words = []uint32{0x297, 0x28293, 0x2a503,
						0x317, 0x30313, 0x32583, 0x00b50533,
						uint32(increment)<<20 | 0x50513, 0x00a32023, 0x32503, 0x05d00893, 0x73}
				}
				var s strings.Builder
				s.WriteString(core)
				s.WriteString("putchar: (ch: c.Int): c.Int = c.extern(\"putchar\")\nmain: (): i32 {\n")
				fmt.Fprintf(&s, "source: [48]u8\ntext: [48]u8\ndata: [%d]u8\nimage: [%d]u8\nlayout: [1]u32\n", dataSize, 8192+dataSize)
				if dataSize > 0 {
					s.WriteString("data[u32(0)] = u8(20)\n")
				}
				s.WriteString("names: [13]u8 = [u8(95), u8(115), u8(116), u8(97), u8(114), u8(116), u8(98), u8(115), u8(115), u8(100), u8(97), u8(116), u8(97)]\n")
				s.WriteString("objects: [1]NativeObject = [NativeObject { source: u32(0), size: u32(48), alignment: u32(4) }]\n")
				fmt.Fprintf(&s, "symbols: [3]NativeSymbol = [NativeSymbol { name: u32(0), length: u32(6), object: u32(0), offset: u32(0) }, NativeSymbol { name: u32(6), length: u32(3), object: u32(4294967294), offset: u32(4096) }, NativeSymbol { name: u32(9), length: u32(4), object: u32(%d), offset: u32(0) }]\n", dataOwner)
				fmt.Fprintf(&s, "plan: [2]NativeObjectRelocation = [NativeObjectRelocation { object: u32(0), offset: u32(0), kind: u32(%d), name: u32(9), length: u32(4) }, NativeObjectRelocation { object: u32(0), offset: u32(12), kind: u32(%d), name: u32(6), length: u32(3) }]\n", kind, kind)
				fmt.Fprintf(&s, "p: NativeELFDataLayout = native_elf_data_layout(u32(48), u32(%d), u32(4100), u64(65536), u32(%d))\nassert(p.status == u32(0) && p.data_address == u64(69632))\n", dataSize, 8192+dataSize)
				s.WriteString("true ? { dst: [*]u8 = span(&source)\n")
				for i, w := range words {
					fmt.Fprintf(&s, "native_write_word(dst, u32(%d), u32(%d))\n", i*4, w)
				}
				s.WriteString("}\nentry: u32 = 0\ntrue ? { dst: [*]u8 = span(&text)\nscratch: [*]u32 = span(&layout)\n")
				fmt.Fprintf(&s, "r: NativeLinkResult = native_link_objects_data(dst, scratch, view(&source), view(&objects), view(&names), view(&symbols), view(&plan), u32(%d), u64(65536), u32(0), u32(6), p.data_address, u32(%d), u32(4100))\nassert(r.status == u32(0) && r.size == u32(48))\nentry = r.entry\n}\n", archID, dataSize)
				s.WriteString("written: u32 = 0\ntrue ? { dst: [*]u8 = span(&image)\n")
				fmt.Fprintf(&s, "written = native_elf_data_image(dst, view(&text), view(&data), u32(4100), u32(%d), u64(65536), entry)\n}\nassert(written == u32(%d))\n", archID, 8192+dataSize)
				s.WriteString("i: u32 = 0\nwhile i < written { putchar(c.Int(i32_bits_u32(u32(image[i]))))\ni = i + u32(1) }\n0\n}\n")
				stdout, code, abnormal := buildAndRunOutput(t, "selfhost_elf_data", s.String())
				if code != 0 || abnormal {
					t.Fatalf("image generator exit (%d,%v)", code, abnormal)
				}
				image := []byte(stdout)
				file, err := elf.NewFile(bytes.NewReader(image))
				if err != nil {
					t.Fatal(err)
				}
				defer file.Close()
				machine := elf.EM_AARCH64
				if archID == 2 {
					machine = elf.EM_RISCV
				}
				if len(image) != 8192+dataSize || len(file.Progs) != 2 || file.Entry != 65536 || file.Machine != machine {
					t.Fatalf("unexpected ELF: %+v", file.FileHeader)
				}
				rx, rw := file.Progs[0], file.Progs[1]
				if rx.Type != elf.PT_LOAD || rx.Flags != elf.PF_R|elf.PF_X || rx.Off != 4096 || rx.Vaddr != 65536 || rx.Filesz != 48 || rx.Memsz != 48 || rx.Align != 4096 {
					t.Fatalf("text segment: %+v", rx.ProgHeader)
				}
				if rw.Type != elf.PT_LOAD || rw.Flags != elf.PF_R|elf.PF_W || rw.Off != 8192 || rw.Vaddr != 69632 || rw.Filesz != uint64(dataSize) || rw.Memsz != uint64(dataSize+4100) || rw.Align != 4096 {
					t.Fatalf("data segment: %+v", rw.ProgHeader)
				}
				if !bytes.Equal(image[4096+48:8192], make([]byte, 4096-48)) {
					t.Fatal("nonzero file padding")
				}
				if dataSize > 0 && !bytes.Equal(image[8192:], []byte{20, 0, 0, 0}) {
					t.Fatal("initialized data changed")
				}
				// Decode emitted instruction fields independently to bind named
				// definitions to the segment's actual virtual addresses.
				for _, c := range []struct {
					at      int
					address uint64
				}{{0, 69632}, {12, uint64(69632 + dataSize + 4096)}} {
					a := binary.LittleEndian.Uint32(image[4096+c.at:])
					b := binary.LittleEndian.Uint32(image[4100+c.at:])
					var address int64
					if archID == 1 {
						imm := ((a >> 29) & 3) | (((a >> 5) & 0x7ffff) << 2)
						delta := int64(int32(imm<<11) >> 11)
						address = int64((65536+c.at)&^4095) + delta*4096 + int64((b>>10)&4095)
					} else {
						address = int64(65536+c.at) + int64(int32(a&0xfffff000)) + int64(int32(b)>>20)
					}
					if uint64(address) != c.address {
						t.Fatalf("relocation at %d reaches %#x, want %#x", c.at, address, c.address)
					}
				}
				runSelfhostELF(t, image, arch)
			})
		}
	}
}

func TestE2ESelfHostedELFDataAdmission(t *testing.T) {
	var s strings.Builder
	s.WriteString(selfhostDataCore(t))
	s.WriteString(`unchanged: (bytes: []u8): Bool {
  good: Bool = true
  i: u32 = 0
  while i < len(bytes) { good = good && bytes[i] == u8(165)
    i = i + u32(1) }
  good
}
main: (): i32 {
  image: [8200]u8
  short: [8195]u8
  text: [4]u8
  bad_text: [3]u8
  data: [4]u8
  i: u32 = 0
  while i < len(image) { image[i] = u8(165)
    i = i + u32(1) }
  i = u32(0)
  while i < len(short) { short[i] = u8(165)
    i = i + u32(1) }
`)
	for _, c := range []struct {
		text  string
		bss   uint32
		arch  uint32
		base  uint64
		entry uint32
	}{
		{"text", 4, 0, 65536, 0}, {"text", 4, 1, 65537, 0}, {"text", 4, 1, 65536, 4},
		{"text", 4, 1, 65536, 2}, {"bad_text", 4, 1, 65536, 0},
		{"text", ^uint32(0), 1, 65536, 0}, {"text", 4, 1, 0xfffffffffffff000, 0},
	} {
		fmt.Fprintf(&s, "true ? { dst: [*]u8 = span(&image)\nassert(native_elf_data_image(dst, view(&%s), view(&data), u32(%d), u32(%d), u64(%d), u32(%d)) == u32(0))\n}\nassert(unchanged(view(&image)))\n", c.text, c.bss, c.arch, c.base, c.entry)
	}
	s.WriteString(`true ? { dst: [*]u8 = span(&short)
  assert(native_elf_data_image(dst, view(&text), view(&data), u32(4), u32(1), u64(65536), u32(0)) == u32(0))
}
assert(unchanged(view(&short)))
assert(native_elf_data_layout(u32(4), u32(0), u32(0), u64(65536), u32(8200)).status != u32(0))
assert(native_elf_data_layout(u32(4294967292), u32(4), u32(4), u64(0), u32(4294967295)).status != u32(0))
true ? { dst: [*]u8 = span(&image)
  assert(native_elf_data_image(dst, view(&text), view(&data), u32(0), u32(1), u64(65536), u32(0)) == u32(8196))
}
assert(image[u32(8196)] == u8(165) && image[u32(8199)] == u8(165))
42
}
`)
	code, abnormal := buildAndRun(t, "selfhost_elf_data_admission", s.String())
	if code != 42 || abnormal {
		t.Fatalf("admission corpus exit (%d,%v)", code, abnormal)
	}
}
