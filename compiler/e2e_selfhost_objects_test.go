package compiler

import (
	"bytes"
	"encoding/binary"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// Exercise admission in the compiled Oak implementation, including failures
// after earlier valid records. Each case checks the entire destination, not
// just the status or the words at the relocation site.
func TestE2ESelfHostedObjects(t *testing.T) {
	type object struct{ source, size, alignment uint32 }
	type symbol struct{ name, length, object, offset uint32 }
	type relocation struct{ object, offset, kind, name, length uint32 }
	type fixture struct {
		name                          string
		objects                       []object
		symbols                       []symbol
		plan                          []relocation
		words                         []uint32
		names                         string
		arch, capacity, scratch       uint32
		entryName, entryLength, entry uint32
		base                          uint64
		want                          []byte // nil means refusal
	}
	wordBytes := func(words ...uint32) []byte {
		out := make([]byte, 4*len(words))
		for i, w := range words {
			binary.LittleEndian.PutUint32(out[i*4:], w)
		}
		return out
	}
	valid := func() fixture {
		return fixture{
			objects: []object{{0, 12, 4}, {12, 8, 16}},
			symbols: []symbol{{0, 5, 0, 0}, {5, 3, 1, 0}, {8, 4, 1, 4}},
			plan:    []relocation{{0, 0, 2, 5, 3}, {0, 4, 1, 0, 5}, {1, 0, 1, 0, 5}},
			words:   []uint32{0x94000000, 0x14000000, 0xd503201f, 0x14000000, 0xd65f03c0},
			names:   "entryfoofoozmissing",
			arch:    1, capacity: 32, scratch: 2, entryLength: 5, base: 65536,
			want: wordBytes(0x94000004, 0x17ffffff, 0xd503201f, 0, 0x17fffffc, 0xd65f03c0),
		}
	}
	var cases []fixture
	add := func(name string, reject bool, mutate func(*fixture)) {
		f := valid()
		f.name = name
		if mutate != nil {
			mutate(&f)
		}
		if reject {
			f.want = nil
		}
		cases = append(cases, f)
	}
	add("forward_backward_and_padding", false, nil)
	add("entry_at_nonzero_symbol_offset", false, func(f *fixture) { f.entryName, f.entryLength, f.entry = 8, 4, 20 })
	add("absolute_alignment", false, func(f *fixture) {
		f.base = 65540
		f.want = wordBytes(0x94000003, 0x17ffffff, 0xd503201f, 0x17fffffd, 0xd65f03c0)
	})
	add("leading_padding", false, func(f *fixture) {
		f.base, f.objects[0].alignment, f.capacity, f.entry = 65540, 16, 40, 12
		f.want = append(make([]byte, 12), f.want...)
	})
	add("high_addresses", false, func(f *fixture) { f.base = 0xffffffffffffffe0 })
	add("empty_relocation_plan", false, func(f *fixture) {
		f.plan = nil
		f.want = wordBytes(0x94000000, 0x14000000, 0xd503201f, 0, 0x14000000, 0xd65f03c0)
	})
	add("opaque_names_with_zero_bytes", false, func(f *fixture) { f.names = "\x00ntryfoofoozmissing" })
	add("exact_destination_extent", false, func(f *fixture) { f.capacity = 24 })
	add("no_objects", true, func(f *fixture) { f.objects = nil })
	add("no_symbols", true, func(f *fixture) { f.symbols = nil })
	add("short_scratch", true, func(f *fixture) { f.scratch = 1 })
	add("short_destination", true, func(f *fixture) { f.capacity = 23 })
	add("unknown_arch", true, func(f *fixture) { f.arch = 3 })
	add("unaligned_base", true, func(f *fixture) { f.base++ })
	add("address_overflow", true, func(f *fixture) { f.base = 0xfffffffffffffff0 })
	add("empty_object", true, func(f *fixture) { f.objects[1].size = 0 })
	add("partial_instruction", true, func(f *fixture) { f.objects[1].size = 7 })
	add("source_out_of_bounds", true, func(f *fixture) { f.objects[1].source = 16 })
	add("source_offset_overflow", true, func(f *fixture) { f.objects[1].source = 0xffffffff })
	add("source_size_overflow", true, func(f *fixture) { f.objects[1].size = 0xfffffffc })
	for _, alignment := range []uint32{0, 1, 2, 3, 6, 8192, 0xffffffff} {
		add(fmt.Sprintf("bad_alignment_%d", alignment), true, func(f *fixture) { f.objects[1].alignment = alignment })
	}
	add("duplicate_definition", true, func(f *fixture) { f.symbols[2] = f.symbols[1] })
	add("unsorted_definitions", true, func(f *fixture) { f.symbols[1], f.symbols[2] = f.symbols[2], f.symbols[1] })
	add("empty_definition_name", true, func(f *fixture) { f.symbols[2].length = 0 })
	add("bad_definition_name", true, func(f *fixture) { f.symbols[2].length = 0xffffffff })
	add("bad_definition_name_offset", true, func(f *fixture) { f.symbols[2].name = 0xffffffff })
	add("bad_definition_owner", true, func(f *fixture) { f.symbols[2].object = 2 })
	add("symbol_at_end_of_object", true, func(f *fixture) { f.symbols[2].offset = 8 })
	add("unaligned_symbol", true, func(f *fixture) { f.symbols[2].offset = 2 })
	add("missing_entry", true, func(f *fixture) { f.entryName, f.entryLength = 12, 7 })
	add("entry_prefix_is_not_match", true, func(f *fixture) { f.entryLength = 4 })
	add("empty_entry", true, func(f *fixture) { f.entryLength = 0 })
	add("entry_name_out_of_bounds", true, func(f *fixture) { f.entryName = 0xffffffff })
	add("missing_late_symbol", true, func(f *fixture) { f.plan[2].name, f.plan[2].length = 12, 7 })
	add("empty_relocation_name", true, func(f *fixture) { f.plan[2].length = 0 })
	add("bad_relocation_name", true, func(f *fixture) { f.plan[2].length = 0xffffffff })
	add("bad_relocation_owner", true, func(f *fixture) { f.plan[2].object = 2 })
	add("overlapping_relocations", true, func(f *fixture) { f.plan[1] = f.plan[0] })
	add("unsorted_relocations", true, func(f *fixture) { f.plan[0], f.plan[2] = f.plan[2], f.plan[0] })
	add("relocation_at_object_end", true, func(f *fixture) { f.plan[2].offset = 8 })
	add("unaligned_relocation", true, func(f *fixture) { f.plan[2].offset = 2 })
	add("relocation_offset_overflow", true, func(f *fixture) { f.plan[2].offset = 0xffffffff })
	add("unknown_relocation", true, func(f *fixture) { f.plan[2].kind = 0 })
	add("wrong_arch_relocation", true, func(f *fixture) { f.plan[2].kind = 4 })
	add("malformed_late_instruction", true, func(f *fixture) { f.words[3] = 0xd65f03c0 })
	add("pair_crosses_object_boundary", true, func(f *fixture) { f.plan[2].kind, f.plan[2].offset = 3, 4 })
	// The same named lookup and cross-object ownership path drives RV64 pairs.
	addRV := func(name string, reject bool, mutate func(*fixture)) {
		add(name, reject, func(f *fixture) {
			f.arch = 2
			f.objects = []object{{0, 8, 4}, {8, 8, 16}}
			f.words = []uint32{0x97, 0x80e7, 0x02a00513, 0x8067}
			f.plan = []relocation{{0, 0, 4, 5, 3}}
			f.want = wordBytes(0x97, 0x010080e7, 0, 0, 0x02a00513, 0x8067)
			if mutate != nil {
				mutate(f)
			}
		})
	}
	addRV("rv64_named_call", false, nil)
	addRV("rv64_named_address", false, func(f *fixture) {
		f.plan[0].kind, f.words[0], f.words[1] = 5, 0x297, 0x28293
		f.want = wordBytes(0x297, 0x01028293, 0, 0, 0x02a00513, 0x8067)
	})
	addRV("rv64_halfword_place_rejected_for_non_C_profile", true, func(f *fixture) { f.plan[0].offset = 2 })
	addRV("rv64_wrong_arch", true, func(f *fixture) { f.plan[0].kind = 2 })
	addRV("rv64_mismatched_registers", true, func(f *fixture) { f.words[1] = 0x8067 })
	addRV("rv64_truncated_pair", true, func(f *fixture) { f.objects[0].size = 4 })

	var s strings.Builder
	for _, name := range []string{"native.oak", "objects.oak"} {
		source, err := os.ReadFile(filepath.Join("..", "asm", "selfhost", name))
		if err != nil {
			t.Fatal(err)
		}
		s.Write(source)
		s.WriteByte('\n')
	}
	s.WriteString(`putchar: (ch: c.Int): c.Int = c.extern("putchar")
emit: (word: u32): () {
  i: u32 = 0
  while i < u32(4) { putchar(c.Int(i32_bits_u32((word >> (i * u32(8))) & u32(255))))
    i = i + u32(1) }
}
main: (): i32 {
`)
	for _, f := range cases {
		fmt.Fprintf(&s, "  true ? { // %s\n", f.name)
		fmt.Fprintf(&s, "    source: [%d]u8\n    dst: [%d]u8\n    scratch: [%d]u32\n", len(f.words)*4, f.capacity, f.scratch)
		fmt.Fprintf(&s, "    objects: [%d]NativeObject\n    symbols: [%d]NativeSymbol\n    plan: [%d]NativeObjectRelocation\n", len(f.objects), len(f.symbols), len(f.plan))
		fmt.Fprintf(&s, "    names: [%d]u8\n", len(f.names))
		for i := range f.names {
			fmt.Fprintf(&s, "    names[u32(%d)] = u8(%d)\n", i, f.names[i])
		}
		for i, o := range f.objects {
			fmt.Fprintf(&s, "    objects[u32(%d)] = NativeObject { source: u32(%d), size: u32(%d), alignment: u32(%d) }\n", i, o.source, o.size, o.alignment)
		}
		for i, d := range f.symbols {
			fmt.Fprintf(&s, "    symbols[u32(%d)] = NativeSymbol { name: u32(%d), length: u32(%d), object: u32(%d), offset: u32(%d) }\n", i, d.name, d.length, d.object, d.offset)
		}
		for i, r := range f.plan {
			fmt.Fprintf(&s, "    plan[u32(%d)] = NativeObjectRelocation { object: u32(%d), offset: u32(%d), kind: u32(%d), name: u32(%d), length: u32(%d) }\n", i, r.object, r.offset, r.kind, r.name, r.length)
		}
		s.WriteString("    true ? { buffer: [*]u8 = span(&source)\n")
		for i, w := range f.words {
			fmt.Fprintf(&s, "      native_write_word(buffer, u32(%d), u32(%d))\n", i*4, w)
		}
		s.WriteString("    }\n    i: u32 = 0\n    while i < len(dst) { dst[i] = u8(165)\n      i = i + u32(1) }\n")
		s.WriteString("    true ? { buffer: [*]u8 = span(&dst)\n      offsets: [*]u32 = span(&scratch)\n")
		fmt.Fprintf(&s, "      r: NativeLinkResult = native_link_objects(buffer, offsets, view(&source), view(&objects), view(&names), view(&symbols), view(&plan), u32(%d), u64(%d), u32(%d), u32(%d))\n", f.arch, f.base, f.entryName, f.entryLength)
		s.WriteString("      emit(r.status)\n      emit(r.size)\n      emit(r.entry)\n    }\n    i = u32(0)\n    while i < len(dst) { putchar(c.Int(i32_bits_u32(u32(dst[i]))))\n      i = i + u32(1) }\n  }\n")
	}
	s.WriteString("  0\n}\n")
	stdout, code, abnormal := buildAndRunOutput(t, "selfhost_objects", s.String())
	if code != 0 || abnormal {
		t.Fatalf("object admission corpus exit (%d,%v)", code, abnormal)
	}
	output := []byte(stdout)
	for _, f := range cases {
		n := 12 + int(f.capacity)
		if len(output) < n {
			t.Fatalf("truncated output at %s", f.name)
		}
		record := output[:n]
		output = output[n:]
		t.Run(f.name, func(t *testing.T) {
			status, size, entry := binary.LittleEndian.Uint32(record), binary.LittleEndian.Uint32(record[4:]), binary.LittleEndian.Uint32(record[8:])
			want := bytes.Repeat([]byte{165}, int(f.capacity))
			if f.want == nil {
				if status != 1 || size != 0 || entry != 0 {
					t.Fatalf("refusal returned {%d,%d,%d}", status, size, entry)
				}
			} else {
				if status != 0 || size != uint32(len(f.want)) || entry != f.entry {
					t.Fatalf("success returned {%d,%d,%d}, want {0,%d,%d}", status, size, entry, len(f.want), f.entry)
				}
				copy(want, f.want)
			}
			if !bytes.Equal(record[12:], want) {
				t.Fatalf("destination %x, want %x", record[12:], want)
			}
		})
	}
	if len(output) != 0 {
		t.Fatalf("unexpected trailing output: %x", output)
	}
}
