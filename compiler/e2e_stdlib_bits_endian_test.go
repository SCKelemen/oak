package compiler

import (
	"encoding/binary"
	"fmt"
	"strings"
	"testing"
)

func TestE2EStdlibEndian(t *testing.T) {
	skipInShort(t)
	for _, width := range []int{16, 32, 64} {
		for _, order := range []string{"le", "be"} {
			t.Run(fmt.Sprintf("u%d_%s", width, order), func(t *testing.T) {
				var src strings.Builder
				src.WriteString("import(std)\nmain: (): i32 {\n")
				n := width / 8
				mask := ^uint64(0) >> (64 - width)
				for k, value := range []uint64{0, 1, mask, 0x8123456789abcdef & mask} {
					var encoded [8]byte
					var byteOrder binary.ByteOrder = binary.LittleEndian
					if order == "be" {
						byteOrder = binary.BigEndian
					}
					switch width {
					case 16:
						byteOrder.PutUint16(encoded[:], uint16(value))
					case 32:
						byteOrder.PutUint32(encoded[:], uint32(value))
					case 64:
						byteOrder.PutUint64(encoded[:], value)
					}
					fmt.Fprintf(&src, "dst%d: [%d]u8\ns%d: [*]u8 = span(&dst%d)\ns%d[0] = u8(91)\ns%d[%d] = u8(92)\n", k, n+2, k, k, k, k, n+1)
					fmt.Fprintf(&src, "w%d: Result[u32, EndianError] = bytes_write_u%d_%s(s%d, u32(1), u%d(%d))\nwc%d: u32 = w%d ? | .Ok(v) => v | .Err(e) => u32(99)\nassert(wc%d == u32(%d))\n", k, width, order, k, width, value, k, k, k, n)
					for i := 0; i < n; i++ {
						fmt.Fprintf(&src, "assert(s%d[%d] == u8(%d))\n", k, i+1, encoded[i])
					}
					fmt.Fprintf(&src, "assert(s%d[0] == u8(91) && s%d[%d] == u8(92))\ninput%d: [%d]u8\n", k, k, n+1, k, n+2)
					for i := 0; i < n; i++ {
						fmt.Fprintf(&src, "input%d[%d] = u8(%d)\n", k, i+1, encoded[i])
					}
					fmt.Fprintf(&src, "v%d: []u8 = view(&input%d)\nr%d: Result[u%d, EndianError] = bytes_read_u%d_%s(v%d, u32(1))\nrv%d: u%d = r%d ? | .Ok(v) => v | .Err(e) => u%d(0)\nassert(rv%d == u%d(%d))\nok%d: Bool = r%d ? | .Ok(v) => true | .Err(e) => false\nassert(ok%d)\n", k, k, k, width, width, order, k, k, width, k, width, k, width, value, k, k, k)
					for j, offset := range []uint32{3, uint32(n + 2), ^uint32(0)} {
						fmt.Fprintf(&src, "badw%d_%d: Result[u32, EndianError] = bytes_write_u%d_%s(s%d, u32(%d), u%d(0))\nbw%d_%d: Bool = badw%d_%d ? | .Ok(v) => false | .Err(e) => true\nassert(bw%d_%d)\n", k, j, width, order, k, offset, width, k, j, k, j, k, j)
						fmt.Fprintf(&src, "badr%d_%d: Result[u%d, EndianError] = bytes_read_u%d_%s(v%d, u32(%d))\nbr%d_%d: Bool = badr%d_%d ? | .Ok(v) => false | .Err(e) => true\nassert(br%d_%d)\n", k, j, width, width, order, k, offset, k, j, k, j, k, j)
					}
					for i := 0; i < n; i++ {
						fmt.Fprintf(&src, "assert(s%d[%d] == u8(%d))\n", k, i+1, encoded[i])
					}
					fmt.Fprintf(&src, "assert(s%d[0] == u8(91) && s%d[%d] == u8(92))\n", k, k, n+1)
					fmt.Fprintf(&src, "exact%d: Result[u32, EndianError] = bytes_write_u%d_%s(s%d, u32(2), u%d(%d))\nex%d: u32 = exact%d ? | .Ok(v) => v | .Err(e) => u32(99)\nassert(ex%d == u32(%d))\n", k, width, order, k, width, value, k, k, k, n)
					for i := 0; i < n; i++ {
						fmt.Fprintf(&src, "assert(s%d[%d] == u8(%d))\n", k, i+2, encoded[i])
					}
					expected := value >> 8
					if order == "be" {
						expected = (value << 8) & mask
					}
					fmt.Fprintf(&src, "exactr%d: Result[u%d, EndianError] = bytes_read_u%d_%s(v%d, u32(2))\nexr%d: Bool = exactr%d ? | .Ok(v) => v == u%d(%d) | .Err(e) => false\nassert(exr%d)\n", k, width, width, order, k, k, k, width, expected, k)
				}
				src.WriteString("42\n}\n")
				// Oak currently parses integer literals through signed 64-bit storage.
				// Construct high unsigned values from representable halves.
				program := src.String()
				for _, value := range []uint64{mask, 0x8123456789abcdef & mask, (mask << 8) & mask, uint64(0x23456789abcdef00) & mask} {
					if value > uint64(1<<63-1) {
						program = strings.ReplaceAll(program, fmt.Sprintf("u64(%d)", value), fmt.Sprintf("((u64(%d) << u64(32)) | u64(%d))", value>>32, uint32(value)))
					}
				}
				code, abnormal := buildAndRun(t, "endian", program)
				if abnormal || code != 42 {
					t.Fatalf("exit=(%d,%v)", code, abnormal)
				}
			})
		}
	}
}

func TestE2EStdlibBitset(t *testing.T) {
	skipInShort(t)
	for _, bits := range []int{0, 1, 7, 8, 9, 63, 64, 65} {
		t.Run(fmt.Sprint(bits), func(t *testing.T) {
			var src strings.Builder
			fmt.Fprintf(&src, "import(std)\nmain: (): i32 {\ndata: [10]u8\ns: [*]u8 = span(&data)\n")
			model := [10]byte{255, 255, 255, 255, 255, 255, 255, 255, 255, 255}
			for i := range model {
				fmt.Fprintf(&src, "s[%d] = u8(255)\n", i)
			}
			seed := uint32(771)
			for i := 0; i < 100; i++ {
				seed = seed*1664525 + 1013904223
				index := int(seed % uint32(bits+2))
				value := seed>>31 != 0
				previous := model[index/8]&(1<<uint(index%8)) != 0
				fmt.Fprintf(&src, "r%d: Result[Bool, BitSetError] = bitset_set(s, u32(%d), u32(%d), %t)\n", i, bits, index, value)
				if index >= bits {
					fmt.Fprintf(&src, "e%d: Bool = r%d ? | .Ok(v) => false | .Err(e) => true\nassert(e%d)\n", i, i, i)
				} else {
					fmt.Fprintf(&src, "p%d: Bool = r%d ? | .Ok(v) => v == %t | .Err(e) => false\nassert(p%d)\n", i, i, previous, i)
					if value {
						model[index/8] |= 1 << uint(index%8)
					} else {
						model[index/8] &^= 1 << uint(index%8)
					}
				}
				for j, b := range model {
					fmt.Fprintf(&src, "assert(s[%d] == u8(%d))\n", j, b)
				}
			}
			// Independently constructed read view exercises logical tail handling.
			src.WriteString("input: [10]u8\n")
			count := 0
			for i, b := range model {
				fmt.Fprintf(&src, "input[%d] = u8(%d)\n", i, b)
			}
			src.WriteString("v: []u8 = view(&input)\n")
			for i := 0; i < bits; i++ {
				present := model[i/8]&(1<<uint(i%8)) != 0
				if present {
					count++
				}
				fmt.Fprintf(&src, "c%d: Result[Bool, BitSetError] = bitset_contains(v, u32(%d), u32(%d))\ncv%d: Bool = c%d ? | .Ok(v) => v == %t | .Err(e) => false\nassert(cv%d)\n", i, bits, i, i, i, present, i)
			}
			fmt.Fprintf(&src, "total: Result[u32, BitSetError] = bitset_count(v, u32(%d))\nactual: u32 = total ? | .Ok(v) => v | .Err(e) => u32(999)\nassert(actual == u32(%d))\n", bits, count)
			src.WriteString("assert(bitset_storage_bytes(u32(4294967295)) == u32(536870912))\n42\n}\n")
			code, abnormal := buildAndRun(t, "bitset", src.String())
			if abnormal || code != 42 {
				t.Fatalf("exit=(%d,%v)", code, abnormal)
			}
		})
	}
}

func TestE2EStdlibBitsetBounds(t *testing.T) {
	src := `
import(std)
is_storage_error: (reason: BitSetError): Bool = reason ?
 | .StorageTooSmall => true
 | .BitOutOfRange => false
main: (): i32 {
 data: [1]u8
 s: [*]u8 = span(&data)
 s[0] = u8(123)
 a: Result[Bool, BitSetError] = bitset_set(s, u32(9), u32(0), false)
 ae: Bool = a ? | .Ok(v) => false | .Err(e) => is_storage_error(e)
 assert(ae && s[0] == u8(123))
 b: Result[Bool, BitSetError] = bitset_set(s, u32(8), u32(4294967295), true)
 be: Bool = b ? | .Ok(v) => false | .Err(e) => !is_storage_error(e)
 assert(be && s[0] == u8(123))
 input: [1]u8
 v: []u8 = view(&input)
 c: Result[Bool, BitSetError] = bitset_contains(v, u32(9), u32(0))
 ce: Bool = c ? | .Ok(v) => false | .Err(e) => true
 d: Result[u32, BitSetError] = bitset_count(v, u32(4294967295))
 de: Bool = d ? | .Ok(v) => false | .Err(e) => true
 empty_result: Result[Bool, BitSetError] = bitset_contains(v, u32(0), u32(0))
 ee: Bool = empty_result ? | .Ok(v) => false | .Err(e) => true
 assert(ce && de && ee)
 42
}
`
	code, abnormal := buildAndRun(t, "bitsetbounds", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestE2EVariantPayloadIndexBounds(t *testing.T) {
	src := `
Maybe[T]: type = Some: T | None
read: (data: []u8, index: u32): Maybe[u8] = .Some(data[index])
main: (): i32 {
 data: [1]u8
 data[0] = u8(42)
 v: []u8 = view(&data)
 r: Maybe[u8] = read(v, u32(0))
 r ? | .Some(value) => i32(value) | .None => 0
}
`
	code, abnormal := buildAndRun(t, "variantindex", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	_, abnormal = buildAndRun(t, "variantindexbounds", strings.Replace(src, "read(v, u32(0))", "read(v, u32(1))", 1))
	if !abnormal {
		t.Fatal("out-of-bounds indexing in a variant payload must trap")
	}
}
