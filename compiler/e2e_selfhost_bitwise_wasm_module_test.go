package compiler

import (
	"bytes"
	"fmt"
	"math"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/wasm/check"
)

func selfhostBitwiseWasmSource(t *testing.T) string {
	t.Helper()
	var source strings.Builder
	for _, name := range []string{"wasm.oak", "bitwise_wasm.oak"} {
		data, err := os.ReadFile(filepath.Join("..", "asm", "selfhost", name))
		if err != nil {
			t.Fatal(err)
		}
		source.Write(data)
		source.WriteByte('\n')
	}
	return source.String()
}

func selfhostBitwiseWasmArray(data []byte) string {
	values := make([]string, len(data))
	for i, b := range data {
		values[i] = fmt.Sprintf("u8(%d)", b)
	}
	return fmt.Sprintf("[%s]", strings.Join(values, ","))
}

// Capture the entire module emitted by compiled Oak directly from binary
// stdout. No Go-produced envelope, body, metadata or padding is added. The Go
// seed's EmitC and the system C compiler remain explicit bootstrap boundaries.
func captureSelfhostBitwiseWasm(t *testing.T, op uint32, name []byte, capacity int) []byte {
	t.Helper()
	requireSelfhostImageCC(t)
	source := selfhostBitwiseWasmSource(t) + fmt.Sprintf(`
putchar: (ch: c.Int): c.Int = c.extern("putchar")
main: (): i32 {
  bytes: [%d]u8
  name: [%d]u8 = %s
  size: u32 = 0
  true ? { dst: [*]u8 = span(&bytes)
    i: u32 = 0
    while i < len(dst) { dst[i] = u8(165); i = i + u32(1) }
    size = wasm_bitwise_module(dst, u32(%d), view(&name))
    assert(size != u32(0) && size <= len(dst))
    i = size
    while i < len(dst) { assert(dst[i] == u8(165)); i = i + u32(1) }
  }
  i: u32 = 0
  while i < size { putchar(c.Int(i32_bits_u32(u32(bytes[i])))); i = i + u32(1) }
  0
}
`, capacity, len(name), selfhostBitwiseWasmArray(name), op)
	out, code, abnormal := buildAndRunOutput(t, "selfhost_bitwise_module", source)
	if abnormal || code != 0 {
		t.Fatalf("Oak complete module exit (%d,%v)", code, abnormal)
	}
	return append([]byte(nil), []byte(out)...)
}

func TestE2ESelfHostedWasmBitwiseModule(t *testing.T) {
	names := []struct{ label, name string }{
		{"bitwise", "bitwise"}, {"Mix9", "Mix9"}, {"one", "Z"},
		{"n123", strings.Repeat("A", 123)}, {"n124", strings.Repeat("B", 124)},
		{"n127", strings.Repeat("C", 127)}, {"n128", strings.Repeat("D", 128)},
		{"max256", strings.Repeat("E", 256)},
	}
	for _, op := range []struct {
		label, symbol string
		tag           uint32
	}{{"and", "&", 1}, {"or", "|", 2}, {"xor", "^", 3}} {
		for _, name := range names {
			t.Run(op.label+"_"+name.label, func(t *testing.T) {
				original := fmt.Sprintf("%s: (left0: u32, Right9: u32): u32 = left0 %s Right9\n", name.name, op.symbol)
				fresh, err := New().WithSource("bitwise_module.oak", original).EmitWasm().Get()
				if err != nil {
					t.Fatal(err)
				}
				if fresh.TranslationVerified || fresh.ByteValidation == nil {
					t.Fatal("fresh production oracle lost validation or claimed translation proof")
				}
				for _, capacity := range []int{len(fresh.Bytes), len(fresh.Bytes) + 17} {
					actual := captureSelfhostBitwiseWasm(t, op.tag, []byte(name.name), capacity)
					if !bytes.Equal(actual, fresh.Bytes) {
						t.Fatalf("complete Oak/Go module mismatch (capacity %d): got %x, want %x", capacity, actual, fresh.Bytes)
					}
					if _, err := check.Validate(actual); err != nil {
						t.Fatalf("actual complete Oak module: %v", err)
					}
				}
			})
		}
	}
}

type selfhostBitwiseWasmRefusal struct {
	label    string
	op       uint32
	name     []byte
	capacity int
}

func selfhostBitwiseWasmRefusals() []selfhostBitwiseWasmRefusal {
	cases := []selfhostBitwiseWasmRefusal{
		{"invalid_op_zero", 0, []byte("bitwise"), 320},
		{"invalid_op_four", 4, []byte("bitwise"), 320},
		{"invalid_op_max", math.MaxUint32, []byte("bitwise"), 320},
		{"empty_name", 1, nil, 320},
		{"name257", 1, bytes.Repeat([]byte{'A'}, 257), 320},
		{"name257_late_invalid", 1, append(bytes.Repeat([]byte{'A'}, 256), 255), 320},
		{"nul_name", 1, []byte{0}, 320},
		{"non_ascii_name", 1, []byte{128}, 320},
		{"late_nul_name", 1, append(bytes.Repeat([]byte{'A'}, 255), 0), 320},
		{"late_non_ascii_name", 1, append(bytes.Repeat([]byte{'A'}, 255), 255), 320},
		{"empty_buffer", 1, []byte("bitwise"), 0},
		{"one_byte_buffer", 1, []byte("bitwise"), 1},
	}
	for _, n := range []int{1, 7, 123, 124, 127, 128, 256} {
		nameSize, exportSizeSize := 1, 1
		if n >= 128 {
			nameSize = 2
		}
		if n+nameSize+3 >= 128 {
			exportSizeSize = 2
		}
		for op := uint32(1); op <= 3; op++ {
			cases = append(cases, selfhostBitwiseWasmRefusal{fmt.Sprintf("short_n%d_op%d", n, op), op, bytes.Repeat([]byte{'A'}, n), 36 + n + nameSize + exportSizeSize - 1})
		}
	}
	return cases
}

func TestE2ESelfHostedWasmBitwiseModuleRefusal(t *testing.T) {
	requireSelfhostImageCC(t)
	var source strings.Builder
	source.WriteString(selfhostBitwiseWasmSource(t))
	source.WriteString("\nputchar: (ch: c.Int): c.Int = c.extern(\"putchar\")\nmain: (): i32 {\n")
	total := 0
	for _, tc := range selfhostBitwiseWasmRefusals() {
		fmt.Fprintf(&source, `
  true ? {
    bytes: [%d]u8
    name: [%d]u8 = %s
    true ? { dst: [*]u8 = span(&bytes)
      i: u32 = 0
      while i < len(dst) { dst[i] = u8(165); i = i + u32(1) }
      assert(wasm_bitwise_module(dst, u32(%d), view(&name)) == u32(0))
      i = u32(0)
      while i < len(dst) { assert(dst[i] == u8(165)); i = i + u32(1) }
    }
    i: u32 = 0
    while i < len(bytes) { putchar(c.Int(i32_bits_u32(u32(bytes[i])))); i = i + u32(1) }
  }
`, tc.capacity, len(tc.name), selfhostBitwiseWasmArray(tc.name), tc.op)
		total += tc.capacity
	}
	source.WriteString("  0\n}\n")
	out, code, abnormal := buildAndRunOutput(t, "selfhost_bitwise_module_refusal", source.String())
	if abnormal || code != 0 || !bytes.Equal([]byte(out), bytes.Repeat([]byte{165}, total)) {
		t.Fatalf("Oak refusal corpus did not preserve every buffer: exit (%d,%v), bytes %d, want %d", code, abnormal, len(out), total)
	}
	data := []byte(out)
	for _, tc := range selfhostBitwiseWasmRefusals() {
		t.Run(tc.label, func(t *testing.T) {
			if !bytes.Equal(data[:tc.capacity], bytes.Repeat([]byte{165}, tc.capacity)) {
				t.Fatal("captured refusal buffer changed")
			}
		})
		data = data[tc.capacity:]
	}
	t.Logf("checked %d refusals and %d unchanged destination bytes", len(selfhostBitwiseWasmRefusals()), total)
}
