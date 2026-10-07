package compiler

import (
	"bytes"
	"context"
	"encoding/base64"
	"fmt"
	"math"
	"math/rand"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/internal/wasmtest"
	"github.com/SCKelemen/oak/wasm/check"
	"github.com/SCKelemen/oak/wasm/encoding"
)

func TestE2ESelfHostedWasmAssembler(t *testing.T) {
	core, err := os.ReadFile(filepath.Join("..", "asm", "selfhost", "wasm.oak"))
	if err != nil {
		t.Fatal(err)
	}
	var plans, sizes []string
	var expected []byte
	pin := func(op uint32, v int64) {
		var encoded []byte
		if op <= 255 {
			encoded, _ = encoding.Assemble([]encoding.Instruction{{Opcode: byte(op), Immediate: v}})
		}
		plans = append(plans, fmt.Sprintf("WasmInstruction { opcode: u32(%d), immediate: i64_bits_u64(u64(%d)) }", op, uint64(v)))
		sizes = append(sizes, fmt.Sprintf("u32(%d)", len(encoded)))
		expected = append(expected, encoded...)
	}

	for _, tc := range selfhostWasmInstructionCases() {
		pin(tc.opcode, tc.immediate)
	}
	var s strings.Builder
	s.Write(core)
	s.WriteString("\nmain: (): i32 {\n  bytes: [16]u8\n")
	fmt.Fprintf(&s, "  plans: [%d]WasmInstruction = [%s]\n  sizes: [%d]u32 = [%s]\n", len(plans), strings.Join(plans, ","), len(sizes), strings.Join(sizes, ","))
	fmt.Fprintf(&s, "  expected: [%d]u8 = [", len(expected))
	for i, b := range expected {
		if i > 0 {
			s.WriteString(",")
		}
		fmt.Fprintf(&s, "u8(%d)", b)
	}
	s.WriteString(`]
  case_index: u32 = 0
  expected_offset: u32 = 0
  while case_index < len(plans) {
    ins: WasmInstruction = plans[case_index]
    size: u32 = sizes[case_index]
    true ? { dst: [*]u8 = span(&bytes)
      i: u32 = 0
      while i < len(dst) { dst[i] = u8(165); i = i + u32(1) }
      assert(wasm_instruction_size(ins) == size)
      assert(wasm_write_instruction(dst, u32(2), ins) == size)
      i = u32(0)
      while i < len(dst) {
        i >= u32(2) && i - u32(2) < size ? {
          assert(dst[i] == expected[expected_offset + i - u32(2)])
        } | { assert(dst[i] == u8(165)) }
        i = i + u32(1)
      }
      i = u32(0)
      while i < len(dst) { dst[i] = u8(165); i = i + u32(1) }
      size != u32(0) ? { assert(wasm_write_instruction(dst, u32(17) - size, ins) == u32(0)) }
      assert(wasm_write_instruction(dst, u32(4294967295), ins) == u32(0))
      i = u32(0)
      while i < len(dst) { assert(dst[i] == u8(165)); i = i + u32(1) }
    }
    expected_offset = expected_offset + size
    case_index = case_index + u32(1)
  }
`)

	s.WriteString(`
  bad: [2]WasmInstruction = [WasmInstruction { opcode: u32(1), immediate: i64(0) }, WasmInstruction { opcode: u32(255), immediate: i64(0) }]
  true ? { dst: [*]u8 = span(&bytes)
    r: WasmAssembly = wasm_assemble(dst, u32(0), view(&bad))
    assert(r.status == u32(1) && r.size == u32(0))
    i: u32 = 0
    while i < len(dst) { assert(dst[i] == u8(165)); i = i + u32(1) }
  }
  large: [2]WasmInstruction = [WasmInstruction { opcode: u32(66), immediate: i64(9223372036854775807) }, WasmInstruction { opcode: u32(66), immediate: i64(9223372036854775807) }]
  empty: [0]WasmInstruction
  true ? { dst: [*]u8 = span(&bytes)
    full: WasmAssembly = wasm_assemble(dst, u32(0), view(&large))
    assert(full.status == u32(1) && full.size == u32(0))
    outside: WasmAssembly = wasm_assemble(dst, u32(4294967295), view(&large))
    assert(outside.status == u32(1) && outside.size == u32(0))
    zero: WasmAssembly = wasm_assemble(dst, len(dst), view(&empty))
    assert(zero.status == u32(0) && zero.size == u32(0))
    i: u32 = 0
    while i < len(dst) { assert(dst[i] == u8(165)); i = i + u32(1) }
  }
  42
}
`)
	code, abnormal := buildAndRun(t, "selfhost_wasm", s.String())
	if abnormal || code != 42 {
		t.Fatalf("Oak assembler exit (%d,%v)", code, abnormal)
	}
	t.Logf("executed %d Go/Oak instruction comparisons with footprint and refusal checks", len(plans))
}

func TestE2ESelfHostedWasmLEB(t *testing.T) {
	core, err := os.ReadFile(filepath.Join("..", "asm", "selfhost", "wasm.oak"))
	if err != nil {
		t.Fatal(err)
	}
	var values, unsignedSizes, signedSizes []string
	var expected []byte
	for _, v := range selfhostWasmLEBValues() {
		u, s := encoding.AppendUnsigned(nil, v), encoding.AppendSigned(nil, int64(v))
		values = append(values, fmt.Sprintf("u64(%d)", v))
		unsignedSizes = append(unsignedSizes, fmt.Sprintf("u32(%d)", len(u)))
		signedSizes = append(signedSizes, fmt.Sprintf("u32(%d)", len(s)))
		expected = append(expected, u...)
		expected = append(expected, s...)
	}
	var source strings.Builder
	source.Write(core)
	source.WriteString("\nmain: (): i32 {\n  bytes: [24]u8\n")
	fmt.Fprintf(&source, "  values: [%d]u64 = [%s]\n  unsigned_sizes: [%d]u32 = [%s]\n  signed_sizes: [%d]u32 = [%s]\n", len(values), strings.Join(values, ","), len(values), strings.Join(unsignedSizes, ","), len(values), strings.Join(signedSizes, ","))
	fmt.Fprintf(&source, "  expected: [%d]u8 = [", len(expected))
	for i, b := range expected {
		if i > 0 {
			source.WriteString(",")
		}
		fmt.Fprintf(&source, "u8(%d)", b)
	}
	source.WriteString(`]
  case_index: u32 = 0
  expected_offset: u32 = 0
  while case_index < len(values) {
    value: u64 = values[case_index]
    unsigned_size: u32 = unsigned_sizes[case_index]
    signed_size: u32 = signed_sizes[case_index]
    true ? { dst: [*]u8 = span(&bytes)
      i: u32 = 0
      while i < len(dst) { dst[i] = u8(165); i = i + u32(1) }
      assert(wasm_uleb_size(value) == unsigned_size)
      assert(wasm_sleb_size(i64_bits_u64(value)) == signed_size)
      assert(wasm_write_uleb(dst, u32(2), value) == unsigned_size)
      assert(wasm_write_sleb(dst, u32(2) + unsigned_size, i64_bits_u64(value)) == signed_size)
      i = u32(0)
      while i < len(dst) {
        i >= u32(2) && i - u32(2) < unsigned_size + signed_size ? {
          assert(dst[i] == expected[expected_offset + i - u32(2)])
        } | { assert(dst[i] == u8(165)) }
        i = i + u32(1)
      }
      i = u32(0)
      while i < len(dst) { dst[i] = u8(165); i = i + u32(1) }
      assert(wasm_write_uleb(dst, u32(25) - unsigned_size, value) == u32(0))
      assert(wasm_write_sleb(dst, u32(25) - signed_size, i64_bits_u64(value)) == u32(0))
      assert(wasm_write_uleb(dst, u32(4294967295), value) == u32(0))
      assert(wasm_write_sleb(dst, u32(4294967295), i64_bits_u64(value)) == u32(0))
      i = u32(0)
      while i < len(dst) { assert(dst[i] == u8(165)); i = i + u32(1) }
    }
    expected_offset = expected_offset + unsigned_size + signed_size
    case_index = case_index + u32(1)
  }
  42
}
`)
	code, abnormal := buildAndRun(t, "selfhost_wasm_leb", source.String())
	if code != 42 || abnormal {
		t.Fatalf("Oak LEB encoder exit (%d,%v)", code, abnormal)
	}
	t.Logf("executed %d full-width Go/Oak LEB comparisons with frame and refusal checks", 2*len(values))
}

// Execute instruction bytes assembled by compiled Oak in an independent engine.
func TestE2ESelfHostedWasmExecution(t *testing.T) {
	engine := wasmtest.Require(t)
	core, err := os.ReadFile(filepath.Join("..", "asm", "selfhost", "wasm.oak"))
	if err != nil {
		t.Fatal(err)
	}
	// A module exporting main(x:i64,y:i64):i64, computing x*y + (-65).
	plan := []encoding.Instruction{{Opcode: 0x20, Immediate: 0}, {Opcode: 0x20, Immediate: 1}, {Opcode: 0x7e}, {Opcode: 0x42, Immediate: -65}, {Opcode: 0x7c}, {Opcode: 0x0b}}
	want, err := encoding.Assemble(plan)
	if err != nil {
		t.Fatal(err)
	}
	var s strings.Builder
	s.Write(core)
	s.WriteString("\nputchar: (ch: c.Int): c.Int = c.extern(\"putchar\")\nmain: (): i32 {\n  bytes: [64]u8\n")
	fmt.Fprintf(&s, "  plan: [%d]WasmInstruction = [", len(plan))
	for i, ins := range plan {
		if i > 0 {
			s.WriteString(",")
		}
		fmt.Fprintf(&s, "WasmInstruction { opcode: u32(%d), immediate: i64(%d) }", ins.Opcode, ins.Immediate)
	}
	s.WriteString("]\n  size: u32 = 0\n  true ? { dst: [*]u8 = span(&bytes)\n    r: WasmAssembly = wasm_assemble(dst, u32(0), view(&plan))\n    assert(r.status == u32(0))\n    size = r.size\n  }\n  i: u32 = 0\n  while i < size { putchar(c.Int(i32_bits_u32(u32(bytes[i])))); i = i + u32(1) }\n  0\n}\n")
	out, code, abnormal := buildAndRunOutput(t, "selfhost_wasm_execution", s.String())
	if abnormal || code != 0 || !bytes.Equal([]byte(out), want) {
		t.Fatalf("Oak output %x, want %x, exit (%d,%v)", out, want, code, abnormal)
	}
	module := []byte{0, 97, 115, 109, 1, 0, 0, 0, 1, 7, 1, 0x60, 2, 0x7e, 0x7e, 1, 0x7e, 3, 2, 1, 0, 7, 8, 1, 4, 'm', 'a', 'i', 'n', 0, 0}
	body := append([]byte{0}, []byte(out)...)
	payload := encoding.AppendUnsigned([]byte{1}, uint64(len(body)))
	payload = append(payload, body...)
	module = encoding.AppendUnsigned(append(module, 10), uint64(len(payload)))
	module = append(module, payload...)
	if _, err := check.Validate(module); err != nil {
		t.Fatal(err)
	}
	script := `const b=Uint8Array.from(atob(process.argv[1]),c=>c.charCodeAt(0));
const e=new WebAssembly.Instance(new WebAssembly.Module(b),{}).exports;
for(const x of [0n,1n,-1n,9223372036854775807n,-9223372036854775808n])
for(const y of [0n,1n,-1n,63n,9223372036854775807n])
if(e.main(x,y)!==BigInt.asIntN(64,x*y-65n))throw Error('Oak assembler mismatch');`
	script = strings.Replace(script, "process.argv[1]", `(typeof Deno!=="undefined"?Deno.args[0]:process.argv[1])`, 1)
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script, base64.StdEncoding.EncodeToString(module)).CombinedOutput(); err != nil {
		t.Fatalf("Wasm engine: %v\n%s", err, out)
	}
}

// Shared with the kernel-checked extraction oracle. Both consumers use the
// production Go encoder as the byte oracle, including expected refusals.
type selfhostWasmInstruction struct {
	opcode    uint32
	immediate int64
}

func selfhostWasmInstructionCases() []selfhostWasmInstruction {
	var cases []selfhostWasmInstruction
	add := func(op uint32, v int64) { cases = append(cases, selfhostWasmInstruction{op, v}) }

	for op := uint32(0); op < 256; op++ {
		add(op, 0)
		add(op, 1)   // nonzero immediates must refuse on every plain instruction
		add(op, 126) // nested block-type predicates must not admit other opcodes
	}
	for _, op := range []uint32{2, 3, 4, 12, 13, 16, 32, 33, 34, 65, 66} {
		for _, v := range []int64{math.MinInt64, math.MinInt32 - 1, math.MinInt32, -8193, -65, -64, -1, 1, 63, 64, 126, 127, 128, 8192, math.MaxInt32, math.MaxInt32 + 1, math.MaxUint32, math.MaxUint32 + 1, math.MaxInt64} {
			add(op, v)
		}
	}
	for _, op := range []uint32{256, 258, math.MaxUint32} {
		add(op, 0)
	}
	rng := rand.New(rand.NewSource(20261006))
	for i := 0; i < 40; i++ {
		add(66, int64(rng.Uint64()))
	}
	return cases
}

func selfhostWasmLEBValues() []uint64 {
	var values []uint64
	for shift := uint(0); shift < 64; shift++ {
		values = append(values, 1<<shift-1, 1<<shift, ^uint64(0)-(1<<shift-1))
	}
	return values
}

type selfhostWasmPlanCase struct {
	plan     []encoding.Instruction
	offset   uint32
	capacity int
}

func selfhostWasmPlanCases() []selfhostWasmPlanCase {
	plans := [][]encoding.Instruction{
		nil,
		{{Opcode: 0x0b}},
		{{Opcode: 0x41, Immediate: math.MinInt32}, {Opcode: 0x42, Immediate: math.MinInt64}, {Opcode: 0x6a}},
		{{Opcode: 0x02, Immediate: 0x40}, {Opcode: 0x20, Immediate: math.MaxUint32}, {Opcode: 0x0b}},
		{{Opcode: 0x01}, {Opcode: 0xff}},                                // late invalid opcode
		{{Opcode: 0x42, Immediate: -65}, {Opcode: 0x20, Immediate: -1}}, // late invalid immediate
	}
	// Put a maximum-width operand after enough instructions to exceed the
	// former fixed extraction budget; both production and Lean share this plan.
	longPlan := make([]encoding.Instruction, 8)
	for i := range longPlan {
		longPlan[i] = encoding.Instruction{Opcode: 0x01}
	}
	longPlan[len(longPlan)-1] = encoding.Instruction{Opcode: 0x42, Immediate: math.MinInt64}
	plans = append(plans, longPlan)
	var cases []selfhostWasmPlanCase
	for _, plan := range plans {
		encoded, _ := encoding.Assemble(plan)
		for _, pair := range []struct {
			offset   uint32
			capacity int
		}{
			{0, 0}, {2, 32}, {2, 2 + len(encoded)}, {3, 2 + len(encoded)}, {math.MaxUint32, 32},
		} {
			cases = append(cases, selfhostWasmPlanCase{plan, pair.offset, pair.capacity})
		}
	}
	return cases
}

func (tc selfhostWasmPlanCase) expected() (status, size uint32, dst []byte) {
	dst = bytes.Repeat([]byte{165}, tc.capacity)
	encoded, err := encoding.Assemble(tc.plan)
	if err != nil || uint64(tc.offset)+uint64(len(encoded)) > uint64(tc.capacity) {
		return 1, 0, dst
	}
	copy(dst[tc.offset:], encoded)
	return 0, uint32(len(encoded)), dst
}

func (tc selfhostWasmPlanCase) leanPlan() string {
	var items []string
	for _, ins := range tc.plan {
		items = append(items, fmt.Sprintf("{ opcode := %d, immediate := (%d) }", ins.Opcode, ins.Immediate))
	}
	return "#[" + strings.Join(items, ",") + "]"
}

func TestE2ESelfHostedWasmTransactions(t *testing.T) {
	core, err := os.ReadFile(filepath.Join("..", "asm", "selfhost", "wasm.oak"))
	if err != nil {
		t.Fatal(err)
	}
	var source strings.Builder
	source.Write(core)
	source.WriteString("\nmain: (): i32 {\n")
	for _, tc := range selfhostWasmPlanCases() {
		status, size, dst := tc.expected()
		fmt.Fprintf(&source, " true ? {\n bytes: [%d]u8\n plan: [%d]WasmInstruction", tc.capacity, len(tc.plan))
		if len(tc.plan) != 0 {
			source.WriteString(" = [")
			for i, ins := range tc.plan {
				if i != 0 {
					source.WriteString(",")
				}
				fmt.Fprintf(&source, "WasmInstruction { opcode: u32(%d), immediate: i64_bits_u64(u64(%d)) }", ins.Opcode, uint64(ins.Immediate))
			}
			source.WriteString("]")
		}
		fmt.Fprintf(&source, "\n expected: [%d]u8", len(dst))
		if len(dst) != 0 {
			source.WriteString(" = [")
			for i, b := range dst {
				if i != 0 {
					source.WriteString(",")
				}
				fmt.Fprintf(&source, "u8(%d)", b)
			}
			source.WriteString("]")
		}
		source.WriteString("\n dst: [*]u8 = span(&bytes)\n i: u32 = 0\n while i < len(dst) { dst[i] = u8(165); i = i + u32(1) }\n")
		fmt.Fprintf(&source, " result: WasmAssembly = wasm_assemble(dst, u32(%d), view(&plan))\n assert(result.status == u32(%d) && result.size == u32(%d))\n", tc.offset, status, size)
		source.WriteString(" i = u32(0)\n while i < len(dst) { assert(dst[i] == expected[i]); i = i + u32(1) }\n }\n")
	}
	source.WriteString(" 42\n}\n")
	code, abnormal := buildAndRun(t, "selfhost_wasm_transactions", source.String())
	if code != 42 || abnormal {
		t.Fatalf("Oak assembly transaction exit (%d,%v)", code, abnormal)
	}
	t.Logf("executed %d shared-corpus transactions with full-buffer comparisons", len(selfhostWasmPlanCases()))
}
