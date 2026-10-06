package asm

import (
	"encoding/binary"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

var rv64LiteralBoundaries = []int64{
	-2147483648, -2147483647, -2147481601, -2147481600,
	-131073, -131072, -131071, -4097, -4096, -4095, -2049, -2048, -2047,
	-33, -32, -31, -1, 0, 1, 31, 32, 33, 2047, 2048, 2049,
	4095, 4096, 4097, 126976, 131071, 131072,
	2147481599, 2147481600, 2147481601, 2147483646, 2147483647,
}

// Interpret only the materializer's emitted instruction subset, independently
// of rv64Base, rv64Expand, the field table, and rvcForm. Registers are updated
// after each decoded instruction, including x0's discard rule.
func rv64ExecuteLiteral(t *testing.T, code []byte, rd int, regs [32]uint64) ([32]uint64, []string) {
	t.Helper()
	var forms []string
	for pc := 0; pc < len(code); {
		if len(code)-pc < 2 {
			t.Fatal("truncated halfword")
		}
		half := binary.LittleEndian.Uint16(code[pc:])
		dst := int(half >> 7 & 31)
		var value uint64
		var form string
		if half&3 == 3 {
			if len(code)-pc < 4 {
				t.Fatal("truncated word")
			}
			word := binary.LittleEndian.Uint32(code[pc:])
			src := int(word >> 15 & 31)
			imm := int64(int32(word) >> 20)
			switch {
			case word&127 == 0x37:
				form, value = "lui", uint64(int64(int32(word&0xfffff000)))
			case word&0x707f == 0x13 && src == 0:
				form, value = "addi", uint64(imm)
			case word&0x707f == 0x1b && src == dst:
				form, value = "addiw", uint64(int64(int32(uint32(regs[src])+uint32(imm))))
			default:
				t.Fatalf("unexpected materialization word %#08x at %d", word, pc)
			}
			pc += 4
		} else {
			imm := int64(int8(((half>>12)&1)<<5|((half>>2)&31))<<2) >> 2
			switch {
			case half == 1 && rd == 0:
				form, value = "c.nop", 0
			case half&0xe003 == 0x4001 && dst != 0:
				form, value = "c.li", uint64(imm)
			case half&0xe003 == 0x6001 && dst != 0 && dst != 2 && imm != 0:
				form, value = "c.lui", uint64(imm<<12)
			case half&0xe003 == 0x2001 && dst != 0:
				form, value = "c.addiw", uint64(int64(int32(uint32(regs[dst])+uint32(imm))))
			default:
				t.Fatalf("unexpected materialization halfword %#04x at %d", half, pc)
			}
			pc += 2
		}
		if dst != rd {
			t.Fatalf("instruction wrote x%d, want x%d", dst, rd)
		}
		if dst != 0 {
			regs[dst] = value
		}
		forms = append(forms, form)
	}
	return regs, forms
}

func rv64Literal(t *testing.T, value int64, rd int, compressed bool) ([]byte, []string, []string, uint64) {
	t.Helper()
	reg := Register{Class: ClassRV64X, Num: rd, Lane: -1}
	instr := Instruction{Mnemonic: "li", Operands: []Operand{reg, Immediate{Value: value}}}
	fn := &Function{Name: "literal", Arch: ArchRV64, Compressed: compressed, Items: []Item{
		Label{Name: "begin"}, instr, Label{Name: "end"},
	}}
	units, labels, err := rv64Expand(fn)
	if err != nil {
		t.Fatalf("li x%d, %d: %v", rd, value, err)
	}
	if len(units) < 1 || len(units) > 2 || rv64Words(instr) != len(units) || labels["begin"] != 0 || labels["end"] != len(units) {
		t.Fatalf("bad expansion length/labels: %d, %v", len(units), labels)
	}
	var expansion []string
	for _, unit := range units {
		ops := unit.base.Operands
		if unit.size != 4 || unit.fromCall || unit.callSym != "" || unit.laSym != "" || ops[0].(Register).Num != rd {
			t.Fatal("invalid expansion metadata or destination")
		}
		imm := ops[len(ops)-1].(Immediate).Value
		switch unit.base.Mnemonic {
		case "addi":
			if ops[1].(Register).Num != 0 || imm < -2048 || imm > 2047 {
				t.Fatal("ADDI must read zero and carry a signed 12-bit immediate")
			}
		case "addiw":
			if ops[1].(Register).Num != rd || imm < -2048 || imm > 2047 {
				t.Fatal("ADDIW must read the destination and carry a signed 12-bit immediate")
			}
		case "lui":
			if imm < -(1<<19) || imm >= 1<<20 {
				t.Fatal("LUI immediate is not encodable")
			}
		default:
			t.Fatalf("unexpected expansion mnemonic %s", unit.base.Mnemonic)
		}
		expansion = append(expansion, fmt.Sprintf(".%s (%d)", unit.base.Mnemonic, imm))
	}
	code, relocs, err := encodeRV64Function(fn)
	if err != nil || len(relocs) != 0 || len(code) < 2 || len(code) > 8 || (!compressed && len(code) != 4*len(units)) {
		t.Fatalf("li x%d, %d, rvc=%v: bytes=%x relocs=%v err=%v", rd, value, compressed, code, relocs, err)
	}
	var before [32]uint64
	for i := 1; i < len(before); i++ {
		before[i] = 0xfedcba9876543210 ^ uint64(i)*0x0101010101010101
	}
	after, forms := rv64ExecuteLiteral(t, code, rd, before)
	for i, got := range after {
		want := before[i]
		if i == rd && rd != 0 {
			want = uint64(value)
		}
		if got != want {
			t.Fatalf("li x%d, %d, rvc=%v (%x): x%d=%#016x want %#016x", rd, value, compressed, code, i, got, want)
		}
	}
	return code, expansion, forms, before[rd]
}

func TestRV64MaterializationBoundaries(t *testing.T) {
	seen := map[string]bool{}
	for _, value := range rv64LiteralBoundaries {
		for rd := 0; rd < 32; rd++ {
			for _, compressed := range []bool{false, true} {
				_, _, forms, _ := rv64Literal(t, value, rd, compressed)
				for _, form := range forms {
					seen[form] = true
				}
			}
		}
	}
	for _, form := range []string{"addi", "lui", "addiw", "c.nop", "c.li", "c.lui", "c.addiw"} {
		if !seen[form] {
			t.Errorf("no emitted %s was exercised", form)
		}
	}
}

// Every signed 12-bit remainder at ten upper-part boundaries. Invalid values
// at the two signed-32 endpoints are omitted: 36,864 distinct valid literals,
// x2 and x8, with and without RVC = 147,456 actual function byte streams.
func TestRV64MaterializationCarrySweep(t *testing.T) {
	for _, upper := range []int64{-524288, -33, -32, -1, 0, 1, 31, 32, 524287, 524288} {
		for lower := int64(-2048); lower <= 2047; lower++ {
			value := upper*4096 + lower
			if value < -(1<<31) || value >= 1<<31 {
				continue
			}
			hi, lo := rv64SplitImmediate(value)
			if hi != upper || lo != lower {
				t.Fatalf("split(%d)=(%d,%d), want (%d,%d)", value, hi, lo, upper, lower)
			}
			for _, rd := range []int{2, 8} {
				for _, compressed := range []bool{false, true} {
					rv64Literal(t, value, rd, compressed)
				}
			}
		}
	}
}

func TestRV64MaterializationMatchesLean(t *testing.T) {
	var claims []string
	for _, value := range rv64LiteralBoundaries {
		hi, lo := rv64SplitImmediate(value)
		claims = append(claims, fmt.Sprintf("example : (high (%d), low (%d)) = (%d, %d) := by decide", value, value, hi, lo))
		for _, rd := range []int{0, 1, 2, 8, 31} {
			for _, compressed := range []bool{false, true} {
				code, expansion, _, initial := rv64Literal(t, value, rd, compressed)
				if rd == 0 && !compressed {
					claims = append(claims, fmt.Sprintf("example : expand (%d) = some [%s] := by decide", value, strings.Join(expansion, ", ")))
				}
				bytes := make([]string, len(code))
				for i, b := range code {
					bytes[i] = fmt.Sprintf("%d#8", b)
				}
				want := uint64(value)
				if rd == 0 {
					want = 0
				}
				claims = append(claims, fmt.Sprintf("example : observeBytes %d#5 0x%016x#64 [%s] = some 0x%016x#64 := by decide", rd, initial, strings.Join(bytes, ", "), want))
			}
		}
	}
	const max = int64(^uint64(0) >> 1)
	for _, value := range []int64{-max - 1, -(1 << 31) - 1, 1 << 31, max} {
		for _, compressed := range []bool{false, true} {
			fn := &Function{Name: "invalid", Arch: ArchRV64, Compressed: compressed, Items: []Item{
				Instruction{Mnemonic: "li", Operands: []Operand{Register{Class: ClassRV64X, Num: 8, Lane: -1}, Immediate{Value: value}}},
			}}
			if code, relocs, err := encodeRV64Function(fn); err == nil || len(code) != 0 || len(relocs) != 0 {
				t.Fatalf("invalid li %d accepted: %x %v %v", value, code, relocs, err)
			}
		}
		claims = append(claims, fmt.Sprintf("example : expand (%d) = none := by decide", value))
	}
	source := "import Oak.RiscVMaterialization\nopen Oak.RiscVMaterialization\n" + strings.Join(claims, "\n") + "\n"
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_RV64_LEAN") != "" {
			t.Fatal("lake required for RV64 materialization correspondence")
		}
		t.Skip("lake not on PATH; formal workflow requires this oracle")
	}
	path := filepath.Join(t.TempDir(), "RV64MaterializationProductionPins.lean")
	if err := os.WriteFile(path, []byte(source), 0600); err != nil {
		t.Fatal(err)
	}
	buildLeanImports(t, lake, path)
	cmd := exec.Command(lake, "env", "lean", path)
	cmd.Dir = filepath.Join("..", "spec", "lean")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("RV64 materialization correspondence: %v\n%s", err, out)
	}
	t.Logf("checked %d Lean production claims", len(claims))
}
