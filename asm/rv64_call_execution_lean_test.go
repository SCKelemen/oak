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

// Independent architectural execution of the emitted subset. It reads the
// source before committing the destination, including when rd == rs1.
func rv64ExecuteCallBytes(t *testing.T, code []byte, pc uint64, regs [32]uint64) (uint64, [32]uint64) {
	t.Helper()
	for off := 0; off < len(code); {
		if len(code)-off < 2 {
			t.Fatal("truncated instruction")
		}
		half := binary.LittleEndian.Uint16(code[off:])
		var rd int
		var value, next uint64
		if half&3 == 3 {
			if len(code)-off < 4 {
				t.Fatal("truncated word")
			}
			w := binary.LittleEndian.Uint32(code[off:])
			rd = int(w >> 7 & 31)
			rs := int(w >> 15 & 31)
			imm := uint64(int64(int32(w) >> 20))
			next = pc + 4
			switch {
			case w&127 == 0x17:
				value = pc + uint64(int64(int32(w&0xfffff000)))
			case w&0x707f == 0x13:
				value = regs[rs] + imm
			case w&0x707f == 0x67:
				value, next = pc+4, (regs[rs]+imm)&^1
			default:
				t.Fatalf("unexpected word %08x", w)
			}
			off += 4
		} else {
			rs := int(half >> 7 & 31)
			if rs == 0 {
				t.Fatal("reserved or EBREAK compressed jump")
			}
			switch half & 0xf07f {
			case 0x8002:
				rd = 0
			case 0x9002:
				rd = 1
			default:
				t.Fatalf("unexpected halfword %04x", half)
			}
			value, next = pc+2, regs[rs]&^1
			off += 2
		}
		if rd != 0 {
			regs[rd] = value
		}
		regs[0] = 0
		pc = next
	}
	return pc, regs
}

func rv64CallPins(t *testing.T) []string {
	t.Helper()
	var pins []string
	reg := func(n int) Register { return Register{Class: ClassRV64X, Num: n, Lane: -1} }
	check := func(code []byte, pc, initial uint64, rd int, wantPC, wantRD uint64) {
		var regs [32]uint64
		for i := 1; i < 32; i++ {
			regs[i] = initial
		}
		gotPC, after := rv64ExecuteCallBytes(t, code, pc, regs)
		if gotPC != wantPC {
			t.Fatalf("%x pc=%x want %x", code, gotPC, wantPC)
		}
		for i, v := range after {
			want := regs[i]
			if i == rd && rd != 0 {
				want = wantRD
			}
			if v != want {
				t.Fatalf("%x x%d=%x want %x", code, i, v, want)
			}
		}
		bs := make([]string, len(code))
		for i, b := range code {
			bs[i] = fmt.Sprintf("%d#8", b)
		}
		pins = append(pins, fmt.Sprintf("example : observe [%s] 0x%x#64 0x%x#64 %d#5 = some (0x%x#64, 0x%x#64, 0#64) := by decide", strings.Join(bs, ","), pc, initial, rd, wantPC, after[rd]))
	}
	// Obtain pairs and relocation metadata from the real function encoder, then
	// apply the real symbol resolver. A leading NOP tests nonzero relocation offsets.
	for _, compressed := range []bool{false, true} {
		for _, call := range []bool{false, true} {
			for _, rd := range []int{1, 2, 8, 31} {
				if call && rd != 1 {
					continue
				}
				instr := Instruction{Mnemonic: "la", Operands: []Operand{reg(rd), Symbol{Name: "target"}}}
				if call {
					instr = Instruction{Mnemonic: "call", Operands: []Operand{Symbol{Name: "target"}}}
				}
				fn := &Function{Name: "pair", Arch: ArchRV64, Compressed: compressed, Items: []Item{Instruction{Mnemonic: "nop"}, instr}}
				code, relocs, err := encodeRV64Function(fn)
				if err != nil || len(relocs) != 1 {
					t.Fatalf("encode pair: %v %v", err, relocs)
				}
				rel := relocs[0]
				offset := 4
				if compressed {
					offset = 2
				}
				kind := "riscv_pcrel"
				if call {
					kind = "riscv_call_plt"
				}
				if rel.Offset != offset || rel.Kind != kind || rel.Symbol != "target" || len(code) != offset+8 {
					t.Fatalf("pair layout/relocation: %x %+v", code, rel)
				}
				for _, place := range []uint64{uint64(1) << 33, ^uint64(0) - 7} {
					for _, delta := range []int64{-2147485696, -2147483648, -4097, -2049, -2048, -2, -1, 0, 1, 2, 2047, 2048, 4096, 2147481598, 2147481599} {
						if call && delta&1 != 0 {
							continue
						}
						if delta > 0 && uint64(delta) > ^uint64(0)-place {
							continue
						}
						target := place + uint64(delta)
						text := append([]byte(nil), code...)
						layout := &textLayout{text: text, relocs: []placedReloc{{offset: int64(offset), kind: kind, symbol: "target"}}}
						if err := resolveRelocations(layout, place-uint64(offset), map[string]uint64{"target": target}); err != nil {
							t.Fatal(err)
						}
						if string(text[:offset]) != string(code[:offset]) {
							t.Fatal("relocation changed prefix")
						}
						wantPC, wantRD := place+8, target
						if call {
							wantPC, wantRD = target, place+8
						}
						check(text[offset:], place, 0xfedcba9876543211, rd, wantPC, wantRD)
					}
				}
			}
		}
	}
	// All source registers; all destination/source alias classes; immediate
	// boundaries; odd targets and u64 wrap; compressed and ordinary link lengths.
	for _, compressed := range []bool{false, true} {
		for rs := 0; rs < 32; rs++ {
			for _, rd := range []int{0, 1, rs, 31} {
				for _, imm := range []int64{-2048, -1, 0, 1, 2047} {
					instr := Instruction{Mnemonic: "jalr", Operands: []Operand{reg(rd), Memory{Base: reg(rs), Offset: imm, Mode: MemOffset}}}
					code, relocs, err := encodeRV64Function(&Function{Name: "indirect", Arch: ArchRV64, Compressed: compressed, Items: []Item{instr}})
					if err != nil || len(relocs) != 0 {
						t.Fatalf("jalr: %v", err)
					}
					for _, initial := range []uint64{0, 1, ^uint64(0), 0x8000000000000001} {
						base := initial
						if rs == 0 {
							base = 0
						}
						pc := ^uint64(0) - 1
						check(code, pc, initial, rd, (base+uint64(imm))&^1, pc+uint64(len(code)))
					}
				}
			}
		}
		for _, name := range []string{"ret", "jr"} {
			for rs := 1; rs < 32; rs++ {
				if name == "ret" && rs != 1 {
					continue
				}
				instr := Instruction{Mnemonic: name}
				if name == "jr" {
					instr.Operands = []Operand{reg(rs)}
				}
				code, _, err := encodeRV64Function(&Function{Name: name, Arch: ArchRV64, Compressed: compressed, Items: []Item{instr}})
				if err != nil {
					t.Fatal(err)
				}
				check(code, 0x1002, 0x12345679, 0, 0x12345678, 0)
			}
		}
	}
	return pins
}

func TestRV64CallExecutionBytes(t *testing.T) { t.Logf("checked %d streams", len(rv64CallPins(t))) }
func TestRV64CallExecutionMatchesLean(t *testing.T) {
	pins := rv64CallPins(t)
	source := "import Oak.RiscVCallExecution\nopen Oak.RiscVCallExecution\n" + strings.Join(pins, "\n") + "\n"
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_RV64_LEAN") != "" {
			t.Fatal("lake required for RV64 call execution")
		}
		t.Skip("lake unavailable; formal CI requires this oracle")
	}
	path := filepath.Join(t.TempDir(), "RV64CallProductionPins.lean")
	if err := os.WriteFile(path, []byte(source), 0600); err != nil {
		t.Fatal(err)
	}
	buildLeanImports(t, lake, path)
	cmd := exec.Command(lake, "env", "lean", path)
	cmd.Dir = filepath.Join("..", "spec", "lean")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("Lean call execution: %v\n%s", err, out)
	}
	t.Logf("checked %d Lean claims", len(pins))
}
