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

func rv64DirectDecision(name string, a, b uint64) bool {
	switch name {
	case "beq":
		return a == b
	case "bne":
		return a != b
	case "blt":
		return int64(a) < int64(b)
	case "bge":
		return int64(a) >= int64(b)
	case "bltu":
		return a < b
	case "bgeu":
		return a >= b
	}
	panic("unknown branch")
}

// Decode the actual instruction independently of the encoder and verifier.
func rv64DirectExecute(t *testing.T, code []byte, pc uint64, regs [32]uint64) (uint64, [32]uint64) {
	t.Helper()
	next := pc + uint64(len(code))
	rd := -1
	var delta int64
	var take bool
	if len(code) == 4 {
		w := binary.LittleEndian.Uint32(code)
		switch w & 127 {
		case 0x6f:
			rd = int(w >> 7 & 31)
			delta = rv64ProofDisplacement("jal", w)
			take = true
		case 0x63:
			names := map[uint32]string{0: "beq", 1: "bne", 4: "blt", 5: "bge", 6: "bltu", 7: "bgeu"}
			name, ok := names[w>>12&7]
			if !ok {
				t.Fatal("reserved branch condition")
			}
			take = rv64DirectDecision(name, regs[w>>15&31], regs[w>>20&31])
			delta = rv64ProofDisplacement(name, w)
		default:
			t.Fatalf("unexpected direct word %08x", w)
		}
	} else if len(code) == 2 {
		w := binary.LittleEndian.Uint16(code)
		rs := 8 + int(w>>7&7)
		switch w & 0xe003 {
		case 0xc001:
			take = regs[rs] == 0
		case 0xe001:
			take = regs[rs] != 0
		case 0xa001:
			take = true
			rd = 0
		default:
			t.Fatalf("unexpected direct halfword %04x", w)
		}
		delta = rv64ProofCompressedDisplacement(rd == 0, w)
	} else {
		t.Fatal("bad instruction length")
	}
	if rd > 0 {
		regs[rd] = next
	}
	if take {
		next = pc + uint64(delta)
	}
	return next, regs
}

func rv64DirectPins(t *testing.T) []string {
	t.Helper()
	var pins []string
	values := [][2]uint64{{0, 0}, {0, 1}, {1, 0}, {^uint64(0), 0}, {1 << 63, 0}, {1 << 63, ^uint64(0)}, {^uint64(0), 1 << 63}, {0xffffffff, 0x100000000}, {^uint64(0), ^uint64(0)}}
	reg := func(n int) Register { return Register{Class: ClassRV64X, Num: n, Lane: -1} }
	check := func(instr Instruction, code []byte, pc uint64, delta int64, r1, r2 int, a, b uint64) {
		var before [32]uint64
		for r := 1; r < 32; r++ {
			before[r] = 99
			if r == r1 {
				before[r] = a
			} else if r == r2 {
				before[r] = b
			}
		}
		base := rv64Base(instr)
		rd := -1
		take := true
		if base.Mnemonic == "jal" {
			rd = base.Operands[0].(Register).Num
		} else {
			rs1 := rv64Number(base.Operands[0].(Register))
			rs2 := rv64Number(base.Operands[1].(Register))
			take = rv64DirectDecision(base.Mnemonic, before[rs1], before[rs2])
			state := &symbolicState{arch: ArchRV64, regs: map[int]*term{}}
			for r := 1; r < 32; r++ {
				state.regs[r] = constTerm(before[r], 64)
			}
			cond, reason, ok := branchCondition(instr, state)
			if !ok || cond == nil || (cond.eval(nil) != 0) != take {
				t.Fatalf("verifier %s: %s", instr.Mnemonic, reason)
			}
		}
		wantPC := pc + uint64(len(code))
		if take {
			wantPC = pc + uint64(delta)
		}
		gotPC, after := rv64DirectExecute(t, code, pc, before)
		if gotPC != wantPC {
			t.Fatalf("%s %x pc=%x want %x", instr.Mnemonic, code, gotPC, wantPC)
		}
		for r, v := range after {
			want := before[r]
			if r == rd && rd > 0 {
				want = pc + uint64(len(code))
			}
			if v != want {
				t.Fatalf("%s x%d=%x want %x", instr.Mnemonic, r, v, want)
			}
		}
		dest := r1
		if rd >= 0 {
			dest = rd
		}
		bs := make([]string, len(code))
		for i, b := range code {
			bs[i] = fmt.Sprintf("%d#8", b)
		}
		pins = append(pins, fmt.Sprintf("example : observe [%s] 0x%x#64 0x%x#64 0x%x#64 %d#5 %d#5 %d#5 = some (0x%x#64,0x%x#64,0#64) := by decide", strings.Join(bs, ","), pc, a, b, r1, r2, dest, wantPC, after[dest]))
	}
	// Every register number, all six conditions, signed/unsigned edge values,
	// both displacement endpoints and zero, plus PC wrap at execution time.
	for _, name := range rv64BranchProofMnemonics {
		for r := 0; r < 32; r++ {
			instr := rv64ProofBranch(name, r, 31-r)
			deltas := []int64{-4096, 0, 4094}
			vs := values
			if name == "jal" {
				deltas = []int64{-1048576, 0, 1048574}
				vs = values[:1]
			}
			for _, d := range deltas {
				w, err := encodeRV64Instruction(instr, 1<<21, map[string]int64{"target": (1 << 21) + d})
				if err != nil {
					t.Fatal(err)
				}
				code := binary.LittleEndian.AppendUint32(nil, w)
				for _, v := range vs {
					check(instr, code, ^uint64(0)-1, d, r, 31-r, v[0], v[1])
				}
			}
		}
	}
	// Equal source registers, including x0, exercise aliasing separately.
	for _, name := range rv64BranchProofMnemonics[:6] {
		for _, r := range []int{0, 1, 8, 31} {
			instr := rv64ProofBranch(name, r, r)
			w, err := encodeRV64Instruction(instr, 0, map[string]int64{"target": 8})
			if err != nil {
				t.Fatal(err)
			}
			check(instr, binary.LittleEndian.AppendUint32(nil, w), 0, 8, r, r, ^uint64(0), 0)
		}
	}
	// Compression and pseudo lowering go through full function layout. Test
	// both forward and backward labels and the actual resulting instruction size.
	names := []string{"beqz", "bnez", "bgez", "bltz", "blez", "bgtz", "j"}
	for _, compressed := range []bool{false, true} {
		for _, backward := range []bool{false, true} {
			for _, name := range names {
				for _, r := range []int{0, 1, 8, 15, 31} {
					instr := Instruction{Mnemonic: name, Operands: []Operand{reg(r), Symbol{Name: "target"}}}
					if name == "j" {
						instr.Operands = []Operand{Symbol{Name: "target"}}
					}
					nops := []Item{Instruction{Mnemonic: "nop"}, Instruction{Mnemonic: "nop"}}
					items := []Item{instr}
					items = append(items, nops...)
					items = append(items, Label{Name: "target"})
					if backward {
						items = []Item{Label{Name: "target"}}
						items = append(items, nops...)
						items = append(items, instr)
					}
					code, relocs, err := encodeRV64Function(&Function{Name: "branch", Arch: ArchRV64, Compressed: compressed, Items: items})
					if err != nil || len(relocs) != 0 {
						t.Fatalf("%s: %v", name, err)
					}
					padding := 8
					if compressed {
						padding = 4
					}
					var insn []byte
					var d int64
					if backward {
						insn = code[padding:]
						d = -int64(padding)
					} else {
						insn = code[:len(code)-padding]
						d = int64(len(code))
					}
					for _, a := range []uint64{0, 1, 1 << 63} {
						check(instr, insn, 0x1002, d, r, 0, a, 0)
					}
				}
			}
		}
	}
	return pins
}
func TestRV64DirectControlBytes(t *testing.T) { t.Logf("checked %d streams", len(rv64DirectPins(t))) }
func TestRV64DirectControlMatchesLean(t *testing.T) {
	pins := rv64DirectPins(t)
	source := "import Oak.RiscVDirectControl\nopen Oak.RiscVDirectControl\n" + strings.Join(pins, "\n") + "\n"
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_RV64_LEAN") != "" {
			t.Fatal("lake required for RV64 direct control")
		}
		t.Skip("lake unavailable; formal CI requires this oracle")
	}
	path := filepath.Join(t.TempDir(), "RV64DirectControlPins.lean")
	if err := os.WriteFile(path, []byte(source), 0600); err != nil {
		t.Fatal(err)
	}
	buildLeanImports(t, lake, path)
	cmd := exec.Command(lake, "env", "lean", path)
	cmd.Dir = filepath.Join("..", "spec", "lean")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("Lean direct control: %v\n%s", err, out)
	}
	t.Logf("checked %d Lean claims", len(pins))
}
