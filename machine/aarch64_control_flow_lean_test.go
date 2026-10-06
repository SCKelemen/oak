package machine

import (
	"encoding/binary"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/optir"
)

func TestAArch64ControlFlowAlwaysEdges(t *testing.T) {
	for _, mnemonic := range []string{"b.", "b"} {
		for _, cond := range []string{"eq", "ne", "cs", "cc", "mi", "pl", "vs", "vc", "hi", "ls", "ge", "lt", "gt", "le", "al", "nv"} {
			branch := asm.Instruction{Mnemonic: mnemonic, Cond: cond, Operands: []asm.Operand{sym("out")}}
			lifted, err := Lift(fn(branch, ins("nop"), ins("ret"), label("out"), ins("ret")))
			if err != nil {
				t.Fatal(err)
			}
			want := 2
			if cond == "al" || cond == "nv" {
				want = 1
			}
			succs := lifted.Blocks[0].Succs
			if len(succs) != want || succs[0].Label != "out" {
				t.Fatalf("%s/%s successors = %v, want target and %d total", mnemonic, cond, succs, want)
			}
		}
	}
}

// Exercise the actual selector's terminator, then EncodeFunction's label
// layout and bytes. The Lean certificate composes with checked_successor for
// every register/flag state, not just two sampled Bool inputs.
func TestAArch64ControlFlowSelectorMatchesLean(t *testing.T) {
	var examples []string
	shapes := map[string]bool{}
	for _, order := range aarch64BlockOrders(nil, []int{0, 1, 2, 3}) {
		for _, same := range []bool{false, true} {
			for _, register := range []int{0, 9, 15, 16} {
				yes, no := optir.BlockID(1), optir.BlockID(2)
				if same {
					no = yes
				}
				var next optir.BlockID
				hasNext := false
				for i, id := range order {
					if id == 0 && i+1 < len(order) {
						next, hasNext = optir.BlockID(order[i+1]), true
					}
				}
				selector := optIRArm64Selector{
					cfg:   optir.CFG{Blocks: []optir.Block{{ID: 1}, {ID: 2}, {ID: 3}}},
					types: map[optir.ValueID]optir.Type{1: optir.TypeBool}, colors: map[optir.ValueID]int{1: register},
					labels: map[optir.BlockID]string{1: "b1", 2: "b2", 3: "b3"},
				}
				block := optir.Block{ID: 0, Terminator: optir.Terminator{Kind: optir.TerminatorCondBranch,
					Condition: 1, True: optir.Edge{Target: yes}, False: optir.Edge{Target: no}}}
				if err := selector.terminator(block, next, hasNext, 1); err != nil {
					t.Fatal(err)
				}
				var items []asm.Item
				addresses := map[int]int{}
				pc := 0
				for _, id := range order {
					addresses[id] = pc
					items = append(items, label(fmt.Sprintf("b%d", id)))
					if id == 0 {
						items = append(items, selector.items...)
						pc += 4 * len(selector.items)
					} else {
						// Different block lengths exercise offsets independently of IDs.
						for n := 0; n < id; n++ {
							items = append(items, ins("nop"))
							pc += 4
						}
						items = append(items, ins("ret"))
						pc += 4
					}
				}
				body, relocs, err := asm.EncodeFunction(fn(items...))
				if err != nil || len(relocs) != 0 {
					t.Fatalf("encode selector %v: %v / %v", order, err, relocs)
				}
				var words []string
				var shape []string
				for i, item := range selector.items {
					shape = append(shape, item.(asm.Instruction).Mnemonic)
					word := binary.LittleEndian.Uint32(body[addresses[0]+4*i:])
					words = append(words, fmt.Sprintf("0x%08x#32", word))
				}
				shapes[strings.Join(shape, ",")] = true
				following := "none"
				if hasNext {
					following = fmt.Sprintf("(some %d)", next)
				}
				address := fmt.Sprintf("(fun id => match id with | 0 => %d | 1 => %d | 2 => %d | _ => %d)", addresses[0], addresses[1], addresses[2], addresses[3])
				check := fmt.Sprintf("check %d %d %s %d %s %d [%s]", yes, no, following, addresses[0], address, register, strings.Join(words, ", "))
				examples = append(examples, "example : "+check+" = true := by decide")
				if !same {
					swapped := fmt.Sprintf("check %d %d %s %d %s %d [%s]", no, yes, following, addresses[0], address, register, strings.Join(words, ", "))
					examples = append(examples, "example : "+swapped+" = false := by decide")
				}
				// An empty terminator must not be accepted when its next block
				// starts four bytes beyond the actual end of the emitted plan.
				if len(words) == 0 {
					bad := fmt.Sprintf("check %d %d %s %d %s %d []", yes, no, following, addresses[0]+4, address, register)
					examples = append(examples, "example : "+bad+" = false := by decide")
				} else {
					badWords := append([]string(nil), words...)
					badWords[0] = "0xd503201f#32" // NOP cannot stand for the selected transfer.
					bad := fmt.Sprintf("check %d %d %s %d %s %d [%s]", yes, no, following, addresses[0], address, register, strings.Join(badWords, ", "))
					examples = append(examples, "example : "+bad+" = false := by decide")
				}
			}
		}
	}
	for _, shape := range []string{"", "b", "cbz", "cbnz", "cbnz,b"} {
		if !shapes[shape] {
			t.Fatalf("selector case %q was not exercised", shape)
		}
	}
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_ARM64_COND19_LEAN") != "" {
			t.Fatal("lake required for ARM64 control-flow certificates")
		}
		t.Skip("lake not on PATH; ARM64 proof workflow requires this oracle")
	}
	root := filepath.Join("..", "spec", "lean")
	build := exec.Command(lake, "build", "Oak.AArch64ControlFlow")
	build.Dir = root
	if out, err := build.CombinedOutput(); err != nil {
		t.Fatalf("build control-flow proof: %v\n%s", err, out)
	}
	path := filepath.Join(t.TempDir(), "Selector.lean")
	if err := os.WriteFile(path, []byte("import Oak.AArch64ControlFlow\nopen Oak.AArch64ControlFlow\n"+strings.Join(examples, "\n")+"\n"), 0600); err != nil {
		t.Fatal(err)
	}
	run := exec.Command(lake, "env", "lean", path)
	run.Dir = root
	if out, err := run.CombinedOutput(); err != nil {
		t.Fatalf("selector certificates: %v\n%s", err, out)
	}
	t.Logf("Lean checked %d production layout certificates and mutations", len(examples))
}

func aarch64BlockOrders(prefix, rest []int) [][]int {
	if len(rest) == 0 {
		return [][]int{prefix}
	}
	var out [][]int
	for i, id := range rest {
		next := append(append([]int(nil), rest[:i]...), rest[i+1:]...)
		out = append(out, aarch64BlockOrders(append(append([]int(nil), prefix...), id), next)...)
	}
	return out
}
