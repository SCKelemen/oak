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

// Exercise the actual selector's terminator, then EncodeFunction's label
// layout and bytes. The Lean certificate composes with checked_successor for
// every register state, not just two sampled Bool inputs.
func rv64SelectorCertificates(t *testing.T) []string {
	t.Helper()
	var examples []string
	shapes := map[string]bool{}
	for _, order := range aarch64BlockOrders(nil, []int{0, 1, 2, 3}) {
		for _, same := range []bool{false, true} {
			for _, register := range []int{5, 8, 15, 31} {
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
				selector := optIRRV64Selector{
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
				body, relocs, err := asm.EncodeFunction(&asm.Function{Name: "routing", Arch: asm.ArchRV64, Items: items})
				if err != nil || len(relocs) != 0 {
					t.Fatalf("encode selector %v: %v / %v", order, err, relocs)
				}
				var words []string
				var raw []uint32
				var shape []string
				for i, item := range selector.items {
					shape = append(shape, item.(asm.Instruction).Mnemonic)
					word := binary.LittleEndian.Uint32(body[addresses[0]+4*i:])
					raw = append(raw, word)
					words = append(words, fmt.Sprintf("0x%08x#32", word))
				}
				for _, value := range []uint64{0, 1, 1 << 32, 1 << 63, ^uint64(0)} {
					want := addresses[int(no)]
					if value != 0 {
						want = addresses[int(yes)]
					}
					if got := rv64RunTerminator(t, raw, uint64(addresses[0]), register, value); got != uint64(want) {
						t.Fatalf("order=%v same=%v reg=%d value=%x reached %d want %d", order, same, register, value, got, want)
					}
				}
				shapes[strings.Join(shape, ",")] = true
				following := "none"
				if hasNext {
					following = fmt.Sprintf("(some %d)", next)
				}
				address := fmt.Sprintf("(fun id => match id with | 0 => %d | 1 => %d | 2 => %d | _ => %d)", addresses[0], addresses[1], addresses[2], addresses[3])
				check := fmt.Sprintf("check %d %d %s %d %s %d [%s]", yes, no, following, addresses[0], address, register, strings.Join(words, ", "))
				examples = append(examples, "example : "+check+" = true := by decide")
				examples = append(examples, fmt.Sprintf("example (regs : Registers) (hz : regs 0#5 = 0#64) : run [%s] ⟨%d, regs⟩ = some ⟨if boolValue regs %d then %d else %d, regs⟩ := checked_successor %d %d %s %d %s %d [%s] (by decide) regs hz", strings.Join(words, ", "), addresses[0], register, addresses[int(yes)], addresses[int(no)], yes, no, following, addresses[0], address, register, strings.Join(words, ", ")))

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
					badWords[0] = "0x00000013#32" // NOP cannot stand for the selected transfer.
					bad := fmt.Sprintf("check %d %d %s %d %s %d [%s]", yes, no, following, addresses[0], address, register, strings.Join(badWords, ", "))
					examples = append(examples, "example : "+bad+" = false := by decide")
				}
			}
		}
	}
	for _, shape := range []string{"", "j", "beqz", "bnez", "bnez,j"} {
		if !shapes[shape] {
			t.Fatalf("selector case %q was not exercised", shape)
		}
	}
	return examples
}

func checkRV64SelectorLean(t *testing.T, module string, examples []string) {
	t.Helper()
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_RV64_LEAN") != "" {
			t.Fatal("lake required for RV64 control-flow certificates")
		}
		t.Skip("lake not on PATH; RV64 proof workflow requires this oracle")
	}
	root := filepath.Join("..", "spec", "lean")
	build := exec.Command(lake, "build", "Oak."+module)
	build.Dir = root
	if out, err := build.CombinedOutput(); err != nil {
		t.Fatalf("build control-flow proof: %v\n%s", err, out)
	}
	path := filepath.Join(t.TempDir(), "Selector.lean")
	header := "import Oak." + module + "\nopen Oak." + module + " Oak.RiscVControlFlow\n"
	if err := os.WriteFile(path, []byte(header+strings.Join(examples, "\n")+"\n"), 0600); err != nil {
		t.Fatal(err)
	}
	run := exec.Command(lake, "env", "lean", path)
	run.Dir = root
	if out, err := run.CombinedOutput(); err != nil {
		t.Fatalf("selector certificates: %v\n%s", err, out)
	}
	t.Logf("Lean checked %d production certificates and mutations", len(examples))
}

func TestRV64ControlFlowSelectorBytes(t *testing.T) {
	t.Logf("checked %d certificates and mutations", len(rv64SelectorCertificates(t)))
}
func TestRV64ControlFlowSelectorMatchesLean(t *testing.T) {
	checkRV64SelectorLean(t, "RiscVControlFlow", rv64SelectorCertificates(t))
}

// Independent execution of the selected finite terminator. A taken transfer
// ends the trace even when its target numerically equals the next instruction.
func rv64RunTerminator(t *testing.T, words []uint32, pc uint64, register int, value uint64) uint64 {
	t.Helper()
	for _, w := range words {
		switch w & 127 {
		case 0x6f:
			if w>>7&31 != 0 {
				t.Fatal("terminator jump writes a link")
			}
			half := (w>>31)<<19 | (w>>12&255)<<11 | (w>>20&1)<<10 | (w >> 21 & 1023)
			return pc + uint64((int64(half)<<44>>44)*2)
		case 0x63:
			if int(w>>15&31) != register || w>>20&31 != 0 {
				t.Fatal("wrong condition register")
			}
			take := value == 0
			switch w >> 12 & 7 {
			case 0:
			case 1:
				take = !take
			default:
				t.Fatal("unexpected condition")
			}
			if take {
				half := (w>>31)<<11 | (w>>7&1)<<10 | (w>>25&63)<<4 | (w >> 8 & 15)
				return pc + uint64((int64(half)<<52>>52)*2)
			}
			pc += 4
		default:
			t.Fatal("unexpected terminator word")
		}
	}
	return pc
}
