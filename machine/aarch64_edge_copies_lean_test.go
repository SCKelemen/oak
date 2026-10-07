package machine

import (
	"encoding/binary"
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/optir"
)

// Certify the actual edgeMoves/emitEdgeCopies/terminator and assembler output.
// Expectations come directly from SSA arguments and parameter locations, before
// the scheduler mutates its pending move list.
func TestAArch64EdgeCopiesSelectorLean(t *testing.T) {
	scenarios := [][]int{
		{0, 1, 2, 3}, {1, 0, 2, 3}, {1, 2, 0, 3}, {1, 2, 3, 0}, {1, 0, 3, 2},
		{9, 0, 1, 2}, {9, 9, 9, 9}, {1, 2, 9, 1}, {2, 2, 3, 9},
	}
	var examples []string
	positives, negatives := 0, 0
	for _, sources := range scenarios {
		for widths := 0; widths < 16; widths++ {
			for _, layout := range []string{"fall", "forward", "backward"} {
				selector := optIRArm64Selector{written: map[int]bool{}, types: map[optir.ValueID]optir.Type{}, colors: map[optir.ValueID]int{}, labels: map[optir.BlockID]string{1: "target"}}
				target := optir.Block{ID: 1}
				edge := optir.Edge{Target: 1}
				var moves []string
				for dst, src := range sources {
					typ := optir.Type("u64")
					narrow := "false"
					if widths&(1<<dst) != 0 {
						typ = "u32"
						narrow = "true"
					}
					param, arg := optir.ValueID(10+dst), optir.ValueID(20+dst)
					target.Parameters = append(target.Parameters, optir.Value{ID: param, Type: typ})
					edge.Arguments = append(edge.Arguments, arg)
					selector.types[param], selector.types[arg] = typ, typ
					selector.colors[param], selector.colors[arg] = dst, src
					moves = append(moves, fmt.Sprintf("⟨%d, %d, %s⟩", dst, src, narrow))
				}
				selector.cfg = optir.CFG{Blocks: []optir.Block{target}}
				block := optir.Block{ID: 0, Terminator: optir.Terminator{Kind: optir.TerminatorBranch, True: edge}}
				if err := selector.terminator(block, 1, layout == "fall", 1); err != nil {
					t.Fatal(err)
				}
				count := len(selector.items)
				copyCount := count
				if layout != "fall" {
					copyCount--
				}
				var items []asm.Item
				start, targetPC := 0, 0
				if layout == "backward" {
					items = append(items, label("target"), ins("ret"))
					start = 4
				}
				items = append(items, selector.items...)
				if layout != "backward" {
					if layout == "forward" {
						items = append(items, ins("nop"))
					}
					targetPC = 4 * len(items)
					items = append(items, label("target"), ins("ret"))
				}
				body, relocs, err := asm.EncodeFunction(fn(items...))
				if err != nil || len(relocs) != 0 {
					t.Fatalf("encode: %v %v", err, relocs)
				}
				var words, branch []string
				for i := 0; i < count; i++ {
					w := fmt.Sprintf("0x%08x#32", binary.LittleEndian.Uint32(body[start+4*i:]))
					if i < copyCount {
						words = append(words, w)
					} else {
						branch = append(branch, w)
					}
				}
				expected := "[" + strings.Join(moves, ",") + "]"
				encoded := "[" + strings.Join(words, ",") + "]"
				next := "none"
				if layout == "fall" {
					next = "(some 1)"
				}
				route := fmt.Sprintf("check 1 1 %s %d (fun _ => %d) 0 [%s]", next, start+4*copyCount, targetPC, strings.Join(branch, ","))
				examples = append(examples, fmt.Sprintf("example : checkCopies %s %s = true ∧ %s = true := by decide", expected, encoded, route))
				positives++
				if copyCount > 0 {
					// Omitting the first scheduled move loses either a destination or a
					// cycle save. A non-MOV opcode must also be refused.
					examples = append(examples, fmt.Sprintf("example : checkCopies %s [%s] = false := by decide", expected, strings.Join(words[1:], ",")))
					corrupt := append([]string(nil), words...)
					corrupt[0] = "0xd503201f#32"
					examples = append(examples, fmt.Sprintf("example : checkCopies %s [%s] = false := by decide", expected, strings.Join(corrupt, ",")))
					negatives += 2
				}
			}
		}
	}
	// Contract violations and the naive sequential swap are rejected.
	for _, example := range []string{
		"checkCopies [⟨0,1,false⟩,⟨1,0,false⟩] [0xaa0103e0#32,0xaa0003e1#32]",
		"checkCopies [⟨17,0,false⟩] []",
		"checkCopies [⟨0,17,false⟩] []",
		"checkCopies [⟨31,0,false⟩] []",
		"checkCopies [⟨0,0,false⟩,⟨0,0,false⟩] []",
	} {
		examples = append(examples, "example : "+example+" = false := by decide")
		negatives++
	}
	t.Logf("%d accepted edge certificates, %d rejected mutations/contracts", positives, negatives)
	checkAArch64SelectorLean(t, "AArch64EdgeCopies", examples)
}

func TestAArch64EdgeCopiesConditionalLean(t *testing.T) {
	var examples []string
	for _, typ := range []optir.Type{"u32", "u64"} {
		for _, condition := range []int{0, 9} {
			for _, backward := range []bool{false, true} {
				selector := optIRArm64Selector{written: map[int]bool{}, types: map[optir.ValueID]optir.Type{99: optir.TypeBool}, colors: map[optir.ValueID]int{99: condition}, labels: map[optir.BlockID]string{1: "yes", 2: "no"}}
				edges := []optir.Edge{{Target: 1}, {Target: 2}}
				expected := []string{}
				for k, sources := range [][]int{{1, 0, 2}, {1, 2, 0}} {
					block := optir.Block{ID: optir.BlockID(k + 1)}
					var ms []string
					for d, src := range sources {
						p, a := optir.ValueID(10+k*10+d), optir.ValueID(40+k*10+d)
						block.Parameters = append(block.Parameters, optir.Value{ID: p, Type: typ})
						edges[k].Arguments = append(edges[k].Arguments, a)
						selector.types[p], selector.types[a] = typ, typ
						selector.colors[p], selector.colors[a] = d, src
						ms = append(ms, fmt.Sprintf("⟨%d,%d,%t⟩", d, src, typ == "u32"))
					}
					selector.cfg.Blocks = append(selector.cfg.Blocks, block)
					expected = append(expected, "["+strings.Join(ms, ",")+"]")
				}
				block := optir.Block{ID: 0, Terminator: optir.Terminator{Kind: optir.TerminatorCondBranch, Condition: 99, True: edges[0], False: edges[1]}}
				if err := selector.terminator(block, 1, false, 1); err != nil {
					t.Fatal(err)
				}
				var items []asm.Item
				if backward {
					items = append(items, label("yes"), ins("ret"), label("no"), ins("ret"))
				}
				items = append(items, label("entry"))
				items = append(items, selector.items...)
				if !backward {
					items = append(items, label("yes"), ins("ret"), label("no"), ins("ret"))
				}
				addresses := map[string]int{}
				pc := 0
				for _, item := range items {
					switch v := item.(type) {
					case asm.Label:
						addresses[v.Name] = pc
					case asm.Instruction:
						pc += 4
					default:
						t.Fatalf("unexpected %T", item)
					}
				}
				body, relocs, err := asm.EncodeFunction(fn(items...))
				if err != nil || len(relocs) != 0 {
					t.Fatalf("encode %v %v", err, relocs)
				}
				var stubLabels []string
				for _, item := range selector.items {
					if lab, ok := item.(asm.Label); ok {
						stubLabels = append(stubLabels, lab.Name)
					}
				}
				if len(stubLabels) != 2 {
					t.Fatalf("expected two edge stubs, got %v", stubLabels)
				}
				entry, yp, np := addresses["entry"], addresses[stubLabels[0]], addresses[stubLabels[1]]
				end := pc - 8
				if backward {
					end = pc
				}
				words := func(start, end int) string {
					var ws []string
					for at := start; at < end; at += 4 {
						ws = append(ws, fmt.Sprintf("0x%08x#32", binary.LittleEndian.Uint32(body[at:])))
					}
					return "[" + strings.Join(ws, ",") + "]"
				}
				dispatch, yc, yb, nc, nb := words(entry, yp), words(yp, np-4), words(np-4, np), words(np, end-4), words(end-4, end)
				addr := fmt.Sprintf("(fun id => if id = 1 then %d else %d)", addresses["yes"], addresses["no"])
				cert := fmt.Sprintf("check 0 1 none %d (fun id => if id = 0 then %d else %d) %d %s = true ∧ checkCopies %s %s = true ∧ checkCopies %s %s = true ∧ check 1 1 none %d %s 0 %s = true ∧ check 2 2 none %d %s 0 %s = true", entry, yp, np, condition, dispatch, expected[0], yc, expected[1], nc, np-4, addr, yb, end-4, addr, nb)
				examples = append(examples, "example : "+cert+" := by decide")
				// Also instantiate the full semantic theorem for arbitrary initial state.
				examples = append(examples, fmt.Sprintf("example (s : Oak.AArch64BranchExecution.State) (hpc : s.pc = %d) : ∃ out, runConditional %s %s %s %s %s %d %d s = some out ∧ out.pc = (if boolValue s.regs %d then %s 1 else %s 2) ∧ out.flags = s.flags ∧ ∀ r, r ≠ 17#5 → out.regs r = eval s.regs (expected (if boolValue s.regs %d then %s else %s) r) := by\n  apply checked_conditional %s %s %s %s %s %s %s %d %d 1 2 %s %d s (by decide)\n  · rw [hpc]; decide\n  all_goals decide", entry, dispatch, yc, yb, nc, nb, yp, np, condition, addr, addr, condition, expected[0], expected[1], expected[0], expected[1], dispatch, yc, yb, nc, nb, yp, np, addr, condition))
			}
		}
	}
	checkAArch64SelectorLean(t, "AArch64EdgeCopies", examples)
}
