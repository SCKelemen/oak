package machine

import (
	"encoding/binary"
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/optir"
)

// Invoke both real selector routines and take the prefix/terminator words
// from EncodeFunction. Each accepted pair of certificates instantiates the
// universal checked_comparison_successor theorem, including input aliasing.
func TestAArch64ConditionProvenanceSelectorLean(t *testing.T) {
	operations := []struct{ code, predicate string }{
		{optir.OpEqual, "eq"}, {optir.OpNotEqual, "ne"}, {optir.OpLess, "lt"},
		{optir.OpLessEqual, "le"}, {optir.OpGreater, "gt"}, {optir.OpGreaterEqual, "ge"},
	}
	layouts := []struct {
		order []int
		no    optir.BlockID
	}{
		{[]int{0, 1, 2, 3}, 2}, {[]int{0, 2, 1, 3}, 2}, {[]int{0, 3, 1, 2}, 2},
		{[]int{1, 2, 3, 0}, 2}, {[]int{1, 0, 2, 3}, 2},
		{[]int{0, 1, 2, 3}, 1}, {[]int{0, 2, 1, 3}, 1},
	}
	var examples []string
	for _, typ := range []optir.Type{"u32", "i32", "u64", "i64"} {
		width := "w32"
		if strings.HasSuffix(string(typ), "64") {
			width = "x64"
		}
		for _, operation := range operations {
			predicate := operation.predicate
			if predicate != "eq" && predicate != "ne" {
				prefix := "u"
				if strings.HasPrefix(string(typ), "i") {
					prefix = "s"
				}
				predicate = prefix + predicate
			}
			for _, destination := range []int{9, 0, 1} {
				for _, layout := range layouts {
					selector := optIRArm64Selector{
						written: map[int]bool{},
						cfg:     optir.CFG{Blocks: []optir.Block{{ID: 1}, {ID: 2}, {ID: 3}}},
						types:   map[optir.ValueID]optir.Type{1: typ, 2: typ, 3: optir.TypeBool},
						colors:  map[optir.ValueID]int{1: 0, 2: 1, 3: destination},
						labels:  map[optir.BlockID]string{1: "b1", 2: "b2", 3: "b3"},
					}
					comparison := optir.Operation{Code: operation.code, Operands: []optir.ValueID{1, 2},
						Results: []optir.Value{{ID: 3, Type: optir.TypeBool}}}
					if err := selector.compare(comparison, 1); err != nil {
						t.Fatal(err)
					}
					if len(selector.items) != 2 {
						t.Fatalf("comparison acquired a non-CMP/CSET prefix: %v", selector.items)
					}
					var next optir.BlockID
					hasNext := false
					for i, id := range layout.order {
						if id == 0 && i+1 < len(layout.order) {
							next, hasNext = optir.BlockID(layout.order[i+1]), true
						}
					}
					block := optir.Block{ID: 0, Terminator: optir.Terminator{Kind: optir.TerminatorCondBranch,
						Condition: 3, True: optir.Edge{Target: 1}, False: optir.Edge{Target: layout.no}}}
					if err := selector.terminator(block, next, hasNext, 1); err != nil {
						t.Fatal(err)
					}
					var items []asm.Item
					addresses := map[int]int{}
					pc := 0
					for _, id := range layout.order {
						addresses[id] = pc
						items = append(items, label(fmt.Sprintf("b%d", id)))
						if id == 0 {
							items = append(items, selector.items...)
							pc += 4 * len(selector.items)
						} else {
							items = append(items, ins("nop"), ins("ret"))
							pc += 8
						}
					}
					body, relocs, err := asm.EncodeFunction(fn(items...))
					if err != nil || len(relocs) != 0 {
						t.Fatalf("encode comparison/terminator: %v / %v", err, relocs)
					}
					at := addresses[0]
					cmp, set := binary.LittleEndian.Uint32(body[at:]), binary.LittleEndian.Uint32(body[at+4:])
					producer := fmt.Sprintf("checkProducer .%s .%s 0 1 %d 0x%08x#32 0x%08x#32", width, predicate, destination, cmp, set)
					var words []string
					for i := 2; i < len(selector.items); i++ {
						words = append(words, fmt.Sprintf("0x%08x#32", binary.LittleEndian.Uint32(body[at+4*i:])))
					}
					following := "none"
					if hasNext {
						following = fmt.Sprintf("(some %d)", next)
					}
					addr := fmt.Sprintf("(fun id => match id with | 0 => %d | 1 => %d | 2 => %d | _ => %d)", addresses[0], addresses[1], addresses[2], addresses[3])
					branch := fmt.Sprintf("check 1 %d %s %d %s %d [%s]", layout.no, following, at+8, addr, destination, strings.Join(words, ", "))
					examples = append(examples, fmt.Sprintf("example : %s = true ∧ %s = true := by decide", producer, branch))
					// A wrong operand width or missed CSET condition inversion
					// cannot be certified as the original source comparison.
					examples = append(examples, fmt.Sprintf("example : checkProducer .%s .%s 0 1 %d 0x%08x#32 0x%08x#32 = false := by decide", width, predicate, destination, cmp^(1<<31), set))
					examples = append(examples, fmt.Sprintf("example : checkProducer .%s .%s 0 1 %d 0x%08x#32 0x%08x#32 = false := by decide", width, predicate, destination, cmp, set^(1<<12)))
				}
			}
		}
	}
	// Destination WZR discards the comparison result, so it cannot discharge
	// the Boolean-register invariant even when both instruction words match.
	examples = append(examples, "example : checkProducer .w32 .eq 0 1 31 (cmpWord .w32 0 1) (csetWord .eq 31) = false := by decide")
	checkAArch64SelectorLean(t, "AArch64ConditionProvenance", examples)
}
