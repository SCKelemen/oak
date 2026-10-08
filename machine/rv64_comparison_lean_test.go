package machine

import (
	"encoding/binary"
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/optir"
)

// Actual selector + assembler bytes, composed with an all-state Lean theorem.
// i64/u64 deliberately avoid assuming any narrow-value canonicalization proof.
func rv64ComparisonCertificates(t *testing.T) []string {
	t.Helper()
	operations := []struct {
		code string
		lean string
	}{
		{optir.OpEqual, "eq"}, {optir.OpNotEqual, "ne"},
		{optir.OpLess, "lt"}, {optir.OpLessEqual, "le"},
		{optir.OpGreater, "gt"}, {optir.OpGreaterEqual, "ge"},
	}
	layouts := []struct {
		order []int
		same  bool
	}{
		{[]int{0, 1, 2, 3}, true},  // fall
		{[]int{1, 0, 2, 3}, true},  // jump backward
		{[]int{0, 1, 2, 3}, false}, // zero
		{[]int{1, 0, 2, 3}, false}, // nonzero, backward
		{[]int{1, 2, 0, 3}, false}, // pair, next is unrelated
		{[]int{1, 2, 3, 0}, false}, // pair, no next block
	}
	registers := [][3]int{{5, 6, 7}, {5, 5, 7}, {7, 5, 7}, {31, 31, 31}, {8, 15, 15}, {15, 8, 31}}
	values := []uint64{0, 1, 2, 0x7fffffff, 0x80000000, 0xffffffff, 1 << 32,
		1<<63 - 1, 1 << 63, 1<<63 + 1, ^uint64(0) - 1, ^uint64(0)}
	var examples []string
	cases, executions := 0, 0
	for _, op := range operations {
		for _, signed := range []bool{false, true} {
			typ := optir.Type("u64")
			if signed {
				typ = "i64"
			}
			for _, regs := range registers {
				rd, left, right := regs[0], regs[1], regs[2]
				for _, layout := range layouts {
					yes, no := optir.BlockID(1), optir.BlockID(2)
					if layout.same {
						no = yes
					}
					selector := optIRRV64Selector{
						cfg:    optir.CFG{Blocks: []optir.Block{{ID: 1}, {ID: 2}, {ID: 3}}},
						types:  map[optir.ValueID]optir.Type{1: typ, 2: typ, 3: optir.TypeBool},
						colors: map[optir.ValueID]int{1: left, 2: right, 3: rd},
						labels: map[optir.BlockID]string{1: "b1", 2: "b2", 3: "b3"}, written: map[int]bool{},
					}
					operation := optir.Operation{Code: op.code, Operands: []optir.ValueID{1, 2},
						Results: []optir.Value{{ID: 3, Type: optir.TypeBool}}}
					if err := selector.registerOperation(operation); err != nil {
						t.Fatal(err)
					}
					producerCount := len(selector.items)
					var next optir.BlockID
					hasNext := false
					for i, id := range layout.order {
						if id == 0 && i+1 < len(layout.order) {
							next, hasNext = optir.BlockID(layout.order[i+1]), true
						}
					}
					block := optir.Block{ID: 0, Terminator: optir.Terminator{Kind: optir.TerminatorCondBranch,
						Condition: 3, True: optir.Edge{Target: yes}, False: optir.Edge{Target: no}}}
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
							for n := 0; n < id; n++ {
								items = append(items, ins("nop"))
								pc += 4
							}
							items = append(items, ins("ret"))
							pc += 4
						}
					}
					body, relocs, err := asm.EncodeFunction(&asm.Function{Name: "comparison", Arch: asm.ArchRV64, Items: items})
					if err != nil || len(relocs) != 0 || len(body) != pc {
						t.Fatalf("encode comparison: %v / %v / length %d want %d", err, relocs, len(body), pc)
					}
					var raw []uint32
					for i := range selector.items {
						raw = append(raw, binary.LittleEndian.Uint32(body[addresses[0]+4*i:]))
					}
					producer, control := raw[:producerCount], raw[producerCount:]
					for _, a := range values {
						for _, b := range values {
							if left == right && a != b {
								continue // one physical register denotes one input value
							}
							var before [32]uint64
							for i := 1; i < 32; i++ {
								before[i] = uint64(i)*0x123456789abcdef + 7
							}
							before[left], before[right] = a, b
							after := rv64ExecuteComparison(t, producer, before)
							want := uint64(0)
							if rv64SourceComparison(op.code, signed, a, b) {
								want = 1
							}
							if after[rd] != want {
								t.Fatalf("%s %s regs=%v a=%x b=%x: got %x want %d", op.code, typ, regs, a, b, after[rd], want)
							}
							for r := range before {
								if r != rd && before[r] != after[r] {
									t.Fatalf("comparison clobbered x%d", r)
								}
							}
							wantPC := addresses[int(no)]
							if want != 0 {
								wantPC = addresses[int(yes)]
							}
							if got := rv64RunTerminator(t, control, uint64(addresses[0]+4*producerCount), rd, after[rd]); got != uint64(wantPC) {
								t.Fatalf("comparison routed to %d, want %d", got, wantPC)
							}
							executions++
						}
					}
					args := fmt.Sprintf(".%s %t %d %d %d", op.lean, signed, rd, left, right)
					prodWords, ctrlWords := rv64ComparisonWords(producer), rv64ComparisonWords(control)
					examples = append(examples, fmt.Sprintf("example : checkProducer %s %s = true := by decide", args, prodWords))
					following := "none"
					if hasNext {
						following = fmt.Sprintf("(some %d)", next)
					}
					address := fmt.Sprintf("(fun id => match id with | 0 => %d | 1 => %d | 2 => %d | _ => %d)", addresses[0], addresses[1], addresses[2], addresses[3])
					examples = append(examples, fmt.Sprintf("example (regs : Registers) : runCompared %s %s ⟨%d, regs⟩ = some ⟨if predicate .%s %t (Oak.RiscVCallExecution.read ⟨%d, regs⟩ %d) (Oak.RiscVCallExecution.read ⟨%d, regs⟩ %d) then %d else %d, (result %s ⟨%d, regs⟩).regs⟩ := checked_comparison_successor %s %s %s (by decide) ⟨%d, regs⟩ %d %d %s %s (by dsimp only [result]; decide)", prodWords, ctrlWords, addresses[0], op.lean, signed, addresses[0], left, addresses[0], right, addresses[int(yes)], addresses[int(no)], args, addresses[0], args, prodWords, ctrlWords, addresses[0], yes, no, following, address))
					// Mutate every producer word: destination and opcode. Even dead
					// conditions (equal successors) must have a valid producer.
					for i := range producer {
						for _, mask := range []uint32{1 << 7, 1} {
							bad := append([]uint32(nil), producer...)
							bad[i] ^= mask
							examples = append(examples, fmt.Sprintf("example : checkProducer %s %s = false := by decide", args, rv64ComparisonWords(bad)))
						}
					}
					// Every truncated prefix is rejected, including a missing
					// normalization or inversion after SUB/SLT/SLTU.
					for n := 0; n < len(producer); n++ {
						examples = append(examples, fmt.Sprintf("example : checkProducer %s %s = false := by decide", args, rv64ComparisonWords(producer[:n])))
					}
					if op.code != optir.OpEqual && op.code != optir.OpNotEqual {
						examples = append(examples, fmt.Sprintf("example : checkProducer .%s %t %d %d %d %s = false := by decide", op.lean, !signed, rd, left, right, prodWords))
					}
					// Certificate admission is closed: zero destination and trailing
					// bytes must be rejected, not silently ignored.
					examples = append(examples, fmt.Sprintf("example : checkProducer .%s %t 0 %d %d %s = false := by decide", op.lean, signed, left, right, prodWords))
					extra := append(append([]uint32(nil), producer...), 0x13)
					examples = append(examples, fmt.Sprintf("example : checkProducer %s %s = false := by decide", args, rv64ComparisonWords(extra)))
					cases++
				}
			}
		}
	}
	t.Logf("%d comparison/layout cases, %d independent executions, %d Lean declarations", cases, executions, len(examples))
	return examples
}

func rv64ComparisonWords(words []uint32) string {
	out := make([]string, len(words))
	for i, word := range words {
		out[i] = fmt.Sprintf("0x%08x#32", word)
	}
	return "[" + strings.Join(out, ", ") + "]"
}

func rv64SourceComparison(op string, signed bool, a, b uint64) bool {
	switch op {
	case optir.OpEqual:
		return a == b
	case optir.OpNotEqual:
		return a != b
	case optir.OpLess:
		if signed {
			return int64(a) < int64(b)
		}
		return a < b
	case optir.OpLessEqual:
		if signed {
			return int64(a) <= int64(b)
		}
		return a <= b
	case optir.OpGreater:
		if signed {
			return int64(a) > int64(b)
		}
		return a > b
	case optir.OpGreaterEqual:
		if signed {
			return int64(a) >= int64(b)
		}
		return a >= b
	default:
		panic("unexpected comparison")
	}
}

// Decode raw instruction fields independently of the Lean plan and selector.
func rv64ExecuteComparison(t *testing.T, words []uint32, regs [32]uint64) [32]uint64 {
	t.Helper()
	for _, w := range words {
		rd, left, right := w>>7&31, w>>15&31, w>>20&31
		a, b := regs[left], regs[right]
		value := uint64(0)
		switch w & 0x7f {
		case 0x33:
			switch w & 0xfe00707f {
			case 0x40000033:
				value = a - b
			case 0x2033:
				if int64(a) < int64(b) {
					value = 1
				}
			case 0x3033:
				if a < b {
					value = 1
				}
			default:
				t.Fatalf("unexpected register comparison instruction %08x", w)
			}
		case 0x13:
			imm := uint64(int64(int32(w)) >> 20)
			switch w >> 12 & 7 {
			case 3:
				if a < imm {
					value = 1
				}
			case 4:
				value = a ^ imm
			default:
				t.Fatalf("unexpected immediate comparison instruction %08x", w)
			}
		default:
			t.Fatalf("unexpected comparison opcode %08x", w)
		}
		if rd != 0 {
			regs[rd] = value
		}
		regs[0] = 0
	}
	return regs
}

func TestRV64ComparisonSelectorBytes(t *testing.T) {
	rv64ComparisonCertificates(t)
}
func TestRV64ComparisonSelectorMatchesLean(t *testing.T) {
	checkRV64SelectorLean(t, "RiscVComparison", rv64ComparisonCertificates(t))
}
