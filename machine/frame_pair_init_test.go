package machine

import (
	"reflect"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
)

func framePairFixture() *asm.Function {
	return framed(
		ins("sub", sp(), sp(), imm(64)),
		ins("mov", x(9), x(0)),
		ins("mov", x(10), x(1)),
		ins("stp", x(9), x(10), mem(sp(), 16)),
		ins("ldr", w(0), mem(sp(), 16)),
		ins("ldr", w(11), mem(sp(), 20)),
		ins("add", w(0), w(0), w(11)),
		ins("ldr", w(11), mem(sp(), 24)),
		ins("add", w(0), w(0), w(11)),
		ins("ldr", w(11), mem(sp(), 28)),
		ins("add", w(0), w(0), w(11)),
		ins("add", sp(), sp(), imm(64)),
		ins("ret"),
	)
}

func splitPairFixture(t *testing.T, f *asm.Function, objects []FrameObject) (*asm.Function, map[int64]bool) {
	t.Helper()
	lifted, err := Lift(f)
	if err != nil {
		t.Fatal(err)
	}
	split, words, err := splitFramePairInitializers(lifted, objects)
	if err != nil {
		t.Fatal(err)
	}
	return split, words
}

func insertPairItems(f *asm.Function, index int, items ...asm.Item) {
	tail := append([]asm.Item(nil), f.Items[index:]...)
	f.Items = append(append(f.Items[:index], items...), tail...)
}

func TestSplitFramePairInitializersExactSequence(t *testing.T) {
	f := framePairFixture()
	// A pair source load must remain before every resulting store, with
	// source position metadata unchanged. Labels do not affect indexing.
	f.Items[1] = ins("ldp", x(9), x(10), mem(x(0), 0))
	f.Items[2] = label("initialized")
	pair := f.Items[3].(asm.Instruction)
	pair.Line = 17
	f.Items[3] = pair
	before := cloneFunction(f)
	split, words := splitPairFixture(t, f, []FrameObject{{16, 16}})
	if split == nil || !reflect.DeepEqual(words, map[int64]bool{16: true, 20: true, 24: true, 28: true}) {
		t.Fatalf("split = %v, words = %v", split, words)
	}
	want := []asm.Item{
		ins("str", w(9), mem(sp(), 16)),
		ins("lsr", x(9), x(9), imm(32)),
		ins("str", w(9), mem(sp(), 20)),
		ins("str", w(10), mem(sp(), 24)),
		ins("lsr", x(10), x(10), imm(32)),
		ins("str", w(10), mem(sp(), 28)),
	}
	for i, item := range want {
		instruction := item.(asm.Instruction)
		instruction.Line = 17
		want[i] = instruction
	}
	if !reflect.DeepEqual(split.Items[3:9], want) || !reflect.DeepEqual(split.Items[:3], before.Items[:3]) ||
		!reflect.DeepEqual(split.Items[9:], before.Items[4:]) {
		t.Fatalf("unexpected split:\n%s", text(split.Items))
	}
	if !reflect.DeepEqual(f, before) {
		t.Fatal("splitting changed its input")
	}
	// The output may be rewritten later without modifying input operands.
	split.Items[1].(asm.Instruction).Operands[0] = x(12)
	if !reflect.DeepEqual(f, before) {
		t.Fatal("split output aliases input operands")
	}
}

func TestSplitFramePairInitializersRefusals(t *testing.T) {
	tests := []struct {
		name   string
		mutate func(*asm.Function)
		layout []FrameObject
	}{
		{"no-layout", func(*asm.Function) {}, nil},
		{"short-object", func(*asm.Function) {}, []FrameObject{{16, 12}}},
		{"negative-object", func(*asm.Function) {}, []FrameObject{{-16, 48}}},
		{"outside-frame-object", func(*asm.Function) {}, []FrameObject{{16, 64}}},
		{"not-clobbered", func(f *asm.Function) { f.Clobbers = []asm.Register{x(11)} }, []FrameObject{{16, 16}}},
		{"same-register", func(f *asm.Function) { f.Items[3] = ins("stp", x(9), x(9), mem(sp(), 16)) }, []FrameObject{{16, 16}}},
		{"zero-register", func(f *asm.Function) { f.Items[3] = ins("stp", x(9), x(31), mem(sp(), 16)) }, []FrameObject{{16, 16}}},
		{"w-pair", func(f *asm.Function) { f.Items[3] = ins("stp", w(9), w(10), mem(sp(), 16)) }, []FrameObject{{16, 16}}},
		{"non-frame-pair", func(f *asm.Function) { f.Items[3] = ins("stp", x(9), x(10), mem(x(2), 16)) }, []FrameObject{{16, 16}}},
		{"live-x-source", func(f *asm.Function) { insertPairItems(f, 4, ins("add", x(0), x(9), x(10))) }, []FrameObject{{16, 16}}},
		{"live-w-source", func(f *asm.Function) { insertPairItems(f, 4, ins("add", w(0), w(9), w(10))) }, []FrameObject{{16, 16}}},
		{"live-through-branch", func(f *asm.Function) {
			insertPairItems(f, 4, ins("cmp", w(2), imm(0)), bcond("eq", "join"),
				ins("add", w(0), w(9), w(10)), label("join"))
		}, []FrameObject{{16, 16}}},
		{"live-through-backedge", func(f *asm.Function) {
			insertPairItems(f, 3, label("again"))
			insertPairItems(f, 12, ins("cmp", w(2), imm(0)), bcond("ne", "again"))
		}, []FrameObject{{16, 16}}},
		{"wide-overlap", func(f *asm.Function) { f.Items[4] = ins("ldr", x(0), mem(sp(), 16)) }, []FrameObject{{16, 16}}},
		{"narrow-overlap", func(f *asm.Function) { f.Items[4] = ins("ldrh", w(0), mem(sp(), 16)) }, []FrameObject{{16, 16}}},
		{"pair-overlap", func(f *asm.Function) { f.Items[4] = ins("ldp", w(0), w(11), mem(sp(), 16)) }, []FrameObject{{16, 16}}},
		{"duplicate-store", func(f *asm.Function) { f.Items[4] = ins("stp", x(9), x(10), mem(sp(), 16)) }, []FrameObject{{16, 16}}},
		{"frame-address", func(f *asm.Function) { f.Items[6] = ins("add", x(0), sp(), imm(16)) }, []FrameObject{{16, 16}}},
		{"out-of-frame-read", func(f *asm.Function) { f.Items[6] = ins("ldr", w(0), mem(sp(), 64)) }, []FrameObject{{16, 16}}},
		{"missing-high-word", func(f *asm.Function) { f.Items[9] = ins("mov", w(11), imm(0)) }, []FrameObject{{16, 16}}},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			f := framePairFixture()
			test.mutate(f)
			if split, words := splitPairFixture(t, f, test.layout); split != nil || len(words) != 0 {
				t.Fatalf("unsafe or unsupported pair split:\n%s", text(split.Items))
			}
		})
	}
}

func TestSplitFramePairInitializersPreservesLiveSource(t *testing.T) {
	// A source consumed on one successor must retain the original complete
	// X value. Refusal is observable, not just a successful liveness query.
	declaration := optIRRV64Declaration(t, `pair_live: (a: u64, b: u64): u64 = a`)
	f := framePairFixture()
	f.Name, f.Signature, f.Fallback = "pair_live", declaration, true
	f.Bindings = []asm.Binding{{Register: x(0), Param: "a"}, {Register: x(1), Param: "b"}}
	f.Clobbers = append(f.Clobbers, x(0))
	insertPairItems(f, len(f.Items)-2, ins("mov", x(0), x(9)))
	if split, _ := splitPairFixture(t, f, []FrameObject{{16, 16}}); split != nil {
		t.Fatal("a live source was destroyed")
	}
	before := cloneFunction(f)
	promoted, count, err := PromoteWith(f, []FrameObject{{16, 16}})
	if err != nil || count != 0 || !reflect.DeepEqual(before, promoted) {
		t.Fatalf("live-source body changed: promoted %d: %v", count, err)
	}
	if verdict := asm.Verify(promoted, declaration, declaration.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("live-source body was not proven: %s: %s", verdict.Kind, verdict.Message)
	}
}

func TestSplitFramePairInitializersRefusesReservedSources(t *testing.T) {
	for _, reserved := range []int{8, 18, 29, 30} {
		for operand := range 2 {
			t.Run("x"+itoa(reserved)+"/operand"+itoa(operand), func(t *testing.T) {
				f := framePairFixture()
				f.Items[1+operand] = ins("mov", x(reserved), x(operand))
				f.Items[3].(asm.Instruction).Operands[operand] = x(reserved)
				f.Clobbers = append(f.Clobbers, x(reserved))
				// Keep the old pair source dead even when the register has
				// an implicit later reader (LR at ret). Declaring a reserved
				// register clobbered still must not authorize splitting it.
				insertPairItems(f, 4, ins("mov", x(reserved), imm(0)))
				lifted, err := Lift(f)
				if err != nil {
					t.Fatal(err)
				}
				webs, err := lifted.Webs()
				if err != nil {
					t.Fatal(err)
				}
				lifted.Liveness(webs)
				for _, web := range webs {
					if web.Reg == (Reg{GPR, reserved}) && web.liveAt(defPos(lifted.Instrs[3])) {
						t.Fatal("fixture relies on source liveness instead of the reserved-register guard")
					}
				}
				split, words, err := splitFramePairInitializers(lifted, []FrameObject{{16, 16}})
				if err != nil || split != nil || len(words) != 0 {
					t.Fatalf("reserved source admitted: split=%v words=%v error=%v", split, words, err)
				}
			})
		}
	}
}

func TestPromoteSplitFramePairProven(t *testing.T) {
	declaration := optIRRV64Declaration(t, `pair_sum: (a: u64, b: u64): u32 {
		u32(a) + u32(a >> u64(32)) + u32(b) + u32(b >> u64(32))
	}`)
	f := framePairFixture()
	f.Name, f.Signature, f.Fallback = "pair_sum", declaration, true
	f.Bindings = []asm.Binding{{Register: x(0), Param: "a"}, {Register: x(1), Param: "b"}}
	f.Clobbers = append(f.Clobbers, x(0))
	before := cloneFunction(f)
	split, _ := splitPairFixture(t, f, []FrameObject{{16, 16}})
	if split == nil {
		t.Fatal("expected pair split")
	}
	promoted, count, err := PromoteWith(f, []FrameObject{{16, 16}})
	if err != nil || count != 4 {
		t.Fatalf("promoted %d, error %v", count, err)
	}
	if strings.Contains(text(promoted.Items), "[sp,#") {
		t.Fatalf("word storage survived promotion:\n%s", text(promoted.Items))
	}
	reallocated, allocation, err := ReallocateWith(f, []FrameObject{{16, 16}})
	if err != nil || allocation.Promoted != 4 {
		t.Fatalf("reallocated %v: %v", allocation, err)
	}
	for name, body := range map[string]*asm.Function{"original": f, "split": split, "promoted": promoted, "reallocated": reallocated} {
		t.Run(name, func(t *testing.T) {
			if findings := asm.Check(body, declaration, nil); len(findings) != 0 {
				t.Fatalf("seam refused: %v\n%s", findings, text(body.Items))
			}
			if verdict := asm.Verify(body, declaration, declaration.Body); verdict.Kind != asm.VerdictProven {
				t.Fatalf("verdict %s: %s\n%s", verdict.Kind, verdict.Message, text(body.Items))
			}
		})
	}
	if !reflect.DeepEqual(f, before) {
		t.Fatal("promotion changed its input")
	}
	// A wrong split is not authorized by the machine transform: its
	// candidate still has to pass the independent semantic verifier.
	wrong := cloneFunction(split)
	for _, item := range wrong.Items {
		if instruction, ok := item.(asm.Instruction); ok && instruction.Mnemonic == "lsr" {
			instruction.Operands[2] = imm(31)
			break
		}
	}
	if verdict := asm.Verify(wrong, declaration, declaration.Body); verdict.Kind != asm.VerdictMismatch {
		t.Fatalf("wrong high half was not refuted: %s: %s", verdict.Kind, verdict.Message)
	}
}

func TestSplitFramePairInitializersEveryWordProven(t *testing.T) {
	// Prove each output separately: a word permutation could preserve the
	// sum above while changing the actual 16 bytes written by the pair.
	for index, expression := range []string{"u32(a)", "u32(a >> u64(32))", "u32(b)", "u32(b >> u64(32))"} {
		t.Run(itoa(index), func(t *testing.T) {
			declaration := optIRRV64Declaration(t, "pair_word: (a: u64, b: u64): u32 = "+expression)
			f := framePairFixture()
			f.Name, f.Signature, f.Fallback = "pair_word", declaration, true
			f.Bindings = []asm.Binding{{Register: x(0), Param: "a"}, {Register: x(1), Param: "b"}}
			f.Clobbers = append(f.Clobbers, x(0))
			insertPairItems(f, len(f.Items)-2, ins("ldr", w(0), mem(sp(), int64(16+4*index))))
			split, _ := splitPairFixture(t, f, []FrameObject{{16, 16}})
			if split == nil {
				t.Fatal("expected pair split")
			}
			allocated, allocation, err := ReallocateWith(f, []FrameObject{{16, 16}})
			if err != nil || allocation.Promoted != 4 {
				t.Fatalf("reallocated %v: %v", allocation, err)
			}
			for name, body := range map[string]*asm.Function{"original": f, "split": split, "reallocated": allocated} {
				if findings := asm.Check(body, declaration, nil); len(findings) != 0 {
					t.Fatalf("%s seam refused: %v", name, findings)
				}
				if verdict := asm.Verify(body, declaration, declaration.Body); verdict.Kind != asm.VerdictProven {
					t.Fatalf("%s word %d: %s: %s", name, index, verdict.Kind, verdict.Message)
				}
			}
		})
	}
}

func TestPromoteSplitFramePairRequiresSplitWordBenefit(t *testing.T) {
	// Pair words cross a call, with no saved callee register. An unrelated
	// word stored after the call can still promote, but must not retain a
	// split that did not help any of the four exposed words.
	f := framePairFixture()
	f.Items = append(f.Items[:4], append([]asm.Item{
		ins("bl", sym("g")),
		ins("str", w(0), mem(sp(), 32)),
		ins("ldr", w(0), mem(sp(), 32)),
	}, f.Items[4:]...)...)
	f.Clobbers = append(f.Clobbers, x(30))
	objects := []FrameObject{{16, 16}, {32, 4}}
	split, _ := splitPairFixture(t, f, objects)
	if split == nil {
		t.Fatal("fixture must pass pair splitting before allocation")
	}
	want, wantCount, err := promoteWith(f, objects, false)
	if err != nil || wantCount != 1 {
		t.Fatalf("baseline promoted %d: %v", wantCount, err)
	}
	got, count, err := PromoteWith(f, objects)
	if err != nil || count != wantCount || !reflect.DeepEqual(got, want) {
		t.Fatalf("unhelpful split was retained: promoted %d: %v\n%s", count, err, text(got.Items))
	}
}
