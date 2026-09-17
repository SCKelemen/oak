package machine

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
)

func x(n int) asm.Register {
	if n == 31 {
		return asm.Register{Text: "xzr", Class: asm.ClassX, Num: 31, Lane: -1}
	}
	return asm.Register{Text: "x" + itoa(n), Class: asm.ClassX, Num: n, Lane: -1}
}

func w(n int) asm.Register {
	if n == 31 {
		return asm.Register{Text: "wzr", Class: asm.ClassW, Num: 31, Lane: -1}
	}
	return asm.Register{Text: "w" + itoa(n), Class: asm.ClassW, Num: n, Lane: -1}
}

func v(n int, arr string) asm.Register {
	return asm.Register{Text: "v" + itoa(n) + "." + arr, Class: asm.ClassV, Num: n, Vec: arr, Lane: -1}
}

func q(n int) asm.Register {
	return asm.Register{Text: "q" + itoa(n), Class: asm.ClassV, Num: n, Vec: "q", Lane: -1}
}

func sp() asm.Register { return asm.Register{Text: "sp", Class: asm.ClassSP, Num: -1, Lane: -1} }

func imm(n int64) asm.Immediate { return asm.Immediate{Value: n} }

func mem(base asm.Register, off int64) asm.Memory { return asm.Memory{Base: base, Offset: off} }

func sym(name string) asm.Symbol { return asm.Symbol{Name: name} }

func ins(m string, ops ...asm.Operand) asm.Instruction {
	return asm.Instruction{Mnemonic: m, Operands: ops}
}

func bcond(cond, label string) asm.Instruction {
	return asm.Instruction{Mnemonic: "b", Cond: cond, Operands: []asm.Operand{sym(label)}}
}

func label(name string) asm.Label { return asm.Label{Name: name} }

func fn(items ...asm.Item) *asm.Function {
	return &asm.Function{Name: "f", Arch: asm.ArchArm64, Items: items, Clobbers: []asm.Register{x(9), x(10), x(11)}}
}

// text spells the items for comparison.
func text(items []asm.Item) string {
	var b strings.Builder
	for _, item := range items {
		switch it := item.(type) {
		case asm.Label:
			b.WriteString(it.Name + ":\n")
		case asm.Instruction:
			b.WriteString(it.Mnemonic)
			if it.Cond != "" {
				b.WriteString("." + it.Cond)
			}
			for i, op := range it.Operands {
				if i > 0 {
					b.WriteString(",")
				}
				b.WriteString(" ")
				switch o := op.(type) {
				case asm.Register:
					b.WriteString(o.Text)
				case asm.Immediate:
					b.WriteString("#" + itoa(int(o.Value)))
				case asm.Memory:
					b.WriteString("[" + o.Base.Text + ",#" + itoa(int(o.Offset)) + "]")
				case asm.Symbol:
					b.WriteString(o.Name)
				}
			}
			b.WriteString("\n")
		}
	}
	return b.String()
}

func TestLiftBlocksAndEdges(t *testing.T) {
	f, err := Lift(fn(
		ins("mov", w(9), w(0)),
		label("loop_1"),
		ins("cmp", w(9), w(1)),
		bcond("hs", "done_2"),
		ins("add", w(9), w(9), imm(1)),
		ins("b", sym("loop_1")),
		label("done_2"),
		ins("mov", w(0), w(9)),
		ins("ret"),
	))
	if err != nil {
		t.Fatal(err)
	}
	if len(f.Blocks) != 4 {
		t.Fatalf("%d blocks", len(f.Blocks))
	}
	// entry -> loop_1 -> {done_2, body}; body -> loop_1; done_2 -> none.
	loop := f.labels["loop_1"]
	if len(loop.Preds) != 2 || len(loop.Succs) != 2 {
		t.Fatalf("loop_1 preds %d succs %d", len(loop.Preds), len(loop.Succs))
	}
	if len(f.labels["done_2"].Succs) != 0 {
		t.Fatal("ret must end the flow")
	}
	if !f.Instrs[len(f.Instrs)-1].Ret || !f.Instrs[2].Branch {
		t.Fatal("instruction kinds")
	}
}

func TestLiftRefusesUnknownShapes(t *testing.T) {
	for _, body := range [][]asm.Item{
		{ins("frobnicate", w(9), w(0)), ins("ret")},
		{ins("br", x(9))},
		{ins("ldr", w(9), asm.Memory{Base: x(0), Offset: 8, Mode: asm.MemPostIndex}), ins("ret")},
		{ins("b", sym("nowhere"))},
	} {
		if _, err := Lift(fn(body...)); err == nil {
			t.Errorf("lift admitted %s", text(body))
		}
	}
}

func TestWebsAndLiveness(t *testing.T) {
	// x0 (parameter) copied to w9; w9 counts in a loop; w10 is a temporary
	// defined and used inside one iteration; the result copies w9 to w0.
	f, err := Lift(fn(
		ins("mov", w(9), w(0)),
		label("loop_1"),
		ins("cmp", w(9), w(1)),
		bcond("hs", "done_2"),
		ins("lsl", w(10), w(9), imm(1)),
		ins("add", w(9), w(10), imm(1)),
		ins("b", sym("loop_1")),
		label("done_2"),
		ins("mov", w(0), w(9)),
		ins("ret"),
	))
	if err != nil {
		t.Fatal(err)
	}
	webs, err := f.Webs()
	if err != nil {
		t.Fatal(err)
	}
	f.Liveness(webs)
	var w9, w10 *Web
	for _, wb := range webs {
		switch {
		case wb.Reg == (Reg{GPR, 9}) && len(wb.Uses) > 0:
			w9 = wb
		case wb.Reg == (Reg{GPR, 10}) && len(wb.Uses) > 0:
			w10 = wb
		}
	}
	if w9 == nil || w10 == nil {
		t.Fatal("webs of w9 and w10 not found")
	}
	// w9's two definitions (the copy, the add) reach the loop's compare:
	// one web, live from the copy through the final read.
	if len(w9.Defs) != 2 || len(w9.Uses) != 3 {
		t.Fatalf("w9 web: %d defs %d uses", len(w9.Defs), len(w9.Uses))
	}
	if w9.Pinned {
		t.Fatalf("w9 pinned: %s", w9.Why)
	}
	if w9.From != defPos(f.Instrs[0]) || w9.To != usePos(f.Instrs[6]) {
		t.Fatalf("w9 range %d–%d", w9.From, w9.To)
	}
	if w10.From != defPos(f.Instrs[3]) || w10.To != usePos(f.Instrs[4]) {
		t.Fatalf("w10 range %d–%d", w10.From, w10.To)
	}
	// The parameter web of x0 and the result web (w0 before ret) are pinned.
	for _, wb := range webs {
		if wb.Reg == (Reg{GPR, 0}) && len(wb.Uses) > 0 && !wb.Pinned {
			t.Fatalf("x0 web not pinned: defs %d uses %d", len(wb.Defs), len(wb.Uses))
		}
	}
}

func TestReallocateCoalescesCopyChains(t *testing.T) {
	// The lowering's `mov w10, wzr; mov w9, w10; ... mov w0, w9` shape: the
	// zero lands in w9 directly and the result copy stays pinned to w0.
	out, alloc, err := Reallocate(fn(
		ins("mov", w(10), w(31)),
		ins("mov", w(9), w(10)),
		ins("add", w(9), w(9), w(1)),
		ins("mov", w(0), w(9)),
		ins("ret"),
	))
	if err != nil {
		t.Fatal(err)
	}
	// Both copies go: the counter's web takes the zero's register and the
	// sum lands in w0 directly.
	got := text(out.Items)
	if alloc.Coalesced+alloc.Propagated != 2 || strings.Count(got, "mov") != 1 || !strings.Contains(got, "add w0, w10, w1") {
		t.Fatalf("coalesced %d propagated %d:\n%s", alloc.Coalesced, alloc.Propagated, got)
	}
}

func TestReallocateKeepsNarrowingCopies(t *testing.T) {
	// x10 is written wide; `mov w9, w10` truncates and zero-extends; x9 is
	// read wide: the copy changes the value and must not be removed.
	out, alloc, err := Reallocate(fn(
		ins("lsl", x(10), x(0), imm(40)),
		ins("mov", w(9), w(10)),
		ins("add", x(0), x(9), x(1)),
		ins("ret"),
	))
	if err != nil {
		t.Fatal(err)
	}
	if alloc.Coalesced != 0 || !strings.Contains(text(out.Items), "mov w") {
		t.Fatalf("a narrowing copy was removed:\n%s", text(out.Items))
	}
	// Read narrow, the copy is a plain rename.
	out, alloc, err = Reallocate(fn(
		ins("lsl", x(10), x(0), imm(40)),
		ins("mov", w(9), w(10)),
		ins("add", w(0), w(9), w(1)),
		ins("ret"),
	))
	if err != nil {
		t.Fatal(err)
	}
	if alloc.Coalesced+alloc.Propagated != 1 || strings.Contains(text(out.Items), "mov w") {
		t.Fatalf("a safe copy stayed:\n%s", text(out.Items))
	}
}

func TestReallocateRespectsCalls(t *testing.T) {
	// w9 is live across the call: it may not move to a caller-saved
	// register, and the pinned argument/result webs stay in x0.
	f := fn(
		ins("sub", sp(), sp(), imm(32)),
		ins("stp", x(29), x(30), mem(sp(), 0)),
		ins("str", x(19), mem(sp(), 16)),
		ins("mov", w(19), w(0)),
		ins("mov", w(0), w(1)),
		ins("bl", sym("g")),
		ins("mov", w(9), w(0)),
		ins("add", w(0), w(9), w(19)),
		ins("ldr", x(19), mem(sp(), 16)),
		ins("ldp", x(29), x(30), mem(sp(), 0)),
		ins("add", sp(), sp(), imm(32)),
		ins("ret"),
	)
	f.Clobbers = []asm.Register{x(9), x(0), x(30)}
	out, alloc, err := Reallocate(f)
	if err != nil {
		t.Fatal(err)
	}
	got := text(out.Items)
	if !strings.Contains(got, "mov w19, w0") || !strings.Contains(got, "add w0, w") {
		t.Fatalf("call-crossing value moved:\n%s", got)
	}
	if !strings.Contains(got, "bl g") || !strings.Contains(got, "ldr x19, [sp,#16]") {
		t.Fatalf("frame code changed:\n%s", got)
	}
	// `mov w9, w0` after the call: w0 is a pinned result web, so w9's web
	// takes x0 only if free — x0 is written by the add right after, and the
	// copy's source dies at the copy, so the copy coalesces away.
	if alloc.Coalesced != 1 {
		t.Fatalf("coalesced %d:\n%s", alloc.Coalesced, got)
	}
}

func TestReallocateIsIdentityWithoutCopies(t *testing.T) {
	f := fn(
		ins("add", w(9), w(0), w(1)),
		ins("lsl", w(10), w(9), imm(2)),
		ins("sub", w(0), w(10), w(9)),
		ins("ret"),
	)
	before := text(f.Items)
	out, alloc, err := Reallocate(f)
	if err != nil {
		t.Fatal(err)
	}
	if text(out.Items) != before || alloc.Renamed != 0 || alloc.Coalesced != 0 {
		t.Fatalf("changed:\n%s\nto\n%s", before, text(out.Items))
	}
	if text(f.Items) != before {
		t.Fatal("the input was modified")
	}
}

func TestReallocateVectorCopies(t *testing.T) {
	// A vector accumulator copied into a home register and back (the
	// lowering's `orr v31.16b, v16.16b, v16.16b` moves) with no call.
	out, alloc, err := Reallocate(&asm.Function{Name: "f", Arch: asm.ArchArm64, Clobbers: []asm.Register{x(9)},
		Items: []asm.Item{
			ins("dup", v(16, "4s"), w(0)),
			ins("orr", v(31, "16b"), v(16, "16b"), v(16, "16b")),
			ins("add", v(16, "4s"), v(31, "4s"), v(31, "4s")),
			ins("orr", v(31, "16b"), v(16, "16b"), v(16, "16b")),
			ins("str", q(31), mem(x(1), 0)),
			ins("ret"),
		}})
	if err != nil {
		t.Fatal(err)
	}
	got := text(out.Items)
	if alloc.Coalesced+alloc.Propagated != 2 || strings.Contains(got, "orr") {
		t.Fatalf("coalesced %d propagated %d:\n%s", alloc.Coalesced, alloc.Propagated, got)
	}
	// Clobbers cover every register the body now writes.
	written := map[string]bool{}
	for _, c := range out.Clobbers {
		written[c.Text] = true
	}
	for _, item := range out.Items {
		if i, ok := item.(asm.Instruction); ok && (i.Mnemonic == "dup" || i.Mnemonic == "add") {
			r := i.Operands[0].(asm.Register)
			if !written["v"+itoa(r.Num)] {
				t.Fatalf("v%d written but not declared: %v", r.Num, out.Clobbers)
			}
		}
	}
}

func TestSpellKeepsViews(t *testing.T) {
	for _, c := range []struct {
		from asm.Register
		want string
	}{
		{w(9), "w3"}, {x(9), "x3"}, {v(9, "4s"), "v3.4s"}, {q(9), "q3"},
		{asm.Register{Text: "d9", Class: asm.ClassV, Num: 9, Vec: "d", Lane: -1}, "d3"},
		{asm.Register{Text: "v9.s[1]", Class: asm.ClassV, Num: 9, Vec: "s", Lane: 1}, "v3.s[1]"},
		{asm.Register{Text: "v9", Class: asm.ClassV, Num: 9, Lane: -1}, "v3"},
	} {
		to := Reg{GPR, 3}
		if c.from.Class == asm.ClassV {
			to = Reg{VEC, 3}
		}
		if got := spell(c.from, to).Text; got != c.want {
			t.Errorf("spell(%s) = %s, want %s", c.from.Text, got, c.want)
		}
	}
}

func framed(items ...asm.Item) *asm.Function {
	f := fn(items...)
	f.Frame = 64
	return f
}

func TestPromoteMovesSlotsIntoRegisters(t *testing.T) {
	// A value parked in [sp, #16] between its definition and two reads,
	// no call: the slot becomes a register and the copies coalesce.
	f := framed(
		ins("sub", sp(), sp(), imm(64)),
		ins("add", w(9), w(0), w(1)),
		ins("str", w(9), mem(sp(), 16)),
		ins("mul", w(9), w(0), w(0)),
		ins("ldr", w(10), mem(sp(), 16)),
		ins("add", w(9), w(9), w(10)),
		ins("ldr", w(10), mem(sp(), 16)),
		ins("sub", w(0), w(9), w(10)),
		ins("add", sp(), sp(), imm(64)),
		ins("ret"),
	)
	out, alloc, err := Reallocate(f)
	if err != nil {
		t.Fatal(err)
	}
	got := text(out.Items)
	if alloc.Promoted != 1 || strings.Contains(got, "[sp,#16]") {
		t.Fatalf("promoted %d:\n%s", alloc.Promoted, got)
	}
	// The first read coalesces with the value's own register; the second
	// overlaps it (both are live in the add) and stays one copy.
	if strings.Count(got, "mov w") > 1 {
		t.Fatalf("the slot copies must coalesce:\n%s", got)
	}
}

func TestPromoteRefusesEscapedAndCrossingSlots(t *testing.T) {
	// The slot's address is taken (an array at 16): not promotable.
	f := framed(
		ins("sub", sp(), sp(), imm(64)),
		ins("str", w(0), mem(sp(), 16)),
		ins("add", x(9), sp(), imm(16)),
		ins("ldr", w(10), mem(sp(), 16)),
		ins("add", w(0), w(10), w(9)),
		ins("add", sp(), sp(), imm(64)),
		ins("ret"),
	)
	if _, alloc, err := Reallocate(f); err != nil || alloc.Promoted != 0 {
		t.Fatalf("escaped slot promoted (%v): %+v", err, alloc)
	}
	// A slot live across a call with no saved callee-saved register: stays.
	f = framed(
		ins("sub", sp(), sp(), imm(64)),
		ins("stp", x(29), x(30), mem(sp(), 0)),
		ins("str", w(1), mem(sp(), 16)),
		ins("bl", sym("g")),
		ins("ldr", w(10), mem(sp(), 16)),
		ins("add", w(0), w(0), w(10)),
		ins("ldp", x(29), x(30), mem(sp(), 0)),
		ins("add", sp(), sp(), imm(64)),
		ins("ret"),
	)
	f.Clobbers = []asm.Register{x(10), x(30)}
	if _, alloc, err := Reallocate(f); err != nil || alloc.Promoted != 0 {
		t.Fatalf("call-crossing slot promoted (%v): %+v", err, alloc)
	}
	// With x19 saved by the prologue, the slot moves into it across the call.
	f = framed(
		ins("sub", sp(), sp(), imm(64)),
		ins("stp", x(29), x(30), mem(sp(), 0)),
		ins("str", x(19), mem(sp(), 32)),
		ins("mov", w(19), w(2)),
		ins("str", w(1), mem(sp(), 16)),
		ins("bl", sym("g")),
		ins("ldr", w(10), mem(sp(), 16)),
		ins("add", w(0), w(0), w(10)),
		ins("add", w(0), w(0), w(19)),
		ins("ldr", x(19), mem(sp(), 32)),
		ins("ldp", x(29), x(30), mem(sp(), 0)),
		ins("add", sp(), sp(), imm(64)),
		ins("ret"),
	)
	f.Clobbers = []asm.Register{x(10), x(30)}
	out, alloc, err := Reallocate(f)
	if err != nil {
		t.Fatal(err)
	}
	// x19 is busy across the call (it holds w2), so x20 is saved beside it
	// — the next slot of the save area, [sp, #40] — and the value moves
	// there; the save slot of x19 itself is never promoted (its load is a
	// restore with no reader).
	got := text(out.Items)
	if alloc.Promoted != 1 || strings.Contains(got, "[sp,#16]") || !strings.Contains(got, "str x20, [sp,#40]") || !strings.Contains(got, "ldr x20, [sp,#40]") || !strings.Contains(got, "ldr x19, [sp,#32]") {
		t.Fatalf("promoted %d:\n%s", alloc.Promoted, got)
	}
	// The restore precedes the pair's, the save follows x19's.
	if strings.Index(got, "ldr x20, [sp,#40]") > strings.Index(got, "ldp x29, x30") || strings.Index(got, "str x20, [sp,#40]") < strings.Index(got, "str x19, [sp,#32]") {
		t.Fatalf("save/restore placement:\n%s", got)
	}
}

func TestGrowCalleeSavedRefusals(t *testing.T) {
	// The would-be save slot [sp, #40] is used by another value: no growth.
	f := framed(
		ins("sub", sp(), sp(), imm(64)),
		ins("stp", x(29), x(30), mem(sp(), 0)),
		ins("str", x(19), mem(sp(), 32)),
		ins("mov", w(19), w(2)),
		ins("str", w(1), mem(sp(), 16)),
		ins("str", x(3), mem(sp(), 40)),
		ins("bl", sym("g")),
		ins("ldr", w(10), mem(sp(), 16)),
		ins("ldr", x(11), mem(sp(), 40)),
		ins("add", x(0), x(10), x(11)),
		ins("add", w(0), w(0), w(19)),
		ins("ldr", x(19), mem(sp(), 32)),
		ins("ldp", x(29), x(30), mem(sp(), 0)),
		ins("add", sp(), sp(), imm(64)),
		ins("ret"),
	)
	f.Clobbers = []asm.Register{x(10), x(11), x(30)}
	if _, alloc, err := Reallocate(f); err != nil || alloc.Promoted != 0 {
		t.Fatalf("promoted %d (%v)", alloc.Promoted, err)
	}
	// Two returns: no growth.
	f = framed(
		ins("sub", sp(), sp(), imm(64)),
		ins("stp", x(29), x(30), mem(sp(), 0)),
		ins("str", w(1), mem(sp(), 16)),
		ins("bl", sym("g")),
		ins("cbz", w(0), sym("zero_1")),
		ins("ldr", w(10), mem(sp(), 16)),
		ins("add", w(0), w(0), w(10)),
		ins("ldp", x(29), x(30), mem(sp(), 0)),
		ins("add", sp(), sp(), imm(64)),
		ins("ret"),
		label("zero_1"),
		ins("ldr", w(0), mem(sp(), 16)),
		ins("ldp", x(29), x(30), mem(sp(), 0)),
		ins("add", sp(), sp(), imm(64)),
		ins("ret"),
	)
	f.Clobbers = []asm.Register{x(10), x(30)}
	if _, alloc, err := Reallocate(f); err != nil || alloc.Promoted != 0 {
		t.Fatalf("promoted %d with two returns (%v)", alloc.Promoted, err)
	}
	// No [x29, x30] pair (the shape of a leaf): no growth.
	f = framed(
		ins("sub", sp(), sp(), imm(64)),
		ins("str", w(1), mem(sp(), 16)),
		ins("bl", sym("g")),
		ins("ldr", w(10), mem(sp(), 16)),
		ins("add", w(0), w(0), w(10)),
		ins("add", sp(), sp(), imm(64)),
		ins("ret"),
	)
	f.Clobbers = []asm.Register{x(10), x(30)}
	if _, alloc, err := Reallocate(f); err != nil || alloc.Promoted != 0 {
		t.Fatalf("promoted %d without a pair (%v)", alloc.Promoted, err)
	}
}

func TestPromoteMixedWidthAndUninitializedSlots(t *testing.T) {
	f := framed(
		ins("sub", sp(), sp(), imm(64)),
		ins("str", x(0), mem(sp(), 16)),
		ins("ldr", w(10), mem(sp(), 16)), // a narrower read: not one width
		ins("ldr", w(11), mem(sp(), 24)), // read before any store
		ins("str", w(11), mem(sp(), 24)),
		ins("add", w(0), w(10), w(11)),
		ins("add", sp(), sp(), imm(64)),
		ins("ret"),
	)
	if _, alloc, err := Reallocate(f); err != nil || alloc.Promoted != 0 {
		t.Fatalf("promoted %d (%v)", alloc.Promoted, err)
	}
}

func TestPromoteVectorSlot(t *testing.T) {
	f := framed(
		ins("sub", sp(), sp(), imm(64)),
		ins("dup", v(16, "4s"), w(0)),
		ins("str", q(16), mem(sp(), 16)),
		ins("dup", v(16, "4s"), w(1)),
		ins("ldr", q(17), mem(sp(), 16)),
		ins("add", v(0, "4s"), v(16, "4s"), v(17, "4s")),
		ins("add", sp(), sp(), imm(64)),
		ins("ret"),
	)
	out, alloc, err := Reallocate(f)
	if err != nil {
		t.Fatal(err)
	}
	got := text(out.Items)
	if alloc.Promoted != 1 || strings.Contains(got, "[sp,#16]") || strings.Contains(got, "orr") {
		t.Fatalf("promoted %d:\n%s", alloc.Promoted, got)
	}
}

func TestPromoteKeepsWordsReadAsChunks(t *testing.T) {
	// Two u32 elements stored as words at 96 and 100 and read as one
	// 64-bit chunk at 96: neither word is a slot of its own.
	f := fn(
		ins("sub", sp(), sp(), imm(128)),
		ins("str", w(0), mem(sp(), 96)),
		ins("str", w(1), mem(sp(), 100)),
		ins("ldr", w(9), mem(sp(), 100)),
		ins("ldr", x(10), mem(sp(), 96)),
		ins("add", x(0), x(10), x(9)),
		ins("add", sp(), sp(), imm(128)),
		ins("ret"),
	)
	f.Frame = 128
	if _, alloc, err := Reallocate(f); err != nil || alloc.Promoted != 0 {
		t.Fatalf("promoted %d (%v)", alloc.Promoted, err)
	}
}

// RV64 spellings.
func rx(n int) asm.Register {
	return asm.Register{Text: rv64Names[n], Class: asm.ClassRV64X, Num: n, Lane: -1}
}

func rf(n int) asm.Register {
	return asm.Register{Text: rv64FNames[n], Class: asm.ClassRV64F, Num: n, Lane: -1}
}

func rvfn(items ...asm.Item) *asm.Function {
	return &asm.Function{Name: "f", Arch: asm.ArchRV64, Items: items, Frame: 64, Clobbers: []asm.Register{rx(5), rx(6), rx(7)}}
}

func TestRV64LiftAndCoalesce(t *testing.T) {
	// The lowering's copies through a scratch: `mv t0, a0; ... mv a0, t0`.
	out, alloc, err := Reallocate(rvfn(
		ins("mv", rx(5), rx(10)),
		ins("addi", rx(5), rx(5), imm(1)),
		ins("mv", rx(10), rx(5)),
		ins("ret"),
	))
	if err != nil {
		t.Fatal(err)
	}
	got := text(out.Items)
	if alloc.Coalesced+alloc.Propagated != 2 || !strings.Contains(got, "addi a0, a0, #1") {
		t.Fatalf("coalesced %d propagated %d:\n%s", alloc.Coalesced, alloc.Propagated, got)
	}
	// Unknown shapes refuse: an indirect jump, an instruction the lane
	// never emits.
	for _, body := range [][]asm.Item{
		{ins("jr", rx(5))},
		{ins("vfwcvt.f.x.v", asm.Register{Text: "v1", Class: asm.ClassRV64V, Num: 1, Lane: -1}, asm.Register{Text: "v2", Class: asm.ClassRV64V, Num: 2, Lane: -1}), ins("ret")},
	} {
		if _, err := Lift(rvfn(body...)); err == nil {
			t.Errorf("lift admitted %s", text(body))
		}
	}
}

func TestRV64CallContractAndSlots(t *testing.T) {
	// A value parked in the frame across a call moves into s2, saved
	// beside s1; a word slot (sw/lw) is not a slot; ra's save is not one.
	f := rvfn(
		ins("addi", sp(), sp(), imm(-64)),
		ins("sd", rx(1), mem(sp(), 0)),
		ins("sd", rx(9), mem(sp(), 16)),
		ins("mv", rx(9), rx(11)),
		ins("sd", rx(10), mem(sp(), 32)),
		ins("sw", rx(12), mem(sp(), 40)),
		ins("mv", rx(10), rx(12)),
		ins("call", sym("g")),
		ins("ld", rx(5), mem(sp(), 32)),
		ins("lw", rx(6), mem(sp(), 40)),
		ins("add", rx(10), rx(10), rx(5)),
		ins("add", rx(10), rx(10), rx(6)),
		ins("add", rx(10), rx(10), rx(9)),
		ins("ld", rx(9), mem(sp(), 16)),
		ins("ld", rx(1), mem(sp(), 0)),
		ins("addi", sp(), sp(), imm(64)),
		ins("ret"),
	)
	f.Clobbers = []asm.Register{rx(5), rx(6)}
	out, alloc, err := Reallocate(f)
	if err != nil {
		t.Fatal(err)
	}
	got := text(out.Items)
	if alloc.Promoted != 1 || strings.Contains(got, "[sp,#32]") || !strings.Contains(got, "sd s2, [sp,#24]") || !strings.Contains(got, "ld s2, [sp,#24]") {
		t.Fatalf("promoted %d:\n%s", alloc.Promoted, got)
	}
	if !strings.Contains(got, "sw a2, [sp,#40]") || !strings.Contains(got, "lw ") || !strings.Contains(got, "sd s1, [sp,#16]") || !strings.Contains(got, "ld ra, [sp,#0]") {
		t.Fatalf("frame code changed:\n%s", got)
	}
	// No callee-saved register is declared a clobber (the checker refuses).
	for _, c := range out.Clobbers {
		if r, _, _, ok, _ := rv64Target.regOf(c); ok && rv64Target.calleeSaved(r) {
			t.Fatalf("callee-saved %s declared a clobber", c.Text)
		}
	}
}

func TestDominatorsAndLoops(t *testing.T) {
	// entry -> outer header; outer body: inner loop; inner latch back to
	// inner header; outer latch back to outer header; exit.
	f, err := Lift(fn(
		ins("mov", w(9), w(0)),
		label("outer_1"),
		ins("cmp", w(9), w(1)),
		bcond("hs", "done_4"),
		ins("mov", w(10), w(31)),
		label("inner_2"),
		ins("cmp", w(10), w(2)),
		bcond("hs", "next_3"),
		ins("add", w(10), w(10), imm(1)),
		ins("b", sym("inner_2")),
		label("next_3"),
		ins("add", w(9), w(9), imm(1)),
		ins("b", sym("outer_1")),
		label("done_4"),
		ins("ret"),
	))
	if err != nil {
		t.Fatal(err)
	}
	d := f.Dominators()
	outer, inner, next, done := f.labels["outer_1"], f.labels["inner_2"], f.labels["next_3"], f.labels["done_4"]
	if !d.Dominates(outer, inner) || !d.Dominates(inner, next) || !d.Dominates(outer, done) || d.Dominates(inner, done) {
		t.Fatal("dominance")
	}
	if d.Idom(next) != inner || d.Idom(inner) == nil || d.Idom(f.Blocks[0]) != nil {
		t.Fatalf("idom: next %v inner %v", d.Idom(next), d.Idom(inner))
	}
	loops := d.Loops()
	if len(loops) != 2 || loops[0].Header != outer || loops[1].Header != inner {
		t.Fatalf("loops: %d", len(loops))
	}
	if loops[0].Depth != 1 || loops[1].Depth != 2 || loops[1].Parent != loops[0] {
		t.Fatalf("nesting: %d %d", loops[0].Depth, loops[1].Depth)
	}
	if loops[0].Preheader != f.Blocks[0] || loops[1].Preheader == nil || !loops[0].Contains(next) || loops[1].Contains(next) {
		t.Fatalf("preheaders/bodies: outer %v inner %v", loops[0].Preheader, loops[1].Preheader)
	}
}

func TestSimplifyPropagatesAndEliminates(t *testing.T) {
	// `mov w10, w9; add w0, w0, w10` with w9 live after: the add reads w9
	// and the copy goes; a dead frame reload goes, and so does the store
	// to that slot once nothing reads it (Promote's dead stores); a dead
	// compare and a call's unread result stay.
	f := framed(
		ins("sub", sp(), sp(), imm(64)),
		ins("stp", x(29), x(30), mem(sp(), 0)),
		ins("add", w(9), w(0), w(1)),
		ins("mov", w(10), w(9)),
		ins("add", w(0), w(0), w(10)),
		ins("sub", w(0), w(0), w(9)),
		ins("ldr", q(16), mem(sp(), 16)),
		ins("dup", v(16, "4s"), w(0)),
		ins("str", q(16), mem(sp(), 16)),
		ins("cmp", w(0), w(1)),
		ins("bl", sym("g")),
		ins("ldp", x(29), x(30), mem(sp(), 0)),
		ins("add", sp(), sp(), imm(64)),
		ins("ret"),
	)
	f.Clobbers = []asm.Register{x(9), x(10), x(30)}
	out, alloc, err := Reallocate(f)
	if err != nil {
		t.Fatal(err)
	}
	got := text(out.Items)
	if alloc.Propagated != 1 || alloc.Eliminated < 2 {
		t.Fatalf("propagated %d eliminated %d:\n%s", alloc.Propagated, alloc.Eliminated, got)
	}
	if strings.Contains(got, "mov w10") || !strings.Contains(got, "add w0, w0, w9") {
		t.Fatalf("copy not propagated:\n%s", got)
	}
	if strings.Contains(got, "ldr q16") || strings.Contains(got, "str q16") || alloc.DeadStores != 1 || !strings.Contains(got, "cmp w0, w1") || !strings.Contains(got, "bl g") {
		t.Fatalf("elimination (dead stores %d):\n%s", alloc.DeadStores, got)
	}
}

func TestSimplifyKeepsUnsafeCopies(t *testing.T) {
	// The source is written twice: the copy's value would change.
	f := fn(
		ins("add", w(9), w(0), w(1)),
		ins("mov", w(10), w(9)),
		ins("add", w(9), w(9), w(1)),
		ins("add", w(0), w(9), w(10)),
		ins("ret"),
	)
	out, alloc, err := Reallocate(f)
	if err != nil {
		t.Fatal(err)
	}
	if alloc.Propagated != 0 || alloc.Coalesced != 0 || !strings.Contains(text(out.Items), "mov w") {
		t.Fatalf("propagated %d coalesced %d:\n%s", alloc.Propagated, alloc.Coalesced, text(out.Items))
	}
	// A narrowing copy read wide stays.
	f = fn(
		ins("lsl", x(9), x(0), imm(40)),
		ins("mov", w(10), w(9)),
		ins("add", x(0), x(10), x(9)),
		ins("ret"),
	)
	out, alloc, err = Reallocate(f)
	if err != nil {
		t.Fatal(err)
	}
	if alloc.Propagated != 0 || !strings.Contains(text(out.Items), "mov w10, w9") {
		t.Fatalf("propagated a narrowing copy:\n%s", text(out.Items))
	}
}

func TestHoistInvariants(t *testing.T) {
	// `movz w9, #3; mul w10, w20, w9` is the same every trip: both move
	// to the preheader. The counter's increment, the compare, and a csel
	// on the loop's flags stay.
	f := fn(
		ins("mov", w(20), w(1)),
		ins("mov", w(21), w(31)),
		ins("mov", w(22), w(31)),
		label("loop_1"),
		ins("cmp", w(21), w(0)),
		bcond("hs", "done_2"),
		ins("movz", w(9), imm(3)),
		ins("mul", w(10), w(20), w(9)),
		ins("add", w(22), w(22), w(10)),
		ins("csel", w(11), w(22), w(20), asm.Condition{Code: "lo"}),
		ins("add", w(22), w(22), w(11)),
		ins("add", w(21), w(21), imm(1)),
		ins("b", sym("loop_1")),
		label("done_2"),
		ins("mov", w(0), w(22)),
		ins("ret"),
	)
	f.Clobbers = []asm.Register{x(9), x(10), x(11), x(20), x(21), x(22)}
	lifted, err := Lift(cloneFunction(f))
	if err != nil {
		t.Fatal(err)
	}
	hoisted, err := lifted.HoistInvariants()
	if err != nil {
		t.Fatal(err)
	}
	got := text(lifted.Items())
	if hoisted != 2 {
		t.Fatalf("hoisted %d:\n%s", hoisted, got)
	}
	loopAt := strings.Index(got, "loop_1:")
	if strings.Index(got, "movz w9") > loopAt || strings.Index(got, "mul w10") > loopAt || strings.Index(got, "csel") < loopAt || strings.Index(got, "add w21") < loopAt {
		t.Fatalf("placement:\n%s", got)
	}
}

func TestHoistRefusals(t *testing.T) {
	// A frame load stays when the loop stores to the frame; an invariant
	// whose register is busy inside the loop stays.
	f := framed(
		ins("sub", sp(), sp(), imm(64)),
		ins("mov", w(20), w(1)),
		ins("mov", w(21), w(31)),
		ins("str", w(20), mem(sp(), 16)),
		label("loop_1"),
		ins("cmp", w(21), w(0)),
		bcond("hs", "done_2"),
		ins("ldr", w(9), mem(sp(), 16)),
		ins("add", w(9), w(9), w(21)),
		ins("str", w(9), mem(sp(), 16)),
		ins("movz", w(10), imm(7)),
		ins("add", w(21), w(21), w(10)),
		ins("mul", w(10), w(21), w(21)),
		ins("add", w(21), w(21), w(10)),
		ins("b", sym("loop_1")),
		label("done_2"),
		ins("ldr", w(0), mem(sp(), 16)),
		ins("add", sp(), sp(), imm(64)),
		ins("ret"),
	)
	f.Clobbers = []asm.Register{x(9), x(10), x(20), x(21)}
	lifted, err := Lift(cloneFunction(f))
	if err != nil {
		t.Fatal(err)
	}
	hoisted, err := lifted.HoistInvariants()
	if err != nil {
		t.Fatal(err)
	}
	got := text(lifted.Items())
	loopAt := strings.Index(got, "loop_1:")
	if hoisted != 0 || strings.Index(got, "ldr w9") < loopAt || strings.Index(got, "movz w10") < loopAt {
		t.Fatalf("hoisted %d:\n%s", hoisted, got)
	}
}

func TestHoistNestedLoops(t *testing.T) {
	// An invariant of the inner loop climbs to the inner preheader, then,
	// being invariant in the outer loop too, out of both.
	f := fn(
		ins("mov", w(20), w(1)),
		ins("mov", w(21), w(31)),
		ins("mov", w(23), w(31)),
		label("outer_1"),
		ins("cmp", w(21), w(0)),
		bcond("hs", "done_4"),
		ins("mov", w(22), w(31)),
		label("inner_2"),
		ins("cmp", w(22), w(0)),
		bcond("hs", "next_3"),
		ins("lsl", w(9), w(20), imm(2)),
		ins("add", w(23), w(23), w(9)),
		ins("add", w(22), w(22), imm(1)),
		ins("b", sym("inner_2")),
		label("next_3"),
		ins("add", w(21), w(21), imm(1)),
		ins("b", sym("outer_1")),
		label("done_4"),
		ins("mov", w(0), w(23)),
		ins("ret"),
	)
	f.Clobbers = []asm.Register{x(9), x(20), x(21), x(22), x(23)}
	lifted, err := Lift(cloneFunction(f))
	if err != nil {
		t.Fatal(err)
	}
	hoisted, err := lifted.HoistInvariants()
	if err != nil {
		t.Fatal(err)
	}
	got := text(lifted.Items())
	if hoisted != 2 || strings.Index(got, "lsl w9") > strings.Index(got, "outer_1:") {
		t.Fatalf("hoisted %d:\n%s", hoisted, got)
	}
}

func TestShapesInductionAndRemainder(t *testing.T) {
	// A main loop striding by four, then its remainder by one over the
	// same index and bound; a constant-bounded loop with a known trip
	// count; an increment that is not the exit's index.
	f := fn(
		ins("mov", w(9), w(31)),
		ins("mov", w(11), w(31)),
		label("main_1"),
		ins("cmp", w(9), w(20)),
		bcond("hi", "rest_2"),
		ins("add", w(11), w(11), imm(2)),
		ins("add", w(9), w(9), imm(4)),
		ins("b", sym("main_1")),
		label("rest_2"),
		ins("cmp", w(9), w(1)),
		bcond("hs", "count_3"),
		ins("add", w(9), w(9), imm(1)),
		ins("b", sym("rest_2")),
		label("count_3"),
		ins("movz", w(10), imm(0)),
		label("loop_4"),
		ins("cmp", w(10), imm(10)),
		bcond("hs", "done_5"),
		ins("add", w(11), w(11), w(10)),
		ins("add", w(10), w(10), imm(3)),
		ins("b", sym("loop_4")),
		label("done_5"),
		ins("mov", w(0), w(11)),
		ins("ret"),
	)
	f.Clobbers = []asm.Register{x(9), x(10), x(11)}
	shapes, err := LoopShapes(f)
	if err != nil {
		t.Fatal(err)
	}
	if len(shapes) != 3 {
		t.Fatalf("%d loops", len(shapes))
	}
	by := map[string]*LoopShape{}
	for _, sh := range shapes {
		by[sh.Header] = sh
	}
	main, rest, count := by["main_1"], by["rest_2"], by["loop_4"]
	if main == nil || main.Index == nil || main.Stride != 4 || main.Index.Reg != (Reg{GPR, 9}) || main.BoundReg != (Reg{GPR, 20}) || main.MaxTrips != 0 {
		t.Fatalf("main: %v", main)
	}
	if len(main.Inductions) != 2 {
		t.Fatalf("main inductions: %d (w11 steps by two every trip too)", len(main.Inductions))
	}
	// The remainder's bound differs (w1 against w20), so no trip bound.
	if rest == nil || rest.Stride != 1 || rest.MaxTrips != 0 {
		t.Fatalf("rest: %v", rest)
	}
	if count == nil || count.Stride != 3 || !count.BoundIsImm || count.BoundImm != 10 || !count.Index.StartKnown || count.MaxTrips != 4 {
		t.Fatalf("count: %v", count)
	}
}

func TestShapesRemainderBound(t *testing.T) {
	f := fn(
		ins("mov", w(9), w(31)),
		label("main_1"),
		ins("cmp", w(9), w(20)),
		bcond("hi", "rest_2"),
		ins("add", w(9), w(9), imm(4)),
		ins("b", sym("main_1")),
		label("rest_2"),
		ins("cmp", w(9), w(20)),
		bcond("hs", "done_3"),
		ins("add", w(9), w(9), imm(1)),
		ins("b", sym("rest_2")),
		label("done_3"),
		ins("mov", w(0), w(9)),
		ins("ret"),
	)
	shapes, err := LoopShapes(f)
	if err != nil {
		t.Fatal(err)
	}
	if len(shapes) != 2 || shapes[1].MaxTrips != 3 || shapes[0].Stride != 4 {
		t.Fatalf("%v / %v", shapes[0], shapes[1])
	}
	// An index incremented under a condition is not an induction.
	f = fn(
		ins("mov", w(9), w(31)),
		label("loop_1"),
		ins("cmp", w(9), w(20)),
		bcond("hs", "done_3"),
		ins("cbz", w(1), sym("skip_2")),
		ins("add", w(9), w(9), imm(2)),
		label("skip_2"),
		ins("add", w(9), w(9), imm(1)),
		ins("b", sym("loop_1")),
		label("done_3"),
		ins("ret"),
	)
	shapes, err = LoopShapes(f)
	if err != nil {
		t.Fatal(err)
	}
	if len(shapes) != 1 || shapes[0].Index != nil || shapes[0].Stride != 1 {
		t.Fatalf("conditional increment: %v", shapes[0])
	}
}

func TestShapesVectorCleanupBound(t *testing.T) {
	f := fn(
		ins("mov", w(9), w(31)),
		label("main_1"),
		ins("cmp", w(9), w(20)), bcond("hi", "vectors_2"),
		ins("add", w(9), w(9), imm(8)), ins("b", sym("main_1")),
		label("vectors_2"),
		ins("cmp", w(9), w(20)), bcond("hi", "scalar_3"),
		ins("add", w(9), w(9), imm(4)), ins("b", sym("vectors_2")),
		label("scalar_3"),
		ins("cmp", w(9), w(20)), bcond("hs", "done_4"),
		ins("add", w(9), w(9), imm(1)), ins("b", sym("scalar_3")),
		label("done_4"), ins("mov", w(0), w(9)), ins("ret"),
	)
	shapes, err := LoopShapes(f)
	if err != nil {
		t.Fatal(err)
	}
	if len(shapes) != 3 || shapes[1].Stride != 4 || shapes[1].MaxTrips != 1 || shapes[2].MaxTrips != 3 {
		t.Fatalf("unexpected vector/scalar cleanup shapes: %+v", shapes)
	}
}

func TestShapesRV64(t *testing.T) {
	f := rvfn(
		ins("mv", rx(5), rx(0)),
		label("loop_1"),
		ins("bgeu", rx(5), rx(11), sym("done_2")),
		ins("addi", rx(5), rx(5), imm(8)),
		ins("j", sym("loop_1")),
		label("done_2"),
		ins("ret"),
	)
	shapes, err := LoopShapes(f)
	if err != nil {
		t.Fatal(err)
	}
	if len(shapes) != 1 || shapes[0].Stride != 8 || shapes[0].BoundReg != (Reg{GPR, 11}) || !shapes[0].Index.StartKnown {
		t.Fatalf("%v", shapes[0])
	}
}

func TestLiftExtendedOperands(t *testing.T) {
	// `add x9, x19, w3, uxtw #2` reads w3 through an extended operand;
	// reallocation respells it with the register it gives w3's web.
	f := fn(
		ins("mov", w(10), w(0)),
		ins("mov", w(3), w(10)),
		ins("add", x(9), x(19), asm.Extended{Reg: w(3), Kind: "uxtw", Amount: 2}),
		ins("ldr", w(0), mem(x(9), 0)),
		ins("ret"),
	)
	f.Clobbers = []asm.Register{x(9), x(10), x(3)}
	out, alloc, err := Reallocate(f)
	if err != nil {
		t.Fatal(err)
	}
	if alloc.Coalesced+alloc.Propagated == 0 {
		t.Fatalf("no copy removed:\n%v", out.Items)
	}
	var ext asm.Extended
	for _, item := range out.Items {
		if i, ok := item.(asm.Instruction); ok && i.Mnemonic == "add" {
			ext = i.Operands[2].(asm.Extended)
		}
	}
	if ext.Reg.Text != "w0" && ext.Reg.Text != "w10" {
		t.Fatalf("extended register respelled to %q", ext.Reg.Text)
	}
}

func TestPromoteWithFrameLayout(t *testing.T) {
	// An array at [16, 48) whose address is taken, and a scalar slot at 56
	// above it: with the layout known the scalar moves; without it, the
	// escape blocks everything above 16.
	body := func() *asm.Function {
		return framed(
			ins("sub", sp(), sp(), imm(64)),
			ins("add", w(9), w(0), w(1)),
			ins("str", w(9), mem(sp(), 56)),
			ins("add", x(10), sp(), imm(16)),
			ins("str", w(1), mem(x(10), 4)),
			ins("mul", w(9), w(0), w(0)),
			ins("ldr", w(11), mem(sp(), 56)),
			ins("add", w(0), w(9), w(11)),
			ins("add", sp(), sp(), imm(64)),
			ins("ret"),
		)
	}
	_, alloc, err := ReallocateWith(body(), []FrameObject{{Offset: 16, Size: 32}})
	if err != nil {
		t.Fatal(err)
	}
	if alloc.Promoted != 1 {
		t.Fatalf("with the layout: promoted %d", alloc.Promoted)
	}
	_, alloc, err = Reallocate(body())
	if err != nil {
		t.Fatal(err)
	}
	if alloc.Promoted != 0 {
		t.Fatalf("without the layout: promoted %d", alloc.Promoted)
	}
	// A slot inside the object never moves, layout or not.
	f := framed(
		ins("sub", sp(), sp(), imm(64)),
		ins("str", w(1), mem(sp(), 24)),
		ins("add", x(10), sp(), imm(16)),
		ins("ldr", w(11), mem(sp(), 24)),
		ins("add", w(0), w(11), w(10)),
		ins("add", sp(), sp(), imm(64)),
		ins("ret"),
	)
	if _, alloc, err := ReallocateWith(f, []FrameObject{{Offset: 16, Size: 32}}); err != nil || alloc.Promoted != 0 {
		t.Fatalf("inside the object: promoted %d (%v)", alloc.Promoted, err)
	}
}

func TestShapesInvariantBoundInHeader(t *testing.T) {
	// The bound `w9 = w20 - 16` is computed in the header from an
	// invariant: the loop still has an index of stride 16.
	f := fn(
		ins("mov", w(3), w(31)),
		label("loop_1"),
		ins("sub", w(9), w(20), imm(16)),
		ins("cmp", w(3), w(9)),
		bcond("hi", "done_2"),
		ins("add", w(3), w(3), imm(16)),
		ins("b", sym("loop_1")),
		label("done_2"),
		ins("ret"),
	)
	shapes, err := LoopShapes(f)
	if err != nil {
		t.Fatal(err)
	}
	if len(shapes) != 1 || shapes[0].Index == nil || shapes[0].Stride != 16 || shapes[0].BoundReg != (Reg{GPR, 9}) {
		t.Fatalf("%v", shapes[0])
	}
}

func TestScheduleSeparatesLoadsFromUses(t *testing.T) {
	// The load's consumer waits four cycles; two independent adds fill
	// the gap. The store keeps its order against the load, and the compare
	// stays before its branch.
	f := fn(
		ins("ldr", w(9), mem(x(0), 0)),
		ins("add", w(10), w(9), imm(1)),
		ins("add", w(11), w(1), imm(2)),
		ins("add", w(12), w(2), imm(3)),
		ins("str", w(11), mem(x(0), 8)),
		ins("cmp", w(10), w(12)),
		bcond("hs", "done_1"),
		ins("ret"),
		label("done_1"),
		ins("ret"),
	)
	f.Clobbers = []asm.Register{x(9), x(10), x(11), x(12)}
	lifted, err := Lift(cloneFunction(f))
	if err != nil {
		t.Fatal(err)
	}
	before, _ := lifted.Stalls()
	moved := lifted.Schedule()
	after, _ := lifted.Stalls()
	got := text(lifted.Items())
	if moved == 0 || after >= before {
		t.Fatalf("moved %d, stalls %d -> %d:\n%s", moved, before, after, got)
	}
	ldr, use, st, cmp, br := strings.Index(got, "ldr w9"), strings.Index(got, "add w10, w9"), strings.Index(got, "str w11"), strings.Index(got, "cmp w10"), strings.Index(got, "b.hs")
	if !(ldr < use && use < cmp && cmp < br && ldr < st) {
		t.Fatalf("order:\n%s", got)
	}
	if strings.Index(got, "add w11") > use || strings.Index(got, "add w12") > use {
		t.Fatalf("the gap was not filled:\n%s", got)
	}
}

func TestScheduleKeepsMemoryAndCallOrder(t *testing.T) {
	f := fn(
		ins("str", w(1), mem(x(0), 0)),
		ins("ldr", w(9), mem(x(0), 4)),
		ins("add", w(10), w(9), imm(1)),
		ins("bl", sym("g")),
		ins("ldr", w(11), mem(x(0), 8)),
		ins("add", w(0), w(11), w(10)),
		ins("ret"),
	)
	f.Clobbers = []asm.Register{x(9), x(10), x(11), x(30)}
	lifted, err := Lift(cloneFunction(f))
	if err != nil {
		t.Fatal(err)
	}
	lifted.Schedule()
	got := text(lifted.Items())
	if strings.Index(got, "str w1") > strings.Index(got, "ldr w9") || strings.Index(got, "bl g") > strings.Index(got, "ldr w11") || strings.Index(got, "add w10") > strings.Index(got, "bl g") {
		t.Fatalf("order:\n%s", got)
	}
}

func TestScheduleKeepsTLBIAsMaintenanceBoundary(t *testing.T) {
	f := fn(
		ins("str", w(1), mem(x(0), 0)),
		ins("add", w(9), w(2), imm(1)),
		ins("tlbi", asm.Option{Name: "vmalls12e1is"}),
		ins("ldr", w(10), mem(x(0), 4)),
		ins("add", w(11), w(10), w(9)),
		ins("ret"),
	)
	lifted, err := Lift(cloneFunction(f))
	if err != nil {
		t.Fatal(err)
	}
	var maintenance *Instr
	for _, instruction := range lifted.Instrs {
		if instruction.Asm.Mnemonic == "tlbi" {
			maintenance = instruction
			break
		}
	}
	if maintenance == nil || !lifted.t.barrier(maintenance) {
		t.Fatal("TLBI did not lift as an immovable scheduling boundary")
	}
	lifted.Schedule()
	got := text(lifted.Items())
	store := strings.Index(got, "str w1")
	tlbi := strings.Index(got, "tlbi")
	load := strings.Index(got, "ldr w10")
	if store < 0 || tlbi < 0 || load < 0 || !(store < tlbi && tlbi < load) {
		t.Fatalf("store/TLBI/load order changed:\n%s", got)
	}
}

func TestScheduleRV64(t *testing.T) {
	f := rvfn(
		ins("ld", rx(5), mem(rx(10), 0)),
		ins("addi", rx(6), rx(5), imm(1)),
		ins("addi", rx(7), rx(11), imm(2)),
		ins("add", rx(10), rx(6), rx(7)),
		ins("ret"),
	)
	out, moved, err := Schedule(f)
	if err != nil {
		t.Fatal(err)
	}
	got := text(out.Items)
	if moved == 0 || strings.Index(got, "addi t2") > strings.Index(got, "addi t1") {
		t.Fatalf("moved %d:\n%s", moved, got)
	}
}

func TestScheduleKeepsBondedPairs(t *testing.T) {
	// The RV64 length normalization `slli s3, s2, 32; srli s3, s3, 32` is
	// one definition to the checker only as adjacent halves: the scheduler
	// moves the independent copies around the pair, never between.
	f := rvfn(
		ins("mv", rx(18), rx(11)),
		ins("slli", rx(19), rx(18), imm(32)),
		ins("mv", rx(9), rx(10)),
		ins("mv", rx(20), rx(12)),
		ins("srli", rx(19), rx(19), imm(32)),
		ins("ld", rx(5), mem(rx(9), 0)),
		ins("add", rx(10), rx(5), rx(19)),
		ins("ret"),
	)
	out, _, err := Schedule(f)
	if err != nil {
		t.Fatal(err)
	}
	got := text(out.Items)
	lines := strings.Split(got, "\n")
	adjacent := false
	for i := 0; i+1 < len(lines); i++ {
		if strings.HasPrefix(strings.TrimSpace(lines[i]), "slli s3") && strings.HasPrefix(strings.TrimSpace(lines[i+1]), "srli s3") {
			adjacent = true
		}
	}
	if !adjacent {
		t.Fatalf("the normalization halves came apart:\n%s", got)
	}
}

func rvv(n int) asm.Register {
	return asm.Register{Text: "v" + itoa(n), Class: asm.ClassRV64V, Num: n, Lane: -1}
}

func vopt(name string) asm.Option { return asm.Option{Name: name} }

// The RV64 lane's vector loop lifts: the vector registers are a class of
// their own that keeps its assignment, the configuration is a barrier no
// vector instruction crosses, and the recurrence analysis reads the
// index's stride off the loop.
func TestLiftRV64VectorLoop(t *testing.T) {
	f := rvfn(
		ins("li", rx(14), imm(0)),
		asm.Label{Name: "loop_1"},
		ins("bgeu", rx(14), rx(11), asm.Symbol{Name: "done_2"}),
		ins("slli", rx(5), rx(14), imm(2)),
		ins("add", rx(5), rx(10), rx(5)),
		ins("vsetivli", rx(0), imm(16), vopt("e8"), vopt("m1"), vopt("ta"), vopt("ma")),
		ins("vle8.v", rvv(1), mem(rx(5), 0)),
		ins("vsetivli", rx(0), imm(4), vopt("e32"), vopt("m1"), vopt("ta"), vopt("ma")),
		ins("vmv.v.x", rvv(2), rx(12)),
		ins("vadd.vv", rvv(1), rvv(1), rvv(2)),
		ins("vsetivli", rx(0), imm(16), vopt("e8"), vopt("m1"), vopt("ta"), vopt("ma")),
		ins("vse8.v", rvv(1), mem(rx(5), 0)),
		ins("addi", rx(14), rx(14), imm(4)),
		ins("j", asm.Symbol{Name: "loop_1"}),
		asm.Label{Name: "done_2"},
		ins("ret"),
	)
	lifted, err := Lift(cloneFunction(f))
	if err != nil {
		t.Fatalf("lift: %v", err)
	}
	shapes, err := lifted.Shapes()
	if err != nil {
		t.Fatal(err)
	}
	if len(shapes) != 1 || shapes[0].Stride != 4 {
		t.Fatalf("shapes %v: want one loop of stride 4", shapes)
	}
	out, _, err := Schedule(f)
	if err != nil {
		t.Fatal(err)
	}
	got := text(out.Items)
	// Every vector instruction stays between the configurations it was
	// emitted under.
	lines := strings.Split(got, "\n")
	config := ""
	for _, line := range lines {
		line = strings.TrimSpace(line)
		switch {
		case strings.HasPrefix(line, "vsetivli"):
			config = line
		case strings.HasPrefix(line, "vle8") || strings.HasPrefix(line, "vse8"):
			if !strings.Contains(config, "16") {
				t.Fatalf("%s under %q:\n%s", line, config, got)
			}
		case strings.HasPrefix(line, "vadd") || strings.HasPrefix(line, "vmv"):
			if !strings.Contains(config, "#4") { // the four-lane e32 configuration

				t.Fatalf("%s under %q:\n%s", line, config, got)
			}
		}
	}
	re, alloc, err := ReallocateWith(f, nil)
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(text(re.Items), "vadd.vv v1, v1, v2") {
		t.Fatalf("the vector registers must keep their assignment (%d renamed):\n%s", alloc.Renamed, text(re.Items))
	}
}

// The binary search's inner loop: the shift folds into the add's shifted
// operand and the increment into a csinc, two instructions fewer.
func TestFuseShiftAndIncrement(t *testing.T) {
	f := fn(
		ins("sub", w(9), w(23), w(7)),
		ins("lsr", w(9), w(9), imm(1)),
		ins("add", w(25), w(7), w(9)),
		ins("ldr", x(26), mem(x(0), 0)),
		ins("add", w(10), w(25), imm(1)),
		ins("cmp", x(26), x(6)),
		ins("csel", w(7), w(10), w(7), asm.Condition{Code: "lo"}),
		ins("csel", w(23), w(25), w(23), asm.Condition{Code: "hi"}),
		ins("add", w(0), w(7), w(23)),
		ins("ret"),
	)
	out, fused, err := Fuse(f)
	if err != nil {
		t.Fatal(err)
	}
	got := text(out.Items)
	shifted, incremented := false, false
	for _, item := range out.Items {
		ins, ok := item.(asm.Instruction)
		if !ok {
			continue
		}
		if ins.Mnemonic == "add" && len(ins.Operands) == 3 {
			if sh, isShifted := ins.Operands[2].(asm.Shifted); isShifted && sh.Kind == "lsr" && sh.Amount == 1 && sh.Reg.Num == 9 {
				shifted = true
			}
		}
		if ins.Mnemonic == "csinc" && len(ins.Operands) == 4 {
			if c, isCond := ins.Operands[3].(asm.Condition); isCond && c.Code == "hs" && ins.Operands[2].(asm.Register).Num == 25 && ins.Operands[1].(asm.Register).Num == 7 {
				incremented = true
			}
		}
	}
	if fused != 2 || !shifted || !incremented || strings.Contains(got, "lsr w9") || strings.Contains(got, "add w10") {
		t.Fatalf("fused %d (shifted %v, incremented %v):\n%s", fused, shifted, incremented, got)
	}
	// Not fused: the shift's source rewritten before the add, a
	// two-use intermediate.
	g := fn(
		ins("lsr", w(9), w(8), imm(2)),
		ins("add", w(8), w(8), imm(4)),
		ins("add", w(10), w(7), w(9)),
		ins("add", w(11), w(10), w(9)),
		ins("add", w(0), w(11), w(8)),
		ins("ret"),
	)
	out, fused, err = Fuse(g)
	if err != nil {
		t.Fatal(err)
	}
	if fused != 0 {
		t.Fatalf("fused %d:\n%s", fused, text(out.Items))
	}
}

// A rotated loop's two exit tests fold into one conditional compare:
// `b.hs done; cbz w5, loop` becomes `ccmp w5, #0, #0, lo; b.eq loop`.
func TestFuseExitTests(t *testing.T) {
	f := fn(
		ins("mov", w(5), w(0)),
		asm.Label{Name: "loop_4"},
		ins("add", w(3), w(3), imm(1)),
		ins("cmp", w(3), w(4)),
		asm.Instruction{Mnemonic: "b", Cond: "hs", Operands: []asm.Operand{asm.Symbol{Name: "done_5"}}},
		ins("cbz", w(5), asm.Symbol{Name: "loop_4"}),
		asm.Label{Name: "done_5"},
		ins("mov", w(0), w(3)),
		ins("ret"),
	)
	out, fused, err := FuseExits(f)
	if err != nil {
		t.Fatal(err)
	}
	var ccmp, back bool
	for _, item := range out.Items {
		ins, ok := item.(asm.Instruction)
		if !ok {
			continue
		}
		if ins.Mnemonic == "ccmp" && len(ins.Operands) == 4 {
			if c, isCond := ins.Operands[3].(asm.Condition); isCond && c.Code == "lo" && ins.Operands[2].(asm.Immediate).Value == 0 {
				ccmp = true
			}
		}
		if ins.Mnemonic == "b" && ins.Cond == "eq" {
			back = true
		}
		if ins.Mnemonic == "cbz" {
			t.Fatalf("the cbz survived:\n%s", text(out.Items))
		}
	}
	if fused != 1 || !ccmp || !back {
		t.Fatalf("fused %d (ccmp %v, back %v):\n%s", fused, ccmp, back, text(out.Items))
	}
}

// A store to a qualified slot no load reaches is dead: the lowering wrote
// a variable's frame home whose reads never came back to it. The store
// goes with the promotion; a slot that is read keeps its store (promoted
// or not), and a store the epilogue restores stays a save.
func TestPromoteRemovesDeadSlotStores(t *testing.T) {
	f := framed(
		ins("sub", sp(), sp(), imm(64)),
		ins("add", w(9), w(0), w(1)),
		ins("str", w(9), mem(sp(), 16)),
		ins("eor", w(9), w(9), w(1)),
		ins("str", w(9), mem(sp(), 16)),
		ins("mul", w(10), w(9), w(0)),
		ins("str", w(10), mem(sp(), 24)),
		ins("ldr", w(11), mem(sp(), 24)),
		ins("sub", w(0), w(9), w(11)),
		ins("add", sp(), sp(), imm(64)),
		ins("ret"),
	)
	out, alloc, err := Reallocate(f)
	if err != nil {
		t.Fatal(err)
	}
	got := text(out.Items)
	if alloc.DeadStores != 2 || strings.Contains(got, "[sp,#16]") {
		t.Fatalf("both stores to the unread slot must go (dead %d):\n%s", alloc.DeadStores, got)
	}
	if alloc.Promoted != 1 || strings.Contains(got, "[sp,#24]") {
		t.Fatalf("the read slot must be promoted (promoted %d):\n%s", alloc.Promoted, got)
	}
}

// The shift folds into the logical operations too: the CRC's fold
// `lsr w9, w24, #8; eor w24, w11, w9` becomes `eor w24, w11, w24, lsr #8`,
// one instruction a byte fewer; a flag-setting or conditional consumer
// keeps the shift.
func TestFuseShiftIntoLogical(t *testing.T) {
	f := fn(
		ins("ldr", w(11), mem(x(0), 0)),
		ins("lsr", w(9), w(24), imm(8)),
		ins("eor", w(24), w(11), w(9)),
		ins("mov", w(0), w(24)),
		ins("ret"),
	)
	out, fused, err := Fuse(f)
	if err != nil {
		t.Fatal(err)
	}
	folded := false
	for _, item := range out.Items {
		if ins, ok := item.(asm.Instruction); ok && ins.Mnemonic == "eor" && len(ins.Operands) == 3 {
			if sh, isShifted := ins.Operands[2].(asm.Shifted); isShifted && sh.Kind == "lsr" && sh.Amount == 8 {
				folded = true
			}
		}
		if ins, ok := item.(asm.Instruction); ok && ins.Mnemonic == "lsr" {
			t.Fatalf("the shift must fold into the eor:\n%s", text(out.Items))
		}
	}
	if fused != 1 || !folded {
		t.Fatalf("fused %d, folded %v:\n%s", fused, folded, text(out.Items))
	}
}
