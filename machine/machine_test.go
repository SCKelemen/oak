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
	if alloc.Coalesced != 2 || strings.Count(got, "mov") != 1 || !strings.Contains(got, "add w0, w10, w1") {
		t.Fatalf("coalesced %d:\n%s", alloc.Coalesced, got)
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
	if alloc.Coalesced != 1 || strings.Contains(text(out.Items), "mov w") {
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
	if alloc.Coalesced != 2 || strings.Contains(got, "orr") {
		t.Fatalf("coalesced %d:\n%s", alloc.Coalesced, got)
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
