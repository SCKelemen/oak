package machine

import (
	"fmt"
	"reflect"
	"testing"

	"github.com/SCKelemen/oak/asm"
)

// Rebuilding after every rewrite is the reference for the cheaper DCE path.
// Compare both counts and complete assembly, including effects and restores.
func checkSimplifyRebuild(t *testing.T, body *asm.Function) (int, int) {
	t.Helper()
	f, err := Lift(cloneFunction(body))
	if err != nil {
		t.Fatal(err)
	}
	ref, err := Lift(cloneFunction(body))
	if err != nil {
		t.Fatal(err)
	}
	p, e, err := f.Simplify()
	if err != nil {
		t.Fatal(err)
	}
	wantP, wantE := 0, 0
	for round := 0; round < simplifyRounds; round++ {
		webs, err := ref.Webs()
		if err != nil {
			t.Fatal(err)
		}
		ref.Liveness(webs)
		copied := ref.propagateCopy(webs) != nil
		if copied {
			wantP++
			webs, err = ref.Webs()
			if err != nil {
				t.Fatal(err)
			}
		}
		removed := ref.eliminateDead(webs, nil)
		wantE += removed
		if !copied && removed == 0 {
			break
		}
	}
	if p != wantP || e != wantE || !reflect.DeepEqual(f.Items(), ref.Items()) {
		t.Fatalf("reused analysis: propagated=%d eliminated=%d\n%s\nfresh analysis: propagated=%d eliminated=%d\n%s",
			p, e, text(f.Items()), wantP, wantE, text(ref.Items()))
	}
	return p, e
}

func TestSimplifyReusesWebsForDCE(t *testing.T) {
	for _, test := range []struct {
		name string
		body *asm.Function
		want int // propagated copies
	}{
		{"independent copies", websBenchmarkBody(1, 8, false), 8},
		{"copy chain", fn(
			ins("add", w(9), w(0), w(1)), ins("mov", w(10), w(9)), ins("mov", w(11), w(10)),
			ins("eor", w(0), w(11), w(10)), ins("eor", w(0), w(0), w(9)), ins("ret"),
		), 2},
		{"both successors read copy", fn(
			ins("add", w(9), w(0), w(1)), ins("mov", w(10), w(9)), ins("cbz", w(2), sym("right")),
			ins("eor", w(0), w(10), w(9)), ins("b", sym("done")),
			label("right"), ins("add", w(0), w(10), w(9)), label("done"), ins("ret"),
		), 1},
		{"source definitions meet", fn(
			ins("cbz", w(0), sym("right")), ins("add", w(9), w(1), imm(1)), ins("b", sym("join")),
			label("right"), ins("add", w(9), w(2), imm(2)), label("join"),
			ins("mov", w(10), w(9)), ins("eor", w(0), w(10), w(9)), ins("ret"),
		), 1},
		{"self copy after source definitions meet", selfCopyJoinBody(), 0},
		{"loop source", fn(
			ins("add", w(9), w(0), imm(1)), label("loop"), ins("mov", w(10), w(9)),
			ins("eor", w(0), w(10), w(9)), ins("add", w(9), w(9), imm(1)),
			ins("cmp", w(9), w(1)), bcond("lo", "loop"), ins("ret"),
		), 1},
		{"source overwritten", fn(
			ins("add", w(9), w(0), w(1)), ins("mov", w(10), w(9)),
			ins("add", w(9), w(9), w(1)), ins("add", w(0), w(9), w(10)), ins("ret"),
		), 0},
		{"call clobbers source", fn(
			ins("add", w(9), w(0), w(1)), ins("mov", w(20), w(9)), ins("bl", sym("g")),
			ins("add", w(0), w(20), w(9)), ins("ret"),
		), 0},
		{"implicit return use", fn(ins("mov", w(0), w(1)), ins("ret")), 0},
		{"narrow copy read wide", fn(
			ins("lsl", x(9), x(0), imm(40)), ins("mov", w(10), w(9)),
			ins("add", x(0), x(10), x(9)), ins("ret"),
		), 0},
		{"tied vector destination", fn(
			ins("mov", v(16, "16b"), v(17, "16b")),
			ins("mla", v(16, "4s"), v(17, "4s"), v(18, "4s")),
			ins("str", q(16), mem(x(0), 0)), ins("ret"),
		), 0},
		{"callee saved destination stays", fn(
			ins("add", w(9), w(0), w(1)), ins("mov", w(20), w(9)),
			ins("eor", w(0), w(20), w(9)), ins("ret"),
		), 1},
		{"dead uses cascade", fn(
			ins("add", w(9), w(0), w(1)), ins("mov", w(10), w(9)), ins("eor", w(11), w(10), w(9)),
			ins("ldr", w(12), mem(sp(), 16)), ins("cmp", w(0), w(1)), ins("ret"),
		), 1},
		{"rv64 copy", rvfn(
			ins("addi", rx(5), rx(10), imm(1)), ins("mv", rx(6), rx(5)),
			ins("xor", rx(10), rx(6), rx(5)), ins("ret"),
		), 1},
	} {
		t.Run(test.name, func(t *testing.T) {
			p, _ := checkSimplifyRebuild(t, test.body)
			if p != test.want {
				t.Fatalf("propagated=%d, want %d", p, test.want)
			}
		})
	}
}

func selfCopyJoinBody() *asm.Function {
	return fn(
		ins("cbz", w(0), sym("right")), ins("add", w(9), w(1), imm(1)), ins("b", sym("join")),
		label("right"), ins("add", w(9), w(2), imm(2)), label("join"),
		ins("mov", w(9), w(9)), ins("eor", w(0), w(9), w(1)), ins("ret"),
	)
}

func TestSimplifyContinuesPastSelfCopy(t *testing.T) {
	for _, test := range []struct {
		name string
		body *asm.Function
		want *asm.Function
	}{
		{"arm64", fn(
			ins("cbz", w(0), sym("right")), ins("add", w(9), w(1), imm(1)), ins("b", sym("join")),
			label("right"), ins("add", w(9), w(2), imm(2)), label("join"),
			ins("mov", w(9), w(9)), ins("mov", w(10), w(9)), ins("add", w(0), w(10), w(9)), ins("ret"),
		), fn(
			ins("cbz", w(0), sym("right")), ins("add", w(9), w(1), imm(1)), ins("b", sym("join")),
			label("right"), ins("add", w(9), w(2), imm(2)), label("join"),
			ins("mov", w(9), w(9)), ins("add", w(0), w(9), w(9)), ins("ret"),
		)},
		{"rv64", rvfn(
			ins("beqz", rx(10), sym("right")), ins("addi", rx(5), rx(11), imm(1)), ins("j", sym("join")),
			label("right"), ins("addi", rx(5), rx(12), imm(2)), label("join"),
			ins("mv", rx(5), rx(5)), ins("mv", rx(6), rx(5)), ins("add", rx(10), rx(6), rx(5)), ins("ret"),
		), rvfn(
			ins("beqz", rx(10), sym("right")), ins("addi", rx(5), rx(11), imm(1)), ins("j", sym("join")),
			label("right"), ins("addi", rx(5), rx(12), imm(2)), label("join"),
			ins("mv", rx(5), rx(5)), ins("add", rx(10), rx(5), rx(5)), ins("ret"),
		)},
	} {
		t.Run(test.name, func(t *testing.T) {
			f, err := Lift(test.body)
			if err != nil {
				t.Fatal(err)
			}
			for round := 0; round < 2; round++ {
				p, e, err := f.Simplify()
				wantCount := 1 - round
				if err != nil || p != wantCount || e != wantCount || !reflect.DeepEqual(f.Items(), test.want.Items) {
					t.Fatalf("round %d: propagated=%d eliminated=%d error=%v\n%s", round, p, e, err, text(f.Items()))
				}
			}
		})
	}
}

func TestSimplifyPreservesNarrowingSelfCopy(t *testing.T) {
	// Writing W9 clears X9's upper half. Skipping a propagation that would
	// respell its users identically must not delete that write.
	body := fn(ins("lsl", x(9), x(0), imm(40)), ins("mov", w(9), w(9)),
		ins("add", x(0), x(9), x(1)), ins("ret"))
	f, err := Lift(cloneFunction(body))
	if err != nil {
		t.Fatal(err)
	}
	if p, e, err := f.Simplify(); err != nil || p != 0 || e != 0 || !reflect.DeepEqual(f.Items(), body.Items) {
		t.Fatalf("narrow self-copy changed: propagated=%d eliminated=%d error=%v\n%s", p, e, err, text(f.Items()))
	}
	out, _, err := Reallocate(body)
	if err != nil {
		t.Fatal(err)
	}
	found := false
	for _, item := range out.Items {
		if move, ok := item.(asm.Instruction); ok && move.Mnemonic == "mov" && len(move.Operands) == 2 {
			dst, dstOK := move.Operands[0].(asm.Register)
			src, srcOK := move.Operands[1].(asm.Register)
			found = found || (dstOK && srcOK && dst.Class == asm.ClassW && src.Class == asm.ClassW)
		}
	}
	if !found {
		t.Fatalf("allocation lost the narrowing copy:\n%s", text(out.Items))
	}
}

func TestSimplifyRebuildRegisterReuse(t *testing.T) {
	// Vary source/destination overlap across copies, source overwrites, dead
	// consumers, memory effects and CFG joins. The same physical register can
	// belong to several distinct webs, some read and some dead.
	for seed := 0; seed < 128; seed++ {
		t.Run(fmt.Sprint(seed), func(t *testing.T) {
			var items []asm.Item
			for i := 0; i < 6; i++ {
				src, dst := 9+(seed+i)%3, 9+(seed/3+i+1)%3
				items = append(items, ins("add", w(src), w(0), imm(int64(i+1))), ins("mov", w(dst), w(src)))
				if seed&(1<<i) != 0 {
					items = append(items, ins("add", w(src), w(src), imm(1)))
				}
				result := 0
				if seed&64 != 0 {
					result = 12 // unread consumer; DCE exposes another round
				}
				items = append(items, ins("eor", w(result), w(dst), w(src)))
				if i == 2 {
					items = append(items, ins("cbz", w(1), sym("join")), ins("str", w(dst), mem(x(2), 0)), label("join"))
				}
			}
			checkSimplifyRebuild(t, fn(append(items, ins("ret"))...))
		})
	}
}
