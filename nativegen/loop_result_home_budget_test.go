package nativegen

import (
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
)

const loopResultBudgetCandidates = 10

func loopResultBudgetAssignments(out *strings.Builder, name string) {
	for i := 0; i < loopResultBudgetCandidates; i++ {
		fmt.Fprintf(out, "    %s[%d] = %s[%d] + %s[%d]\n", name, i, name, i, name, i)
	}
}

func loopResultBudgetSource(loops int, withFrame bool) string {
	var out strings.Builder
	out.WriteString("f: (n: u32): [16]u32 {\n  v: [16]u32\n")
	if withFrame {
		out.WriteString("  z: [16]u32\n")
	}
	for loop := 0; loop < loops; loop++ {
		fmt.Fprintf(&out, "  i%d: u32 = 0\n  while i%d < n {\n", loop, loop)
		loopResultBudgetAssignments(&out, "v")
		if withFrame {
			loopResultBudgetAssignments(&out, "z")
		}
		fmt.Fprintf(&out, "    i%d = i%d + u32(1)\n  }\n", loop, loop)
	}
	out.WriteString("  v\n}")
	return out.String()
}

func loopResultBudgetGenerator(t *testing.T, loops int, withFrame bool) (*generator, *arrayLocal, []*ast.WhileStatement) {
	t.Helper()
	if loopResultHomeBudget < 1 || loopResultHomeBudget > 8 || loopResultHomeBudget >= loopResultBudgetCandidates {
		t.Fatalf("test requires a result-home budget in [1,8] below %d, got %d", loopResultBudgetCandidates, loopResultHomeBudget)
	}
	g, result, _ := resultHomeGenerator(t, "u32")
	fn, _ := parseLoopHomes(t, loopResultBudgetSource(loops, withFrame))
	g.fn = fn
	// More than the overall eight-home cap, all in the true callee-saved range.
	g.freeCallee = []int{19, 20, 21, 22, 23, 24, 25, 26, 27, 28}
	if withFrame {
		g.loopArrayHomesEnabled = true
		g.arrays["z"] = &arrayLocal{elem: scalars["u32"], length: 16, offset: 128}
	}
	var found []*ast.WhileStatement
	for _, statement := range fn.Body.(*ast.BlockExpression).Block.Statements {
		if loop, ok := statement.(*ast.WhileStatement); ok {
			found = append(found, loop)
		}
	}
	if len(found) != loops {
		t.Fatalf("parsed %d loops, want %d", len(found), loops)
	}
	return g, result, found
}

func TestLoopResultHomeBudgetDeterministicFallback(t *testing.T) {
	g, result, loops := loopResultBudgetGenerator(t, 1, false)
	finish := g.beginLoopArrayHomes(loops[0])
	if finish == nil {
		t.Fatal("profitable result loop acquired no homes")
	}
	budget := loopResultHomeBudget
	set := g.activeArrayHomes["v"]
	if set == nil || len(set.homes) != budget || g.resultHomesCount != budget || g.arrayHomesCount != 0 || len(g.items) != budget {
		t.Fatalf("selected=%v result count=%d frame count=%d items=%d, want %d result homes", set, g.resultHomesCount, g.arrayHomesCount, len(g.items), budget)
	}
	for i := 0; i < budget; i++ {
		home, selected := set.homes[int64(i)]
		if !selected || !home.written {
			t.Fatalf("deterministic result index %d not selected for write: %v", i, set.homes)
		}
		instruction, ok := g.items[i].(asm.Instruction)
		want := g.memOf(result.loc().plus(int64(i) * result.elemSize()))
		if !ok || instruction.Mnemonic != "ldr" || instruction.Operands[1] != want {
			t.Fatalf("preload %d = %v, want ldr from %v", i, g.items[i], want)
		}
	}

	// The first candidate past the result budget must keep the ordinary
	// result-memory path rather than acquiring a hidden scalar identity.
	unselected := int64(budget)
	index := &ast.IndexExpression{
		Left:  &ast.Identifier{Value: "v"},
		Index: &ast.IntegerLiteral{Value: unselected},
	}
	if _, found := set.homes[unselected]; found {
		t.Fatalf("result index %d exceeded budget %d", unselected, budget)
	}
	if _, _, found := g.scalarElement(index); found {
		t.Fatalf("unselected result index %d acquired a scalar home", unselected)
	}
	address, indexReg, baseReg, err := g.arrayAddress(result, index.Index, &index.Token)
	if err != nil {
		t.Fatal(err)
	}
	wantAddress := g.memOf(result.loc().plus(unselected * result.elemSize()))
	if address != wantAddress || indexReg != -1 || baseReg != -1 {
		t.Fatalf("unselected result index lowered to %v (%d,%d), want direct memory %v", address, indexReg, baseReg, wantAddress)
	}

	beforeFlush := len(g.items)
	finish()
	if len(g.items) != beforeFlush+budget {
		t.Fatalf("flush emitted %d instructions, want %d", len(g.items)-beforeFlush, budget)
	}
	for i := 0; i < budget; i++ {
		instruction, ok := g.items[beforeFlush+i].(asm.Instruction)
		want := g.memOf(result.loc().plus(int64(i) * result.elemSize()))
		if !ok || instruction.Mnemonic != "str" || instruction.Operands[1] != want {
			t.Fatalf("flush %d = %v, want str to %v", i, g.items[beforeFlush+i], want)
		}
	}
}

func TestLoopResultHomeBudgetResetsPerLoop(t *testing.T) {
	g, _, loops := loopResultBudgetGenerator(t, 2, false)
	for i, loop := range loops {
		finish := g.beginLoopArrayHomes(loop)
		if finish == nil {
			t.Fatalf("loop %d acquired no result homes", i)
		}
		set := g.activeArrayHomes["v"]
		if set == nil || len(set.homes) != loopResultHomeBudget {
			t.Fatalf("loop %d selected %v, want %d independent homes", i, set, loopResultHomeBudget)
		}
		if want := (i + 1) * loopResultHomeBudget; g.resultHomesCount != want {
			t.Fatalf("loop %d cumulative metric=%d, want %d", i, g.resultHomesCount, want)
		}
		finish()
	}
}

func TestLoopResultHomeBudgetIndependentOfFrameHomes(t *testing.T) {
	g, _, loops := loopResultBudgetGenerator(t, 1, true)
	finish := g.beginLoopArrayHomes(loops[0])
	if finish == nil {
		t.Fatal("mixed result/frame loop acquired no homes")
	}
	const overallBudget = 8
	wantFrame := overallBudget - loopResultHomeBudget
	if g.resultHomesCount != loopResultHomeBudget || g.arrayHomesCount != wantFrame || g.resultHomesCount+g.arrayHomesCount != overallBudget {
		t.Fatalf("result homes=%d frame homes=%d, want %d+%d under overall cap %d", g.resultHomesCount, g.arrayHomesCount, loopResultHomeBudget, wantFrame, overallBudget)
	}
	resultSet := g.activeArrayHomes["v"]
	if resultSet == nil || len(resultSet.homes) != loopResultHomeBudget {
		t.Fatalf("result selections=%v, want %d", resultSet, loopResultHomeBudget)
	}
	frameSet := g.activeArrayHomes["z"]
	if wantFrame == 0 {
		if frameSet != nil {
			t.Fatalf("frame selections=%v past overall cap", frameSet.homes)
		}
	} else if frameSet == nil || len(frameSet.homes) != wantFrame {
		t.Fatalf("frame selections=%v, want %d independent homes", frameSet, wantFrame)
	}
	finish()
}
