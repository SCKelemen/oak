package compiler

import (
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
)

// Pair copies (docs/spec/94-assembler.md §9): an aggregate copy of sixteen
// bytes or more between 8-aligned locations moves register pairs — a
// 40-byte record copies as two `ldp`/`stp` pairs and one word. The C
// backend's realization of the same program is the oracle.
const nativePairCopiesProgram = `
Wide: type = struct {
  a: u64
  b: u64
  c: u64
  d: u64
  e: u64
}

// A parameter copied into a local the body writes (the copy is a copy),
// returned through x8 (the copy out).
shift: (w: Wide, by: u64): Wide {
  out: Wide = w
  out.a = out.a + by
  out.e = out.e + by
  out.c = out.d
  out
}

sum: (w: Wide): u64 = w.a + w.b + w.c + w.d + w.e

main: (): i32 {
  w: Wide = Wide { a: u64(1), b: u64(2), c: u64(3), d: u64(4), e: u64(5) }
  s: Wide = shift(w, u64(10))
  assert(sum(s) == u64(11 + 2 + 4 + 4 + 15))
  assert(sum(w) == u64(15))
  42
}
`

func TestE2ENativePairCopies(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("pairs.oak", nativePairCopiesProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_pair_copies", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native pair copies: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"shift", "sum", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	if !strings.Contains(joined, "asm unit shift: proven") {
		t.Errorf("shift must stay proven with its copies as pairs; diagnostics:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_pair_copies_c", New().WithSource("pairs.oak", nativePairCopiesProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestNativeShapesPairCopies(t *testing.T) {
	model, err := New().WithSource("pairs.oak", nativePairCopiesProgram).WithNativeBodies().WithNativeAsm().SemanticModel().Get()
	if err != nil {
		t.Fatal(err)
	}
	var shift *asm.Function
	for _, fn := range model.AsmFunctions {
		if fn.Name == "shift" {
			shift = fn
		}
	}
	if shift == nil {
		t.Fatal("shift was not lowered natively")
	}
	ldp, stp, singles := 0, 0, 0
	for _, item := range shift.Items {
		ins, isIns := item.(asm.Instruction)
		if !isIns {
			continue
		}
		switch ins.Mnemonic {
		case "ldp":
			ldp++
		case "stp":
			stp++
		case "ldr", "str":
			if r, isReg := ins.Operands[0].(asm.Register); isReg && r.Class == asm.ClassX {
				singles++
			}
		}
	}
	// The result is built in the x8 area (§9 "Copies at the boundary"), so
	// the 40-byte record is copied once, from the parameter's address into
	// that area: two pairs and one word. The copy out is gone. The single
	// words are the copy's tail, the three field updates (a load and a
	// store each), and the saved register's store and reload.
	if ldp != 2 || stp != 2 {
		t.Errorf("shift must copy its record by pairs, once; got %d ldp and %d stp:\n%s", ldp, stp, fmt.Sprint(shift.Items))
	}
	if singles > 10 {
		t.Errorf("shift moves too many single words (%d) for a 40-byte record copied once:\n%s", singles, fmt.Sprint(shift.Items))
	}
}
