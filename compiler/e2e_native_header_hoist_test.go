package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/nativegen"
)

// A strided loop's header computes `len(v) - N` every iteration
// (`sub w9, w20, #4` between the two exit tests). The loop-invariant pass
// (docs/spec/94-assembler.md §9 "Loop invariants") hoists it before the
// loop into a fresh register the exit test reads; the checker's slack fact
// reaches the header through the label state, the loads stay guard-free,
// and the body is proven as before. One instruction less per iteration
// of every strided loop.
const nativeHeaderHoistProgram = `
pairs: (v: []u64): u64 {
  acc: u64 = 0
  i: u32 = 0
  while len(v) >= u32(4) && i <= len(v) - u32(4) {
    acc = acc + v[i] + v[i + u32(1)] + v[i + u32(2)] + v[i + u32(3)]
    i = i + u32(4)
  }
  acc
}

main: (): i32 {
  xs: [10]u64 = [10]u64{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 }
  // 1 + … + 8 = 36; the tail of two stays.
  i32_bits_u32(u32_trunc_u64(pairs(view(&xs))))
}
`

func TestE2ENativeHeaderHoist(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("hoist.oak", nativeHeaderHoistProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	model, err := comp.SemanticModel().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v\n%s", err, strings.Join(infos, "\n"))
	}
	var fn *asm.Function
	for _, f := range model.AsmFunctions {
		if f.Name == "pairs" {
			fn = f
		}
	}
	joined := strings.Join(infos, "\n")
	if fn == nil {
		t.Fatalf("pairs was not lowered natively:\n%s", joined)
	}
	if !strings.Contains(joined, "asm unit pairs: proven equal to its Oak body") {
		t.Errorf("pairs must stay proven with its header hoisted; diagnostics:\n%s", joined)
	}
	inLoop, subsInLoop, subsBefore := false, 0, 0
	for _, item := range fn.Items {
		switch it := item.(type) {
		case asm.Label:
			if strings.HasPrefix(it.Name, "loop") {
				inLoop = true
			} else if inLoop {
				inLoop = false
			}
		case asm.Instruction:
			if it.Mnemonic == "sub" {
				if _, isImm := it.Operands[len(it.Operands)-1].(asm.Immediate); isImm {
					if inLoop {
						subsInLoop++
					} else {
						subsBefore++
					}
				}
			}
		}
	}
	if subsInLoop != 0 || subsBefore == 0 {
		t.Errorf("the header's `len - 4` must be computed before the loop (in loop: %d, before: %d):\n%s", subsInLoop, subsBefore, nativegen.Describe(fn))
	}
	_, code, abnormal := buildAndRunFrom(t, "native_header_hoist", comp)
	if abnormal || code != 36 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 36\n%s", code, abnormal, joined)
	}
}
