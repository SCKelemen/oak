package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/nativegen"
)

// Constant-trip unrolling (docs/spec/94-assembler.md §9 "Constant-trip
// loops"; nativegen/unroll_constant.go, the `unroll-constant` candidate).
// A loop from zero to a literal bound becomes its trips with the index a
// literal in each (Oak.ConstantUnroll.loop_eq_unrolled), so a frame array
// the loop indexed by its variable is indexed by constants and its words
// need no address arithmetic; the body is proven against the rewritten
// form, and a conditional on the index folds per trip.
const nativeUnrollConstantProgram = `
mix: (a: u32, b: u32, c: u32, d: u32, k: u32): u32 {
  v: [4]u32 = [4]u32{ a, b, c, d }
  round: u32 = 0
  while round < u32(3) {
    v[0] = v[0] + v[1] + k
    v[1] = v[1] ^ (v[0] >> u32(3))
    v[2] = v[2] + v[3]
    round < u32(2) ? { v[3] = v[3] ^ round }
    round = round + u32(1)
  }
  i: u32 = 0
  while i < u32(2) {
    v[i] = v[i] ^ v[i + u32(2)]
    i = i + u32(1)
  }
  v[0] + v[1] + v[2] + v[3] + round + i
}

main: () -> i32 {
  i32_bits_u32(mix(u32(1), u32(2), u32(3), u32(4), u32(5)) & u32(255))
}
`

func TestE2ENativeUnrollConstant(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("unrollc.oak", nativeUnrollConstantProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	model, err := comp.SemanticModel().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v\n%s", err, strings.Join(infos, "\n"))
	}
	var unit *asm.Function
	for _, fn := range model.AsmFunctions {
		if fn.Name == "mix" {
			unit = fn
		}
	}
	joined := strings.Join(infos, "\n")
	if unit == nil {
		t.Fatalf("mix was not lowered natively:\n%s", joined)
	}
	if !strings.Contains(joined, "asm unit mix: proven equal to its Oak body") {
		t.Errorf("mix must be proven; diagnostics:\n%s", joined)
	}
	// One site: the rewrite reports per body, both loops in it.
	if n := nativegen.UnrolledConstant(unit); n != 1 {
		t.Errorf("mix must unroll its constant-trip loops, got %d site(s):\n%s\n%s", n, nativegen.Describe(unit), joined)
	}
	// No loop is left: no label a branch returns to, and no indexed frame
	// access — every word of v is reached at a constant offset.
	for _, item := range unit.Items {
		switch x := item.(type) {
		case asm.Label:
			if strings.HasPrefix(x.Name, "loop_") {
				t.Errorf("mix must keep no loop, found %s:\n%s", x.Name, nativegen.Describe(unit))
			}
		case asm.Instruction:
			for _, op := range x.Operands {
				if mem, isMem := op.(asm.Memory); isMem && mem.Index != nil && mem.Base.Class == asm.ClassSP {
					t.Errorf("mix must not index its frame: %v", x)
				}
			}
		}
	}
	// Two rounds of the three: 1+2+5=8, 2^(8>>3)=3, 3+4=7, 4^0=4; 8+3+5=16,
	// 3^2=1, 7+4=11, 4^1=5; 16+1+5=22, 1^2=3, 11+5=16, 5 (round 2 skips);
	// then v[0]=22^16=6, v[1]=3^5=6: 6+6+16+5+3+2 = 38.
	_, code, abnormal := buildAndRunFrom(t, "native_unroll_constant", comp)
	if abnormal || code != 38 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 38\n%s", code, abnormal, joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_unroll_constant_c", New().WithSource("unrollc.oak", nativeUnrollConstantProgram)); abnormal || code != 38 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 38", code, abnormal)
	}
}
