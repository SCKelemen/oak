package compiler

import (
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
)

// A 64-bit constant inside a loop is a movz and up to three movk into one
// register (docs/spec/94-assembler.md §9 "Loop invariants"): the loop
// invariants hoist the whole chain or none of it — the first two alone
// left the later movk extending a register the loop had taken for
// something else, which the verifier caught as a disagreement on an
// inlined JSON scan. The C backend's realization is the oracle.
const nativeLICMConstantProgram = `
fold: (v: []u64): u64 {
  acc: u64 = u64(0)
  i: u32 = 0
  while i < len(v) {
    acc = acc ^ (v[i] & u64(0x8040201008040201)) ^ (u64(i) * u64(0x0101010101010101))
    i = i + u32(1)
  }
  acc
}

main: (): i32 {
  xs: [4]u64 = [4]u64{ u64(0xFFFFFFFFFFFFFFFF), u64(0x0F0F0F0F0F0F0F0F), u64(1), u64(0x8040201008040201) }
  assert(fold(view(&xs)) == (u64(0x8040201008040201) ^ u64(0x0000000008040201) ^ u64(1) ^ u64(0x8040201008040201) ^ u64(0x0101010101010101) ^ u64(0x0202020202020202) ^ u64(0x0303030303030303)))
  42
}
`

func TestE2ENativeLICMConstantChain(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("licm_const.oak", nativeLICMConstantProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_licm_const", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native constant chain: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	if !strings.Contains(joined, "asm unit fold:") {
		t.Fatalf("fold was not lowered by the native backend; diagnostics:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_licm_const_c", New().WithSource("licm_const.oak", nativeLICMConstantProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestNativeShapesLICMConstantChain(t *testing.T) {
	model, err := New().WithSource("licm_const.oak", nativeLICMConstantProgram).WithNativeBodies().WithNativeAsm().SemanticModel().Get()
	if err != nil {
		t.Fatal(err)
	}
	var fold *asm.Function
	for _, fn := range model.AsmFunctions {
		if fn.Name == "fold" {
			fold = fn
		}
	}
	if fold == nil {
		t.Fatal("fold was not lowered natively")
	}
	inLoop := false
	for _, item := range fold.Items {
		switch it := item.(type) {
		case asm.Label:
			if strings.HasPrefix(it.Name, "loop") {
				inLoop = true
			} else if strings.HasPrefix(it.Name, "done") {
				inLoop = false
			}
		case asm.Instruction:
			if inLoop && (it.Mnemonic == "movk" || it.Mnemonic == "movz") {
				t.Errorf("the loop still builds a constant: %s\n%s", fmt.Sprint(it), fmt.Sprint(fold.Items))
			}
		}
	}
}
