package compiler

import (
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
)

// Frame-slot forwarding and compare-and-branch on a computed operand
// (docs/spec/94-assembler.md §9 "Slot forwarding"): the byte loop of a
// SHA-256-style absorber keeps a record field's increment in the register
// it computed it in (`ldr; add; str` with no reload), and tests `filled ==
// 64` as `cmp; b.ne` rather than `cmp; cset; cbz`. The C backend's
// realization of the same program is the oracle.
const nativeForwardingProgram = `
Acc: type = struct {
  filled: u32
  blocks: u32
  block: [64]u8
}

feed: (src: []u8): u32 {
  a: Acc
  a.filled = u32(0)
  a.blocks = u32(0)
  i: u32 = 0
  while i < len(src) {
    a.filled < u32(64) ? {
      a.block[a.filled] = src[i]
    }
    a.filled = a.filled + u32(1)
    a.filled == u32(64) ? {
      a.blocks = a.blocks + u32(1)
      a.filled = u32(0)
    }
    i = i + u32(1)
  }
  a.blocks * u32(64) + a.filled
}

main: (): i32 {
  buf: [200]u8
  assert(feed(view(&buf)) == u32(200))
  assert(feed(view(&buf)[u32(0):u32(64)]) == u32(64))
  assert(feed(view(&buf)[u32(0):u32(7)]) == u32(7))
  42
}
`

func TestE2ENativeForwarding(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("forward.oak", nativeForwardingProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_forwarding", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native forwarding: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	if !strings.Contains(joined, "asm unit feed:") {
		t.Fatalf("feed was not lowered by the native backend; diagnostics:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_forwarding_c", New().WithSource("forward.oak", nativeForwardingProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestNativeShapesForwarding(t *testing.T) {
	model, err := New().WithSource("forward.oak", nativeForwardingProgram).WithNativeBodies().WithNativeAsm().SemanticModel().Get()
	if err != nil {
		t.Fatal(err)
	}
	var feed *asm.Function
	for _, fn := range model.AsmFunctions {
		if fn.Name == "feed" {
			feed = fn
		}
	}
	if feed == nil {
		t.Fatal("feed was not lowered natively")
	}
	// The whole loop: from the loop label to the label after its back edge.
	var body []asm.Instruction
	inLoop := false
	for _, item := range feed.Items {
		switch it := item.(type) {
		case asm.Label:
			if strings.HasPrefix(it.Name, "loop") {
				inLoop = true
			} else if strings.HasPrefix(it.Name, "done") && inLoop {
				inLoop = false
			}
		case asm.Instruction:
			if inLoop {
				body = append(body, it)
			}
		}
	}
	forwarded := false
	for i, ins := range body {
		if ins.Mnemonic == "cset" {
			t.Errorf("the loop materializes a Bool for a compare: %s", fmt.Sprint(ins))
		}
		if ins.Mnemonic == "ldr" && i > 0 && body[i-1].Mnemonic == "str" {
			mem, isMem := ins.Operands[1].(asm.Memory)
			prev, prevMem := body[i-1].Operands[1].(asm.Memory)
			if isMem && prevMem && mem.Base.Class == asm.ClassSP && prev.Base.Class == asm.ClassSP && prev.Offset == mem.Offset {
				t.Errorf("a slot is reloaded right after its store: %s; %s", fmt.Sprint(body[i-1]), fmt.Sprint(ins))
			}
		}
		// The `== 64` test reads the register the increment was stored from.
		if ins.Mnemonic == "cmp" && i > 0 && body[i-1].Mnemonic == "str" {
			stored, _ := body[i-1].Operands[0].(asm.Register)
			compared, _ := ins.Operands[0].(asm.Register)
			if stored.Text == compared.Text {
				forwarded = true
			}
		}
	}
	if !forwarded {
		t.Errorf("the `filled == 64` test must compare the register the increment was stored from:\n%s", fmt.Sprint(body))
	}
}
