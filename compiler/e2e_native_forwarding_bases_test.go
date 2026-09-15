package compiler

import (
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
)

// Slot forwarding through any base register (docs/spec/94-assembler.md §9
// "Slot forwarding"): a record built in the x8 result area is addressed
// through the result register, and a field incremented there and tested
// next — `next.n = next.n + u32(1)` then `next.n == u32(3)` — is read back
// from the register that stored it, not reloaded from `[xR, #off]`. The C
// backend's realization is the oracle.
const nativeForwardingBasesProgram = `
Big: type = struct {
  a: u64
  b: u64
  c: u64
  n: u32
  pad: u32
}

tick: (s: Big): Big {
  next: Big = s
  next.n = next.n + u32(1)
  next.n == u32(3) ? {
    next.a = next.a + u64(100)
    next.n = u32(0)
  }
  next
}

main: (): i32 {
  x: Big
  x.a = u64(1)
  x.n = u32(0)
  y: Big = tick(tick(tick(x)))
  assert(y.a == u64(101) && y.n == u32(0))
  z: Big = tick(y)
  assert(z.a == u64(101) && z.n == u32(1))
  42
}
`

func TestE2ENativeForwardingBases(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("fwdbases.oak", nativeForwardingBasesProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_fwd_bases", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native forwarding through bases: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	if !strings.Contains(joined, "asm unit tick: proven") {
		t.Errorf("tick must be proven equal to its Oak body; diagnostics:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_fwd_bases_c", New().WithSource("fwdbases.oak", nativeForwardingBasesProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestNativeShapesForwardingBases(t *testing.T) {
	model, err := New().WithSource("fwdbases.oak", nativeForwardingBasesProgram).WithNativeBodies().WithNativeAsm().SemanticModel().Get()
	if err != nil {
		t.Fatal(err)
	}
	var tick *asm.Function
	for _, fn := range model.AsmFunctions {
		if fn.Name == "tick" {
			tick = fn
		}
	}
	if tick == nil {
		t.Fatal("tick was not lowered natively")
	}
	items := tick.Items
	forwarded := false
	for i := 1; i < len(items); i++ {
		st, okS := items[i-1].(asm.Instruction)
		next, okN := items[i].(asm.Instruction)
		if !okS || !okN || st.Mnemonic != "str" {
			continue
		}
		mem, isMem := st.Operands[1].(asm.Memory)
		if !isMem || mem.Base.Class == asm.ClassSP {
			continue
		}
		if next.Mnemonic == "ldr" {
			if to, ok := next.Operands[1].(asm.Memory); ok && to.Base.Num == mem.Base.Num && to.Offset == mem.Offset {
				t.Errorf("the field is reloaded through the result register right after its store: %s; %s\n%s", fmt.Sprint(st), fmt.Sprint(next), fmt.Sprint(items))
			}
		}
		stored, _ := st.Operands[0].(asm.Register)
		if next.Mnemonic == "cmp" {
			if compared, ok := next.Operands[0].(asm.Register); ok && compared.Text == stored.Text {
				forwarded = true
			}
		}
		if next.Mnemonic == "mov" && len(next.Operands) == 2 {
			if src, ok := next.Operands[1].(asm.Register); ok && src.Text == stored.Text {
				forwarded = true
			}
		}
	}
	if !forwarded {
		t.Errorf("the `== 3` test must read next.n from the register the increment was stored from:\n%s", fmt.Sprint(items))
	}
}
