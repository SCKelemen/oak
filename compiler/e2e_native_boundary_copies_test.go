package compiler

import (
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
)

// Copies at the boundary (docs/spec/94-assembler.md §9): a record local a
// function returns through x8 is built in the caller's result area (no
// copy at the return), a by-reference argument the callee only reads is
// passed as the caller's own storage (no copy before the call), and a
// local initialized from a call receives the callee's result directly.
// The C backend's realization of the same program is the oracle.
const nativeBoundaryCopiesProgram = `
Big: type = struct {
  a: u64
  b: u64
  c: u64
  d: u32
  tag: [12]u8
}

// A by-reference parameter read in place; the result built in the area.
// The loop keeps step a callee of its own: a small aggregate helper
// without one expands at its calls (§9 "Aggregate helpers"), and then
// there is no boundary to observe.
step: (s: Big, by: u64): Big {
  next: Big = s
  next.a = next.a + by
  next.b = next.b + next.a
  next.d = next.d + u32(1)
  i: u32 = 0
  while i <= next.d {
    next.tag[i] = u8(7)
    i = i + u32(1)
  }
  next
}

// An untouched parameter: its caller passes its own storage.
total: (s: Big): u64 = s.a + s.b + s.c + u64(s.d) + u64(s.tag[1])

// A returned local initialized from a call: the callee writes this
// function's own result area.
relay: (s: Big): Big {
  y: Big = step(s, u64(5))
  y
}

// The result of a call lands in the fresh local directly.
twice: (s: Big): u64 {
  y: Big = step(s, u64(10))
  z: Big = step(y, u64(100))
  total(y) + total(z)
}

main: (): i32 {
  x: Big
  x.a = u64(1)
  x.b = u64(2)
  x.c = u64(3)
  x.d = u32(0)
  assert(total(x) == u64(6))
  assert(twice(x) == u64(11 + 13 + 3 + 1 + 7) + u64(111 + 124 + 3 + 2 + 7))
  r: Big = relay(x)
  assert(r.a == u64(6) && r.b == u64(8) && r.d == u32(1) && r.tag[1] == u8(7))
  assert(total(relay(relay(x))) == u64(11 + 19 + 3 + 2 + 7))
  42
}
`

func TestE2ENativeBoundaryCopies(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("copies.oak", nativeBoundaryCopiesProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_boundary_copies", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native boundary copies: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"step", "total", "relay", "twice", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_boundary_copies_c", New().WithSource("copies.oak", nativeBoundaryCopiesProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestNativeShapesBoundaryCopies(t *testing.T) {
	model, err := New().WithSource("copies.oak", nativeBoundaryCopiesProgram).WithNativeBodies().WithNativeAsm().SemanticModel().Get()
	if err != nil {
		t.Fatal(err)
	}
	units := map[string]*asm.Function{}
	for _, fn := range model.AsmFunctions {
		units[fn.Name] = fn
	}
	// spMemory counts the sp-relative accesses of the body proper: between
	// the head label and the return label, past the prologue's saves and
	// before the epilogue's restores.
	spMemory := func(fn *asm.Function, mnemonic string) int {
		n := 0
		inBody := false
		for _, item := range fn.Items {
			if label, isLabel := item.(asm.Label); isLabel {
				inBody = strings.HasPrefix(label.Name, "head")
				continue
			}
			ins, isIns := item.(asm.Instruction)
			if !inBody || !isIns || ins.Mnemonic != mnemonic || len(ins.Operands) < 2 {
				continue
			}
			if mem, isMem := ins.Operands[len(ins.Operands)-1].(asm.Memory); isMem && mem.Base.Class == asm.ClassSP {
				n++
			}
		}
		return n
	}
	step, ok := units["step"]
	if !ok {
		t.Fatal("step was not lowered natively")
	}
	// `next` is the result area: no frame slot is loaded or stored (the
	// parameter is read in place, the fields are written through the
	// parked result register), so the frame holds only the saved registers.
	if loads, stores := spMemory(step, "ldr"), spMemory(step, "str"); loads != 0 || stores != 0 {
		t.Errorf("step must build its result in the x8 area without frame slots; got %d slot loads and %d slot stores:\n%s", loads, stores, fmt.Sprint(step.Items))
	}
	twice, ok := units["twice"]
	if !ok {
		t.Fatal("twice was not lowered natively")
	}
	// step is called twice — the boundary is real — and y and z receive
	// the callee's result directly (written through x8 into their own
	// slots) and are read in place: no frame store copies them anywhere.
	// total expands at its calls (§9 "Aggregate helpers") and reads the
	// fields from the slots directly; the one store allowed is the spill
	// of total(y) across the second call.
	calls := 0
	for _, item := range twice.Items {
		if ins, isIns := item.(asm.Instruction); isIns && ins.Mnemonic == "bl" {
			if sym, isSym := ins.Operands[0].(asm.Symbol); isSym && sym.Name == "step" {
				calls++
			}
		}
	}
	if calls != 2 {
		t.Errorf("twice must call step twice (the helper with a loop is not expanded); got %d calls:\n%s", calls, fmt.Sprint(twice.Items))
	}
	if stores := spMemory(twice, "str") + spMemory(twice, "stp"); stores > 1 {
		t.Errorf("twice must receive results in place, copying nothing; got %d slot stores:\n%s", stores, fmt.Sprint(twice.Items))
	}
}
