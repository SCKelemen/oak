package compiler

import (
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
)

// Read-only borrows (docs/spec/94-assembler.md §9): `view(&block)` of a
// by-value parameter reads it and nothing else, so the parameter stays
// untouched — the callee reads it in place and the caller passes its own
// storage instead of a 64-byte copy. A writable span of the same storage
// passed alongside keeps the copy (the callee could write through it).
// The C backend's realization is the oracle.
const nativeReadOnlyBorrowProgram = `
Blob: type = struct {
  block: [64]u8
  n: u32
}

total: (v: []u8): u32 {
  s: u32 = 0
  i: u32 = 0
  while i < len(v) {
    s = s + u32(v[i])
    i = i + u32(1)
  }
  s
}

// The parameter borrowed read-only: no copy anywhere.
sum: (block: [64]u8): u32 = total(view(&block))

// A writable span of the caller's storage alongside the by-value copy:
// the copy must stay, and reads the value before the write.
bump_first: (block: [64]u8, s: [*]u8): u32 {
  s[0] = u8(200)
  u32(block[0])
}

main: (): i32 {
  b: Blob
  j: u32 = 0
  while j < u32(64) {
    b.block[j] = u8_trunc_u32(j + u32(1))
    j = j + u32(1)
  }
  assert(sum(b.block) == u32(2080))
  r: u32 = bump_first(b.block, span(&b.block))
  assert(r == u32(1))
  assert(b.block[0] == u8(200))
  42
}
`

func TestE2ENativeReadOnlyBorrow(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("borrow.oak", nativeReadOnlyBorrowProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_readonly_borrow", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native read-only borrow: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"sum", "bump_first", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_readonly_borrow_c", New().WithSource("borrow.oak", nativeReadOnlyBorrowProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestNativeShapesReadOnlyBorrow(t *testing.T) {
	model, err := New().WithSource("borrow.oak", nativeReadOnlyBorrowProgram).WithNativeBodies().WithNativeAsm().SemanticModel().Get()
	if err != nil {
		t.Fatal(err)
	}
	units := map[string]*asm.Function{}
	for _, fn := range model.AsmFunctions {
		units[fn.Name] = fn
	}
	sum, ok := units["sum"]
	if !ok {
		t.Fatal("sum was not lowered natively")
	}
	// The parameter is read in place: no frame slot is loaded or stored
	// in the body (between the head label and the return label).
	inBody := false
	for _, item := range sum.Items {
		if label, isLabel := item.(asm.Label); isLabel {
			inBody = strings.HasPrefix(label.Name, "head")
			continue
		}
		ins, isIns := item.(asm.Instruction)
		if !inBody || !isIns || len(ins.Operands) < 2 {
			continue
		}
		if mem, isMem := ins.Operands[len(ins.Operands)-1].(asm.Memory); isMem && mem.Base.Class == asm.ClassSP && (strings.HasPrefix(ins.Mnemonic, "ld") || strings.HasPrefix(ins.Mnemonic, "st")) {
			t.Errorf("sum copies its parameter into the frame: %s\n%s", fmt.Sprint(ins), fmt.Sprint(sum.Items))
		}
	}
	main, ok := units["main"]
	if !ok {
		t.Fatal("main was not lowered natively")
	}
	// One 64-byte copy in main: the one for bump_first, whose writable
	// span could reach the storage; sum's argument is the storage itself.
	stp := 0
	for _, item := range main.Items {
		if ins, isIns := item.(asm.Instruction); isIns && ins.Mnemonic == "stp" {
			a, _ := ins.Operands[0].(asm.Register)
			b, _ := ins.Operands[1].(asm.Register)
			if mem, isMem := ins.Operands[2].(asm.Memory); isMem && mem.Base.Class == asm.ClassSP && mem.Offset >= 80 && a.Text != b.Text {
				stp++ // a copy pair, not the zero-fill's `stp x9, x9`
			}
		}
	}
	if stp != 4 {
		t.Errorf("main must copy the block once (four pairs, for bump_first) and pass it to sum in place; got %d pair stores:\n%s", stp, fmt.Sprint(main.Items))
	}
}
