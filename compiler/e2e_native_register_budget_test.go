package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// The register budget (docs/spec/94-assembler.md §9): the callee-saved
// registers the second lowering pass reserves for the loop invariants
// yield to a declaration that would otherwise refuse the body — here a
// span local inside a loop whose three span parameters, two scalar locals,
// and reserve fill the file. The C backend's realization is the oracle.
const nativeRegisterBudgetProgram = `
// A helper with a loop of its own: a real call inside scan's loop, so the
// loop invariants need callee-saved registers and reserve them.
sum4: (w: []u8): u32 {
  s: u32 = 0
  k: u32 = 0
  while k < len(w) {
    s = s + u32(w[k])
    k = k + u32(1)
  }
  s
}

scan: (a: []u8, b: []u8, c: []u8): u32 {
  total: u32 = 0
  i: u32 = 0
  while len(a) >= u32(4) && i <= len(a) - u32(4) {
    scale: u32 = len(b) * u32(3) + len(c)
    w: []u8 = subslice(a, i, u32(4))
    total = total + sum4(w) * scale
    i = i + u32(4)
  }
  total
}

main: (): i32 {
  buf: [16]u8
  j: u32 = 0
  while j < len(buf) {
    buf[j] = u8_trunc_u32(j + u32(1))
    j = j + u32(1)
  }
  assert(scan(view(&buf), view(&buf)[u32(0):u32(8)], view(&buf)[u32(0):u32(5)]) == u32(136 * 29))
  42
}
`

func TestE2ENativeRegisterBudget(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("budget.oak", nativeRegisterBudgetProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_register_budget", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native register budget: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	if !strings.Contains(joined, "asm unit scan:") {
		t.Errorf("scan must lower natively with its span local taking the invariants' reserve; diagnostics:\n%s", joined)
	}
	if strings.Contains(joined, "callee-saved registers are exhausted") {
		t.Errorf("the register file must not run out for scan; diagnostics:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_register_budget_c", New().WithSource("budget.oak", nativeRegisterBudgetProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
