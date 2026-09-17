package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/nativegen"
)

// In-place expansion of a record update (nativegen/inline.go
// expandInPlace): `acc = step(acc)` where step copies its parameter into
// the local it returns and never reads the parameter again runs step's
// body on acc itself — no copy in, no copy out. The values are the copy
// form's (the copies were identities), so the body is judged as before.
const nativeInPlaceUpdateProgram = `
Acc: type = struct {
  words: [32]u32
  count: u32
}

step: (state: Acc, k: u32): Acc {
  next: Acc = state
  next.words[next.count & u32(31)] = next.words[next.count & u32(31)] + k
  next.count = next.count + u32(1)
  next
}

run: (n: u32): u32 {
  acc: Acc = Acc{ words: [32]u32{ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 }, count: 0 }
  i: u32 = 0
  while i < n {
    acc = step(acc, i)
    i = i + u32(1)
  }
  acc.words[0] + acc.words[1] + acc.count
}

main: () -> i32 = i32_bits_u32(run(u32(40)) & u32(255))
`

func TestE2ENativeInPlaceUpdate(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("inplace.oak", nativeInPlaceUpdateProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
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
		if fn.Name == "run" {
			unit = fn
		}
	}
	joined := strings.Join(infos, "\n")
	if unit == nil {
		t.Fatalf("run was not lowered natively:\n%s", joined)
	}
	// The loop carries no record copy: no pair load or store, no call.
	pairs, calls := 0, 0
	for _, ins := range loopBody(unit) {
		switch ins.Mnemonic {
		case "ldp", "stp":
			pairs++
		case "bl":
			calls++
		}
	}
	if pairs != 0 || calls != 0 {
		t.Errorf("run's loop must update acc in place (pairs %d, calls %d):\n%s\n%s", pairs, calls, nativegen.Describe(unit), joined)
	}
	// 40 steps over words[0..31]: words[0] = 0 + 32 = 32, words[1] = 1 + 33 = 34,
	// count = 40: 106.
	_, code, abnormal := buildAndRunFrom(t, "native_inplace_update", comp)
	if abnormal || code != 106 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 106\n%s", code, abnormal, joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_inplace_update_c", New().WithSource("inplace.oak", nativeInPlaceUpdateProgram)); abnormal || code != 106 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 106", code, abnormal)
	}
}
