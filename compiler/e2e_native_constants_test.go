package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// The OS pilot's N1 (docs/notes/os-language-requests-2026-09.md): a
// function that reads constant top-level bindings — `page_shift`, `mask`,
// the page-table walk's `page_size` and `entries` — lowers through the
// native backend, the reads folded to their typed literals; the C emitter
// keeps the `static const`. A binding some statement writes is not a
// constant and its reader stays with the C backend.
const nativeConstantsProgram = `
page_shift: u64 = u64(14)
mask: u64 = u64(511)
entries: u32 = 512
counter: u32 = u32(0)

index_of: (va: u64): u32 = u32_trunc_u64((va >> page_shift) & mask)
capacity: (): u32 = entries * u32(2)
bump: (): u32 {
  counter = counter + u32(1)
  counter
}

main: (): i32 {
  i32_bits_u32(index_of(u64(16384) * u64(700)) + capacity() + bump())
}
`

func TestE2ENativeConstantReads(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("consts.oak", nativeConstantsProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_constants", comp)
	joined := strings.Join(infos, "\n")
	// 700 % 512 = 188, plus 1024, plus 1 = 1213; the process exit code
	// carries the low byte, 189.
	if abnormal || code != 1213%256 {
		t.Fatalf("exit = (%d, abnormal=%v), want %d\n%s", code, abnormal, 1213%256, joined)
	}
	for _, fn := range []string{"index_of", "capacity"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s reads constants and must lower natively; diagnostics:\n%s", fn, joined)
		}
	}
	if !strings.Contains(joined, "bump left to the C backend") {
		t.Errorf("bump writes a global and stays with the C backend; diagnostics:\n%s", joined)
	}
	emitted, err := New().WithSource("consts.oak", nativeConstantsProgram).WithNativeBodies().EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(emitted, "static const u64 page_shift") {
		t.Errorf("the C keeps the constant global:\n%s", emitted[:min(len(emitted), 400)])
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_constants_c", New().WithSource("consts.oak", nativeConstantsProgram)); abnormal || code != 1213%256 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want %d", code, abnormal, 1213%256)
	}
}
