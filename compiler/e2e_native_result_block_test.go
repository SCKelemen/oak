package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// The dbs pilot's `-native` panic (docs/notes/dbs-feedback-2026-09.md): a
// function whose result is a block or match — `x == u32(7) ? { u8(0) } |
// { u8(1) }` — declares a local on the native lowering's result path,
// where the locals map was never created ("assignment to entry in nil
// map" in asm/verify.go). The program lowers, builds, and runs.
const nativeResultBlockProgram = `
pick: (x: u32): i32 {
  x == u32(7) ? { i32(42) } | { i32(1) }
}
main: (): i32 {
  x: u32 = u32(7)
  x == u32(7) ? { pick(x) } | { i32(2) }
}
`

func TestE2ENativeResultBlock(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("result_block.oak", nativeResultBlockProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_result_block", comp)
	if abnormal || code != 42 {
		t.Fatalf("native result block: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, strings.Join(infos, "\n"))
	}
	if !strings.Contains(strings.Join(infos, "\n"), "asm unit main:") {
		t.Fatalf("main was not lowered by the native backend; diagnostics:\n%s", strings.Join(infos, "\n"))
	}
}
