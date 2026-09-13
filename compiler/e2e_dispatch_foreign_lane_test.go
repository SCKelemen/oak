package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/target"
)

// A dispatch realization exists only on its feature's architecture
// (docs/spec/93-simd.md section 6): a body-less declaration realized by an
// arm64 unit and named only in an arm64 feature's slot must build for
// amd64, where the slot is inert and the dispatch takes its default. Every
// amd64 CI job that loaded the standard library's hash package failed on
// this until the asm gate learned it (the units of #317).
const foreignLaneDispatchProgram = `double: (x: u32): u32 dispatch { crc: double_asm } {
  x + x
}

double_asm: (x: u32): u32

main: (): i32 {
  double(u32(21)) == u32(42) ? 42 | 1
}
`

const foreignLaneUnit = `double_asm: (x: u32): u32 = {
  bind w0 = x
  add w0, w0, w0
  ret
}
`

func TestE2EDispatchRealizationOnForeignLane(t *testing.T) {
	for _, arch := range []string{target.ArchAmd64, target.ArchArm64} {
		output, err := New().WithSource("double.oak", foreignLaneDispatchProgram).WithAsmUnit("double.arm64.oakasm", foreignLaneUnit).WithTarget(target.Target{OS: target.OSLinux, Arch: arch}).EmitC().Get()
		if err != nil {
			t.Fatalf("%s: %v", arch, err)
		}
		if !strings.Contains(output, "OAK_DISPATCH_CRC") {
			t.Fatalf("%s: the dispatch on the crc slot is emitted (inert under the preprocessor off arm64):\n%s", arch, output)
		}
		if !strings.Contains(output, "oak_main(") {
			t.Fatalf("%s: no program emitted:\n%s", arch, output)
		}
	}
	// The same unit without a dispatch slot has no realization on amd64 and
	// fails closed as before.
	direct := strings.Replace(foreignLaneDispatchProgram, "double: (x: u32): u32 dispatch { crc: double_asm } {\n  x + x\n}", "double: (x: u32): u32 = double_asm(x)", 1)
	_, err := New().WithSource("double.oak", direct).WithAsmUnit("double.arm64.oakasm", foreignLaneUnit).WithTarget(target.Target{OS: target.OSLinux, Arch: target.ArchAmd64}).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "no Oak fallback body") {
		t.Fatalf("a foreign unit without a slot or a fallback must fail closed, got %v", err)
	}
	// The standard library's hash package, whose kernels dispatch to arm64
	// units, builds for amd64.
	root := writeModule(t, map[string]string{
		"oak.mod": "module example.com/hashuse\noak 0.1.0\n",
		"main.oak": `package main

import("hash")

main: (): i32 {
  data: [4]u8 = [4]u8{ u8(1), u8(2), u8(3), u8(4) }
  hash.crc32c(view(&data)) != u32(0) ? 42 | 1
}
`,
	})
	if _, err := New().WithPackageDir(root).WithTarget(target.Target{OS: target.OSLinux, Arch: target.ArchAmd64}).EmitC().Get(); err != nil {
		t.Fatalf("hash for linux/amd64: %v", err)
	}
}
