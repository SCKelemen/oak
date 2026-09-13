package testrunner

import (
	"testing"

	"github.com/SCKelemen/oak/target"
	"github.com/SCKelemen/oak/toolchain"
)

// A foreign Linux target's tests run under the tooling's user-mode
// emulator (docs/spec/110-testing.md): the binary zig links for the target
// executes under qemu-<arch>, and the results are the program's. Skips
// without a cross compiler or an emulator (the CI cross-targets job has
// both).
func TestForeignTargetRunsUnderEmulator(t *testing.T) {
	tgt := target.Target{OS: target.OSLinux, Arch: target.ArchRiscv64}
	if _, err := toolchain.ResolveEmulator(tgt, nil, nil); err != nil {
		t.Skipf("no emulator: %v", err)
	}
	if drv, err := toolchain.Resolve(tgt, toolchain.Options{}, nil, nil); err != nil || drv.Kind == "host" {
		t.Skipf("no cross compiler: %v", err)
	}
	files := map[string]string{
		"sum.oak": `package main
total: (a: u32, b: u32): u32 = a + b
main: (): i32 = 0
`,
		"sum_test.oak": `package main
import(testing)
TestTotal: (): () {
  assert(total(u32(40), u32(2)) == u32(42))
}
TestWrong: (): () {
  assert(total(u32(1), u32(1)) == u32(3))
}
`,
		"oak.mod": "module example.com/emu\noak 0.1.0\n",
	}
	dir := fixture(t, files)
	code, results, stderr := runCLI(t, "-target", tgt.String(), "-run", "TestTotal", dir)
	if code != 0 || len(results) != 1 || results[0].Status != "pass" {
		t.Fatalf("a passing test under the emulator: %d %+v %s", code, results, stderr)
	}
	code, results, stderr = runCLI(t, "-target", tgt.String(), "-run", "TestWrong", dir)
	if code != 1 || len(results) != 1 || results[0].Status != "fail" {
		t.Fatalf("a failing test under the emulator fails: %d %+v %s", code, results, stderr)
	}
}
