package compiler

// Steady-state entry points (docs/spec/85-discipline.md section 4): the
// oak.mod `steady <package> <fn>` directive gives each named function the
// implicit forbids { Memory.Allocate }, checked over the call graph.

import (
	"strings"
	"testing"
)

const allocatingLib = `package lib
pub c_malloc: (n: c.UInt64): c.UInt64 effects { Memory.Allocate } = c.extern("malloc")
pub grow: (n: u64): u64 = u64(c_malloc(c.UInt64(n)))
pub size: (n: u64): u64 = n * u64(2)
`

func steadyFixture(t *testing.T, manifestExtra, mainBody string) string {
	t.Helper()
	return writeModule(t, map[string]string{
		"app/oak.mod":  "module example.com/app\noak 0.1.0\nrequire example.com/lib 1.0.0\nreplace example.com/lib => ../lib\n" + manifestExtra,
		"app/main.oak": "package main\nimport(\"example.com/lib\")\n" + mainBody,
		"lib/oak.mod":  "module example.com/lib\noak 0.1.0\n",
		"lib/lib.oak":  allocatingLib,
	})
}

func TestSteadyEntryRejectsReachableAllocation(t *testing.T) {
	root := steadyFixture(t, "steady example.com/app serve\n", `
serve: (n: u64): u64 = lib.grow(n)
main: (): i32 { 0 }
`)
	_, err := New().WithPackageDir(root + "/app").EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), CodeSteadyAllocation) {
		t.Fatalf("want %s, got %v", CodeSteadyAllocation, err)
	}
	for _, want := range []string{"steady example.com/app serve", "Memory.Allocate", "serve -> "} {
		if !strings.Contains(err.Error(), want) {
			t.Fatalf("diagnostic lacks %q: %v", want, err)
		}
	}
}

func TestSteadyEntryCleanCompiles(t *testing.T) {
	root := steadyFixture(t, "steady example.com/app serve\n", `
serve: (n: u64): u64 = lib.size(n)
setup: (n: u64): u64 = lib.grow(n)
main: (): i32 { 0 }
`)
	if _, err := New().WithPackageDir(root + "/app").EmitC().Get(); err != nil {
		t.Fatalf("a steady entry that reaches no allocation must compile (setup may allocate): %v", err)
	}
}

func TestSteadyEntryUnknownFunctionIsAManifestError(t *testing.T) {
	uses := "main: (): i32 { i32_bits_u32(u32_trunc_u64(lib.size(u64(1)))) }\n"
	root := steadyFixture(t, "steady example.com/app nothing\n", uses)
	_, err := New().WithPackageDir(root + "/app").EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), CodeManifest) || !strings.Contains(err.Error(), "nothing") {
		t.Fatalf("want %s naming the entry, got %v", CodeManifest, err)
	}
	root = steadyFixture(t, "steady example.com/lib grow\n", uses)
	_, err = New().WithPackageDir(root + "/app").EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), CodeManifest) {
		t.Fatalf("a steady entry in another module must be a manifest error, got %v", err)
	}
}

func TestSteadyEntryKeepsItsOwnForbids(t *testing.T) {
	root := steadyFixture(t, "steady example.com/app serve\n", `
c_write: (n: c.UInt64): c.UInt64 effects { Os.Syscall } = c.extern("write_one")
serve: (n: u64): u64 forbids { Os.Syscall } = u64(c_write(c.UInt64(n))) + lib.size(n)
main: (): i32 { 0 }
`)
	_, err := New().WithPackageDir(root + "/app").EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), CodeEffectForbidden) {
		t.Fatalf("the declared forbids must still be enforced, got %v", err)
	}
	root = steadyFixture(t, "steady example.com/app serve\n", `
serve: (n: u64): u64 forbids { Os.Syscall } = lib.grow(n)
main: (): i32 { 0 }
`)
	_, err = New().WithPackageDir(root + "/app").EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), CodeSteadyAllocation) {
		t.Fatalf("the implicit allocation clause must be enforced alongside a declared one, got %v", err)
	}
}
