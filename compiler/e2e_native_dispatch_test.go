package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// A function with a dispatch clause (docs/spec/93-simd.md §6) is the
// selection between its realizations, made once at startup from the
// processor's probed features; only its portable body is Oak. The native
// backend leaves it to the C backend, whose definition carries the probe
// and the branch to the hardware unit, and lowers its callers as usual, so
// a native program still reaches the unit. Lowering the body natively
// defined the symbol as the portable realization and made CRC-32C run
// 23x behind the C backend (benchmarks/native/README.md).
func TestE2ENativeDispatchingFunctionStaysWithTheCBackend(t *testing.T) {
	requireArm64Host(t)
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/hash_dispatch\noak 0.1.0\n",
		"main.oak": crcShaProgram,
	})
	var infos []string
	comp := New().WithPackageDir(root).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	native, err := comp.EmitNative(HostObjectFormat()).Get()
	if err != nil {
		t.Fatalf("native build: %v\n%s", err, strings.Join(infos, "\n"))
	}
	joined := strings.Join(infos, "\n")
	for _, fn := range []string{"hash__crc32c_ustep7", "hash__sha256_ublock_uhw"} {
		if !strings.Contains(joined, "native backend: "+fn+" left to the C backend (it dispatches on ") {
			t.Errorf("%s dispatches and must stay with the C backend; diagnostics:\n%s", fn, joined)
		}
		if strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was lowered natively, which hides its hardware realization; diagnostics:\n%s", fn, joined)
		}
	}
	// The callers still lower, and the C keeps the probe and the branch.
	for _, fn := range []string{"hash__crc32c_uchunk", "hash__crc32c_uupdate"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s (a caller of the dispatching function) should still be lowered; diagnostics:\n%s", fn, joined)
		}
	}
	for _, want := range []string{"oak_cpu_features & OAK_CPU_CRC", "oak_cpu_features & OAK_CPU_SHA2", "return oak_hash__crc32c_ustep7_uasm("} {
		if !strings.Contains(native.C, want) {
			t.Errorf("the native build's C lacks %q: the dispatch was lost", want)
		}
	}
}
