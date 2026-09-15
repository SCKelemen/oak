package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
)

const nativeFactTransportProgram = `TABLE: [12]u32 = [12]u32{0, 1, 10, 2, 3, 20, 4, 5, 30, 6, 7, 40}

lookup: (i: u32): u32 {
  table: []u32 = view(&TABLE)
  entries: u32 = len(table) / u32(3)
  i < entries ? { table[i * u32(3) + u32(2)] } | { u32(0) }
}

main: (): i32 = i32_bits_u32(lookup(u32(2)))
`

// The typechecker proves the scaled table index with
// Oak.Extents.div_bound_scaled. Native lowering attaches that exact proof to
// the indexed load, MachineIR leaves the instruction-local reference intact,
// and the seam checker consumes it from independently supplied authority.
func TestE2ENativeCheckedFactTransport(t *testing.T) {
	requireArm64Host(t)
	var diagnostics []string
	comp := New().WithSource("facts.oak", nativeFactTransportProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			diagnostics = append(diagnostics, d.Message)
		}
	})
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	joined := strings.Join(diagnostics, "\n")
	if !strings.Contains(joined, "lookup: 1 element guard(s) elided") {
		t.Fatalf("scaled-index proof did not cross the native seam:\n%s", joined)
	}
	found := false
	for _, function := range model.AsmFunctions {
		if function.Name != "lookup" {
			continue
		}
		for _, item := range function.Items {
			instruction, ok := item.(asm.Instruction)
			if ok && len(instruction.CheckedFacts) > 0 {
				found = true
			}
		}
	}
	if !found {
		t.Fatal("selected lookup body carries no checked fact reference")
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_checked_facts", comp); abnormal || code != 30 {
		t.Fatalf("native execution = (%d, abnormal=%v), want 30", code, abnormal)
	}
}
