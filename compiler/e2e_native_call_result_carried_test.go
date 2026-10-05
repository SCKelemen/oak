package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// A loop variable that travels through a call's argument and result
// register with no move between the iterations: once its registers are
// reallocated, crc32c_update keeps `state` in w0 into the chunk call and
// out of it. The loop summarizer took a summarized call's result
// registers for temporaries, so the register carried nothing, `state`
// had no pairing, and every optimized form of the body was set aside as
// witnessed (docs/spec/94-assembler.md §9). A result register the body
// reads before it writes carries the variable; the optimized form proves
// and is selected.
func TestE2ENativeCallResultRegisterCarriesLoopVariable(t *testing.T) {
	requireArm64Host(t)
	t.Setenv("OAK_NATIVE_ONLY", "hash__crc32c_uupdate")
	t.Setenv("OAK_VERIFY_CACHE", "0")
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/call_result_carried\noak 0.1.0\n",
		"main.oak": crcShaProgram,
	})
	var infos []string
	comp := New().WithPackageDir(root).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" && strings.Contains(d.Message, "hash__crc32c_uupdate") {
			infos = append(infos, d.Message)
		}
	})
	if _, err := comp.EmitNative(HostObjectFormat()).Get(); err != nil {
		t.Fatal(err)
	}
	joined := strings.Join(infos, "\n")
	if !strings.Contains(joined, "asm unit hash__crc32c_uupdate: proven equal to its Oak body at the bit level — 2 data-dependent loops coupled inductively") {
		t.Errorf("crc32c_update must be proven by loop coupling; diagnostics:\n%s", joined)
	}
	if !strings.Contains(joined, "state↔r0") {
		t.Errorf("state must couple with the call's result register r0 in the reallocated form; diagnostics:\n%s", joined)
	}
	if strings.Contains(joined, "hash__crc32c_uupdate keeps its") {
		t.Errorf("the optimized form must be selected, not set aside; diagnostics:\n%s", joined)
	}
}
