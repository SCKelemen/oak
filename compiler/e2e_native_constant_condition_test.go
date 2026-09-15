package compiler

import (
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
)

// Constant conditions (docs/spec/94-assembler.md §9): a conditional whose
// scrutinee is the literal true or false lowers as the selected arm alone —
// no Bool materialized and tested, no label, no dead arm — in statement,
// value, and result position. The C backend's realization is the oracle.
const nativeConstantConditionProgram = `
scope: (x: u32): u32 {
  y: u32 = x
  true ? { y = y + u32(1) }
  false ? { y = y * u32(100) }
  false ? { y = u32(0) } | { y = y + u32(2) }
  z: u32 = true ? y * u32(2) | u32(7)
  z + (false ? u32(1000) | u32(3))
}

pick: (x: u32): u32 = true ? x + u32(1) | x

main: (): i32 {
  assert(scope(u32(5)) == u32(19))
  assert(pick(u32(41)) == u32(42))
  42
}
`

func TestE2ENativeConstantConditions(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("constcond.oak", nativeConstantConditionProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_constcond", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native constant conditions: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"scope", "pick"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") {
			t.Errorf("%s must be proven equal to its Oak body; diagnostics:\n%s", fn, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_constcond_c", New().WithSource("constcond.oak", nativeConstantConditionProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestNativeShapesConstantConditions(t *testing.T) {
	model, err := New().WithSource("constcond.oak", nativeConstantConditionProgram).WithNativeBodies().WithNativeAsm().SemanticModel().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, fn := range model.AsmFunctions {
		if fn.Name != "scope" && fn.Name != "pick" {
			continue
		}
		for _, item := range fn.Items {
			switch it := item.(type) {
			case asm.Instruction:
				switch it.Mnemonic {
				case "cbz", "cbnz", "b.", "b", "cset", "csel":
					t.Errorf("%s branches or selects on a constant condition: %s\n%s", fn.Name, fmt.Sprint(it), fmt.Sprint(fn.Items))
				}
			case asm.Label:
				if strings.HasPrefix(it.Name, "else") || strings.HasPrefix(it.Name, "endif") {
					t.Errorf("%s keeps a conditional's label for a constant condition: %s", fn.Name, it.Name)
				}
			}
		}
	}
}
