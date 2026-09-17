package compiler

import (
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
)

func TestE2ENativeSelectsAndExecutesSpilledOptIR(t *testing.T) {
	requireArm64Host(t)
	const values = 20
	var source strings.Builder
	source.WriteString("pressure: (x: u32): u32 = {\n")
	for index := 1; index <= values; index++ {
		fmt.Fprintf(&source, "  v%d: u32 = x + u32(%d)\n", index, index)
		fmt.Fprintf(&source, "  d%d: u32 = x + u32(%d)\n", index, index)
	}
	source.WriteString("  ")
	for index := 1; index <= values; index++ {
		if index > 1 {
			source.WriteString(" + ")
		}
		fmt.Fprintf(&source, "v%d + d%d", index, index)
	}
	source.WriteString("\n}\n\nmain: (): i32 = pressure(u32(1)) == u32(460) ? i32(42) | i32(1)\n")

	var diagnostics []string
	comp := New().WithSource("native_optir_spills.oak", source.String()).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			diagnostics = append(diagnostics, d.Message)
		}
	})
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	joined := strings.Join(diagnostics, "\n")
	if !strings.Contains(joined, "pressure: optimized OptIR selected") {
		t.Fatalf("spilled optimized SSA candidate was not selected:\n%s", joined)
	}
	if verdict := model.NativeVerdicts["pressure"]; verdict.Kind.String() != "proven" {
		t.Fatalf("pressure verdict = %s (%s)", verdict.Kind, verdict.Message)
	}
	var pressureFrame int64
	var spilled bool
	for _, function := range model.AsmFunctions {
		if function.Name != "pressure" {
			continue
		}
		pressureFrame = function.Frame
		for _, item := range function.Items {
			instruction, ok := item.(asm.Instruction)
			if ok && (instruction.Mnemonic == "ldr" || instruction.Mnemonic == "str") {
				spilled = true
			}
		}
	}
	if pressureFrame == 0 || !spilled {
		t.Fatalf("selected pressure body did not materialize a spill frame: frame=%d", pressureFrame)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_optir_spills", comp); abnormal || code != 42 {
		t.Fatalf("spilled native execution = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// Repeated multiplication gives SSA sharing a real cost advantage. The older
// (x+1)+(x+1) fixture can legitimately prefer native strength reduction, so it
// does not reliably test selection of the SSA candidate.
const nativeOptIRProgram = `
common: (x: u32): u32 {
  left: u32 = x * u32(3)
  right: u32 = x * u32(3)
  dead: u32 = x * u32(2)
  left + right
}

main: (): i32 = i32_bits_u32(common(u32(7)))
`

func TestE2ENativeSelectsVerifiedOptimizedOptIR(t *testing.T) {
	requireArm64Host(t)
	var diagnostics []string
	comp := New().WithSource("native_optir.oak", nativeOptIRProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			diagnostics = append(diagnostics, d.Message)
		}
	})
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	joined := strings.Join(diagnostics, "\n")
	if !strings.Contains(joined, "common: optimized OptIR selected") || !strings.Contains(joined, "generic SSA change(s), proven") {
		t.Fatalf("optimized SSA candidate was not selected and proven:\n%s", joined)
	}
	if verdict := model.NativeVerdicts["common"]; verdict.Kind.String() != "proven" {
		t.Fatalf("common verdict = %s (%s)", verdict.Kind, verdict.Message)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_optir", comp); abnormal || code != 42 {
		t.Fatalf("native execution = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

const nativeNarrowOptIRProgram = `
narrow_u8: (x: u8): u32 {
  left: u8 = x + u8(10)
  right: u8 = x + u8(10)
  dead: u8 = x * u8(3)
  u32(left + right)
}

narrow_i8: (x: i8): i32 {
  left: i8 = x + i8(10)
  right: i8 = x + i8(10)
  dead: i8 = x * i8(3)
  i32(left + right)
}

narrow_u16: (x: u16): u32 {
  left: u16 = x + u16(10)
  right: u16 = x + u16(10)
  dead: u16 = x * u16(3)
  u32(left + right)
}

narrow_i16: (x: i16): i32 {
  left: i16 = x + i16(10)
  right: i16 = x + i16(10)
  dead: i16 = x * i16(3)
  i32(left + right)
}

main: (): i32 {
  ok8: Bool = narrow_u8(u8(250)) == u32(8) && narrow_i8(i8(120)) == i32(4)
  ok16: Bool = narrow_u16(u16(65530)) == u32(8) && narrow_i16(i16(32760)) == i32(4)
  ok8 && ok16 ? i32(42) | i32(1)
}
`

func TestE2ENativeSelectsVerifiedNarrowOptIR(t *testing.T) {
	requireArm64Host(t)
	var diagnostics []string
	comp := New().WithSource("native_narrow_optir.oak", nativeNarrowOptIRProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			diagnostics = append(diagnostics, d.Message)
		}
	})
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	joined := strings.Join(diagnostics, "\n")
	for _, function := range []string{"narrow_u8", "narrow_i8", "narrow_u16", "narrow_i16"} {
		if !strings.Contains(joined, function+": optimized OptIR selected") {
			t.Fatalf("%s optimized narrow SSA candidate was not selected:\n%s", function, joined)
		}
		if verdict := model.NativeVerdicts[function]; verdict.Kind.String() != "proven" {
			t.Fatalf("%s verdict = %s (%s)", function, verdict.Kind, verdict.Message)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_narrow_optir", comp); abnormal || code != 42 {
		t.Fatalf("native execution = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
