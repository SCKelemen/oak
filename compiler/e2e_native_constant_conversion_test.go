package compiler

// A plain constructor over a constant — `u8(0)`, `u8(1)`, `u32(limit)` —
// is the constant at the target width (docs/spec/90-backend.md §16):
// materialized once and normalized by construction, with no width mask
// after it. The OS page walkers' status conditionals (`r = oor ? u8(0) |
// r`) spent a `movz` and an `and wN, wN, #255` per constant.

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/target"
)

const nativeConstantConversionProgram = `limit: u16 = u16(300)

status: (ipa: u64, bound: u64): u8 {
  r: u8 = u8(1)
  oor: Bool = ipa >= bound
  r = oor ? u8(0) | r
  more: Bool = ipa == bound - u64(1)
  r = more ? u8(2) | r
  r
}

cap: (n: u32): u16 {
  over: Bool = n > u32(limit)
  over ? limit | u16_trunc_u32(n)
}

main: (): i32 {
  a: u8 = status(u64(5), u64(10))
  b: u8 = status(u64(10), u64(10))
  c: u8 = status(u64(9), u64(10))
  d: u16 = cap(u32(1000))
  (a == u8(1) && b == u8(0) && c == u8(2) && d == u16(300)) ? 42 | 1
}
`

func TestE2ENativeConstantConstructorsNeedNoMask(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("cconv.oak", nativeConstantConversionProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	model, err := comp.SemanticModel().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v\n%s", err, strings.Join(infos, "\n"))
	}
	units := map[string]*asm.Function{}
	for _, fn := range model.AsmFunctions {
		units[fn.Name] = fn
	}
	joined := strings.Join(infos, "\n")
	for _, name := range []string{"status", "cap"} {
		if units[name] == nil {
			t.Fatalf("%s was not lowered natively:\n%s", name, joined)
		}
		if name == "status" {
			// Every value in status is a u8 constant or a copy of one:
			// no width mask anywhere in the unit (cap truncates a u32 to
			// u16 at run time, which keeps its mask).
			for _, item := range units[name].Items {
				ins, isIns := item.(asm.Instruction)
				if !isIns || ins.Mnemonic != "and" || len(ins.Operands) != 3 {
					continue
				}
				if imm, isImm := ins.Operands[2].(asm.Immediate); isImm && (imm.Value == 0xff || imm.Value == 0xffff) {
					t.Fatalf("%s: a constant constructor needs no width mask, got %v", name, ins)
				}
			}
		}
		if !strings.Contains(joined, "asm unit "+name+": proven") {
			t.Fatalf("%s must stay proven:\n%s", name, joined)
		}
	}
	_, code, abnormal := buildAndRunFrom(t, "cconv", comp)
	if abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
}

func TestE2ENativeRV64ConstantConstructorsProven(t *testing.T) {
	var infos []string
	tgt := target.Target{OS: target.OSLinux, Arch: target.ArchRiscv64}
	comp := New().WithSource("cconv.oak", nativeConstantConversionProgram).WithTarget(tgt).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	if _, err := comp.SemanticModel().Get(); err != nil {
		t.Fatalf("compilation failed: %v\n%s", err, strings.Join(infos, "\n"))
	}
	joined := strings.Join(infos, "\n")
	for _, name := range []string{"status", "cap"} {
		if !strings.Contains(joined, "asm unit "+name+": proven") {
			t.Fatalf("%s must be proven on the RV64 lane:\n%s", name, joined)
		}
	}
}
