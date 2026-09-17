package compiler

// An expression over named module constants is a constant to the native
// lowering (docs/spec/90-backend.md §16): `d & ^(page_size - u64(1))`
// and `ipa & (page_size - u64(1))` — the page walkers' descriptor and
// offset masks — lower to one `and` with a logical immediate, where the
// mask was built in three or four instructions before.

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/target"
)

const nativeConstantFoldProgram = `page_size: u64 = u64(16384)
entries: u32 = u32(2048)
max8: u8 = u8(255)

offset_of: (ipa: u64): u64 { ipa & (page_size - u64(1)) }
frame_of: (d: u64): u64 { d & ^(page_size - u64(1)) }
cells: (tables: u32): u32 { tables * u32(entries) }
widened_wrap: (x: u64): u64 { x + u64(max8 + u8(1)) }

main: (): i32 {
  a: u64 = offset_of(u64(16384) * u64(5) + u64(77))
  b: u64 = frame_of(u64(16384) * u64(5) + u64(77))
  c: u32 = cells(u32(3))
  d: u64 = widened_wrap(u64(42))
  (a == u64(77) && b == u64(81920) && c == u32(6144) && d == u64(42)) ? 42 | 1
}
`

func TestE2ENativeConstantExpressionsFold(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("cfold.oak", nativeConstantFoldProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
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
	for _, name := range []string{"offset_of", "frame_of"} {
		if units[name] == nil {
			t.Fatalf("%s was not lowered natively:\n%s", name, joined)
		}
		ands, others := 0, 0
		for _, item := range units[name].Items {
			ins, isIns := item.(asm.Instruction)
			if !isIns {
				continue
			}
			switch ins.Mnemonic {
			case "and":
				if _, isImm := ins.Operands[2].(asm.Immediate); !isImm {
					t.Fatalf("%s: the mask must be a logical immediate: %v", name, ins)
				}
				ands++
			case "movz", "movk", "sub", "mvn", "orr":
				others++
			}
		}
		if ands != 1 || others != 0 {
			t.Fatalf("%s: one and with an immediate mask and nothing building it; got %d ands, %d mask-building instructions", name, ands, others)
		}
		if !strings.Contains(joined, "asm unit "+name+": proven") {
			t.Fatalf("%s must stay proven:\n%s", name, joined)
		}
	}
	if !strings.Contains(joined, "asm unit cells: proven") {
		t.Fatalf("cells must stay proven:\n%s", joined)
	}
	if !strings.Contains(joined, "asm unit widened_wrap: proven") {
		t.Fatalf("widened_wrap must fold the u8 addition before widening it:\n%s", joined)
	}
	for _, item := range units["widened_wrap"].Items {
		ins, isIns := item.(asm.Instruction)
		if !isIns || ins.Mnemonic != "add" || len(ins.Operands) < 3 {
			continue
		}
		if value, isImm := ins.Operands[2].(asm.Immediate); isImm && value.Value == 256 {
			t.Fatalf("widened_wrap evaluated the u8 addition at the u64 destination width: %v", ins)
		}
	}
	_, code, abnormal := buildAndRunFrom(t, "cfold", comp)
	if abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
}

func TestE2ENativeRV64ConstantExpressionsFold(t *testing.T) {
	var infos []string
	tgt := target.Target{OS: target.OSLinux, Arch: target.ArchRiscv64}
	comp := New().WithSource("cfold.oak", nativeConstantFoldProgram).WithTarget(tgt).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	if _, err := comp.SemanticModel().Get(); err != nil {
		t.Fatalf("compilation failed: %v\n%s", err, strings.Join(infos, "\n"))
	}
	joined := strings.Join(infos, "\n")
	for _, name := range []string{"offset_of", "frame_of", "cells", "widened_wrap"} {
		if !strings.Contains(joined, "asm unit "+name+": proven") {
			t.Fatalf("%s must be proven on the RV64 lane:\n%s", name, joined)
		}
	}
}
