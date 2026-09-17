package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/target"
)

const rareTrapUnit = "rare: (b: u32) -> u32 = {\n  bind w0 = b\n  cmp w0, #1234\n  b.eq trap\n  ret\ntrap:\n  brk #1\n}\n"

func TestE2EVerifiedProfileLoopTrapDomain(t *testing.T) {
	const source = "count: (n: u32) -> u32 = {\n i: u32 = u32(0)\n while i < n {\n  i = i + u32(1)\n }\n i\n}\n"
	const machine = "count: (n: u32) -> u32 = {\n bind w0 = n\n clobber w9\n mov w9, #0\nloop:\n cmp w9, w0\n b.hs done\n cmp w9, #1234\n b.eq trap\n add w9, w9, #1\n b loop\ndone:\n mov w0, w9\n ret\ntrap:\n brk #1\n}\n"
	for _, lane := range []struct {
		os     string
		format asm.ObjectFormat
	}{{target.OSFreestanding, asm.ELF}, {target.OSDarwin, asm.MachO}} {
		t.Run(lane.os, func(t *testing.T) {
			for _, matching := range []bool{false, true} {
				body := source
				if matching {
					body = strings.Replace(body, "  i =", "  assert(i != u32(1234))\n  i =", 1)
				}
				body += "caller: (n: u32) -> u32 = count(n)\n"
				comp := New().WithSource("count.oak", body).
					WithAsmUnit("count.arm64.oakasm", machine).
					WithTarget(target.Target{OS: lane.os, Arch: target.ArchArm64}).WithVerifyFresh()
				if object, err := comp.EmitNativeObject(lane.format).Get(); err != nil || len(object) == 0 {
					t.Fatalf("ordinary loop object (matching %v): %v", matching, err)
				}
				object, err := comp.WithVerifiedProfile().EmitNativeObject(lane.format).Get()
				if matching {
					if err != nil || len(object) == 0 {
						t.Fatalf("matching loop traps must pass strict admission: %v", err)
					}
				} else if err == nil || len(object) != 0 || !strings.Contains(err.Error(), "body trap-domain obligation") || !strings.Contains(err.Error(), "caller (via count)") {
					t.Fatalf("iteration-1234 trap bypassed strict admission: %d bytes, %v", len(object), err)
				}
			}
		})
	}
}

// A real untrusted assembly candidate, not an injected verdict. An unseen
// extra trap must fail the strict profile before either object is emitted.
func TestE2EVerifiedProfileTrapDomain(t *testing.T) {
	for _, test := range []struct {
		os     string
		format asm.ObjectFormat
	}{{target.OSFreestanding, asm.ELF}, {target.OSDarwin, asm.MachO}} {
		t.Run(test.os, func(t *testing.T) {
			for _, sameTrap := range []bool{false, true} {
				body := "b"
				if sameTrap {
					body = "{\n  assert(b != u32(1234))\n  b\n}"
				}
				comp := New().WithSource("rare.oak", "rare: (b: u32) -> u32 = "+body+"\n").
					WithAsmUnit("rare.arm64.oakasm", rareTrapUnit).
					WithTarget(target.Target{OS: test.os, Arch: target.ArchArm64})
				if object, err := comp.EmitNativeObject(test.format).Get(); err != nil || len(object) == 0 {
					t.Fatalf("ordinary native object (matching trap %v): %v", sameTrap, err)
				}
				object, err := comp.WithVerifiedProfile().EmitNativeObject(test.format).Get()
				if sameTrap {
					if err != nil || len(object) == 0 {
						t.Fatalf("matching source/machine traps must prove: %v", err)
					}
					continue
				}
				if err == nil || len(object) != 0 {
					t.Fatalf("extra machine trap reached strict object emission: %d bytes, %v", len(object), err)
				}
				for _, want := range []string{"verified profile: 1 bodies are not proven", "trap-domain obligation", "rare"} {
					if !strings.Contains(err.Error(), want) {
						t.Errorf("refusal lacks %q: %v", want, err)
					}
				}
			}
		})
	}
}

func TestExplicitAsmTrapVerdictsReachCallers(t *testing.T) {
	comp := New().WithSource("rare.oak", "rare: (b: u32) -> u32 = b\ncaller: (b: u32) -> u32 = rare(b)\n").
		WithAsmUnit("rare.arm64.oakasm", rareTrapUnit).
		WithTarget(target.Target{OS: target.OSFreestanding, Arch: target.ArchArm64}).
		WithNativeBodies().WithVerifyFresh()
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	if v := model.NativeVerdicts["rare"]; v.Kind != asm.VerdictWitnessed {
		t.Fatalf("explicit unit's failed trap obligation was lost: %+v", v)
	}
	if v := model.NativeVerdicts["caller"]; v.Kind != asm.VerdictProven || len(v.Callees) != 1 || v.Callees[0] != "rare" {
		t.Fatalf("caller must retain its conditional proof and dependency: %+v", v)
	}
	if via := provenRestingOnUnproven(model.NativeVerdicts)["caller"]; via != "rare" {
		t.Fatalf("caller admitted through unproved explicit unit: via %q", via)
	}
	image, err := comp.WithVerifiedProfile().EmitNativeObject(asm.ELF).Get()
	if err == nil || len(image) != 0 || !strings.Contains(err.Error(), "caller (via rare)") {
		t.Fatalf("strict profile did not close over explicit unit: %d bytes, %v", len(image), err)
	}
}

func TestE2EVerifiedProfileRefusesAsmWithoutSource(t *testing.T) {
	comp := New().WithSource("rare.oak", "rare: (b: u32) -> u32\n").
		WithAsmUnit("rare.arm64.oakasm", rareTrapUnit).
		WithTarget(target.Target{OS: target.OSFreestanding, Arch: target.ArchArm64})
	if object, err := comp.EmitNativeObject(asm.ELF).Get(); err != nil || len(object) == 0 {
		t.Fatalf("ordinary unit without fallback must remain available: %v", err)
	}
	object, err := comp.WithVerifiedProfile().EmitNativeObject(asm.ELF).Get()
	if err == nil || len(object) != 0 || !strings.Contains(err.Error(), "no Oak fallback body") {
		t.Fatalf("unit without source specification bypassed strict profile: %d bytes, %v", len(object), err)
	}
}
