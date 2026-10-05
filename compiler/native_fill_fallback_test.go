package compiler

import (
	"reflect"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/nativegen"
	"github.com/SCKelemen/oak/opt"
)

func TestNativeFillValidationFallbackClonesOnlyRotation(t *testing.T) {
	lane := nativegen.Lane{
		Arch: asm.ArchArm64, UnrollFills: true, RotateLoops: true,
		Strength: true, HoistInvariants: true, Schedule: true, Reallocate: true,
		TrimCalleeSaves: true, ElideRedundantGuards: true, Cleanup: true,
	}
	parent := opt.Identity(lane).
		With(nativegen.TransformUnrollFills, lane, opt.Fact{Proposition: opt.Prop("fill", "source")}).
		With(nativegen.TransformRotate, lane).
		With(nativegen.TransformSchedule, lane).
		With(nativegen.TransformReallocate, lane).
		With(nativegen.TransformTrimCalleeSaves, lane).
		With(nativegen.TransformRedundantGuards, lane).
		With(nativegen.TransformCleanup, lane)
	parent.Body, parent.Key, parent.Cost = "parent body", "parent key", 17
	originalApplied := append([]string(nil), parent.Applied...)
	driver := &nativeDriver{}
	next := driver.ValidationFallback(parent, opt.Verdict{Outcome: opt.Trusted})
	if next == nil {
		t.Fatal("missing blocked-fill fallback")
	}
	want := lane
	want.RotateLoops = false
	if !reflect.DeepEqual(next.Config, want) || next.Body != nil || next.Key != "" || next.Cost != 0 {
		t.Fatalf("fallback changed more than rotation or inherited an artifact: %+v", next)
	}
	if next.Has(nativegen.TransformRotate) || !next.Has(nativegen.TransformSchedule) || !next.Has(nativegen.TransformCleanup) {
		t.Fatalf("wrong transform provenance: %v", next.Applied)
	}
	next.Applied[0] = "mutated"
	next.Facts[0].Proposition.Terms[0] = "mutated"
	if !reflect.DeepEqual(parent.Applied, originalApplied) || parent.Facts[0].Proposition.Terms[0] != "source" || !reflect.DeepEqual(parent.Config, lane) || parent.Body != "parent body" {
		t.Fatal("fallback mutated its parent's plan, facts, or body")
	}
	if driver.ValidationFallback(next, opt.Verdict{Outcome: opt.Trusted}) != nil {
		t.Fatal("fallback proposed recursively without rotation")
	}
}

func TestNativeFillValidationFallbackScope(t *testing.T) {
	for _, tc := range []struct {
		name                  string
		arch                  string
		fill, rotate, applied bool
		outcome               opt.Outcome
		want                  bool
	}{
		{"trusted fill", asm.ArchArm64, true, true, true, opt.Trusted, true},
		{"witnessed fill", asm.ArchArm64, true, true, true, opt.Witnessed, true},
		{"proved", asm.ArchArm64, true, true, true, opt.Proven, false},
		{"mismatch", asm.ArchArm64, true, true, true, opt.Mismatch, false},
		{"refused", asm.ArchArm64, true, true, true, opt.Refused, false},
		{"other lane", asm.ArchRV64, true, true, true, opt.Trusted, false},
		{"implicit lane", "", true, true, true, opt.Trusted, false},
		{"not a fill", asm.ArchArm64, false, true, true, opt.Trusted, false},
		{"not rotated", asm.ArchArm64, true, false, true, opt.Trusted, false},
		{"missing transform", asm.ArchArm64, true, true, false, opt.Trusted, false},
	} {
		t.Run(tc.name, func(t *testing.T) {
			lane := nativegen.Lane{Arch: tc.arch, UnrollFills: tc.fill, RotateLoops: tc.rotate}
			candidate := opt.Identity(lane).With(nativegen.TransformUnrollFills, lane)
			if tc.applied {
				candidate = candidate.With(nativegen.TransformRotate, lane)
			}
			if got := (&nativeDriver{}).ValidationFallback(candidate, opt.Verdict{Outcome: tc.outcome}); (got != nil) != tc.want {
				t.Fatalf("offered=%v, want %v", got != nil, tc.want)
			}
		})
	}
	if (&nativeDriver{}).ValidationFallback(nil, opt.Verdict{Outcome: opt.Trusted}) != nil {
		t.Fatal("nil candidate proposed a fallback")
	}
}
