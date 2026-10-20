package compiler

import (
	"strings"
	"testing"
)

func TestExplicitInitializerRejectsBeforeCompilation(t *testing.T) {
	for _, src := range []string{
		"x: i32 = ;", "fn f(): i32 { x: i32 = ; x }",
		"fn f(): i32 { x: i32; x = ; x }", "fn f(): () { _ = ; }",
		"fn f(): () { a[0] = ; }", "f: (): i32 = ;", "f := fn(): i32 = ;",
	} {
		t.Run(src, func(t *testing.T) {
			comp := New().WithSource("missing_initializer.oak", src)
			for name, err := range map[string]error{"Parse": comp.Parse().Err(), "Check": comp.Check().Err(), "EmitC": comp.EmitC().Err(), "EmitLean": comp.EmitLean("InitializerTest").Err(), "EmitWasm": comp.EmitWasm().Err()} {
				if err == nil || !strings.Contains(err.Error(), "parse failed") || !strings.Contains(err.Error(), "expected value expression after =") {
					t.Errorf("%s must refuse at parsing: %v", name, err)
				}
			}
		})
	}
}

func TestExplicitInitializerRuntimeControls(t *testing.T) {
	for _, tc := range []struct {
		name, src string
		want      int
	}{
		{"present", "main: (): i32 { x: i32 = 1; x }", 1},
		{"absent", "main: (): i32 { x: i32; x }", 0},
		{"assignment", "main: (): i32 { x: i32; x = 2; x }", 2},
		{"unit_body", "main: (): () = {}", 0},
	} {
		t.Run(tc.name, func(t *testing.T) {
			comp := New().WithSource(tc.name+".oak", tc.src)
			if err := comp.Check().Err(); err != nil {
				t.Fatalf("valid control failed checking: %v", err)
			}
			if _, err := comp.EmitC().Get(); err != nil {
				t.Fatalf("valid control failed C emission: %v", err)
			}
			if code, abnormal := buildAndRun(t, "initializer_"+tc.name, tc.src); abnormal || code != tc.want {
				t.Fatalf("exit=(%d, abnormal=%v), want %d", code, abnormal, tc.want)
			}
		})
	}
}
