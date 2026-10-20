package compiler

import (
	"strings"
	"testing"
)

func TestRequiredOperandRejectsBeforeCompilation(t *testing.T) {
	for _, src := range []string{
		"x: i32 = 1 |> ;", "fn f(): i32 { x: i32 = 1 |> ; x }",
		"fn f(): i32 { 1 + ; 7 }", "fn f(): i32 { -; 7 }",
		"bitwise: (a: u32, b: u32): u32 = a & ;",
	} {
		t.Run(src, func(t *testing.T) {
			comp := New().WithSource("missing_operand.oak", src)
			for name, err := range map[string]error{"Parse": comp.Parse().Err(), "Check": comp.Check().Err(), "EmitC": comp.EmitC().Err(), "EmitLean": comp.EmitLean("OperandTest").Err(), "EmitWasm": comp.EmitWasm().Err()} {
				if err == nil || !strings.Contains(err.Error(), "parse failed") || !strings.Contains(err.Error(), "expected operand after") {
					t.Errorf("%s must refuse at parsing: %v", name, err)
				}
			}
		})
	}
}

func TestRequiredOperandRuntimeControls(t *testing.T) {
	for _, tc := range []struct {
		name, src string
		want      int
	}{
		{"pipeline", "fn id(a: i32): i32 { a }\nmain: (): i32 { x: i32 = 1 |> id; x }", 1},
		{"absent_initializer", "main: (): i32 { x: i32; x }", 0},
	} {
		t.Run(tc.name, func(t *testing.T) {
			comp := New().WithSource(tc.name+".oak", tc.src)
			if err := comp.Check().Err(); err != nil {
				t.Fatalf("valid control failed checking: %v", err)
			}
			if _, err := comp.EmitC().Get(); err != nil {
				t.Fatalf("valid control failed C emission: %v", err)
			}
			if code, abnormal := buildAndRun(t, "operand_"+tc.name, tc.src); abnormal || code != tc.want {
				t.Fatalf("exit=(%d, abnormal=%v), want %d", code, abnormal, tc.want)
			}
		})
	}
}
