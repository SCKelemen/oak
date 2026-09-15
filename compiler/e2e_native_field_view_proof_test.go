package compiler

// A view or span of an array field of a record span's element passed to a
// callee — `total(view(&stages[k].coeffs))`, `fill(span(&stages[k].state), v)`
// (docs/spec/50-borrowing.md §2) — is decided by the verifier: the callee's
// span parameter is an alias of the field's leaf memory (`stages.coeffs`)
// at the linear offset k·N with the field's length, on the asm side (the
// element address plus the field offset, the constant length) and the Oak
// side alike (docs/spec/94-assembler.md §8). Before this the callers were
// trusted: "the span argument xs is not one of the caller's span parameters
// passed whole (its base is not a frame address)".

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

const nativeFieldViewProgram = `Stage: type = struct { coeffs: [5]u32, state: [2]u32 }

total: (xs: []u32): u32 {
  acc: u32 = u32(0)
  i: u32 = u32(0)
  while i < len(xs) {
    acc = acc + xs[i]
    i = i + u32(1)
  }
  acc
}

fill: (ys: [*]u32, v: u32): u32 {
  i: u32 = u32(0)
  while i < len(ys) {
    ys[i] = v + i
    i = i + u32(1)
  }
  i
}

sum_coeffs: (stages: []Stage, k: u32): u32 {
  k < len(stages) ? { total(view(&stages[k].coeffs)) } | { u32(0) }
}

reset_state: (stages: [*]Stage, k: u32, v: u32): u32 {
  k < len(stages) ? { fill(span(&stages[k].state), v) } | { u32(0) }
}

first_state: (stages: []Stage, k: u32): u32 {
  k < len(stages) ? { stages[k].state[0] + stages[k].state[1] } | { u32(0) }
}

main: (): i32 {
  stages: [2]Stage = [Stage { coeffs: [1, 2, 3, 4, 5], state: [0, 0] }, Stage { coeffs: [1, 1, 1, 1, 1], state: [0, 0] }]
  a: u32 = sum_coeffs(view(&stages), u32(0))
  b: u32 = sum_coeffs(view(&stages), u32(1))
  n: u32 = reset_state(span(&stages), u32(1), u32(7))
  c: u32 = first_state(view(&stages), u32(1))
  (a == u32(15) && b == u32(5) && n == u32(2) && c == u32(15)) ? 42 | 1
}
`

func TestE2ENativeFieldViewCallsProven(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("field_view.oak", nativeFieldViewProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "field_view", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"total", "fill", "sum_coeffs", "reset_state", "first_state"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") {
			t.Errorf("%s was not proven; diagnostics:\n%s", fn, joined)
		}
	}
	// The callee is taken at its Oak body through the field alias, and the
	// writer's span memory is the record span's leaf memory.
	if !strings.Contains(joined, "asm unit sum_coeffs: proven equal to its Oak body at the bit level") || !strings.Contains(joined, "(callees taken at their Oak bodies: total)") {
		t.Errorf("sum_coeffs must be proven through total's body; diagnostics:\n%s", joined)
	}
	if !strings.Contains(joined, "asm unit reset_state: proven") || !strings.Contains(joined, "span memory it writes (stages.state)") {
		t.Errorf("reset_state's writes through the field span must be decided; diagnostics:\n%s", joined)
	}
	if strings.Contains(joined, "mismatch") {
		t.Errorf("the verifier found a mismatch:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "field_view_c", New().WithSource("field_view.oak", nativeFieldViewProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
