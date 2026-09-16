package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// A payload binder belongs to its arm (asm/verify.go, matchArms): the
// verifier binds it where the arm's body is lowered, after the locals the
// arms fork from are restored, and drops it when the arm is done. Binding
// it earlier lost the payload of every match after the first in a body,
// because the restore put the name back to what it held before — for a
// reused binder, the previous match's last arm. The Oak model then read
// the second match as its fallback and refused the body, which fails the
// native build: `two` was refuted with the Oak term `3*r`, the machine's
// `3*r + w*w` being right.
const nativeUnionBinderProgram = `
Shape: type =
  | Circle: i32
  | Square: i32
  | Empty

area: (s: Shape): i32 = s ?
  | .Circle(x) -> x * 3
  | .Square(x) -> x * x
  | .Empty -> 0

// Two matches in one body, the same binder name in both.
two: (r: i32, w: i32): i32 {
  c: Shape = .Circle(r)
  q: Shape = .Square(w)
  a: i32 = c ?
    | .Circle(x) -> x * 3
    | .Square(x) -> x * x
    | .Empty -> 0
  b: i32 = q ?
    | .Circle(x) -> x * 3
    | .Square(x) -> x * x
    | .Empty -> 0
  a + b
}

// The same scrutinee twice, the second arm body different.
twice: (r: i32): i32 {
  c: Shape = .Circle(r)
  a: i32 = c ?
    | .Circle(x) -> x * 3
    | .Square(x) -> x * x
    | .Empty -> 0
  b: i32 = c ?
    | .Circle(x) -> x * 5
    | .Square(x) -> x * x
    | .Empty -> 0
  a + b
}

main: (): i32 {
  // two(2, 3) = 6 + 9 = 15, twice(2) = 6 + 10 = 16, area(.Square(4)) = 16.
  // 15 + 16 + 16 = 47.
  two(2, 3) + twice(2) + area(.Square(4))
}
`

func TestE2ENativeUnionArmBinders(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("union_binder.oak", nativeUnionBinderProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_union_binder", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 47 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 47\n%s", code, abnormal, joined)
	}
	// A refusal fails the build, so reaching here says the bodies were not
	// refuted; the verdicts must also not be a false mismatch.
	if strings.Contains(joined, "disagrees") {
		t.Errorf("a false mismatch over a match arm's binder:\n%s", joined)
	}
	for _, fn := range []string{"two", "twice", "area"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") && !strings.Contains(joined, "asm unit "+fn+": agrees with its Oak body") {
			t.Errorf("%s must be judged against its Oak body, not trusted; diagnostics:\n%s", fn, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_union_binder_c", New().WithSource("union_binder.oak", nativeUnionBinderProgram)); abnormal || code != 47 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 47", code, abnormal)
	}
}
