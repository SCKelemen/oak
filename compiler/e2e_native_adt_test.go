package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Tagged unions and match through the native backend
// (docs/spec/94-assembler.md §9, tenth increment): an ADT is the synthetic
// record `semir.TaggedUnionLayout` places (the u32 tag, the payload union),
// so it lives in the frame and crosses calls under the composite rules;
// `.Variant(payload)` stores tag and payload, `match` loads the tag once
// and compares it per arm, binding payloads as locals. The C backend's
// realization of the same program is the oracle.
const nativeADTProgram = `
Shape: type =
  | Circle: i32
  | Square: i32
  | Empty

Point: type = struct {
  x: i32
  y: i32
}

Hit: type =
  | At: Point
  | Miss

area2: (s: Shape): i32 = s ?
  | .Circle(r) -> r * 3
  | .Square(w) -> w * w
  | .Empty -> 0

// A record payload bound in an arm, with a wildcard arm.
score: (h: Hit) -> i32 = h ?
  | .At(p) -> 10 + p.x * p.y
  | _ -> 9

// An ADT built and returned by a function, matched by the caller; the
// scrutinee is the call itself.
classify: (n: i32) -> Shape = n < 0 ? .Empty | (n == 0 ? .Square(1) | .Circle(n))

// Statement-position match with a bound payload updating a local.
tally: (h: Hit, k: i32) -> i32 {
  acc: i32 = k
  h ?
    | .At(p) -> { acc = acc + p.x + p.y }
    | .Miss -> { acc = acc - 1 }
  acc
}

// A literal-pattern match over a scalar.
name_len: (n: u32) -> u32 = n ?
  | 1 -> u32(3)
  | 2 -> u32(5)
  | _ -> u32(0)

main: (): i32 {
  c: Shape = .Circle(5)
  q: Shape = .Square(4)
  e: Shape = .Empty
  assert(area2(c) + area2(q) + area2(e) == 31)
  h: Hit = .At(Point { x: 3, y: 4 })
  m: Hit = .Miss
  assert(score(h) == 22)
  assert(score(m) == 9)
  assert(area2(classify(7)) == 21)
  assert(area2(classify(0)) == 1)
  assert(area2(classify(-2)) == 0)
  assert(tally(h, 10) == 17)
  assert(tally(m, 10) == 9)
  assert(name_len(u32(2)) + name_len(u32(9)) == u32(5))
  e = .Circle(2)
  assert(area2(e) == 6)
  42
}
`

func TestE2ENativeADTs(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("adts.oak", nativeADTProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_adts", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native ADTs: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"area2", "score", "classify", "tally", "name_len", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	for _, fn := range []string{"name_len", "classify", "tally"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") {
			t.Errorf("%s must be proven equal to its Oak body (matches as select chains, union parameters and results as leaf terms); diagnostics:\n%s", fn, joined)
		}
	}
	for _, fn := range []string{"area2", "score"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") && !strings.Contains(joined, "asm unit "+fn+": agrees") {
			t.Errorf("%s must be proven or witnessed against its Oak body; diagnostics:\n%s", fn, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_adts_c", New().WithSource("adts.oak", nativeADTProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_adts_portable", New().WithSource("adts.oak", nativeADTProgram).WithNativeBodies(), "-DOAK_PORTABLE_INTRINSICS"); abnormal || code != 42 {
		t.Fatalf("portable realization: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
