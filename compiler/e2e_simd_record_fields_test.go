package compiler

// The SIMD pilot's two ergonomics gaps closed (docs/spec/93-simd.md §1.2a,
// docs/spec/50-borrowing.md §2): a record may hold a fixed vector field —
// placed as its 16-byte lane array, loaded and stored whole by the native
// lane (`ldr`/`str q`) — and `view(&s[i].field)` / `span(&s[i].field)`
// borrow an owned-array field of a span, view, or array element. The C
// backend, the interpreter, and the native lane agree on both programs.

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

const elementFieldViewProgram = `Stage: type = struct { coeffs: [5]f32, state: [2]f32 }

total: (xs: []f32): f32 {
  acc: f32 = 0.0
  i: u32 = u32(0)
  while i < len(xs) {
    acc = acc + xs[i]
    i = i + u32(1)
  }
  acc
}

fill: (ys: [*]f32, v: f32): u32 {
  i: u32 = u32(0)
  while i < len(ys) {
    ys[i] = v + f32_round_u32(i)
    i = i + u32(1)
  }
  i
}

sum_coeffs: (stages: []Stage, k: u32): f32 {
  k < len(stages) ? { total(view(&stages[k].coeffs)) } | { 0.0 }
}

reset_state: (stages: [*]Stage, k: u32, v: f32): u32 {
  k < len(stages) ? { fill(span(&stages[k].state), v) } | { u32(0) }
}

main: (): i32 {
  stages: [2]Stage = [Stage { coeffs: [1.0, 2.0, 3.0, 4.0, 5.0], state: [0.0, 0.0] }, Stage { coeffs: [1.0, 1.0, 1.0, 1.0, 1.0], state: [0.0, 0.0] }]
  a: f32 = sum_coeffs(view(&stages), u32(0))
  b: f32 = sum_coeffs(view(&stages), u32(1))
  n: u32 = reset_state(span(&stages), u32(1), 7.0)
  own: []f32 = view(&stages[1].state)
  c: f32 = total(own)
  (a == 15.0 && b == 5.0 && c == 15.0 && n == u32(2)) ? 42 | 1
}
`

const vectorFieldRecordProgram = `Biquad: type = struct { b0: simd.F32x4, b1: simd.F32x4, gain: f32 }

// A record of vectors read through a view of records: the native lane
// loads each vector field whole (ldr q).
run: (qs: []Biquad, k: u32, x: simd.F32x4): f32 {
  k < len(qs) ? {
    y: simd.F32x4 = simd.add_f32x4(simd.mul_f32x4(qs[k].b0, x), qs[k].b1)
    simd.extract_f32x4(y, 0) * qs[k].gain
  } | { 0.0 }
}

// A record of vectors written in place through a span.
scale: (qs: [*]Biquad, k: u32, f: simd.F32x4): u32 {
  k < len(qs) ? {
    qs[k].b0 = simd.mul_f32x4(qs[k].b0, f)
    qs[k].gain = qs[k].gain * 2.0
    u32(1)
  } | { u32(0) }
}

main: (): i32 {
  cs: [4]f32 = [2.0, 2.0, 2.0, 2.0]
  ds: [4]f32 = [1.0, 1.0, 1.0, 1.0]
  xs: [4]f32 = [3.0, 3.0, 3.0, 3.0]
  q: Biquad = Biquad { b0: simd.load_f32x4(view(&cs), u32(0)), b1: simd.load_f32x4(view(&ds), u32(0)), gain: 0.5 }
  qs: [2]Biquad = [q, Biquad { b0: simd.load_f32x4(view(&ds), u32(0)), b1: simd.load_f32x4(view(&ds), u32(0)), gain: 1.0 }]
  x: simd.F32x4 = simd.load_f32x4(view(&xs), u32(0))
  a: f32 = run(view(&qs), u32(0), x)   // (2*3+1)*0.5 = 3.5
  b: f32 = run(view(&qs), u32(1), x)   // (1*3+1)*1 = 4
  n: u32 = scale(span(&qs), u32(0), x)  // b0 = 6, gain = 1
  c: f32 = run(view(&qs), u32(0), x)   // (6*3+1)*1 = 19
  g: f32 = qs[0].gain
  (a == 3.5 && b == 4.0 && c == 19.0 && n == u32(1) && g == 1.0) ? 42 | 1
}
`

func TestE2EElementFieldViews(t *testing.T) {
	if code, abnormal := buildAndRun(t, "element_field_views", elementFieldViewProgram); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if got := interpretChecked(t, elementFieldViewProgram); got != 42 {
		t.Fatalf("interpreter: main = %d, want 42", got)
	}
}

func TestE2EVectorFieldRecords(t *testing.T) {
	if code, abnormal := buildAndRun(t, "vector_field_records", vectorFieldRecordProgram); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	// The portable lane loops place the lane array exactly as NEON does.
	if _, code, abnormal := buildAndRunOutput(t, "vector_field_records_portable", vectorFieldRecordProgram, "-DOAK_PORTABLE_INTRINSICS"); abnormal || code != 42 {
		t.Fatalf("portable lowering: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if got := interpretChecked(t, vectorFieldRecordProgram); got != 42 {
		t.Fatalf("interpreter: main = %d, want 42", got)
	}
}

// nativeInfos builds and runs a program through the native backend and
// returns its exit and the native diagnostics.
func nativeInfos(t *testing.T, name, src string) (int, bool, string) {
	t.Helper()
	var infos []string
	comp := New().WithSource(name+".oak", src).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, name, comp)
	return code, abnormal, strings.Join(infos, "\n")
}

func TestE2ENativeElementFieldViews(t *testing.T) {
	requireArm64Host(t)
	code, abnormal, joined := nativeInfos(t, "native_element_field_views", elementFieldViewProgram)
	if abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	// The view of a span element's array field is lowered natively: the
	// field's address rebased into the view's own register, the constant
	// length, the callee's elements addressed through it.
	for _, fn := range []string{"sum_coeffs", "reset_state", "total", "fill", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	if strings.Contains(joined, "mismatch") {
		t.Errorf("the verifier found a mismatch:\n%s", joined)
	}
}

func TestE2ENativeVectorFieldRecords(t *testing.T) {
	requireArm64Host(t)
	code, abnormal, joined := nativeInfos(t, "native_vector_field_records", vectorFieldRecordProgram)
	if abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	// run and scale carry a vector in their signatures (the suffixed entry);
	// their record elements' vector fields move whole through q registers.
	for _, fn := range []string{"run_neon_abi", "scale_neon_abi", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	if !strings.Contains(joined, "asm unit main: proven") {
		t.Errorf("main was not proven; diagnostics:\n%s", joined)
	}
	if strings.Contains(joined, "mismatch") {
		t.Errorf("the verifier found a mismatch:\n%s", joined)
	}
}

// A record holding a vector is not passed or returned by value on the
// native lane (AAPCS64 flattens the lane array into the composite's
// members): the function stays with the C backend, reported as such.
const vectorRecordByValueProgram = `
Biquad: type = struct { b0: simd.F32x4, b1: simd.F32x4, gain: f32 }

step: (q: Biquad, x: simd.F32x4): simd.F32x4 = simd.add_f32x4(simd.mul_f32x4(q.b0, x), q.b1)

main: (): i32 {
  cs: [4]f32 = [4]f32{2.0, 2.0, 2.0, 2.0}
  ds: [4]f32 = [4]f32{1.0, 1.0, 1.0, 1.0}
  xs: [4]f32 = [4]f32{3.0, 3.0, 3.0, 3.0}
  q: Biquad = Biquad { b0: simd.load_f32x4(view(&cs), 0), b1: simd.load_f32x4(view(&ds), 0), gain: 0.5 }
  y: simd.F32x4 = step(q, simd.load_f32x4(view(&xs), 0))
  simd.extract_f32x4(y, 0) == 7.0 ? 42 | 1
}
`

func TestE2ENativeVectorRecordByValueFallsBack(t *testing.T) {
	requireArm64Host(t)
	code, abnormal, joined := nativeInfos(t, "native_vector_record_by_value", vectorRecordByValueProgram)
	if abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	if !strings.Contains(joined, "step left to the C backend (parameter q: Biquad holds a vector (by value))") {
		t.Errorf("step must be left to the C backend for its by-value vector record; diagnostics:\n%s", joined)
	}
	if !strings.Contains(joined, "asm unit main: proven") {
		t.Errorf("main was not proven; diagnostics:\n%s", joined)
	}
}
