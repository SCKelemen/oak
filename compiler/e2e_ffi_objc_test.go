package compiler

import (
	"runtime"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

// Objective-C message sends (docs/spec/92-ffi.md section 2.12, ml roadmap
// D5): `c.msg_send[(params) -> ret](receiver, selector, args...)` inside an
// unsafe block calls objc_msgSend under the bracketed signature, with the
// receiver and selector as the two leading pointers. Executed against
// Foundation through the `objc` package and the manifest's `framework`
// line (83-modules.md section 4.6).

func skipWithoutObjC(t *testing.T) {
	t.Helper()
	if runtime.GOOS != "darwin" || runtime.GOARCH != "arm64" {
		t.Skip("the message-send test needs the Objective-C runtime on an arm64 Darwin host")
	}
}

// [[NSString alloc] initWithUTF8String:"oak"] has length 3;
// [NSNumber numberWithInt:41] answers intValue 41; [NSValue valueWithRange:]
// returns its NSRange by value through the same entry point.
func TestE2EMessageSendFoundation(t *testing.T) {
	skipWithoutObjC(t)
	const program = `package main
import("objc")

Range: type = struct { location: u64, length: u64 }

main: (): i32 {
  string_class: c.Ptr = objc.objc_class(str_bytes("NSString\0"))
  number_class: c.Ptr = objc.objc_class(str_bytes("NSNumber\0"))
  value_class: c.Ptr = objc.objc_class(str_bytes("NSValue\0"))
  alloc: c.Ptr = objc.objc_sel(str_bytes("alloc\0"))
  init_utf8: c.Ptr = objc.objc_sel(str_bytes("initWithUTF8String:\0"))
  length_sel: c.Ptr = objc.objc_sel(str_bytes("length\0"))
  number_with_int: c.Ptr = objc.objc_sel(str_bytes("numberWithInt:\0"))
  int_value: c.Ptr = objc.objc_sel(str_bytes("intValue\0"))
  value_with_range: c.Ptr = objc.objc_sel(str_bytes("valueWithRange:\0"))
  range_value: c.Ptr = objc.objc_sel(str_bytes("rangeValue\0"))
  text: [4]u8 = [4]u8{ 111, 97, 107, 0 }
  oak: []u8 = view(&text)
  length: u64 = 0
  answer: i32 = 0
  location: u64 = 0
  span_length: u64 = 0
  unsafe {
    fresh: c.Ptr = c.msg_send[() -> c.Ptr](string_class, alloc)
    s: c.Ptr = c.msg_send[(c.String) -> c.Ptr](fresh, init_utf8, c.cstr(oak))
    length = u64(c.msg_send[() -> c.UInt64](s, length_sel))
    n: c.Ptr = c.msg_send[(c.Int) -> c.Ptr](number_class, number_with_int, c.Int(i32(41)))
    answer = i32(c.msg_send[() -> c.Int](n, int_value)) + i32(1)
    r: Range = Range { location: u64(7), length: u64(9) }
    boxed: c.Ptr = c.msg_send[(Range) -> c.Ptr](value_class, value_with_range, r)
    back: Range = c.msg_send[() -> Range](boxed, range_value)
    location = back.location
    span_length = back.length
  }
  assert_eq(length, u64(3))
  assert_eq(answer, i32(42))
  assert_eq(location, u64(7))
  assert_eq(span_length, u64(9))
  42
}
`
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/objc_send\noak 0.1.0\nframework Foundation\n",
		"main.oak": program,
	})
	if code := buildLinkedAndRun(t, New().WithPackageDir(root)); code != 42 {
		t.Fatalf("exit=%d", code)
	}
}

// The emitted C names objc_msgSend once, casts it per send to the receiver,
// selector, and declared parameters, and carries the arm64 guard.
func TestMessageSendEmission(t *testing.T) {
	const program = `
main: (): i32 {
  r: c.Ptr = c.null()
  s: c.Ptr = c.null()
  n: i32 = 0
  unsafe {
    n = i32(c.msg_send[(c.Int, c.Ptr) -> c.Int](r, s, c.Int(i32(1)), c.null()))
    c.msg_send[() -> ()](r, s)
  }
  n
}
`
	out, err := New().WithSource("send.oak", program).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"extern void objc_msgSend(void);",
		"#if !defined(__aarch64__) && !defined(__arm64__)",
		"(( int (*)( void *, void *, int, void * ) )( objc_msgSend ))(",
		"(( void (*)( void *, void * ) )( objc_msgSend ))(",
	} {
		if !strings.Contains(out, want) {
			t.Fatalf("generated C lacks %q:\n%s", want, out)
		}
	}
	if strings.Count(out, "extern void objc_msgSend(void);") != 1 {
		t.Fatalf("objc_msgSend must be declared exactly once:\n%s", out)
	}
	plain, err := New().WithSource("plain.oak", "main: (): i32 = 42\n").EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(plain, "objc_msgSend") {
		t.Fatal("a program without message sends must not mention objc_msgSend")
	}
}

func TestMessageSendRejections(t *testing.T) {
	cases := []struct {
		name, src, code string
	}{
		{"outside unsafe", `
main: (): i32 {
  r: c.Ptr = c.null()
  s: c.Ptr = c.null()
  n: i32 = i32(c.msg_send[() -> c.Int](r, s))
  n
}
`, "OAK-F0115"},
		{"receiver and selector missing", `
main: (): i32 {
  r: c.Ptr = c.null()
  n: i32 = 0
  unsafe { n = i32(c.msg_send[() -> c.Int](r)) }
  n
}
`, "OAK-F0115"},
		{"brackets left out", `
main: (): i32 {
  r: c.Ptr = c.null()
  s: c.Ptr = c.null()
  n: i32 = 0
  unsafe { n = i32(c.msg_send(r, s)) }
  n
}
`, "OAK-F0115"},
		{"signature with an Oak scalar", `
main: (): i32 {
  r: c.Ptr = c.null()
  s: c.Ptr = c.null()
  n: i32 = 0
  unsafe { n = i32(c.msg_send[(u32) -> c.Int](r, s, u32(1))) }
  n
}
`, "OAK-F0113"},
		{"argument type mismatch", `
main: (): i32 {
  r: c.Ptr = c.null()
  s: c.Ptr = c.null()
  n: i32 = 0
  unsafe { n = i32(c.msg_send[(c.Int) -> c.Int](r, s, c.Int64(i64(1)))) }
  n
}
`, ""},
		{"too many arguments", `
main: (): i32 {
  r: c.Ptr = c.null()
  s: c.Ptr = c.null()
  n: i32 = 0
  unsafe { n = i32(c.msg_send[() -> c.Int](r, s, c.Int(i32(1)))) }
  n
}
`, ""},
		{"receiver not a pointer", `
main: (): i32 {
  s: c.Ptr = c.null()
  n: i32 = 0
  unsafe { n = i32(c.msg_send[() -> c.Int](c.Int(i32(1)), s)) }
  n
}
`, ""},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			_, err := New().WithSource(c.name+".oak", c.src).EmitC().Get()
			if err == nil {
				t.Fatalf("expected a rejection")
			}
			if c.code != "" && !strings.Contains(err.Error(), c.code) {
				t.Fatalf("expected %s, got %v", c.code, err)
			}
		})
	}
}

// A send inside a function that forbids every effect fails closed, like a
// call through a function value whose effects nothing declares.
func TestMessageSendForbidsFailsClosed(t *testing.T) {
	const program = `
send: (r: c.Ptr, s: c.Ptr): i32 forbids { Os.Syscall } {
  n: i32 = 0
  unsafe { n = i32(c.msg_send[() -> c.Int](r, s)) }
  n
}
main: (): i32 = send(c.null(), c.null())
`
	_, err := New().WithSource("forbid.oak", program).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "OAK-E0103") {
		t.Fatalf("a forbids function reaching a message send must fail closed with OAK-E0103, got %v", err)
	}
}

// Each send records the OAK-B0122 assumption; a strict module needs
// `admit OAK-B0122`, and the assumption stays recorded once admitted.
func TestMessageSendRecordsAssumptionAndStrictAdmits(t *testing.T) {
	const program = `package main

main: (): i32 {
  r: c.Ptr = c.null()
  s: c.Ptr = c.null()
  n: i32 = 0
  unsafe { n = i32(c.msg_send[() -> c.Int](r, s)) }
  n
}
`
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/app\noak 0.1.0\nprofile strict\n",
		"main.oak": program,
	})
	_, err := New().WithPackageDir(root).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "OAK-B0122") {
		t.Fatalf("a strict module sending a message must be rejected with OAK-B0122, got %v", err)
	}
	root = writeModule(t, map[string]string{
		"oak.mod":  "module example.com/app\noak 0.1.0\nprofile strict\nadmit OAK-B0122\n",
		"main.oak": program,
	})
	var recorded []*diagnostic.Diagnostic
	comp := New().WithPackageDir(root).WithDiagnosticSink(func(d *diagnostic.Diagnostic) { recorded = append(recorded, d) })
	if _, err := comp.EmitC().Get(); err != nil {
		t.Fatalf("admit OAK-B0122 must let the strict module send messages: %v", err)
	}
	found := false
	for _, d := range recorded {
		if d.Code == "OAK-B0122" && strings.Contains(d.PlainText(), "message send contract assumed") {
			found = true
		}
	}
	if !found {
		t.Fatal("the OAK-B0122 assumption must remain recorded after admission")
	}
}

// The interpreter has no Objective-C runtime; the send is rejected before
// its arguments are evaluated (c.null is itself native-only).
func TestMessageSendInterpreterRejects(t *testing.T) {
	const program = `
main: (): i32 {
  n: i32 = 0
  unsafe { n = i32(c.msg_send[() -> c.Int](c.null(), c.null())) }
  n
}
`
	model, err := New().WithSource("interp.oak", program).Check().Get()
	if err != nil {
		t.Fatalf("check failed: %v", err)
	}
	env := object.NewEnvironment()
	env.SetArithmeticWidths(model.TypeChecker.ArithmeticType)
	if result := evaluator.Eval(model.Tree.Root, env); result != nil {
		if e, isErr := result.(*object.Error); isErr {
			t.Fatalf("interpreter error evaluating program: %s", e.Message)
		}
	}
	p := parser.New(layout.New(scanner.New("main()")))
	call := p.ParseProgram()
	result := evaluator.Eval(call, env)
	evalErr, isErr := result.(*object.Error)
	if !isErr || !strings.Contains(evalErr.Message, "c.msg_send requires the native backend") {
		t.Fatalf("expected the interpreter to reject c.msg_send, got %s", result.Inspect())
	}
}
