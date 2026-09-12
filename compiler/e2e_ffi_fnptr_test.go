package compiler

import (
	"runtime"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Calls through a foreign function pointer (docs/spec/92-ffi.md section
// 2.10, ml roadmap D3): `f: c.Fn[(params) -> ret] = c.fn_at(p)` inside an
// unsafe block names the function at a pointer with a declared boundary
// signature, and `f(args)` is checked and lowered exactly like a call to an
// extern binding of that signature. Executed against libc through dlsym.
const dlHelpers = `
dlopen: (path: c.Ptr, mode: c.Int): c.Ptr = c.extern("dlopen")
dlsym: (handle: c.Ptr, name: c.String): c.Ptr = c.extern("dlsym")
`

func skipWithoutDlsym(t *testing.T) {
	t.Helper()
	if runtime.GOOS != "darwin" && runtime.GOOS != "linux" {
		t.Skip("the function-pointer test needs dlopen/dlsym on a POSIX host")
	}
}

// strlen resolved at runtime and called through the pointer on a c.cstr
// view; time(2) called through a pointer with c.out; the bindings live in
// the unsafe block and every call passes the annotated argument forms.
func TestE2EForeignFunctionPointerCalls(t *testing.T) {
	skipWithoutDlsym(t)
	src := dlHelpers + `
main: (): i32 {
  handle: c.Ptr = dlopen(c.null(), c.Int(i32(2)))
  strlen_ptr: c.Ptr = dlsym(handle, c.String("strlen"))
  time_ptr: c.Ptr = dlsym(handle, c.String("time"))
  text: [6]u8 = [6]u8{ 104, 101, 108, 108, 111, 0 }
  hello: []u8 = view(&text)
  length: u64 = 0
  seconds: i64 = 0
  written: i64 = 0
  unsafe {
    c_strlen: c.Fn[(c.String) -> c.UInt64] = c.fn_at(strlen_ptr)
    length = u64(c_strlen(c.cstr(hello)))
    length = length + u64(c_strlen(c.cstr("ab\0")))
    c_time: c.Fn[(c.Ptr) -> c.Int64] = c.fn_at(time_ptr)
    slot: c.Int64 = c.Int64(i64(0))
    returned: c.Int64 = c_time(c.out(slot))
    seconds = i64(slot)
    written = i64(returned)
  }
  assert_eq(length, u64(7))
  assert(seconds > i64(1600000000) && seconds == written)
  42
}
`
	_, code, abnormal := buildAndRunFrom(t, "ffi_fnptr", New().WithSource("ffi_fnptr.oak", src))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

// c.fn_at of a NULL pointer traps at the conversion, so a call through the
// binding never dereferences NULL.
func TestE2EForeignFunctionNullTraps(t *testing.T) {
	skipWithoutDlsym(t)
	src := `
main: (): i32 {
  p: c.Ptr = c.null()
  r: i32 = 0
  unsafe {
    f: c.Fn[(c.Int) -> c.Int] = c.fn_at(p)
    r = i32(f(c.Int(i32(1))))
  }
  r
}
`
	_, code, abnormal := buildAndRunFrom(t, "ffi_fnptr_null", New().WithSource("ffi_fnptr_null.oak", src))
	if !abnormal && code == 0 {
		t.Fatalf("expected c.fn_at of NULL to trap, got a clean exit")
	}
}

// The form and the type are admitted in one place each: c.fn_at as the
// initializer of an annotated local inside unsafe, c.Fn as that local's
// annotation. A call through the binding is checked as an extern call.
func TestForeignFunctionRejections(t *testing.T) {
	cases := []struct {
		name, src, code string
	}{
		{"fn_at outside unsafe", dlHelpers + `
main: (): i32 {
  p: c.Ptr = dlsym(c.null(), c.String("strlen"))
  f: c.Fn[(c.String) -> c.UInt64] = c.fn_at(p)
  0
}
`, "OAK-F0107"},
		{"fn_at as an argument", dlHelpers + `
call_it: (q: c.Ptr): u32 = 0
main: (): i32 {
  p: c.Ptr = dlsym(c.null(), c.String("strlen"))
  n: u32 = 0
  unsafe { n = call_it(c.fn_at(p)) }
  i32(n)
}
`, "OAK-F0107"},
		{"fn_at without a c.Fn annotation", dlHelpers + `
main: (): i32 {
  p: c.Ptr = dlsym(c.null(), c.String("strlen"))
  unsafe {
    f: c.Ptr = c.fn_at(p)
  }
  0
}
`, "OAK-F0113"},
		{"c.Fn as a record field", `
Hooks: type = struct { run: c.Fn[(c.Int) -> c.Int] }
main: (): i32 { 0 }
`, "OAK-F0113"},
		{"c.Fn as a parameter", `
apply: (f: c.Fn[(c.Int) -> c.Int]): c.Int = f(c.Int(i32(1)))
main: (): i32 { 0 }
`, "OAK-F0113"},
		{"c.Fn as a global", `
hook: c.Fn[(c.Int) -> c.Int] = c.null()
main: (): i32 { 0 }
`, "OAK-F0113"},
		{"signature with an Oak scalar", dlHelpers + `
main: (): i32 {
  p: c.Ptr = dlsym(c.null(), c.String("abs"))
  unsafe {
    f: c.Fn[(i32) -> i32] = c.fn_at(p)
  }
  0
}
`, "OAK-F0113"},
		{"wrong argument type at the call", dlHelpers + `
main: (): i32 {
  p: c.Ptr = dlsym(c.null(), c.String("abs"))
  r: i32 = 0
  unsafe {
    f: c.Fn[(c.Int) -> c.Int] = c.fn_at(p)
    r = i32(f(u32(1)))
  }
  r
}
`, "type"},
		{"wrong arity at the call", dlHelpers + `
main: (): i32 {
  p: c.Ptr = dlsym(c.null(), c.String("abs"))
  r: i32 = 0
  unsafe {
    f: c.Fn[(c.Int) -> c.Int] = c.fn_at(p)
    r = i32(f(c.Int(i32(1)), c.Int(i32(2))))
  }
  r
}
`, "expects 1 arguments"},
		{"forbidding function calls through the pointer", dlHelpers + `
quiet: (p: c.Ptr): i32 forbids { Os.Syscall } {
  r: i32 = 0
  unsafe {
    f: c.Fn[(c.Int) -> c.Int] = c.fn_at(p)
    r = i32(f(c.Int(i32(1))))
  }
  r
}
main: (): i32 { quiet(c.null()) }
`, "OAK-E0103"},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			_, err := New().WithSource("reject.oak", tc.src).EmitC().Get()
			if err == nil || !strings.Contains(err.Error(), tc.code) {
				t.Fatalf("expected %s, got %v", tc.code, err)
			}
		})
	}
}

// Naming a function at a pointer is a trust assumption recorded as
// OAK-B0122: the strict profile rejects it without an admission, and
// `admit OAK-B0122` in the manifest accepts it while keeping it recorded.
func TestForeignFunctionRecordsAssumptionAndStrictAdmits(t *testing.T) {
	const program = `package main

dlopen: (path: c.Ptr, mode: c.Int): c.Ptr = c.extern("dlopen")
dlsym: (handle: c.Ptr, name: c.String): c.Ptr = c.extern("dlsym")

probe: (): u64 {
  p: c.Ptr = dlsym(dlopen(c.null(), c.Int(i32(2))), c.String("strlen"))
  n: u64 = 0
  unsafe {
    f: c.Fn[(c.String) -> c.UInt64] = c.fn_at(p)
    n = u64(f(c.cstr("abc\0")))
  }
  n
}

main: (): i32 { i32_bits_u32(u32_trunc_u64(probe())) }
`
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/app\noak 0.1.0\nprofile strict\n",
		"main.oak": program,
	})
	_, err := New().WithPackageDir(root).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "OAK-B0122") {
		t.Fatalf("a strict module naming a foreign function must be rejected with OAK-B0122, got %v", err)
	}
	root = writeModule(t, map[string]string{
		"oak.mod":  "module example.com/app\noak 0.1.0\nprofile strict\nadmit OAK-B0122\n",
		"main.oak": program,
	})
	var recorded []*diagnostic.Diagnostic
	comp := New().WithPackageDir(root).WithDiagnosticSink(func(d *diagnostic.Diagnostic) { recorded = append(recorded, d) })
	if _, err := comp.EmitC().Get(); err != nil {
		t.Fatalf("admit OAK-B0122 must let the strict module call through the pointer: %v", err)
	}
	found := false
	for _, d := range recorded {
		if d.Code == "OAK-B0122" && strings.Contains(d.PlainText(), "foreign function contract assumed") {
			found = true
			if d.Severity != diagnostic.SeverityWarning {
				t.Fatalf("an admitted assumption keeps its severity, got %v", d.Severity)
			}
		}
	}
	if !found {
		t.Fatal("the OAK-B0122 assumption must remain recorded after admission")
	}
	// Admitting the buffer contract does not admit the function contract.
	root = writeModule(t, map[string]string{
		"oak.mod":  "module example.com/app\noak 0.1.0\nprofile strict\nadmit OAK-B0110\n",
		"main.oak": program,
	})
	_, err = New().WithPackageDir(root).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "OAK-B0122") {
		t.Fatalf("admit OAK-B0110 must not admit OAK-B0122, got %v", err)
	}
}
