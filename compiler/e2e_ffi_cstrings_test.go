package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// C strings both ways (docs/spec/92-ffi.md sections 2.5.3 and 2.7.1):
// c.cstr(v) hands an extern the base pointer of a NUL-terminated []u8 view
// for one call, and c.borrow_string(p) inside an unsafe block views the
// bytes of a NUL-terminated C string the runtime owns, without the
// terminator. Both are executed against libc: strlen reads what Oak
// terminated, getenv returns a pointer Oak reads back.
func TestE2ECStringsBothWays(t *testing.T) {
	t.Setenv("OAK_CSTRING_PROBE", "forty-two")
	src := `
c_strlen: (s: c.String): c.UInt64 = c.extern("strlen")
c_getenv: (name: c.String): c.Ptr = c.extern("getenv")

terminated_length: (): u32 {
  buffer: [6]u8 = [6]u8{ 104, 101, 108, 108, 111, 0 }
  text: []u8 = view(&buffer)
  u32_trunc_u64(u64(c_strlen(c.cstr(text))))
}

literal_length: (): u32 = u32_trunc_u64(u64(c_strlen(c.cstr("abc\0"))))

probe_sum: (): u32 {
  name: [18]u8 = [18]u8{ 79, 65, 75, 95, 67, 83, 84, 82, 73, 78, 71, 95, 80, 82, 79, 66, 69, 0 }
  key: []u8 = view(&name)
  p: c.Ptr = c_getenv(c.cstr(key))
  total: u32 = 0
  unsafe {
    value: []u8 = c.borrow_string(p)
    total = len(value) * u32(100)
    i: u32 = 0
    while i < len(value) {
      total = total + u32(value[i])
      i = i + u32(1)
    }
  }
  total
}

missing_is_empty: (): u32 {
  p: c.Ptr = c_getenv(c.cstr("OAK_CSTRING_PROBE_UNSET_FOR_SURE\0"))
  n: u32 = 7
  unsafe {
    value: []u8 = c.borrow_string(p)
    n = len(value)
  }
  n
}

main: (): i32 {
  assert(terminated_length() == u32(5))
  assert(literal_length() == u32(3))
  // "forty-two": 9 bytes, byte sum 955.
  assert(probe_sum() == u32(900) + u32(955))
  assert(missing_is_empty() == u32(0))
  42
}
`
	_, code, abnormal := buildAndRunFrom(t, "ffi_cstrings", New().WithSource("ffi_cstrings.oak", src))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

// A view whose last byte is not NUL never reaches C: the call traps.
func TestE2ECStringUnterminatedTraps(t *testing.T) {
	src := `
c_strlen: (s: c.String): c.UInt64 = c.extern("strlen")

main: (): i32 {
  buffer: [5]u8 = [5]u8{ 104, 101, 108, 108, 111 }
  text: []u8 = view(&buffer)
  i32_bits_u32(u32_trunc_u64(u64(c_strlen(c.cstr(text)))))
}
`
	comp := New().WithSource("ffi_cstr_trap.oak", src)
	output, err := comp.EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if !strings.Contains(output, "oak_cstr_u8( text, \"ffi_cstr_trap.oak\", 7 )") {
		t.Fatalf("c.cstr over a named view must lower through the checked helper naming its position:\n%s", output)
	}
	_, _, abnormal := buildAndRunFrom(t, "ffi_cstr_trap", New().WithSource("ffi_cstr_trap.oak", src))
	if !abnormal {
		t.Fatal("an unterminated view passed through c.cstr must trap at the call")
	}
}

// The static rules: a literal without a trailing NUL, a c.cstr standing
// for a parameter that is not c.String, a non-view operand, c.cstr passed
// to Oak code or bound as a value, and c.borrow_string outside an unsafe
// block or outside a binding's initializer.
func TestCStringRejections(t *testing.T) {
	cases := []struct {
		name, src, code string
	}{
		{"literal without NUL", `
c_strlen: (s: c.String): c.UInt64 = c.extern("strlen")
main: (): i32 { n: c.UInt64 = c_strlen(c.cstr("abc"))
  0 }
`, "OAK-F0110"},
		{"parameter is not c.String", `
take: (p: c.Ptr): c.Int = c.extern("oak_probe_take")
main: (): i32 {
  buffer: [2]u8 = [2]u8{ 97, 0 }
  text: []u8 = view(&buffer)
  n: c.Int = take(c.cstr(text))
  0
}
`, "OAK-F0110"},
		{"operand is not a byte view", `
c_strlen: (s: c.String): c.UInt64 = c.extern("strlen")
main: (): i32 {
  words: [2]u32 = [2]u32{ 97, 0 }
  text: []u32 = view(&words)
  n: c.UInt64 = c_strlen(c.cstr(text))
  0
}
`, "OAK-F0110"},
		{"passed to Oak code", `
take: (s: c.String): u32 { 0 }
main: (): i32 {
  buffer: [2]u8 = [2]u8{ 97, 0 }
  text: []u8 = view(&buffer)
  n: u32 = take(c.cstr(text))
  0
}
`, "OAK-F0103"},
		{"bound as a value", `
main: (): i32 {
  buffer: [2]u8 = [2]u8{ 97, 0 }
  text: []u8 = view(&buffer)
  s: c.String = c.cstr(text)
  0
}
`, "OAK-F0103"},
		{"borrow_string outside unsafe", `
c_getenv: (name: c.String): c.Ptr = c.extern("getenv")
main: (): i32 {
  p: c.Ptr = c_getenv(c.String("HOME"))
  value: []u8 = c.borrow_string(p)
  i32(len(value))
}
`, "OAK-F0107"},
		{"borrow_string as an argument", `
c_getenv: (name: c.String): c.Ptr = c.extern("getenv")
count: (v: []u8): u32 = len(v)
main: (): i32 {
  p: c.Ptr = c_getenv(c.String("HOME"))
  n: u32 = 0
  unsafe { n = count(c.borrow_string(p)) }
  i32(n)
}
`, "OAK-F0107"},
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

// An inbound C string is the foreign buffer contract: the OAK-B0110
// assumption is recorded, the strict profile rejects it without an
// admission, and `admit OAK-B0110` in the manifest accepts it.
func TestCStringBorrowRecordsAssumptionAndStrictAdmits(t *testing.T) {
	const program = `package main

c_getenv: (name: c.String): c.Ptr = c.extern("getenv")

home_length: (): u32 {
  p: c.Ptr = c_getenv(c.String("HOME"))
  n: u32 = 0
  unsafe {
    value: []u8 = c.borrow_string(p)
    n = len(value)
  }
  n
}

main: (): i32 { i32_bits_u32(home_length()) }
`
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/app\noak 0.1.0\nprofile strict\n",
		"main.oak": program,
	})
	_, err := New().WithPackageDir(root).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "OAK-B0110") {
		t.Fatalf("a strict module borrowing a C string must be rejected with OAK-B0110, got %v", err)
	}
	root = writeModule(t, map[string]string{
		"oak.mod":  "module example.com/app\noak 0.1.0\nprofile strict\nadmit OAK-B0110\n",
		"main.oak": program,
	})
	var recorded []*diagnostic.Diagnostic
	comp := New().WithPackageDir(root).WithDiagnosticSink(func(d *diagnostic.Diagnostic) { recorded = append(recorded, d) })
	if _, err := comp.EmitC().Get(); err != nil {
		t.Fatalf("admit OAK-B0110 must let the strict module borrow a C string: %v", err)
	}
	found := false
	for _, d := range recorded {
		if d.Code == "OAK-B0110" && strings.Contains(d.PlainText(), "NUL-terminated string") {
			found = true
		}
	}
	if !found {
		t.Fatal("the C string contract must be recorded as an OAK-B0110 assumption naming the terminator")
	}
}
