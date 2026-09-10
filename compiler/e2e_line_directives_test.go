package compiler

import (
	"strings"
	"testing"
)

// #line directives (docs/spec/90-backend.md section 10, ml tier 6): with
// the option on, every function and statement is preceded by a directive
// naming its Oak source line, so cc diagnostics and debuggers attribute
// generated code to Oak; off by default, nothing changes.
func TestE2ELineDirectives(t *testing.T) {
	src := `double: (x: u32): u32 {
  y: u32 = x * 2
  y
}
main: (): i32 {
  v: u32 = double(21)
  i32_bits_u32(v)
}
`
	plain, err := New().WithSource("lines.oak", src).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(plain, "#line") {
		t.Fatalf("directives must be off by default:\n%s", plain)
	}
	comp := New().WithSource("lines.oak", src).WithLineDirectives()
	output, err := comp.EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"#line 1 \"lines.oak\"\nOAK_INLINE u32 oak_double( u32 x )",
		"#line 2 \"lines.oak\"\n",
		"#line 5 \"lines.oak\"\ni32 oak_main(",
		"#line 6 \"lines.oak\"\n",
	} {
		if !strings.Contains(output, want) {
			t.Fatalf("generated C lacks %q:\n%s", want, output)
		}
	}
	// The directives are honest C: the program compiles with debug info
	// and runs unchanged.
	_, code, abnormal := buildAndRunFrom(t, "lines", comp, "-g")
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// A cc diagnostic inside a directive-mapped body names the Oak file and
// line, not the generated C's: the whole point of the mapping.
func TestLineDirectivesAttributeDiagnostics(t *testing.T) {
	output, err := New().WithSource("attributed.oak", `main: (): i32 {
  x: u32 = 7
  i32_bits_u32(x)
}
`).WithLineDirectives().EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	// The statement on Oak line 2 is the declaration of x.
	idx := strings.Index(output, "#line 2 \"attributed.oak\"\n")
	if idx < 0 {
		t.Fatalf("no directive for line 2:\n%s", output)
	}
	following := output[idx+len("#line 2 \"attributed.oak\"\n"):]
	if !strings.HasPrefix(strings.TrimSpace(following), "u32 x") {
		t.Fatalf("the directive must immediately precede the declaration it maps:\n%s", following[:80])
	}
}
