package compiler

import (
	"strings"
	"testing"
)

// The codec words are the program's when it declares them (the ml pilot's
// F23): a function named encode and a local named from compile beside an
// imported library; an undeclared `from` used as a value is still the
// codec form, refused with its position.
func TestE2ECodecWordsStayOrdinaryWhenDeclared(t *testing.T) {
	src := `package main

s := import("strings")

encode: (n: u32): u32 = n * 2

Range: type = struct { from: u32, to: u32 }

main: (): i32 = {
  from: u32 = encode(20)
  r: Range = Range { from: from, to: from + 2 }
  low: u8 = s.ascii_lower(u8(65))
  i32(r.to == u32(42) && low == u8(97) ? 42 | 1)
}
`
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": src})
	if code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root)); abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	// Undeclared, `from` is nobody's: refused with its position, whether the
	// codec pass names it or the checker finds no binding.
	undeclared := "package main\n\nmain: (): i32 = {\n  begin: u32 = from\n  i32_bits_u32(begin)\n}\n"
	root = writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": undeclared})
	_, err := New().WithPackageDir(root).SemanticModel().Get()
	if err == nil || !strings.Contains(err.Error(), "4:16") || !strings.Contains(err.Error(), "from") {
		t.Fatalf("an undeclared codec word as a value is refused with its position: %v", err)
	}
}

// F23's remaining bootstrap case: codec entry points are syntax, not
// exported declarations. An ordinary global or function keeps its name.
func TestE2ECodecWordsStayOrdinaryWithStd(t *testing.T) {
	for _, spelling := range []string{"std", `"std"`} {
		t.Run(spelling, func(t *testing.T) {
			source := "package main\nimport(" + spelling + ")\n" + `
from: u32 = 3
encode: (n: u32): u32 = n * 2
decode: (n: u32): u32 = n + from
encoded_size: (n: u32): u32 = n + 1
decode_located: (n: u32): u32 = n + 1
main: (): i32 = {
  total: u32 = decode_located(encoded_size(decode(encode(18))))
  total == 41 && ascii_lower(u8(65)) == u8(97) ? 42 | 1
}
`
			root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": source})
			if code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root)); abnormal || code != 42 {
				t.Fatalf("C exit=(%d,%v), want 42", code, abnormal)
			}
			if got := interpretModule(t, root); got != 42 {
				t.Fatalf("interpreter result=%d, want 42", got)
			}
		})
	}
	// Explicit type arguments still select the ordinary generic function.
	t.Run("generic", func(t *testing.T) {
		source := `import(std)
encode[T]: (value: T): T = value
main: (): i32 = i32_bits_u32(encode[u32](u32(42)))
`
		if code, abnormal := buildAndRun(t, "generic_encode", source); abnormal || code != 42 {
			t.Fatalf("C exit=(%d,%v), want 42", code, abnormal)
		}
		if got := interpretChecked(t, source); got != 42 {
			t.Fatalf("interpreter result=%d, want 42", got)
		}
	})
	// Actual exports still cannot be rebound by the importing package.
	source := "import(std)\nascii_lower: (n: u8): u8 = n\nmain: (): i32 = 0\n"
	if _, err := New().WithSource("collision.oak", source).Check().Get(); err == nil || !strings.Contains(err.Error(), `declaration "ascii_lower" conflicts with a standard library export`) {
		t.Fatalf("real export collision must fail, got %v", err)
	}
}
