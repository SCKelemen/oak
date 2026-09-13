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
