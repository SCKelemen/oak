package compiler

import (
	"strings"
	"testing"
)

// Joining literals (docs/spec/10-syntax.md section 2a; the ml pilot's ninth
// ask): `"a" + "b"` is one literal to every backend, so an emitter's
// spelling assembles from pieces at no run-time cost, and `oak fmt` prints
// the folded literal.
func TestE2EStringLiteralsJoin(t *testing.T) {
	src := `package main

main: (): i32 = {
  s: string = "float " + "acc" + "[" + "0" + "]"
  bytes: []u8 = str_bytes(s)
  parts: []u8 = str_bytes("(" + ")")
  i32(len(bytes) == u32(12) && bytes[6] == u8(97) && len(parts) == u32(2) && parts[1] == u8(41) ? 42 | 1)
}
`
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": src})
	if code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root)); abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	if got := interpretModule(t, root); got != 42 {
		t.Fatalf("interpreted: %d", got)
	}
	emitted, err := New().WithPackageDir(root).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(emitted, `"float acc[0]"`) {
		t.Fatalf("the joined literal reaches the C as one literal:\n%s", emitted)
	}
	tree, err := New().WithPackageDir(root).Parse().Get()
	if err != nil {
		t.Fatal(err)
	}
	// The printer spells a literal by its value; the folded one is one value.
	if printed := tree.Root.String(); !strings.Contains(printed, "s: string = float acc[0]") {
		t.Fatalf("the folded literal prints back:\n%s", printed)
	}
	// Two runtime strings have no `+`.
	runtime := strings.Replace(src, `  bytes: []u8 = str_bytes(s)`, "  u: string = s + s\n  bytes: []u8 = str_bytes(u)", 1)
	root = writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": runtime})
	if _, err := New().WithPackageDir(root).SemanticModel().Get(); err == nil {
		t.Fatal("joining two runtime strings must be a type error")
	}
}
