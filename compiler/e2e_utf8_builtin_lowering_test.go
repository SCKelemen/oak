package compiler

import (
	"strings"
	"testing"
)

// The builtin is_valid_utf8 lowers to the standard library's vector
// validator (docs/spec/70-strings.md section 8): a module build that
// reaches it, or str_from_utf8, loads `utf8` implicitly and the runtime
// helper is a call to the compiled utf8.valid, the program
// Oak.Utf8Blocks.program_valid proves decides Table 3-7. A bare source
// build has no packages and keeps the scalar transliteration.
const utf8BuiltinProgram = `package main

main: (): i32 {
  text: [8]u8 = [u8(104), u8(105), u8(195), u8(169), u8(226), u8(130), u8(172), u8(33)]
  bytes: []u8 = view(&text)
  bad: [3]u8 = [u8(226), u8(65), u8(66)]
  badv: []u8 = view(&bad)
  s: string = str_from_utf8(bytes)
  is_valid_utf8(bytes) && !is_valid_utf8(badv) && len(str_bytes(s)) == u32(8) ? 42 | 1
}
`

func TestE2EIsValidUtf8LowersToTheVectorValidator(t *testing.T) {
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": utf8BuiltinProgram})
	output, err := New().WithPackageDir(root).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if !strings.Contains(output, "static inline Bool oak_is_valid_utf8(oak_view_u8 v) { return oak_utf8__valid( v ); }") {
		t.Fatalf("the builtin did not lower to utf8.valid:\n%s", output)
	}
	if !strings.Contains(output, "Bool oak_utf8__valid( oak_view_u8 bytes ) {") {
		t.Fatalf("the utf8 package was not loaded implicitly:\n%s", output)
	}
	if strings.Contains(output, "if (b0 == 0xF4)") {
		t.Fatalf("the scalar transliteration was emitted beside the lowering:\n%s", output)
	}
	for _, variant := range []struct {
		name  string
		flags []string
	}{{"neon", nil}, {"portable", []string{"-DOAK_PORTABLE_INTRINSICS"}}} {
		_, exit, abnormal := buildAndRunFrom(t, "utf8_builtin_"+variant.name, New().WithPackageDir(root), variant.flags...)
		if abnormal || exit != 42 {
			t.Fatalf("%s: exit %d abnormal %v", variant.name, exit, abnormal)
		}
	}
}

func TestE2EIsValidUtf8KeepsTheScalarHelperWithoutPackages(t *testing.T) {
	src := `
main: (): u32 {
  bad: [3]u8 = [u8(226), u8(65), u8(66)]
  ok: [2]u8 = [u8(195), u8(169)]
  is_valid_utf8(view(&ok)) && !is_valid_utf8(view(&bad)) ? u32(42) | u32(1)
}
`
	output, err := New().WithSource("utf8_scalar.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if !strings.Contains(output, "if (b0 == 0xF4)") || strings.Contains(output, "oak_utf8__valid") {
		t.Fatalf("a source build should keep the scalar transliteration:\n%s", output)
	}
	code, abnormal := buildAndRun(t, "utf8_scalar", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
