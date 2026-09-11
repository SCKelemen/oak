package compiler

import (
	"strings"
	"testing"
)

// F21: an assertion in a multi-package program is attributed to its own
// source file, spelled relative to the package directory, not to the root
// package's directory.
func TestE2EAssertNamesSourceFile(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": "module example.com/traps\noak 0.1.0\n",
		"fuzz/fuzz.oak": `package fuzz

pub check: (n: u32): u32 = {
  assert(n < u32(100))
  n + u32(1)
}
`,
		"main.oak": `package main

import("example.com/traps/fuzz")

main: (): i32 = {
  assert(fuzz.check(u32(40)) == u32(41))
  41
}
`,
	})
	output, err := New().WithPackageDir(root).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	for _, want := range []string{`"fuzz/fuzz.oak", 4`, `"main.oak", 6`} {
		if !strings.Contains(output, want) {
			t.Fatalf("assertion site %s missing from the generated C:\n%s", want, linesContaining(output, "oak_assert("))
		}
	}
	if strings.Contains(output, `"`+root+`", `) {
		t.Fatalf("an assertion still names the package directory:\n%s", linesContaining(output, "oak_assert("))
	}
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 41 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func linesContaining(text, needle string) string {
	var out []string
	for _, line := range strings.Split(text, "\n") {
		if strings.Contains(line, needle) {
			out = append(out, line)
		}
	}
	return strings.Join(out, "\n")
}
