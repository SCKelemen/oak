package compiler

import "testing"

// Exported constants (docs/spec/83-modules.md, ml ask 5.5): a package-level
// `pub NAME: T = literal` is a value an importing package reads as
// pkg.NAME, integer and floating-point alike, so packages need no accessor
// functions for their constants; the constant is also usable inside its own
// package by its bare name.
func TestE2EModuleExportedConstants(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": "module example.com/consts\noak 0.1.0\n",
		"ops/ops.oak": `package ops
pub OP_ADD: u32 = 2
pub OP_MUL: u32 = 3
pub SCALE: f64 = 0.5
pub is_add: (op: u32): Bool = op == OP_ADD
`,
		"main.oak": `package main
import("example.com/consts/ops")
main: (): i32 {
  scaled: f64 = ops.SCALE * 84.0
  code: u32 = ops.is_add(ops.OP_ADD) && !ops.is_add(ops.OP_MUL) ? ops.OP_ADD + ops.OP_MUL | u32(0)
  scaled == 42.0 && code == u32(5) ? 42 | 1
}
`,
	})
	_, code, abnormal := buildAndRunFrom(t, "consts", New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
