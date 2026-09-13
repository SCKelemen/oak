package asm

import (
	"strings"
	"testing"
)

// verifyGlobalsCase is verifyCase over a body that addresses package
// globals: the function declares them, as the native backend does.
func verifyGlobalsCase(t *testing.T, decl, oakBody, asmBody string, globals map[string]Global) Verdict {
	t.Helper()
	unit, errs := ParseUnit("g.oakasm", decl+" = {\n"+asmBody+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	unit.Functions[0].Globals = globals
	sig, err := parseSignature(decl)
	if err != nil {
		t.Fatal(err)
	}
	if findings := Check(unit.Functions[0], sig, nil); len(findings) != 0 {
		t.Fatalf("checker: %v", findings)
	}
	spec, err := parseSignatureWithBody(decl + " = " + oakBody)
	if err != nil {
		t.Fatal(err)
	}
	return Verify(unit.Functions[0], sig, spec.Body)
}

// Package state is verified, not trusted (docs/spec/94-assembler.md §9):
// a read is the cell's entry value, a write is compared cell by cell —
// through conditionals, for unit functions, and against a wrong lowering.
func TestVerifyGlobalWriters(t *testing.T) {
	globals := map[string]Global{"st": {Type: "u32", Bits: 32}, "flag": {Type: "Bool", Bits: 32}}
	address := func(reg, name string) string {
		return "  adrp " + reg + ", " + name + "\n  add " + reg + ", " + reg + ", :lo12:" + name + "\n"
	}
	// bump: (k: u32) -> u32 { st = st + k; st }
	bump := verifyGlobalsCase(t, "bump: (k: u32) -> u32", "{\n  st = st + k\n  st\n}",
		"  bind w0 = k\n  clobber x9, x10\n"+address("x9", "st")+"  ldr w10, [x9]\n  add w10, w10, w0\n  str w10, [x9]\n  mov w0, w10\n  ret", globals)
	if bump.Kind != VerdictProven || !strings.Contains(bump.Message, "package state it writes (st)") {
		t.Fatalf("a writer with a result must be proven in its result and its cell, got %s: %s", bump.Kind, bump.Message)
	}
	// set: (k: u32) -> () { st = k * 2; flag = k == 0 }: a unit writer.
	set := verifyGlobalsCase(t, "set: (k: u32) -> ()", "{\n  st = k * u32(2)\n  flag = k == u32(0)\n}",
		"  bind w0 = k\n  clobber x9, x10\n"+address("x9", "st")+"  lsl w10, w0, #1\n  str w10, [x9]\n"+address("x9", "flag")+"  cmp w0, #0\n  cset w10, eq\n  str w10, [x9]\n  ret", globals)
	if set.Kind != VerdictProven || !strings.Contains(set.Message, "package state it writes (flag, st)") {
		t.Fatalf("a unit writer must be proven in its cells, got %s: %s", set.Kind, set.Message)
	}
	// guarded: (k: u32) -> () { k > 10 ? { st = k } | { } }: a write on one arm meets the entry value on the other.
	guarded := verifyGlobalsCase(t, "guarded: (k: u32) -> ()", "{\n  k > u32(10) ? { st = k } | { }\n}",
		"  bind w0 = k\n  clobber x9\n  cmp w0, #10\n  b.ls done\n"+address("x9", "st")+"  str w0, [x9]\ndone:\n  ret", globals)
	if guarded.Kind != VerdictProven {
		t.Fatalf("a conditional writer must be proven, got %s: %s", guarded.Kind, guarded.Message)
	}
	// The wrong lowering: stores k + 1 where the body stores k.
	wrong := verifyGlobalsCase(t, "set_st: (k: u32) -> ()", "{\n  st = k\n}",
		"  bind w0 = k\n  clobber x9, x10\n"+address("x9", "st")+"  add w10, w0, #1\n  str w10, [x9]\n  ret", globals)
	if wrong.Kind != VerdictMismatch || !strings.Contains(wrong.Message, "the package global st") {
		t.Fatalf("a wrong store must be a mismatch naming the cell, got %s: %s", wrong.Kind, wrong.Message)
	}
	// A store the Oak body does not make is a mismatch too.
	extra := verifyGlobalsCase(t, "ident: (k: u32) -> u32", "{\n  k + st\n}",
		"  bind w0 = k\n  clobber x9, x10\n"+address("x9", "st")+"  ldr w10, [x9]\n  str w0, [x9]\n  add w0, w0, w10\n  ret", globals)
	if extra.Kind != VerdictMismatch || !strings.Contains(extra.Message, "the package global st") {
		t.Fatalf("a store the body does not make must be a mismatch, got %s: %s", extra.Kind, extra.Message)
	}
}
