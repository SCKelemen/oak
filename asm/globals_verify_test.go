package asm

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
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

// Cells thread through calls (docs/spec/94-assembler.md §9): a callee's
// summary sees the caller's current cell values and its writes come back
// to the caller's path; a unit callee is summarized for its writes alone.
func TestVerifyGlobalsThroughCalls(t *testing.T) {
	globals := map[string]Global{"st": {Type: "u32", Bits: 32}}
	callees := map[string]*ast.FunctionStatement{}
	for _, text := range []string{
		"bump_st: () -> () = {\n  st = st + u32(1)\n}",
		"read_st: () -> u32 = {\n  st\n}",
	} {
		fn, err := parseSignatureWithBody(text)
		if err != nil {
			t.Fatal(err)
		}
		callees[fn.Name.Value] = fn
	}
	symbols := map[string]bool{"bump_st": true, "read_st": true}
	run := func(decl, oakBody, asmBody string) Verdict {
		t.Helper()
		unit, errs := ParseUnit("gc.oakasm", decl+" = {\n"+asmBody+"\n}\n")
		if len(errs) != 0 {
			t.Fatal(errs)
		}
		unit.Functions[0].Globals = globals
		unit.Functions[0].Callees = callees
		sig, err := parseSignature(decl)
		if err != nil {
			t.Fatal(err)
		}
		if findings := Check(unit.Functions[0], sig, symbols); len(findings) != 0 {
			t.Fatalf("checker: %v", findings)
		}
		spec, err := parseSignatureWithBody(decl + " = " + oakBody)
		if err != nil {
			t.Fatal(err)
		}
		unit.Functions[0].Callees = callees
		return Verify(unit.Functions[0], sig, spec.Body)
	}
	prologue := "  clobber x9, x29, x30\n  frame 16\n  sub sp, sp, #16\n  stp x29, x30, [sp]\n"
	epilogue := "  ldp x29, x30, [sp]\n  add sp, sp, #16\n  ret"
	address := "  adrp x9, st\n  add x9, x9, :lo12:st\n"
	// after: () -> u32 { bump_st(); st }: the unit callee's write is read back.
	after := run("after: () -> u32", "{\n  bump_st()\n  st\n}", prologue+"  bl bump_st\n"+address+"  ldr w0, [x9]\n"+epilogue)
	if after.Kind != VerdictProven || !strings.Contains(after.Message, "package state it writes (st)") {
		t.Fatalf("a unit callee's write must reach the caller's read and cell, got %s: %s", after.Kind, after.Message)
	}
	unitAfter := run("unit_after: () -> ()", "{\n  bump_st()\n}", prologue+"  bl bump_st\n"+epilogue)
	if unitAfter.Kind != VerdictProven || strings.Join(unitAfter.Callees, ",") != "bump_st" {
		t.Fatalf("a proven unit caller must retain its callee dependency, got %s: %s, callees %v", unitAfter.Kind, unitAfter.Message, unitAfter.Callees)
	}
	// seed: (k: u32) -> u32 { st = k; read_st() }: the caller's store is what the callee reads.
	seed := run("seed: (k: u32) -> u32", "{\n  st = k\n  read_st()\n}", "  bind w0 = k\n"+prologue+address+"  str w0, [x9]\n  bl read_st\n"+epilogue)
	if seed.Kind != VerdictProven || !strings.Contains(seed.Message, "package state it writes (st)") {
		t.Fatalf("a callee must read the caller's stored cell, got %s: %s", seed.Kind, seed.Message)
	}
	// The lowering that forgets the call: the Oak body bumps, the asm does not.
	forgot := run("after: () -> u32", "{\n  bump_st()\n  st\n}", "  clobber x9\n"+address+"  ldr w0, [x9]\n  ret")
	if forgot.Kind != VerdictMismatch {
		t.Fatalf("a lowering that drops the callee's write must be a mismatch, got %s: %s", forgot.Kind, forgot.Message)
	}
}
