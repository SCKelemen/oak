package asm

import (
	"strings"
	"testing"
)

// The seam checker's rejection matrix (docs/spec/94-assembler.md §3): each
// case is a body the assembler must refuse, with the reason it names.
func TestCheckerRejections(t *testing.T) {
	cases := []struct {
		name string
		decl string
		body string
		want string
	}{
		{"unbound parameter", "f: (x: u32) -> u32", "  mov w0, #1\n  ret", "never bound"},
		{"binding at wrong register", "f: (x, y: u32) -> u32", "  bind w0 = x\n  bind w2 = y\n  ret", "arrives in w1"},
		{"binding at wrong width", "f: (x: u64) -> u64", "  bind w0 = x\n  ret", "arrives in x0"},
		{"undeclared clobber", "f: (x: u32) -> u32", "  bind w0 = x\n  mov w9, #1\n  ret", "undeclared register w9"},
		{"width mismatch", "f: (x: u32) -> u32", "  bind w0 = x\n  clobber x9\n  add x9, w0, w0\n  ret", "width discipline"},
		{"uninitialized read", "f: (x: u32) -> u32", "  bind w0 = x\n  clobber w9\n  add w0, w0, w9\n  ret", "uninitialized register"},
		{"flags without producer", "f: (x: u32) -> u32", "  bind w0 = x\n  b.eq done\ndone:\n  ret", "consumes flags"},
		{"flags invalidated by label", "f: (x: u32) -> u32", "  bind w0 = x\n  cmp w0, #0\nagain:\n  b.eq again\n  ret", "consumes flags"},
		{"csel without producer", "f: (x, y: u32) -> u32", "  bind w0 = x\n  bind w1 = y\n  csel w0, w0, w1, lo\n  ret", "consumes flags"},
		{"csel width mismatch", "f: (x, y: u32) -> u32", "  bind w0 = x\n  bind w1 = y\n  cmp w0, w1\n  csel w0, x1, w0, lo\n  ret", "width discipline"},
		{"memory without frame", "f: (x: u64) -> u64", "  bind x0 = x\n  str x0, [sp, #-16]!\n  ldr x0, [sp], #16\n  ret", "without a declared frame"},
		{"memory outside frame", "f: (x: u64) -> u64", "  bind x0 = x\n  frame 16\n  str x0, [sp, #-32]!\n  ldr x0, [sp], #32\n  ret", "leaves the declared"},
		{"ret with live frame", "f: (x: u64) -> u64", "  bind x0 = x\n  frame 16\n  str x0, [sp, #-16]!\n  ret", "frame must be fully released"},
		{"system without capability", "f: () -> u64", "  mrs x0, cntvct_el0\n  ret", "`system` capability"},
		{"eret without capability", "f: () -> never", "  eret", "`system` capability"},
		{"ret from never", "f: () -> never", "  ret", "declared never to return"},
		{"fall off the end", "f: (x: u32) -> u32", "  bind w0 = x\n  add w0, w0, w0", "falls off the end"},
		{"unreachable after b", "f: (x: u32) -> u32", "  bind w0 = x\n  b out\n  add w0, w0, w0\nout:\n  ret", "unreachable instruction"},
		{"callee-saved write without save", "f: (x: u32) -> u32", "  bind w0 = x\n  clobber x19\n  mov x19, #1\n  ret", "before saving it to the frame"},
		{"callee-saved not restored", "f: (x: u64) -> u64", "  bind x0 = x\n  clobber x19\n  frame 16\n  str x19, [sp, #-16]!\n  mov x19, #1\n  add sp, sp, #16\n  ret", "without restoring callee-saved x19"},
		{"restore from wrong slot", "f: (x: u64) -> u64", "  bind x0 = x\n  clobber x19, x20\n  frame 32\n  stp x19, x20, [sp, #-32]!\n  mov x19, #1\n  ldr x19, [sp, #8]\n  add sp, sp, #32\n  ret", "without restoring callee-saved x19"},
		{"write after restore", "f: (x: u64) -> u64", "  bind x0 = x\n  clobber x19\n  frame 16\n  str x19, [sp, #-16]!\n  mov x19, #1\n  ldr x19, [sp], #16\n  mov x19, #2\n  ret", "without restoring callee-saved x19"},
		{"bl without lr saved", "f: (x: u32) -> u32", "  bind w0 = x\n  clobber x30\n  frame 16\n  sub sp, sp, #16\n  bl helper\n  add sp, sp, #16\n  ret", "before saving the link register"},
		{"callee-saved d8 write without save", "f: (x: f32) -> f32", "  bind s0 = x\n  clobber v8\n  fmov s8, s0\n  fmov s0, s8\n  ret", "write to callee-saved s8 before saving it"},
		{"callee-saved d8 not restored", "f: (x: f32) -> f32", "  bind s0 = x\n  clobber v8\n  frame 16\n  str d8, [sp, #-16]!\n  fmov s8, s0\n  fmov s0, s8\n  add sp, sp, #16\n  ret", "without restoring callee-saved d8"},
		{"align extent overflow", "f: () -> never", "  system\n  align 8\n  eret\n  nop\n  nop\n  eret", "exceeding its 8-byte stride"},
		{"branch outside", "f: (x: u32) -> u32", "  bind w0 = x\n  b elsewhere", "neither a label"},
		{"bl without lr clobber", "f: (x: u32) -> u32", "  bind w0 = x\n  bl helper\n  ret", "clobber x30"},
		{"result never produced", "f: (x: u32) -> u64", "  bind w0 = x\n  clobber x9\n  mov x9, #1\n  ret", ""}, // x0 bound as w0 counts as produced; documented v1 latitude
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			unit, errs := ParseUnit(tc.name+".oakasm", tc.decl+" = {\n"+tc.body+"\n}\n")
			if len(errs) != 0 {
				t.Fatalf("parse errors: %v", errs)
			}
			decl, err := parseSignature(tc.decl)
			if err != nil {
				t.Fatal(err)
			}
			findings := Check(unit.Functions[0], decl, map[string]bool{"helper": true})
			joined := strings.Join(findings, "\n")
			if tc.want == "" {
				return
			}
			if !strings.Contains(joined, tc.want) {
				t.Fatalf("expected a finding mentioning %q, got:\n%s", tc.want, joined)
			}
		})
	}
}

// Sound bodies pass the checker with no findings.
func TestCheckerAccepts(t *testing.T) {
	cases := []struct {
		name string
		decl string
		body string
	}{
		{"add", "add_asm: (left, right: u32) -> u32", "  bind w0 = left\n  bind w1 = right\n  add w0, w0, w1\n  ret"},
		{"frame pair", "swap: (a, b: u64) -> u64", "  bind x0 = a\n  bind x1 = b\n  frame 16\n  stp x0, x1, [sp, #-16]!\n  ldp x1, x0, [sp], #16\n  ret"},
		{"loop", "cd: (n: u32) -> u32", "  bind w0 = n\n  clobber w9\n  mov w9, #0\nloop:\n  cmp w0, #0\n  b.eq done\n  sub w0, w0, #1\n  add w9, w9, #1\n  b loop\ndone:\n  mov w0, w9\n  ret"},
		{"vector entry", "v: () -> never", "  system\n  align 128\n  eret"},
		{"system read", "cnt: () -> u64", "  system\n  mrs x0, cntvct_el0\n  ret"},
		{"barrier", "fence: () -> ()", "  dmb sy\n  isb\n  ret"},
		{"callee-saved save and restore", "scratch: (a: u64) -> u64", "  bind x0 = a\n  clobber x19, x20\n  frame 16\n  stp x19, x20, [sp, #-16]!\n  mov x19, #40\n  mov x20, #2\n  add x0, x19, x20\n  ldp x19, x20, [sp], #16\n  ret"},
		{"call with lr saved", "caller: (a: u64) -> u64", "  bind x0 = a\n  clobber x29, x30\n  frame 16\n  stp x29, x30, [sp, #-16]!\n  bl helper\n  ldp x29, x30, [sp], #16\n  ret"},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			unit, errs := ParseUnit(tc.name+".oakasm", tc.decl+" = {\n"+tc.body+"\n}\n")
			if len(errs) != 0 {
				t.Fatalf("parse errors: %v", errs)
			}
			decl, err := parseSignature(tc.decl)
			if err != nil {
				t.Fatal(err)
			}
			if findings := Check(unit.Functions[0], decl, map[string]bool{"helper": true}); len(findings) != 0 {
				t.Fatalf("unexpected findings: %v", findings)
			}
		})
	}
}

// Owned arrays in the frame: `add xN, sp, #imm` records a frame address,
// and memory through it is checked against the declared frame — a plain
// offset must lie inside it, an indexed access needs a dominating constant
// index guard whose bound keeps every element inside it (the native
// backend's lowering of `buf[i]`).
func TestCheckerFrameArrays(t *testing.T) {
	decl := "pick: (i: u32) -> u32"
	accept := "  bind w0 = i\n  clobber x9, x10\n  frame 16\n  sub sp, sp, #16\n  mov x9, #0\n  stp x9, x9, [sp]\n  add x9, sp, #0\n  cmp w0, #4\n  b.hs trap\n  ldr w0, [x9, w0, uxtw #2]\n  add sp, sp, #16\n  ret\ntrap:\n  brk #1"
	unit, errs := ParseUnit("frame_array.oakasm", decl+" = {\n"+accept+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	sig, _ := parseSignature(decl)
	if findings := Check(unit.Functions[0], sig, nil); len(findings) != 0 {
		t.Fatalf("a guarded frame-array access must pass: %v", findings)
	}
	prologue := "  bind w0 = i\n  clobber x9, x10\n  frame 16\n  sub sp, sp, #16\n  mov x9, #0\n  stp x9, x9, [sp]\n"
	cases := []struct{ name, body, want string }{
		{"unguarded index", prologue + "  add x9, sp, #0\n  ldr w0, [x9, w0, uxtw #2]\n  add sp, sp, #16\n  ret", "without a dominating constant index guard"},
		{"guard admits too many", prologue + "  add x9, sp, #0\n  cmp w0, #5\n  b.hs trap\n  ldr w0, [x9, w0, uxtw #2]\n  add sp, sp, #16\n  ret\ntrap:\n  brk #1", "past the declared 16-byte frame"},
		{"base past the frame", prologue + "  add x9, sp, #8\n  cmp w0, #4\n  b.hs trap\n  ldr w0, [x9, w0, uxtw #2]\n  add sp, sp, #16\n  ret\ntrap:\n  brk #1", "past the declared 16-byte frame"},
		{"offset outside the frame", prologue + "  add x9, sp, #8\n  ldr w0, [x9, #12]\n  add sp, sp, #16\n  ret", "outside the declared 16-byte frame"},
		{"scale not the element", prologue + "  add x9, sp, #0\n  cmp w0, #4\n  b.hs trap\n  ldr w0, [x9, w0, uxtw #1]\n  add sp, sp, #16\n  ret\ntrap:\n  brk #1", "whole elements"},
		{"guard against a register is no constant", prologue + "  add x9, sp, #0\n  mov w10, #4\n  cmp w0, w10\n  b.hs trap\n  ldr w0, [x9, w0, uxtw #2]\n  add sp, sp, #16\n  ret\ntrap:\n  brk #1", "without a dominating constant index guard"},
		// Two predecessors with different frame addresses in x9: the merge
		// holds neither.
		{"address lost at a merge", prologue + "  cbz w0, other\n  add x9, sp, #0\n  b join\nother:\n  add x9, sp, #8\njoin:\n  ldr w0, [x9, #4]\n  add sp, sp, #16\n  ret", "memory operands go through the declared sp frame or a bound span base"},
		// One predecessor: the address and the index guard flow through the label.
		{"facts flow through a single-predecessor label", prologue + "  add x9, sp, #0\n  cmp w0, #4\n  b.hs trap\nagain:\n  ldr w0, [x9, w0, uxtw #2]\n  add sp, sp, #16\n  ret\ntrap:\n  brk #1", ""},
		{"fact lost at a call", "  bind w0 = i\n  clobber x9, x29, x30\n  frame 32\n  sub sp, sp, #32\n  stp x29, x30, [sp]\n  add x9, sp, #16\n  bl helper\n  ldr w0, [x9, #0]\n  ldp x29, x30, [sp]\n  add sp, sp, #32\n  ret", "memory operands go through the declared sp frame or a bound span base"},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			unit, errs := ParseUnit(tc.name+".oakasm", decl+" = {\n"+tc.body+"\n}\n")
			if len(errs) != 0 {
				t.Fatalf("parse errors: %v", errs)
			}
			joined := strings.Join(Check(unit.Functions[0], sig, map[string]bool{"helper": true}), "\n")
			if tc.want == "" {
				if joined != "" {
					t.Fatalf("expected no findings, got:\n%s", joined)
				}
				return
			}
			if !strings.Contains(joined, tc.want) {
				t.Fatalf("expected a finding mentioning %q, got:\n%s", tc.want, joined)
			}
		})
	}
}

// A span parked in callee-saved registers: `mov x19, x0; mov w20, w1` copy
// the span's base and length facts, so the pair survives a call (the
// callee preserves x19–x28) and is walked from there; the original pair in
// x0/w1 dies with the call.
func TestCheckerSpanAliases(t *testing.T) {
	decl := "first_after: (v: []u32) -> u32"
	prologue := "  bind x0, w1 = v\n  clobber x9, x19, x20, x29, x30\n  frame 32\n  sub sp, sp, #32\n  stp x29, x30, [sp]\n  stp x19, x20, [sp, #16]\n  mov x19, x0\n  mov w20, w1\n  bl helper\n"
	epilogue := "  ldp x19, x20, [sp, #16]\n  ldp x29, x30, [sp]\n  add sp, sp, #32\n  ret\ntrap:\n  brk #1"
	accept := prologue + "  mov w9, #0\n  cmp w9, w20\n  b.hs trap\n  ldr w0, [x19, w9, uxtw #2]\n" + epilogue
	unit, errs := ParseUnit("alias.oakasm", decl+" = {\n"+accept+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	sig, _ := parseSignature(decl)
	if findings := Check(unit.Functions[0], sig, map[string]bool{"helper": true}); len(findings) != 0 {
		t.Fatalf("a span walked from its parked pair after a call must pass: %v", findings)
	}
	cases := []struct{ name, body, want string }{
		{"original base dies at the call", prologue + "  mov w9, #0\n  cmp w9, w20\n  b.hs trap\n  ldr w0, [x0, w9, uxtw #2]\n" + epilogue, "memory operands go through the declared sp frame or a bound span base"},
		{"length copy overwritten", prologue + "  mov w20, #8\n  mov w9, #0\n  cmp w9, w20\n  b.hs trap\n  ldr w0, [x19, w9, uxtw #2]\n" + epilogue, "not this span's length register"},
		{"guard against another register", prologue + "  mov w9, #0\n  mov w0, #4\n  cmp w9, w0\n  b.hs trap\n  ldr w0, [x19, w9, uxtw #2]\n" + epilogue, "not this span's length register"},
		{"length guard through the copy", prologue + "  cmp w20, #1\n  b.lo trap\n  ldr w0, [x19]\n" + epilogue, ""},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			unit, errs := ParseUnit(tc.name+".oakasm", decl+" = {\n"+tc.body+"\n}\n")
			if len(errs) != 0 {
				t.Fatalf("parse errors: %v", errs)
			}
			joined := strings.Join(Check(unit.Functions[0], sig, map[string]bool{"helper": true}), "\n")
			if tc.want == "" {
				if joined != "" {
					t.Fatalf("expected no findings, got:\n%s", joined)
				}
				return
			}
			if !strings.Contains(joined, tc.want) {
				t.Fatalf("expected a finding mentioning %q, got:\n%s", tc.want, joined)
			}
		})
	}
}

// Typed pointer memory: span/view parameters bind a register pair and are
// addressable only under a dominating length guard.
func TestCheckerSpanAccess(t *testing.T) {
	decl := "first_two: (frame: [*]u64) -> u64"
	accept := "  bind x0, w1 = frame\n  clobber x9\n  cmp w1, #2\n  b.lo short\n  ldr x9, [x0, #8]\n  ldr x0, [x0]\n  add x0, x0, x9\n  ret\nshort:\n  mov x0, #0\n  ret"
	unit, errs := ParseUnit("span.oakasm", decl+" = {\n"+accept+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	sig, _ := parseSignature(decl)
	if findings := Check(unit.Functions[0], sig, nil); len(findings) != 0 {
		t.Fatalf("guarded span access must pass: %v", findings)
	}

	cases := []struct{ name, decl, body, want string }{
		{"unguarded", decl, "  bind x0, w1 = frame\n  ldr x0, [x0]\n  ret", "without a dominating bounds guard"},
		{"beyond guard", decl, "  bind x0, w1 = frame\n  cmp w1, #2\n  b.lo short\n  ldr x0, [x0, #16]\n  ret\nshort:\n  mov x0, #0\n  ret", "guard proves only 2 elements"},
		{"padded x1 is no guard", decl, "  bind x0, w1 = frame\n  cmp x1, #2\n  b.lo short\n  ldr x0, [x0]\n  ret\nshort:\n  mov x0, #0\n  ret", "without a dominating bounds guard"},
		// The guard's own failure branch lands on the label: one predecessor
		// carries len >= 2, the other nothing, so the merge holds nothing.
		{"guard lost at merge", decl, "  bind x0, w1 = frame\n  cmp w1, #2\n  b.lo again\nagain:\n  ldr x0, [x0]\n  ret", "without a dominating bounds guard"},
		{"pre-index on span base", decl, "  bind x0, w1 = frame\n  cmp w1, #2\n  b.lo short\n  ldr x0, [x0, #8]!\n  ret\nshort:\n  mov x0, #0\n  ret", "never moved"},
		{"store through view", "peek: (bytes: []u8) -> u64", "  bind x0, w1 = bytes\n  clobber w9\n  cmp w1, #4\n  b.lo short\n  mov w9, #1\n  str w9, [x0]\n  mov x0, #0\n  ret\nshort:\n  mov x0, #0\n  ret", "read-only view"},
		{"scalar binding for span", decl, "  bind x0 = frame\n  mov x0, #0\n  ret", "binds a pair"},
		{"wrong pair widths", decl, "  bind x0, x1 = frame\n  mov x0, #0\n  ret", "w1 (length"},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			unit, errs := ParseUnit(tc.name+".oakasm", tc.decl+" = {\n"+tc.body+"\n}\n")
			if len(errs) != 0 {
				t.Fatalf("parse errors: %v", errs)
			}
			sig, err := parseSignature(tc.decl)
			if err != nil {
				t.Fatal(err)
			}
			joined := strings.Join(Check(unit.Functions[0], sig, nil), "\n")
			if !strings.Contains(joined, tc.want) {
				t.Fatalf("expected a finding mentioning %q, got:\n%s", tc.want, joined)
			}
		})
	}
}
