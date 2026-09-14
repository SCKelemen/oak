package asm

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
)

// A span argument over the caller's owned frame array (docs/spec/
// 94-assembler.md §8, span arguments over owned arrays): `span(&buf)`
// passes the array's frame address and its constant length, and the call
// summary binds the callee's parameter to the array's contents, writing a
// writable span's final contents back to the slots — so a caller that
// reads its array after the call is proven, and one whose Oak body reads
// another element is refuted.
func TestVerifyFrameArrayArgument(t *testing.T) {
	put, err := parseSignatureWithBody("put: (v: [*]u32, i: u32, x: u32) -> () {\n  v[i] = x\n}")
	if err != nil {
		t.Fatal(err)
	}
	pair := func(t *testing.T, decl, asmBody, oakBody string) Verdict {
		t.Helper()
		unit, errs := ParseUnit("v.oakasm", decl+" = {\n"+asmBody+"\n}\n")
		if len(errs) != 0 {
			t.Fatal(errs)
		}
		sig, err := parseSignature(decl)
		if err != nil {
			t.Fatal(err)
		}
		unit.Functions[0].Callees = map[string]*ast.FunctionStatement{"put": put}
		if findings := Check(unit.Functions[0], sig, map[string]bool{"put": true}); len(findings) != 0 {
			t.Fatalf("checker: %v", findings)
		}
		spec, err := parseSignatureWithBody(decl + " = " + oakBody)
		if err != nil {
			t.Fatal(err)
		}
		return Verify(unit.Functions[0], sig, spec.Body)
	}
	// set_one: (x: u32) -> u32 { buf: [2]u32; put(span(&buf), u32(1), x); buf[1] }
	// The array is zero-filled at [sp, #16], its address and length are
	// the span pair, and the element is read back after the call.
	asmBody := "  bind w0 = x\n  clobber x0, x1, x2, x3, x9, x19, x29, x30\n  frame 48\n  sub sp, sp, #48\n  stp x29, x30, [sp]\n  str x19, [sp, #32]\n  mov w19, w0\n  str xzr, [sp, #16]\n  add x0, sp, #16\n  movz w1, #2\n  movz w2, #1\n  mov w3, w19\n  bl put\n  ldr w0, [sp, #20]\n  ldr x19, [sp, #32]\n  ldp x29, x30, [sp]\n  add sp, sp, #48\n  ret"
	v := pair(t, "set_one: (x: u32) -> u32", asmBody, "{\n  buf: [2]u32\n  put(span(&buf), u32(1), x)\n  buf[1]\n}")
	if v.Kind != VerdictProven {
		t.Fatalf("a read of the element the callee stored must be proven, got %s: %s", v.Kind, v.Message)
	}
	// The other element stayed zero: the Oak body reading it is a mismatch
	// against the machine's read of the stored one.
	v = pair(t, "set_one: (x: u32) -> u32", asmBody, "{\n  buf: [2]u32\n  put(span(&buf), u32(1), x)\n  buf[0]\n}")
	if v.Kind != VerdictMismatch {
		t.Fatalf("reading the untouched element must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	// A length that is not a constant is no owned array.
	v = pair(t, "set_one: (x: u32) -> u32", strings.Replace(asmBody, "  movz w1, #2\n", "  mov w1, w19\n", 1), "{\n  buf: [2]u32\n  put(span(&buf), u32(1), x)\n  buf[1]\n}")
	if v.Kind != VerdictTrusted || !strings.Contains(v.Message, "its length is not a constant") {
		t.Fatalf("a variable length must stay trusted with the reason, got %s: %s", v.Kind, v.Message)
	}
}

// The RV64 lane: the array's frame address by `addi a0, sp, off`, its
// length by `li a1, N`, the callee reached by `call`.
func TestRV64VerifyFrameArrayArgument(t *testing.T) {
	put, err := parseSignatureWithBody("put: (v: [*]u32, i: u32, x: u32) -> () {\n  v[i] = x\n}")
	if err != nil {
		t.Fatal(err)
	}
	pair := func(t *testing.T, decl, asmBody, oakBody string) Verdict {
		t.Helper()
		fn, errs := rv64Unit(t, decl, asmBody)
		if len(errs) != 0 {
			t.Fatalf("parse: %v", errs)
		}
		sig, err := parseSignature(decl)
		if err != nil {
			t.Fatal(err)
		}
		fn.Callees = map[string]*ast.FunctionStatement{"put": put}
		if findings := Check(fn, sig, map[string]bool{"put": true}); len(findings) != 0 {
			t.Fatalf("checker: %v", findings)
		}
		spec, err := parseSignatureWithBody(decl + " = " + oakBody)
		if err != nil {
			t.Fatal(err)
		}
		return Verify(fn, sig, spec.Body)
	}
	asmBody := "  bind a0 = x\n  clobber a0, a1, a2, a3\n  frame 48\n  addi sp, sp, -48\n  sd ra, 0(sp)\n  sd s1, 8(sp)\n  mv s1, a0\n  sd zero, 16(sp)\n  addi a0, sp, 16\n  li a1, 2\n  li a2, 1\n  mv a3, s1\n  call put\n  lw a0, 20(sp)\n  ld s1, 8(sp)\n  ld ra, 0(sp)\n  addi sp, sp, 48\n  ret"
	v := pair(t, "set_one: (x: u32) -> u32", asmBody, "{\n  buf: [2]u32\n  put(span(&buf), u32(1), x)\n  buf[1]\n}")
	if v.Kind != VerdictProven {
		t.Fatalf("a read of the element the callee stored must be proven, got %s: %s", v.Kind, v.Message)
	}
	v = pair(t, "set_one: (x: u32) -> u32", asmBody, "{\n  buf: [2]u32\n  put(span(&buf), u32(1), x)\n  buf[0]\n}")
	if v.Kind != VerdictMismatch {
		t.Fatalf("reading the untouched element must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
}
