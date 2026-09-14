package asm

import (
	"strings"
	"testing"
)

// A parameter beyond the register contract arrives in the caller's
// outgoing area (docs/spec/94-assembler.md §8, thirty-second increment):
// the executor holds it in the frame slot at its offset above the entry
// sp, at the size the caller stored it, so the body's load reads the
// parameter. The native lowering of `nine` (a byte on the stack) and of
// `twelve` (a byte, a halfword, a doubleword, and a Bool).
// verifyPacked is verifyCase for a unit whose stack parameters follow the
// native lowering's packed convention (Function.PackedStackArgs).
func verifyPacked(t *testing.T, decl, oakBody, asmBody string) Verdict {
	t.Helper()
	unit, errs := ParseUnit("v.oakasm", decl+" = {\n"+asmBody+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	unit.Functions[0].PackedStackArgs = true
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

func TestVerifyStackParameters(t *testing.T) {
	nineDecl := "nine: (a, b, c, d, e, f, g, h: u32, i: u8) -> u32"
	nine := `  bind w0 = a
  bind w1 = b
  bind w2 = c
  bind w3 = d
  bind w4 = e
  bind w5 = f
  bind w6 = g
  bind w7 = h
  bind [sp, #0] = i
  clobber x9, x10, x19
  frame 80
  sub sp, sp, #80
  str x19, [sp]
  ldrb w9, [sp, #80]
  and w9, w9, #255
  mov w19, w9
head_1:
  add w9, w0, w1
  add w9, w9, w2
  add w9, w9, w3
  add w9, w9, w4
  add w9, w9, w5
  add w9, w9, w6
  add w9, w9, w7
  mov w10, w19
  add w9, w9, w10
  mov w0, w9
ret_2:
  ldr x19, [sp]
  add sp, sp, #80
  ret`
	v := verifyPacked(t, nineDecl, "a + b + c + d + e + f + g + h + u32(i)", nine)
	if v.Kind != VerdictProven {
		t.Fatalf("nine must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := verifyPacked(t, nineDecl, "a + b + c + d + e + f + g + h", nine); v.Kind != VerdictMismatch {
		t.Fatalf("dropping the stack parameter must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	twelveDecl := "twelve: (a, b, c, d, e, f, g, h: u32, i: u8, j: u16, k: u64, m: Bool) -> u64"
	twelve := `  bind w0 = a
  bind w1 = b
  bind w2 = c
  bind w3 = d
  bind w4 = e
  bind w5 = f
  bind w6 = g
  bind w7 = h
  bind [sp, #0] = i
  bind [sp, #2] = j
  bind [sp, #8] = k
  bind [sp, #16] = m
  clobber x9, x10, x11, x19, x20, x21, x22
  frame 80
  sub sp, sp, #80
  stp x19, x20, [sp]
  stp x21, x22, [sp, #16]
  ldrb w9, [sp, #80]
  and w9, w9, #255
  mov w19, w9
  ldrh w9, [sp, #82]
  and w9, w9, #65535
  mov w20, w9
  ldr x9, [sp, #88]
  mov x21, x9
  ldr w9, [sp, #96]
  and w9, w9, #255
  mov w22, w9
head_1:
  add w9, w0, w1
  add w9, w9, w2
  add w9, w9, w3
  add w9, w9, w4
  add w9, w9, w5
  add w9, w9, w6
  add w9, w9, w7
  mov w9, w9
  mov w10, w19
  add x9, x9, x10
  mov w10, w20
  add x9, x9, x10
  add x9, x9, x21
  cbz w22, else_4
  movz x10, #1
  b endif_5
else_4:
  mov x10, xzr
endif_5:
  add x9, x9, x10
  mov x0, x9
ret_2:
  ldp x19, x20, [sp]
  ldp x21, x22, [sp, #16]
  add sp, sp, #80
  ret`
	// Four stack parameters of three widths and a Bool: the witnesses read
	// them all (the 64-bit sum of many unknowns is beyond the diagrams'
	// budget, so the verdict is evidence); dropping one is refuted.
	v = verifyPacked(t, twelveDecl, "u64(a + b + c + d + e + f + g + h) + u64(i) + u64(j) + k + (m ? u64(1) | u64(0))", twelve)
	if v.Kind != VerdictProven && v.Kind != VerdictWitnessed {
		t.Fatalf("twelve must read its stack parameters, got %s: %s", v.Kind, v.Message)
	}
	if strings.Contains(v.Message, "incoming stack area") {
		t.Fatalf("unexpected message %q", v.Message)
	}
	if v := verifyPacked(t, twelveDecl, "u64(a + b + c + d + e + f + g + h) + u64(i) + k + (m ? u64(1) | u64(0))", twelve); v.Kind != VerdictMismatch {
		t.Fatalf("dropping the halfword parameter must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
}

// The RV64 lane: a scalar beyond a0–a7 lies widened in an XLEN-sized slot
// of the caller's outgoing area, read by `ld` in the prologue.
func TestRV64VerifyStackParameters(t *testing.T) {
	decl := "nine: (a, b, c, d, e, f, g, h: u32, i: u8) -> u32"
	body := `  bind a0 = a
  bind a1 = b
  bind a2 = c
  bind a3 = d
  bind a4 = e
  bind a5 = f
  bind a6 = g
  bind a7 = h
  bind [sp, #0] = i
  clobber t0, t1
  frame 16
  addi sp, sp, -16
  sd s1, 0(sp)
  ld t0, 16(sp)
  mv s1, t0
head_1:
  mv t0, a0
  mv t1, a1
  addw t0, t0, t1
  mv t1, a2
  addw t0, t0, t1
  mv t1, a3
  addw t0, t0, t1
  mv t1, a4
  addw t0, t0, t1
  mv t1, a5
  addw t0, t0, t1
  mv t1, a6
  addw t0, t0, t1
  mv t1, a7
  addw t0, t0, t1
  mv t1, s1
  addw t0, t0, t1
  mv a0, t0
ret_2:
  ld s1, 0(sp)
  addi sp, sp, 16
  ret`
	if v := rv64Verify(t, decl, "a + b + c + d + e + f + g + h + u32(i)", body); v.Kind != VerdictProven {
		t.Fatalf("nine must be proven on RV64, got %s: %s", v.Kind, v.Message)
	}
	if v := rv64Verify(t, decl, "a + b + c + d + e + f + g + h", body); v.Kind != VerdictMismatch {
		t.Fatalf("dropping the stack parameter must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
}
