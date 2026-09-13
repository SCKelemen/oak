package compiler

import "testing"

// `oak run -native` panicked ("assignment to entry in nil map",
// asm/verify.go declareLocal) on any function returning a record whose
// body binds a local: the verifier's Oak lowering never initialized its
// locals table on the Verify path (docs/notes/oak-requests-2026-09-13.md
// finding 1). The standard prelude has such functions, so every `-native`
// build of a program importing std hit it. The program here is
// self-contained: the panic needs only a record-returning function that
// binds a local.
func TestE2ENativeBodiesWithRecordResultAndLocal(t *testing.T) {
	program := `package main

Pair: type = struct {
  lo: u32
  hi: u32
}

split: (x: u32): Pair {
  low: u32 = x & u32(255)
  Pair { lo: low, hi: x >> u32(8) }
}

main: (): u8 {
  p: Pair = split(u32(7))
  x: u32 = p.lo
  x == u32(7) ? { u8(0) } | { u8(1) }
}
`
	if _, err := New().WithSource("main.oak", program).WithNativeBodies().EmitC().Get(); err != nil {
		t.Fatalf("native bodies: %v", err)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_locals", New().WithSource("main.oak", program).WithNativeBodies(), "-DOAK_PORTABLE_INTRINSICS"); abnormal || code != 0 {
		t.Fatalf("exit = (%d, abnormal=%v), want 0", code, abnormal)
	}
}
