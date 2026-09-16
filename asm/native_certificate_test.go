package asm

import (
	"strings"
	"testing"
)

func nativeCertificateCase(t *testing.T, path, decl, oakBody, asmBody string) (CNF, *Function) {
	t.Helper()
	unit, errs := ParseUnit(path, decl+" = {\n"+asmBody+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	spec, err := parseSignatureWithBody(decl + " = " + oakBody)
	if err != nil {
		t.Fatal(err)
	}
	cnf, reason, ok := ExportNativeEqualityCNF(unit.Functions[0], spec)
	if !ok {
		t.Fatalf("native equality CNF refused: %s", reason)
	}
	return cnf, unit.Functions[0]
}

func TestExportNativeEqualityCNFDeterministicAcrossLanes(t *testing.T) {
	decl := "distribute: (a, b, c: u32) -> u32"
	oakBody := "a & (b | c)"
	cases := []struct {
		name, path, body string
	}{
		{
			name: "arm64",
			path: "v.arm64.oakasm",
			body: "  bind w0 = a\n  bind w1 = b\n  bind w2 = c\n  clobber w9\n  and w9, w0, w1\n  and w0, w0, w2\n  orr w0, w9, w0\n  ret",
		},
		{
			name: "rv64",
			path: "v.rv64.oakasm",
			body: "  bind a0 = a\n  bind a1 = b\n  bind a2 = c\n  clobber t0\n  and t0, a0, a1\n  and a0, a0, a2\n  or a0, t0, a0\n  ret",
		},
	}
	for _, test := range cases {
		t.Run(test.name, func(t *testing.T) {
			first, fn := nativeCertificateCase(t, test.path, decl, oakBody, test.body)
			if first.Settled != nil || first.Text == "" || first.Clauses == 0 || first.Variables == 0 {
				t.Fatalf("wanted a nontrivial CNF, got %+v", first)
			}
			spec, err := parseSignatureWithBody(decl + " = " + oakBody)
			if err != nil {
				t.Fatal(err)
			}
			second, reason, ok := ExportNativeEqualityCNF(fn, spec)
			if !ok || reason != "" || second.Text != first.Text {
				t.Fatalf("regeneration drifted: ok=%v reason=%q\nfirst:\n%s\nsecond:\n%s", ok, reason, first.Text, second.Text)
			}
			if !strings.HasPrefix(first.Text, "c oak native equality: "+fn.Arch+":"+fn.Name+"\n") {
				t.Fatalf("formula does not identify its lane and unit: %q", first.Text)
			}
		})
	}
}

func TestExportNativeEqualityCNFBindsReferenceAndMachineTerms(t *testing.T) {
	decl := "combine: (a, b: u32) -> u32"
	correct, _ := nativeCertificateCase(t, "v.arm64.oakasm", decl, "a | b", "  bind w0 = a\n  bind w1 = b\n  orr w0, w0, w1\n  ret")
	wrongSource, _ := nativeCertificateCase(t, "v.arm64.oakasm", decl, "a ^ b", "  bind w0 = a\n  bind w1 = b\n  orr w0, w0, w1\n  ret")
	wrongMachine, _ := nativeCertificateCase(t, "v.arm64.oakasm", decl, "a | b", "  bind w0 = a\n  bind w1 = b\n  and w0, w0, w1\n  ret")
	if correct.Text == wrongSource.Text {
		t.Fatal("changing the exact Oak reference body did not change the formula")
	}
	if correct.Text == wrongMachine.Text {
		t.Fatal("changing the machine operation did not change the formula")
	}
}

func TestExportNativeEqualityCNFClosedSubsetRefusals(t *testing.T) {
	tests := []struct {
		name, path, decl, oak, body, reason string
	}{
		{
			name: "seam rejection", path: "v.arm64.oakasm",
			decl: "f: (a: u32) -> u32", oak: "a", body: "  mov w0, #1\n  ret",
			reason: "seam checker refused",
		},
		{
			name: "span parameter", path: "v.arm64.oakasm",
			decl: "f: (v: []u8) -> u32", oak: "u32(0)", body: "  bind x0, w1 = v\n  mov w0, #0\n  ret",
			reason: "parameter types outside",
		},
		{
			name: "float result", path: "v.arm64.oakasm",
			decl: "f: (a: f32) -> f32", oak: "a", body: "  bind s0 = a\n  ret",
			reason: "parameter types outside",
		},
		{
			name: "dead rv64 float work", path: "v.rv64.oakasm",
			decl: "f: (a: u32) -> u32", oak: "a", body: "  bind a0 = a\n  clobber ft0\n  fmv.w.x ft0, a0\n  ret",
			reason: "floating-point or vector register files",
		},
		{
			name: "source loop", path: "v.arm64.oakasm",
			decl: "f: (a: u32) -> u32", oak: "{ i: u32 = u32(0); while i < u32(1) { i = i + u32(1) }; a }", body: "  bind w0 = a\n  ret",
			reason: "source loops",
		},
		{
			name: "source trap", path: "v.arm64.oakasm",
			decl: "f: (a: u32) -> u32", oak: "{ assert(a != u32(0)); a }", body: "  bind w0 = a\n  ret",
			reason: "Oak trap obligations",
		},
		{
			name: "division operation", path: "v.arm64.oakasm",
			decl: "f: (a, b: u32) -> u32", oak: "a / b", body: "  bind w0 = a\n  bind w1 = b\n  udiv w0, w0, w1\n  ret",
			reason: "Oak trap obligations",
		},
		{
			name: "system capability", path: "v.arm64.oakasm",
			decl: "f: () -> u64", oak: "u64(0)", body: "  system\n  mrs x0, cntvct_el0\n  ret",
			reason: "system-capability bodies",
		},
		{
			name: "machine call", path: "v.arm64.oakasm",
			decl: "f: (a: u32) -> u32", oak: "a", body: "  bind w0 = a\n  bl helper\n  ret",
			reason: "seam checker refused",
		},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			unit, errs := ParseUnit(test.path, test.decl+" = {\n"+test.body+"\n}\n")
			if len(errs) != 0 {
				t.Fatal(errs)
			}
			spec, err := parseSignatureWithBody(test.decl + " = " + test.oak)
			if err != nil {
				t.Fatal(err)
			}
			if _, reason, ok := ExportNativeEqualityCNF(unit.Functions[0], spec); ok || !strings.Contains(reason, test.reason) {
				t.Fatalf("ok=%v reason=%q, want refusal containing %q", ok, reason, test.reason)
			}
		})
	}
}

func TestExportNativeEqualityCNFAllowsStackLocalMemory(t *testing.T) {
	cnf, _ := nativeCertificateCase(t, "v.arm64.oakasm", "spill: (a: u64) -> u64", "a",
		"  bind x0 = a\n  frame 16\n  str x0, [sp, #-16]!\n  ldr x0, [sp], #16\n  ret")
	if cnf.Settled == nil || cnf.Settled.Kind != DecisionProven {
		t.Fatalf("an identity through private stack memory should settle, got %+v", cnf)
	}
}

func TestExportNativeEqualityCNFRefusesMalformedSignature(t *testing.T) {
	_, fn := nativeCertificateCase(t, "v.arm64.oakasm", "identity: (a: u32) -> u32", "a", "  bind w0 = a\n  ret")
	spec, err := parseSignatureWithBody("identity: (a: u32) -> u32 = a")
	if err != nil {
		t.Fatal(err)
	}
	fn.Signature = nil
	if _, reason, ok := ExportNativeEqualityCNF(fn, spec); ok || !strings.Contains(reason, "signature is missing") {
		t.Fatalf("malformed signature: ok=%v reason=%q", ok, reason)
	}
}

func TestExportNativeEqualityCNFRefusesMismatchedIdentity(t *testing.T) {
	_, fn := nativeCertificateCase(t, "v.arm64.oakasm", "identity: (a: u32) -> u32", "a", "  bind w0 = a\n  ret")
	other, err := parseSignatureWithBody("other: (a: u32) -> u32 = a")
	if err != nil {
		t.Fatal(err)
	}
	if _, reason, ok := ExportNativeEqualityCNF(fn, other); ok || !strings.Contains(reason, "identity mismatch") {
		t.Fatalf("mismatched declaration: ok=%v reason=%q", ok, reason)
	}

	identity, err := parseSignatureWithBody("identity: (a: u32) -> u32 = a")
	if err != nil {
		t.Fatal(err)
	}
	fn.Signature.Name = nil
	if _, reason, ok := ExportNativeEqualityCNF(fn, identity); ok || !strings.Contains(reason, "name is missing") {
		t.Fatalf("missing signature name: ok=%v reason=%q", ok, reason)
	}
}
