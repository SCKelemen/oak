package main

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/prove"
)

func TestNativeBitwiseEqualityCertificateCheckedAgainstRegeneratedFormula(t *testing.T) {
	decl := "distribute_bits: (a, b, c: u64) -> u64"
	oakBody := "a & (b | c)"
	lanes := []struct {
		name, path, body string
	}{
		{
			name: "arm64",
			path: "bitcert.arm64.oakasm",
			body: "  bind x0 = a\n  bind x1 = b\n  bind x2 = c\n  clobber x9\n  and x9, x0, x1\n  and x0, x0, x2\n  orr x0, x9, x0\n  ret",
		},
		{
			name: "rv64",
			path: "bitcert.rv64.oakasm",
			body: "  bind a0 = a\n  bind a1 = b\n  bind a2 = c\n  clobber t0\n  and t0, a0, a1\n  and a0, a0, a2\n  or a0, t0, a0\n  ret",
		},
	}
	for _, lane := range lanes {
		t.Run(lane.name, func(t *testing.T) {
			fn, spec := nativeCertificateFixture(t, lane.path, decl, oakBody, lane.body)
			audit, reason, ok := asm.ExportNativeBitwiseEqualityAudit(fn, spec)
			if !ok || reason != "" {
				t.Fatalf("narrow formula unavailable: ok=%v reason=%q", ok, reason)
			}
			if settled, ok := audit.Settled(); ok {
				t.Fatalf("nontrivial audit settled without a formula: %+v", settled)
			}
			cnf := asm.CNF{Variables: audit.Variables(), Clauses: audit.Clauses(), Text: audit.DIMACS()}
			outcome, err := runOakSAT(cnf)
			if err != nil {
				t.Fatal(err)
			}
			if !outcome.Unsatisfiable || strings.TrimSpace(outcome.Certificate) == "" {
				t.Fatalf("narrow native formula was not certified UNSAT: %+v", outcome)
			}
			checked, err := prove.CheckNativeBitwiseEqualityCertificate(fn, spec, outcome.Certificate)
			if err != nil {
				t.Fatal(err)
			}
			if checked.Variables != audit.Variables() || checked.Clauses != audit.Clauses() || checked.LRAT.Additions == 0 {
				t.Fatalf("unexpected checked result: %+v", checked)
			}
			oak, err := runOakLRAT(audit.DIMACS(), outcome.Certificate)
			if err != nil || oak.Status != 0 || oak.Additions == 0 {
				t.Fatalf("Oak checker refused narrow native formula: %+v %v", oak, err)
			}
		})
	}
}

func TestNativeBitwiseEqualityCertificateRefusesReplayAndMalformedProof(t *testing.T) {
	decl := "distribute_bits: (a, b, c: u64) -> u64"
	body := "  bind x0 = a\n  bind x1 = b\n  bind x2 = c\n  clobber x9\n  and x9, x0, x1\n  and x0, x0, x2\n  orr x0, x9, x0\n  ret"
	fn, spec := nativeCertificateFixture(t, "bitcert.arm64.oakasm", decl, "a & (b | c)", body)
	audit, reason, ok := asm.ExportNativeBitwiseEqualityAudit(fn, spec)
	if !ok {
		t.Fatal(reason)
	}
	cnf := asm.CNF{Variables: audit.Variables(), Clauses: audit.Clauses(), Text: audit.DIMACS()}
	outcome, err := runOakSAT(cnf)
	if err != nil || !outcome.Unsatisfiable || outcome.Certificate == "" {
		t.Fatalf("certificate setup: %+v %v", outcome, err)
	}

	_, changedSpec := nativeCertificateFixture(t, "bitcert.arm64.oakasm", decl, "a ^ (b | c)", body)
	changedSourceAudit, reason, ok := asm.ExportNativeBitwiseEqualityAudit(fn, changedSpec)
	if !ok || changedSourceAudit.DIMACS() == "" || changedSourceAudit.DIMACS() == audit.DIMACS() {
		t.Fatalf("changed reference did not produce a distinct narrow formula: ok=%v reason=%q", ok, reason)
	}
	if _, err := prove.CheckNativeBitwiseEqualityCertificate(fn, changedSpec, outcome.Certificate); err == nil || !strings.Contains(err.Error(), "refused") {
		t.Fatalf("certificate replay against a changed reference was accepted: %v", err)
	}

	wrongBody := strings.Replace(body, "orr x0, x9, x0", "eor x0, x9, x0", 1)
	changedFn, sameSpec := nativeCertificateFixture(t, "bitcert.arm64.oakasm", decl, "a & (b | c)", wrongBody)
	changedMachineAudit, reason, ok := asm.ExportNativeBitwiseEqualityAudit(changedFn, sameSpec)
	if !ok || changedMachineAudit.DIMACS() == "" || changedMachineAudit.DIMACS() == audit.DIMACS() {
		t.Fatalf("changed machine body did not produce a distinct narrow formula: ok=%v reason=%q", ok, reason)
	}
	if _, err := prove.CheckNativeBitwiseEqualityCertificate(changedFn, sameSpec, outcome.Certificate); err == nil || !strings.Contains(err.Error(), "refused") {
		t.Fatalf("certificate replay against a changed machine body was accepted: %v", err)
	}

	cut := strings.LastIndex(strings.TrimSuffix(outcome.Certificate, "\n"), "\n")
	truncated := outcome.Certificate
	if cut >= 0 {
		truncated = outcome.Certificate[:cut+1]
	}
	if _, err := prove.CheckNativeBitwiseEqualityCertificate(fn, spec, truncated); err == nil {
		t.Fatal("a truncated native bitwise equality certificate was accepted")
	}
	if _, err := prove.CheckNativeBitwiseEqualityCertificate(fn, spec, "not an LRAT proof\n"); err == nil {
		t.Fatal("a malformed native bitwise equality certificate was accepted")
	}
}

func TestNativeBitwiseEqualityCertificateRefusesSettledAudit(t *testing.T) {
	fn, spec := nativeCertificateFixture(t, "bitcert.arm64.oakasm",
		"bit_identity: (a: u16) -> u16", "a", "  bind w0 = a\n  ret")
	if _, err := prove.CheckNativeBitwiseEqualityCertificate(fn, spec, "1 0 0\n"); err == nil || !strings.Contains(err.Error(), "settled") {
		t.Fatalf("settled narrow audit reached LRAT checking: %v", err)
	}
}
