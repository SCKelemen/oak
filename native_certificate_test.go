package main

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/prove"
	"github.com/SCKelemen/oak/scanner"
)

func nativeCertificateFixture(t *testing.T, path, decl, oakBody, asmBody string) (*asm.Function, *ast.FunctionStatement) {
	t.Helper()
	unit, errs := asm.ParseUnit(path, decl+" = {\n"+asmBody+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	p := parser.New(layout.New(scanner.New(decl + " = " + oakBody)))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatal(errs)
	}
	if program == nil || len(program.Statements) != 1 {
		t.Fatal("fixture did not parse as one Oak function")
	}
	spec, ok := program.Statements[0].(*ast.FunctionStatement)
	if !ok {
		t.Fatalf("fixture parsed as %T", program.Statements[0])
	}
	return unit.Functions[0], spec
}

func TestNativeEqualityCertificateCheckedAgainstExactFormula(t *testing.T) {
	decl := "distribute: (a, b, c: u32) -> u32"
	oakBody := "a & (b | c)"
	lanes := []struct {
		name, path, body string
	}{
		{
			name: "arm64",
			path: "cert.arm64.oakasm",
			body: "  bind w0 = a\n  bind w1 = b\n  bind w2 = c\n  clobber w9\n  and w9, w0, w1\n  and w0, w0, w2\n  orr w0, w9, w0\n  ret",
		},
		{
			name: "rv64",
			path: "cert.rv64.oakasm",
			body: "  bind a0 = a\n  bind a1 = b\n  bind a2 = c\n  clobber t0\n  and t0, a0, a1\n  and a0, a0, a2\n  or a0, t0, a0\n  ret",
		},
	}
	for _, lane := range lanes {
		t.Run(lane.name, func(t *testing.T) {
			fn, spec := nativeCertificateFixture(t, lane.path, decl, oakBody, lane.body)
			cnf, reason, ok := asm.ExportNativeEqualityCNF(fn, spec)
			if !ok || reason != "" || cnf.Settled != nil {
				t.Fatalf("formula unavailable: ok=%v reason=%q settled=%v", ok, reason, cnf.Settled)
			}
			outcome, err := runOakSAT(cnf)
			if err != nil {
				t.Fatal(err)
			}
			if !outcome.Unsatisfiable || outcome.Certificate == "" {
				t.Fatalf("native equality formula was not certified UNSAT: %+v", outcome)
			}
			checked, err := prove.CheckNativeEqualityCertificate(fn, spec, outcome.Certificate)
			if err != nil {
				t.Fatal(err)
			}
			if checked.Variables != cnf.Variables || checked.Clauses != cnf.Clauses || checked.LRAT.Additions == 0 {
				t.Fatalf("unexpected Go certificate result: %+v for CNF %+v", checked, cnf)
			}
			oak, err := runOakLRAT(cnf.Text, outcome.Certificate)
			if err != nil || oak.Status != 0 {
				t.Fatalf("Oak checker refused exact native formula: %+v %v", oak, err)
			}
		})
	}
}

func TestNativeEqualityCertificateRefusesReplayAndMalformedProof(t *testing.T) {
	decl := "distribute: (a, b, c: u32) -> u32"
	body := "  bind w0 = a\n  bind w1 = b\n  bind w2 = c\n  clobber w9\n  and w9, w0, w1\n  and w0, w0, w2\n  orr w0, w9, w0\n  ret"
	fn, spec := nativeCertificateFixture(t, "cert.arm64.oakasm", decl, "a & (b | c)", body)
	cnf, reason, ok := asm.ExportNativeEqualityCNF(fn, spec)
	if !ok {
		t.Fatal(reason)
	}
	outcome, err := runOakSAT(cnf)
	if err != nil || !outcome.Unsatisfiable {
		t.Fatalf("certificate setup: %+v %v", outcome, err)
	}

	_, changedSpec := nativeCertificateFixture(t, "cert.arm64.oakasm", decl, "a ^ (b | c)", body)
	if _, err := prove.CheckNativeEqualityCertificate(fn, changedSpec, outcome.Certificate); err == nil || !strings.Contains(err.Error(), "refused") {
		t.Fatalf("certificate replay against a changed reference was accepted: %v", err)
	}

	wrongBody := strings.Replace(body, "orr w0, w9, w0", "eor w0, w9, w0", 1)
	changedFn, sameSpec := nativeCertificateFixture(t, "cert.arm64.oakasm", decl, "a & (b | c)", wrongBody)
	if _, err := prove.CheckNativeEqualityCertificate(changedFn, sameSpec, outcome.Certificate); err == nil || !strings.Contains(err.Error(), "refused") {
		t.Fatalf("certificate replay against a changed machine body was accepted: %v", err)
	}

	cut := strings.LastIndex(outcome.Certificate, "\n")
	if cut > 0 {
		cut = strings.LastIndex(outcome.Certificate[:cut], "\n")
	}
	truncated := outcome.Certificate
	if cut > 0 {
		truncated = outcome.Certificate[:cut+1]
	}
	if _, err := prove.CheckNativeEqualityCertificate(fn, spec, truncated); err == nil {
		t.Fatal("a truncated native equality certificate was accepted")
	}
}
