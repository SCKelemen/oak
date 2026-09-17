package compiler

import (
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/nativegen"
	"github.com/SCKelemen/oak/opt"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

func TestNativeAllocationReuseDoesNotReuseAdmissionOrVerdicts(t *testing.T) {
	t.Setenv("OAK_VERIFY_CACHE", "0")
	t.Setenv("OAK_VERIFY_BUDGET", "")
	p := parser.New(layout.New(scanner.New("calc: (): u32 { u32(7) }")))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatal(errs)
	}
	fn := program.Statements[0].(*ast.FunctionStatement)
	verified, cached := 0, 0
	driver := &nativeDriver{source: fn, functions: map[string]*ast.FunctionStatement{"calc": fn},
		symbols: map[string]bool{"calc": true}, verdicts: map[*asm.Function]asm.Verdict{}, verified: &verified, fromCache: &cached}
	lower := func() *opt.Candidate {
		t.Helper()
		candidate := opt.Identity(nativegen.Lane{Arch: asm.ArchArm64, NoReductions: true, Reallocate: true})
		if err := driver.Materialize(candidate); err != nil {
			t.Fatal(err)
		}
		if findings := driver.Check(candidate); len(findings) != 0 {
			t.Fatal(findings)
		}
		return candidate
	}
	cold, warm := lower(), lower()
	if cold.Body == warm.Body || driver.Key(cold) != driver.Key(warm) {
		t.Fatal("reuse did not produce an identical, fresh candidate")
	}
	for _, candidate := range []*opt.Candidate{cold, warm} {
		if verdict := driver.Validate(candidate); verdict.Outcome != opt.Proven || verdict.Cached {
			t.Fatalf("candidate did not freshly prove: %+v", verdict)
		}
	}
	if verified != 2 || cached != 0 || driver.compileSession.ReallocationStats().Hits != 1 {
		t.Fatal("an allocation hit bypassed independent validation")
	}
	// Same legal footprint, wrong returned constant: an allocation hit is
	// only a proposal, never authority for a later mutated machine body.
	body := warm.Body.(*asm.Function)
	changed := false
	for i, item := range body.Items {
		instruction, ok := item.(asm.Instruction)
		if !ok || instruction.Mnemonic != "movz" || len(instruction.Operands) != 2 {
			continue
		}
		if immediate, ok := instruction.Operands[1].(asm.Immediate); ok && immediate.Value == 7 {
			immediate.Value++
			instruction.Operands[1] = immediate
			body.Items[i] = instruction
			changed = true
			break
		}
	}
	if !changed {
		t.Fatal("missing constant result instruction")
	}
	if findings := driver.Check(warm); len(findings) != 0 {
		t.Fatalf("negative changed the legal footprint: %v", findings)
	}
	if verdict := driver.Validate(warm); verdict.Outcome != opt.Mismatch {
		t.Fatalf("allocation hit licensed incorrect code: %+v", verdict)
	}
	fresh := lower()
	if driver.Key(fresh) != driver.Key(cold) {
		t.Fatal("mutating a returned candidate poisoned the allocation cache")
	}
	if verdict := driver.Validate(fresh); verdict.Outcome != opt.Proven || verdict.Cached {
		t.Fatalf("fresh copy did not prove: %+v", verdict)
	}
	fresh.Body.(*asm.Function).Items = append(fresh.Body.(*asm.Function).Items, asm.Instruction{Mnemonic: "invalid-instruction"})
	if findings := driver.Check(fresh); len(findings) == 0 {
		t.Fatal("allocation reuse bypassed seam admission")
	}
}
