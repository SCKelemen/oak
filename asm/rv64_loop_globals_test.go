package asm

import (
	"reflect"
	"strings"
	"testing"
)

const rv64LoopGlobalOakBody = `{
  i: u32 = u32(0)
  while i < n {
    state = state + u32(1)
    i = i + u32(1)
  }
  state
}`

func TestVerifyRV64LoopCarriedPackageCell(t *testing.T) {
	verdict := verifyRV64LoopGlobal(t, "addw t2, t2, t1")
	if verdict.Kind != VerdictProven || !strings.Contains(verdict.Message, "package state it writes (state)") {
		t.Fatalf("RV64 loop-carried package cell verdict = %s (%s)", verdict.Kind, verdict.Message)
	}
}

func TestVerifyRV64LoopCarriedPackageCellRejectsWrongUpdate(t *testing.T) {
	verdict := verifyRV64LoopGlobal(t, "li t3, #2\n  addw t2, t2, t3")
	if verdict.Kind != VerdictMismatch || !strings.Contains(verdict.Message, "disagrees with its Oak body") {
		t.Fatalf("wrong RV64 loop-carried package-cell update verdict = %s (%s)", verdict.Kind, verdict.Message)
	}
}

func TestVerifyRV64PromotedLoopCellAliasesRegisterAndGlobal(t *testing.T) {
	verdict := verifyRV64PromotedLoopGlobal(t, "", "t2")
	if verdict.Kind != VerdictProven || !strings.Contains(verdict.Message, "state↔r7") || !strings.Contains(verdict.Message, "state↔global:state") {
		t.Fatalf("RV64 promoted loop-cell alias verdict = %s (%s)", verdict.Kind, verdict.Message)
	}
}

func TestVerifyRV64PromotedLoopCellRejectsDivergentGlobal(t *testing.T) {
	verdict := verifyRV64PromotedLoopGlobal(t, "li t3, #2\n  addw t3, t2, t3", "t3")
	if verdict.Kind == VerdictProven {
		t.Fatalf("divergent promoted loop cell was proven: %s", verdict.Message)
	}
}

func TestRV64LoopPackageCellDiscoveryRequiresLiveScalarGlobalAddress(t *testing.T) {
	t6 := Register{Text: "t6", Class: ClassRV64X, Num: 31, Lane: -1}
	t0 := Register{Text: "t0", Class: ClassRV64X, Num: 5, Lane: -1}
	cell := Memory{Base: t6, Mode: MemOffset}
	la := func(name string) Instruction {
		return Instruction{Mnemonic: "la", Operands: []Operand{t6, Symbol{Name: name}}}
	}
	store := Instruction{Mnemonic: "sw", Operands: []Operand{t0, cell}}
	discovered := func(items ...Item) []string {
		executor := pathExecutor{
			items: items,
			globals: map[string]Global{
				"state":     {Type: "u32", Bits: 32},
				"aggregate": {Type: "[4]u32", Aggregate: true, Size: 16},
			},
		}
		return executor.cellsStoredIn(loopShape{bodyStart: 0, bodyEnd: len(items)})
	}
	if got := discovered(la("state"), store); !reflect.DeepEqual(got, []string{"state"}) {
		t.Fatalf("live scalar-global address discovery = %v, want [state]", got)
	}
	overwrite := Instruction{Mnemonic: "li", Operands: []Operand{t6, Immediate{Value: 0}}}
	if got := discovered(la("state"), overwrite, store); len(got) != 0 {
		t.Fatalf("overwritten RV64 global-address provenance discovered %v", got)
	}
	if got := discovered(la("aggregate"), store); len(got) != 0 {
		t.Fatalf("aggregate global discovered as scalar loop-carried cell: %v", got)
	}
	if got := discovered(la("table"), store); len(got) != 0 {
		t.Fatalf("non-global data symbol discovered as loop-carried cell: %v", got)
	}
}

func verifyRV64LoopGlobal(t *testing.T, update string) Verdict {
	t.Helper()
	const declaration = "rv64_loop_global: (n: u32) -> u32"
	body := `
  bind a0 = n
  clobber t0, t1, t2, t3, t6
  li t0, #0
loop:
  sltu t1, t0, a0
  beqz t1, done
  la t6, state
  lw t2, 0(t6)
  li t1, #1
  ` + update + `
  la t6, state
  sw t2, 0(t6)
  addw t0, t0, t1
  j loop
done:
  la t6, state
  lw t0, 0(t6)
  mv a0, t0
  ret`
	fn, errs := rv64Unit(t, declaration, body)
	if len(errs) != 0 {
		t.Fatalf("parse: %v", errs)
	}
	fn.Globals = map[string]Global{"state": {Type: "u32", Bits: 32}}
	signature, err := parseSignature(declaration)
	if err != nil {
		t.Fatal(err)
	}
	if findings := Check(fn, signature, nil); len(findings) != 0 {
		t.Fatalf("checker: %v", findings)
	}
	specification, err := parseSignatureWithBody(declaration + " = " + rv64LoopGlobalOakBody)
	if err != nil {
		t.Fatal(err)
	}
	return Verify(fn, signature, specification.Body)
}

func verifyRV64PromotedLoopGlobal(t *testing.T, beforeStore, storedRegister string) Verdict {
	t.Helper()
	const declaration = "rv64_promoted_loop_global: (n: u32) -> u32"
	body := `
  bind a0 = n
  clobber t0, t1, t2, t3, t6
  la t6, state
  lw t2, 0(t6)
  li t0, #0
loop:
  sltu t1, t0, a0
  beqz t1, done
  li t1, #1
  addw t2, t2, t1
  ` + beforeStore + `
  la t6, state
  sw ` + storedRegister + `, 0(t6)
  addw t0, t0, t1
  j loop
done:
  mv a0, t2
  ret`
	fn, errs := rv64Unit(t, declaration, body)
	if len(errs) != 0 {
		t.Fatalf("parse: %v", errs)
	}
	fn.Globals = map[string]Global{"state": {Type: "u32", Bits: 32}}
	signature, err := parseSignature(declaration)
	if err != nil {
		t.Fatal(err)
	}
	if findings := Check(fn, signature, nil); len(findings) != 0 {
		t.Fatalf("checker: %v", findings)
	}
	specification, err := parseSignatureWithBody(declaration + " = " + rv64LoopGlobalOakBody)
	if err != nil {
		t.Fatal(err)
	}
	return Verify(fn, signature, specification.Body)
}
