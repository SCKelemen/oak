package asm

import (
	"strings"
	"testing"
)

func nativeBitwiseAuditCase(t *testing.T, path, decl, oakBody, asmBody string) NativeBitwiseEqualityAudit {
	t.Helper()
	unit, errs := ParseUnit(path, decl+" = {\n"+asmBody+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	spec, err := parseSignatureWithBody(decl + " = " + oakBody)
	if err != nil {
		t.Fatal(err)
	}
	audit, reason, ok := ExportNativeBitwiseEqualityAudit(unit.Functions[0], spec)
	if !ok {
		t.Fatalf("native bitwise equality audit refused: %s", reason)
	}
	return audit
}

func TestNativeBitwiseEqualityAuditAcrossLanes(t *testing.T) {
	decl := "distribute: (a, b, c: u64) -> u64"
	oakBody := "a & (b | c)"
	tests := []struct {
		name string
		path string
		body string
	}{
		{
			name: "arm64",
			path: "v.arm64.oakasm",
			body: "  bind x0 = a\n  bind x1 = b\n  bind x2 = c\n  clobber x9\n  and x9, x0, x1\n  and x0, x0, x2\n  orr x0, x9, x0\n  ret",
		},
		{
			name: "rv64",
			path: "v.rv64.oakasm",
			body: "  bind a0 = a\n  bind a1 = b\n  bind a2 = c\n  clobber t0\n  and t0, a0, a1\n  and a0, a0, a2\n  or a0, t0, a0\n  ret",
		},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			audit := nativeBitwiseAuditCase(t, test.path, decl, oakBody, test.body)
			if _, settled := audit.Settled(); settled {
				t.Fatal("nontrivial distributivity audit settled without a formula")
			}
			if audit.Variables() == 0 || audit.Clauses() == 0 || audit.DIMACS() == "" {
				t.Fatalf("incomplete audit: %d variables, %d clauses, %d bytes", audit.Variables(), audit.Clauses(), len(audit.DIMACS()))
			}
			if !strings.HasPrefix(audit.DIMACS(), "c oak native bitwise equality: "+unitArchFromPath(test.path)+":distribute\n") {
				t.Fatalf("formula has the wrong identity header: %.80q", audit.DIMACS())
			}
		})
	}
}

func unitArchFromPath(path string) string {
	if strings.Contains(path, ".rv64.") {
		return ArchRV64
	}
	return ArchArm64
}

func TestNativeBitwiseEqualityAuditSettlesIdentity(t *testing.T) {
	audit := nativeBitwiseAuditCase(t, "v.arm64.oakasm", "identity: (a: u16) -> u16", "a", "  bind w0 = a\n  ret")
	settled, ok := audit.Settled()
	if !ok || settled.Kind != DecisionProven || audit.DIMACS() != "" {
		t.Fatalf("identity did not settle through replay: %+v, ok=%v, formula=%q", settled, ok, audit.DIMACS())
	}
}

func TestNativeBitwiseEqualityAuditBindsExactSourceAndMachineTerms(t *testing.T) {
	decl := "combine: (a, b: u64) -> u64"
	correct := nativeBitwiseAuditCase(t, "v.arm64.oakasm", decl, "a | b",
		"  bind x0 = a\n  bind x1 = b\n  orr x0, x0, x1\n  ret")
	wrongSource := nativeBitwiseAuditCase(t, "v.arm64.oakasm", decl, "a ^ b",
		"  bind x0 = a\n  bind x1 = b\n  orr x0, x0, x1\n  ret")
	wrongMachine := nativeBitwiseAuditCase(t, "v.arm64.oakasm", decl, "a | b",
		"  bind x0 = a\n  bind x1 = b\n  and x0, x0, x1\n  ret")
	if correct.DIMACS() == wrongSource.DIMACS() {
		t.Fatal("changing the exact Oak term did not change the direct-disequality formula")
	}
	if correct.DIMACS() == wrongMachine.DIMACS() {
		t.Fatal("changing the exact machine term did not change the direct-disequality formula")
	}
}

func TestNativeBitwiseEqualityAuditRefusesBroaderTerms(t *testing.T) {
	tests := []struct {
		name, decl, oak, body, reason string
	}{
		{"arithmetic", "f: (a, b: u32) -> u32", "a + b", "  bind w0 = a\n  bind w1 = b\n  add w0, w0, w1\n  ret", `operation "add" outside`},
		{"comparison", "f: (a, b: u32) -> Bool", "a == b", "  bind w0 = a\n  bind w1 = b\n  cmp w0, w1\n  cset w0, eq\n  ret", "term kind"},
		{"shift", "f: (a, b: u32) -> u32", "a << b", "  bind w0 = a\n  bind w1 = b\n  lsl w0, w0, w1\n  ret", "trap obligations"},
		{"fresh frame byte", "f: () -> u8", "u8(0)", "  frame 16\n  sub sp, sp, #16\n  ldrb w0, [sp]\n  add sp, sp, #16\n  ret", "fresh inputs"},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			unit, errs := ParseUnit("v.arm64.oakasm", test.decl+" = {\n"+test.body+"\n}\n")
			if len(errs) != 0 {
				t.Fatal(errs)
			}
			spec, err := parseSignatureWithBody(test.decl + " = " + test.oak)
			if err != nil {
				t.Fatal(err)
			}
			if _, reason, ok := ExportNativeBitwiseEqualityAudit(unit.Functions[0], spec); ok || !strings.Contains(reason, test.reason) {
				t.Fatalf("ok=%v reason=%q, want refusal containing %q", ok, reason, test.reason)
			}
		})
	}
}

type nativeReplayFixture struct {
	bl         *blaster
	machine    *term
	oak        *term
	machineBit []int
	oakBit     []int
	difference int
}

func newNativeReplayFixture(t *testing.T) nativeReplayFixture {
	t.Helper()
	widths := map[string]int{"a": 8, "b": 8}
	machine := &term{kind: termBinary, width: 8, op: "xor",
		left:  &term{kind: termBinary, width: 8, op: "and", left: paramTerm("a", 8), right: paramTerm("b", 8)},
		right: constTerm(0x5a, 8)}
	oak := &term{kind: termBinary, width: 8, op: "or",
		left:  &term{kind: termBinary, width: 8, op: "xor", left: paramTerm("a", 8), right: constTerm(0xa5, 8)},
		right: paramTerm("b", 8)}
	bl := newCNFBlaster([]string{"a", "b"}, widths)
	machineBits := bl.blast(machine)
	oakBits := bl.blast(oak)
	difference := bddFalse
	for bit := range machineBits {
		difference = bl.apply(opOr, difference, bl.apply(opXor, machineBits[bit], oakBits[bit]))
	}
	if bl.exceeded() {
		t.Fatal("fixture exceeded its clause budget")
	}
	return nativeReplayFixture{bl: bl, machine: machine, oak: oak, machineBit: machineBits, oakBit: oakBits, difference: difference}
}

func checkNativeReplayFixture(f nativeReplayFixture) error {
	return validateNativeBitwiseRoots(f.bl, f.machine, f.oak, f.difference)
}

func TestNativeCNFTermRootReplayRefusesMutation(t *testing.T) {
	if err := checkNativeReplayFixture(newNativeReplayFixture(t)); err != nil {
		t.Fatalf("valid replay refused: %v", err)
	}
	tests := []struct {
		name   string
		mutate func(nativeReplayFixture)
	}{
		{"term memo root", func(f nativeReplayFixture) { f.bl.memo[f.machine][0] ^= 1 }},
		{"missing input", func(f nativeReplayFixture) { delete(f.bl.cnf.inputs, 0) }},
		{"extra input", func(f nativeReplayFixture) { f.bl.cnf.inputs[999] = 1 }},
		{"extra term memo", func(f nativeReplayFixture) { f.bl.memo[constTerm(0, 8)] = make([]int, 8) }},
		{"gate operation", func(f nativeReplayFixture) { f.bl.cnf.gates[0].op = 99 }},
		{"gate output", func(f nativeReplayFixture) { f.bl.cnf.gates[0].out++ }},
		{"memo output", func(f nativeReplayFixture) {
			for key, output := range f.bl.cnf.memo {
				f.bl.cnf.memo[key] = output + 1
				break
			}
		}},
		{"unused valid gate", func(f nativeReplayFixture) { f.bl.apply(opAnd, f.machineBit[0], f.oakBit[1]) }},
		{"malformed term width", func(f nativeReplayFixture) { f.machine.width = 0 }},
		{"malformed constant", func(f nativeReplayFixture) {
			f.machine.right.value |= uint64(1) << 12
		}},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			fixture := newNativeReplayFixture(t)
			test.mutate(fixture)
			if err := checkNativeReplayFixture(fixture); err == nil {
				t.Fatal("mutated term/CNF snapshot was accepted")
			}
		})
	}
}

func TestNativeCNFTermRootReplayPinsFinalPolarity(t *testing.T) {
	fixture := newNativeReplayFixture(t)
	if err := validateNativeBitwiseRoots(fixture.bl, fixture.machine, fixture.oak, fixture.difference^1); err == nil {
		t.Fatal("complemented final root was accepted as direct disequality")
	}
}

func TestNativeCNFSettledRefusesAllocatorMutation(t *testing.T) {
	t.Run("consistent input alias", func(t *testing.T) {
		machine := paramTerm("a", 1)
		oak := paramTerm("b", 1)
		bl := newCNFBlaster([]string{"a", "b"}, map[string]int{"a": 1, "b": 1})
		machineBits := bl.blast(machine)
		_ = bl.blast(oak)
		bl.cnf.inputs[1] = bl.cnf.inputs[0]
		bl.memo[oak][0] = machineBits[0]
		if err := validateNativeBitwiseRoots(bl, machine, oak, bddFalse); err != nil {
			t.Fatalf("consistent alias should reach the independent allocator boundary: %v", err)
		}
		if _, reason, ok := serializeNativeBitwiseCNF("alias", bl, bddFalse); ok || !strings.Contains(reason, "share one allocated variable") {
			t.Fatalf("ok=%v reason=%q, want input-alias refusal", ok, reason)
		}
	})

	tests := []struct {
		name       string
		difference int
		mutate     func(*blaster)
		reason     string
	}{
		{
			name:       "input gate collision",
			difference: bddTrue,
			mutate: func(bl *blaster) {
				for source := range bl.cnf.inputs {
					bl.cnf.inputs[source] = bl.cnf.gates[0].out
					break
				}
			},
			reason: "already allocated",
		},
		{
			name:       "unaccounted variable",
			difference: bddFalse,
			mutate:     func(bl *blaster) { bl.cnf.variables++ },
			reason:     "allocator records",
		},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			fixture := newNativeReplayFixture(t)
			test.mutate(fixture.bl)
			if _, reason, ok := serializeNativeBitwiseCNF("mutated", fixture.bl, test.difference); ok || !strings.Contains(reason, test.reason) {
				t.Fatalf("ok=%v reason=%q, want allocator refusal containing %q", ok, reason, test.reason)
			}
		})
	}
}
