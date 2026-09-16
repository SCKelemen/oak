package compiler

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/nativegen"
	"github.com/SCKelemen/oak/opt"
	"github.com/SCKelemen/oak/optir"
)

func TestOptIRMachineCallIdentityAllowsPhysicalReordering(t *testing.T) {
	cfg := nativeCallIdentityCFG()
	for _, arch := range []string{asm.ArchArm64, asm.ArchRV64} {
		t.Run(arch, func(t *testing.T) {
			function := nativeCallIdentityFunction(arch,
				nativeCallIdentityDirect(arch, "beta", 22, 8),
				asm.Instruction{Mnemonic: nativeCallIdentityNoop(arch), Line: 12},
				nativeCallIdentityDirect(arch, "alpha", 11, 16),
			)
			if err := checkOptIRMachineCallIdentity(cfg, function); err != nil {
				t.Fatalf("reordered occurrences rejected: %v", err)
			}
		})
	}
}

func TestOptIRMachineCallIdentityRejectsMismatches(t *testing.T) {
	cfg := nativeCallIdentityCFG()
	for _, arch := range []string{asm.ArchArm64, asm.ArchRV64} {
		arch := arch
		t.Run(arch, func(t *testing.T) {
			direct := func(target string, site uint32) asm.Instruction {
				return nativeCallIdentityDirect(arch, target, site, 4)
			}
			valid := func() *asm.Function {
				return nativeCallIdentityFunction(arch, direct("alpha", 11), direct("beta", 22))
			}
			indirect := "blr"
			if arch == asm.ArchRV64 {
				indirect = "jalr"
			}
			tests := []struct {
				name   string
				mutate func(*asm.Function)
				want   string
			}{
				{
					name: "missing occurrence",
					mutate: func(function *asm.Function) {
						function.Items = function.Items[:1]
					},
					want: "materialized occurrence(s), want 2",
				},
				{
					name: "extra occurrence",
					mutate: func(function *asm.Function) {
						function.Items = append(function.Items, direct("gamma", 33))
					},
					want: "materialized occurrence(s), want 2",
				},
				{
					name: "duplicate identity",
					mutate: func(function *asm.Function) {
						function.Items = append(function.Items, direct("alpha", 11))
					},
					want: "repeats OptIR call-site identity 11",
				},
				{
					name: "unknown identity",
					mutate: func(function *asm.Function) {
						function.Items[1] = direct("beta", 33)
					},
					want: "call site 22 to \"beta\" is missing",
				},
				{
					name: "wrong target",
					mutate: func(function *asm.Function) {
						function.Items[0] = direct("gamma", 11)
					},
					want: "call site 11 targets \"gamma\" in the machine body, want \"alpha\"",
				},
				{
					name: "vector ABI alias",
					mutate: func(function *asm.Function) {
						suffix := "_neon_abi"
						if arch == asm.ArchRV64 {
							suffix = "_rvv_abi"
						}
						function.Items[0] = direct("alpha"+suffix, 11)
					},
					want: "want \"alpha\"",
				},
				{
					name: "swapped identity targets",
					mutate: func(function *asm.Function) {
						function.Items[0] = direct("beta", 11)
						function.Items[1] = direct("alpha", 22)
					},
					want: "targets",
				},
				{
					name: "untagged direct call",
					mutate: func(function *asm.Function) {
						function.Items[0] = direct("alpha", 0)
					},
					want: "untagged direct call",
				},
				{
					name: "tagged non-call",
					mutate: func(function *asm.Function) {
						function.Items[0] = asm.Instruction{Mnemonic: nativeCallIdentityNoop(arch), Line: 4, OptIRCallSite: 11}
					},
					want: "tags non-call",
				},
				{
					name: "indirect call",
					mutate: func(function *asm.Function) {
						function.Items[0] = asm.Instruction{Mnemonic: indirect, Line: 4, OptIRCallSite: 11}
					},
					want: "unsupported indirect or linking call",
				},
				{
					name: "non-symbol target",
					mutate: func(function *asm.Function) {
						function.Items[0] = direct("alpha", 11)
						instruction := function.Items[0].(asm.Instruction)
						instruction.Operands = []asm.Operand{asm.Immediate{Value: 1}}
						function.Items[0] = instruction
					},
					want: "does not have one plain nonempty symbol",
				},
				{
					name: "empty symbol target",
					mutate: func(function *asm.Function) {
						function.Items[0] = direct("", 11)
					},
					want: "does not have one plain nonempty symbol",
				},
				{
					name: "relocation fragment target",
					mutate: func(function *asm.Function) {
						function.Items[0] = direct("alpha", 11)
						instruction := function.Items[0].(asm.Instruction)
						instruction.Operands = []asm.Operand{asm.Symbol{Name: "alpha", Lo12: true}}
						function.Items[0] = instruction
					},
					want: "does not have one plain nonempty symbol",
				},
				{
					name: "rewritten body",
					mutate: func(function *asm.Function) {
						function.Body = &ast.Identifier{Value: "rewritten"}
					},
					want: "requires the selector's body-free output",
				},
			}
			for _, test := range tests {
				t.Run(test.name, func(t *testing.T) {
					function := valid()
					test.mutate(function)
					err := checkOptIRMachineCallIdentity(cfg, function)
					if err == nil || !strings.Contains(err.Error(), test.want) {
						t.Fatalf("error = %v, want substring %q", err, test.want)
					}
				})
			}
		})
	}
}

func TestClassifyMachineCallClosedTable(t *testing.T) {
	tests := []struct {
		arch, mnemonic string
		want           machineCallForm
	}{
		{arch: asm.ArchArm64, mnemonic: "bl", want: machineDirectCall},
		{arch: asm.ArchArm64, mnemonic: "blr", want: machineOpaqueCall},
		{arch: asm.ArchArm64, mnemonic: "blraa", want: machineOpaqueCall},
		{arch: asm.ArchArm64, mnemonic: "blrab", want: machineOpaqueCall},
		{arch: asm.ArchArm64, mnemonic: "blraaz", want: machineOpaqueCall},
		{arch: asm.ArchArm64, mnemonic: "blrabz", want: machineOpaqueCall},
		{arch: asm.ArchArm64, mnemonic: "add", want: machineNonCall},
		{arch: asm.ArchRV64, mnemonic: "call", want: machineDirectCall},
		{arch: asm.ArchRV64, mnemonic: "jal", want: machineOpaqueCall},
		{arch: asm.ArchRV64, mnemonic: "jalr", want: machineOpaqueCall},
		{arch: asm.ArchRV64, mnemonic: "tail", want: machineOpaqueCall},
		{arch: asm.ArchRV64, mnemonic: "add", want: machineNonCall},
		{arch: "future", mnemonic: "bl", want: machineNonCall},
	}
	for _, test := range tests {
		if got := classifyMachineCall(test.arch, test.mnemonic); got != test.want {
			t.Errorf("classifyMachineCall(%q, %q) = %d, want %d", test.arch, test.mnemonic, got, test.want)
		}
	}
	function := nativeCallIdentityFunction("future")
	if err := checkOptIRMachineCallIdentity(nativeCallIdentityCFG(), function); err == nil || !strings.Contains(err.Error(), "does not recognize architecture") {
		t.Fatalf("unknown architecture error = %v", err)
	}
}

func TestOptIRMachineCallIdentityMatchesLeanModel(t *testing.T) {
	contents, err := os.ReadFile(filepath.Join("..", "spec", "lean", "Oak", "OptIRMachineCallIdentity.lean"))
	if err != nil {
		t.Fatal(err)
	}
	lean := strings.Join(strings.Fields(string(contents)), " ")
	for _, statement := range []string{
		`example : check expectedExample [.direct (some 2) "beta", .other, .direct (some 1) "alpha"] = true := by decide`,
		`example : check expectedExample [.direct (some 1) "alpha"] = false := by decide`,
		`example : check expectedExample [.direct (some 1) "alpha", .direct (some 2) "beta", .direct (some 3) "gamma"] = false := by decide`,
		`example : check expectedExample [.direct (some 1) "alpha", .direct (some 2) "gamma"] = false := by decide`,
		`example : check [⟨1, "alpha"⟩] [.direct (some 1) "alpha", .direct (some 1) "alpha"] = false := by decide`,
		`example : check [⟨1, "alpha"⟩] [.direct none "alpha"] = false := by decide`,
		`example : check [] [.other (some 1)] = false := by decide`,
		`example : check [] [.opaque] = false := by decide`,
	} {
		if !strings.Contains(lean, strings.Join(strings.Fields(statement), " ")) {
			t.Errorf("Lean call-identity model is missing production decision pin:\n%s", statement)
		}
	}

	cfg := optir.CFG{
		Name: "root", Entry: 1, Results: []optir.Type{"u32"},
		Blocks: []optir.Block{{
			ID: 1,
			Operations: []optir.Operation{
				nativeCallIdentityOperation(1, "alpha"),
				nativeCallIdentityOperation(2, "beta"),
			},
			Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{2}},
		}},
	}
	for _, arch := range []string{asm.ArchArm64, asm.ArchRV64} {
		direct := func(target string, site uint32) asm.Instruction {
			return nativeCallIdentityDirect(arch, target, site, 1)
		}
		cases := []struct {
			name string
			want bool
			body []asm.Instruction
		}{
			{name: "permutation", want: true, body: []asm.Instruction{direct("beta", 2), {Mnemonic: "nop"}, direct("alpha", 1)}},
			{name: "missing", body: []asm.Instruction{direct("alpha", 1)}},
			{name: "extra", body: []asm.Instruction{direct("alpha", 1), direct("beta", 2), direct("gamma", 3)}},
			{name: "target", body: []asm.Instruction{direct("alpha", 1), direct("gamma", 2)}},
			{name: "duplicate", body: []asm.Instruction{direct("alpha", 1), direct("alpha", 1)}},
			{name: "untagged", body: []asm.Instruction{direct("alpha", 0)}},
			{name: "tagged noncall", body: []asm.Instruction{{Mnemonic: "nop", OptIRCallSite: 1}}},
		}
		for _, test := range cases {
			t.Run(arch+"/"+test.name, func(t *testing.T) {
				accepted := checkOptIRMachineCallIdentity(cfg, nativeCallIdentityFunction(arch, test.body...)) == nil
				if accepted != test.want {
					t.Fatalf("accepted = %v, want %v", accepted, test.want)
				}
			})
		}
	}
}

func TestNativeDriverChecksOptIRMachineCallIdentity(t *testing.T) {
	cfg := nativeCallIdentityCFG()
	function := nativeCallIdentityFunction(asm.ArchArm64,
		nativeCallIdentityDirect(asm.ArchArm64, "wrong", 11, 4),
		nativeCallIdentityDirect(asm.ArchArm64, "beta", 22, 8),
	)
	source := nativeMaterializationFunction(cfg.Name)
	function.Signature = source
	candidate := opt.Identity(nativegen.Lane{Arch: asm.ArchArm64, UseOptIR: true, OptIR: &cfg})
	candidate.Body = function
	driver := &nativeDriver{source: source, symbols: map[string]bool{"wrong": true, "beta": true}}

	findings := driver.Check(candidate)
	if !nativeCallIdentityHasFinding(findings, "OptIR call site 11 targets \"wrong\"") {
		t.Fatalf("native driver did not report OptIR identity mismatch: %v", findings)
	}

	missingAuthority := opt.Identity(nativegen.Lane{Arch: asm.ArchArm64, UseOptIR: true})
	missingAuthority.Body = function
	if findings := driver.Check(missingAuthority); !nativeCallIdentityHasFinding(findings, "has no CFG authority") {
		t.Fatalf("native driver did not reject missing CFG authority: %v", findings)
	}
}

func nativeCallIdentityCFG() optir.CFG {
	return optir.CFG{
		Name:    "root",
		Entry:   1,
		Results: []optir.Type{"u32"},
		Blocks: []optir.Block{{
			ID:         1,
			Operations: []optir.Operation{nativeCallIdentityOperation(11, "alpha"), nativeCallIdentityOperation(22, "beta")},
			Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{22}},
		}},
	}
}

func nativeCallIdentityOperation(id optir.ValueID, target string) optir.Operation {
	return optir.Operation{
		Code:       optir.OpCall,
		Results:    []optir.Value{{ID: id, Type: "u32"}},
		Effects:    []optir.Effect{optir.EffectCall},
		Attributes: []optir.Attribute{{Name: optir.AttributeCallee, Value: target}},
	}
}

func nativeCallIdentityFunction(arch string, instructions ...asm.Instruction) *asm.Function {
	items := make([]asm.Item, len(instructions))
	for index, instruction := range instructions {
		items[index] = instruction
	}
	return &asm.Function{Name: "root", Arch: arch, Items: items}
}

func nativeCallIdentityDirect(arch, target string, site uint32, line int) asm.Instruction {
	mnemonic := "bl"
	if arch == asm.ArchRV64 {
		mnemonic = "call"
	}
	return asm.Instruction{
		Mnemonic:      mnemonic,
		Operands:      []asm.Operand{asm.Symbol{Name: target}},
		Line:          line,
		OptIRCallSite: site,
	}
}

func nativeCallIdentityNoop(arch string) string {
	if arch == asm.ArchRV64 {
		return "nop"
	}
	return "nop"
}

func nativeCallIdentityHasFinding(findings []string, fragment string) bool {
	for _, finding := range findings {
		if strings.Contains(finding, fragment) {
			return true
		}
	}
	return false
}
