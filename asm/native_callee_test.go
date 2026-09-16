package asm

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
)

func TestResolveNativeCalleeUsesCanonicalLaneIdentity(t *testing.T) {
	scalar := nativeCalleeDeclaration(t, "inc: (x: u32) -> u32 = x + u32(1)")
	vector := nativeCalleeDeclaration(t, "double: (v: simd.U8x16) -> simd.U8x16 = simd.add_u8x16(v, v)")
	other := nativeCalleeDeclaration(t, "other: (x: u32) -> u32 = x + u32(2)")

	for _, arch := range []string{ArchArm64, ArchRV64} {
		arch := arch
		t.Run(arch, func(t *testing.T) {
			activeSuffix := VectorEntrySuffix(arch)
			oppositeSuffix := VectorEntrySuffix(ArchArm64)
			if arch == ArchArm64 {
				oppositeSuffix = VectorEntrySuffix(ArchRV64)
			}
			tests := []struct {
				name     string
				symbol   string
				callees  func() map[string]*ast.FunctionStatement
				want     *ast.FunctionStatement
				resolved bool
			}{
				{
					name:   "canonical scalar",
					symbol: "inc",
					callees: func() map[string]*ast.FunctionStatement {
						return map[string]*ast.FunctionStatement{"inc": scalar}
					},
					want: scalar, resolved: true,
				},
				{
					name:   "active vector entry",
					symbol: "double" + activeSuffix,
					callees: func() map[string]*ast.FunctionStatement {
						return map[string]*ast.FunctionStatement{"double": vector}
					},
					want: vector, resolved: true,
				},
				{
					name:   "unsuffixed vector uses another ABI",
					symbol: "double",
					callees: func() map[string]*ast.FunctionStatement {
						return map[string]*ast.FunctionStatement{"double": vector}
					},
				},
				{
					name:   "scalar cannot claim vector entry",
					symbol: "inc" + activeSuffix,
					callees: func() map[string]*ast.FunctionStatement {
						return map[string]*ast.FunctionStatement{"inc": scalar}
					},
				},
				{
					name:   "opposite lane vector entry",
					symbol: "double" + oppositeSuffix,
					callees: func() map[string]*ast.FunctionStatement {
						return map[string]*ast.FunctionStatement{"double": vector}
					},
				},
				{
					name:   "arbitrary alias key",
					symbol: "alias",
					callees: func() map[string]*ast.FunctionStatement {
						return map[string]*ast.FunctionStatement{"alias": scalar}
					},
				},
				{
					name:   "key and declaration name disagree",
					symbol: "inc",
					callees: func() map[string]*ast.FunctionStatement {
						return map[string]*ast.FunctionStatement{"inc": other}
					},
				},
				{
					name:   "exact suffixed shadow is ambiguous",
					symbol: "double" + activeSuffix,
					callees: func() map[string]*ast.FunctionStatement {
						return map[string]*ast.FunctionStatement{
							"double":                vector,
							"double" + activeSuffix: scalar,
						}
					},
				},
				{
					name:   "double suffix",
					symbol: "double" + activeSuffix + activeSuffix,
					callees: func() map[string]*ast.FunctionStatement {
						return map[string]*ast.FunctionStatement{"double": vector}
					},
				},
				{
					name:   "empty suffix base",
					symbol: activeSuffix,
					callees: func() map[string]*ast.FunctionStatement {
						empty := nativeCalleeDeclaration(t, "empty: (x: u32) -> u32 = x")
						empty.Name.Value = ""
						return map[string]*ast.FunctionStatement{"": empty}
					},
				},
				{
					name:   "nil callee",
					symbol: "inc",
					callees: func() map[string]*ast.FunctionStatement {
						return map[string]*ast.FunctionStatement{"inc": nil}
					},
				},
				{
					name:   "nil declaration name",
					symbol: "inc",
					callees: func() map[string]*ast.FunctionStatement {
						unnamed := nativeCalleeDeclaration(t, "inc: (x: u32) -> u32 = x")
						unnamed.Name = nil
						return map[string]*ast.FunctionStatement{"inc": unnamed}
					},
				},
				{
					name:   "empty declaration name",
					symbol: "inc",
					callees: func() map[string]*ast.FunctionStatement {
						unnamed := nativeCalleeDeclaration(t, "inc: (x: u32) -> u32 = x")
						unnamed.Name.Value = ""
						return map[string]*ast.FunctionStatement{"inc": unnamed}
					},
				},
				{
					name:   "nil parameter",
					symbol: "inc",
					callees: func() map[string]*ast.FunctionStatement {
						malformed := nativeCalleeDeclaration(t, "inc: (x: u32) -> u32 = x")
						malformed.Parameters = append(malformed.Parameters, nil)
						return map[string]*ast.FunctionStatement{"inc": malformed}
					},
				},
				{
					name:   "nil parameter name",
					symbol: "inc",
					callees: func() map[string]*ast.FunctionStatement {
						malformed := nativeCalleeDeclaration(t, "inc: (x: u32) -> u32 = x")
						malformed.Parameters[0].Name = nil
						return map[string]*ast.FunctionStatement{"inc": malformed}
					},
				},
				{
					name:   "nil parameter type",
					symbol: "inc",
					callees: func() map[string]*ast.FunctionStatement {
						malformed := nativeCalleeDeclaration(t, "inc: (x: u32) -> u32 = x")
						malformed.Parameters[0].Type = nil
						return map[string]*ast.FunctionStatement{"inc": malformed}
					},
				},
			}
			for _, test := range tests {
				t.Run(test.name, func(t *testing.T) {
					got, resolved := ResolveNativeCallee(arch, test.symbol, test.callees())
					if resolved != test.resolved || got != test.want {
						t.Fatalf("ResolveNativeCallee(%q) = (%p, %v), want (%p, %v)", test.symbol, got, resolved, test.want, test.resolved)
					}
				})
			}
		})
	}
}

func TestVerifyRV64VectorCallUsesActiveNativeEntry(t *testing.T) {
	callee := nativeCalleeDeclaration(t, "double: (v: simd.U8x16) -> simd.U8x16 = simd.add_u8x16(v, v)")
	decl := "through_double: (v: simd.U8x16) -> simd.U8x16"
	symbol := "double" + VectorEntrySuffix(ArchRV64)
	unit, errs := ParseUnit("vector_call.rv64.oakasm", decl+" = {\n  bind v8 = v\n  frame 16\n  addi sp, sp, -16\n  sd ra, 8(sp)\n  call "+symbol+"\n  ld ra, 8(sp)\n  addi sp, sp, 16\n  ret\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	function := unit.Functions[0]
	function.Callees = map[string]*ast.FunctionStatement{"double": callee}
	signature, err := parseSignature(decl)
	if err != nil {
		t.Fatal(err)
	}
	if findings := Check(function, signature, map[string]bool{symbol: true}); len(findings) != 0 {
		t.Fatalf("checker: %v", findings)
	}
	specification := nativeCalleeDeclaration(t, decl+" = double(v)")
	verdict := Verify(function, signature, specification.Body)
	if verdict.Kind != VerdictProven || strings.Join(verdict.Callees, ",") != "double" {
		t.Fatalf("active RV64 vector entry = %s: %s, callees %v", verdict.Kind, verdict.Message, verdict.Callees)
	}
}

func TestVerifyDoesNotSummarizeAliasedCalleeKeys(t *testing.T) {
	callee := nativeCalleeDeclaration(t, "inc: (x: u32) -> u32 = x + u32(1)")
	for _, test := range []struct {
		arch string
		path string
		body string
	}{
		{
			arch: ArchArm64,
			path: "alias.oakasm",
			body: "  bind w0 = x\n  clobber x29, x30\n  frame 16\n  sub sp, sp, #16\n  stp x29, x30, [sp]\n  bl alias\n  ldp x29, x30, [sp]\n  add sp, sp, #16\n  ret",
		},
		{
			arch: ArchRV64,
			path: "alias.rv64.oakasm",
			body: "  bind a0 = x\n  frame 16\n  addi sp, sp, -16\n  sd ra, 8(sp)\n  call alias\n  ld ra, 8(sp)\n  addi sp, sp, 16\n  ret",
		},
	} {
		t.Run(test.arch, func(t *testing.T) {
			decl := "through_alias: (x: u32) -> u32"
			unit, errs := ParseUnit(test.path, decl+" = {\n"+test.body+"\n}\n")
			if len(errs) != 0 {
				t.Fatal(errs)
			}
			function := unit.Functions[0]
			function.Callees = map[string]*ast.FunctionStatement{"alias": callee}
			signature, err := parseSignature(decl)
			if err != nil {
				t.Fatal(err)
			}
			if findings := Check(function, signature, map[string]bool{"alias": true}); len(findings) != 0 {
				t.Fatalf("checker: %v", findings)
			}
			specification := nativeCalleeDeclaration(t, decl+" = inc(x)")
			verdict := Verify(function, signature, specification.Body)
			if verdict.Kind != VerdictTrusted || len(verdict.Callees) != 0 {
				t.Fatalf("aliased key must stay opaque, got %s: %s, callees %v", verdict.Kind, verdict.Message, verdict.Callees)
			}
		})
	}
}

func TestFindLoopsUsesActiveNativeCalleeIdentity(t *testing.T) {
	vector := nativeCalleeDeclaration(t, "double: (v: simd.U8x16) -> simd.U8x16 = simd.add_u8x16(v, v)")
	for _, arch := range []string{ArchArm64, ArchRV64} {
		arch := arch
		t.Run(arch, func(t *testing.T) {
			active := "double" + VectorEntrySuffix(arch)
			opposite := "double" + VectorEntrySuffix(ArchArm64)
			if arch == ArchArm64 {
				opposite = "double" + VectorEntrySuffix(ArchRV64)
			}
			for _, test := range []struct {
				name    string
				symbol  string
				callees map[string]*ast.FunctionStatement
				want    bool
			}{
				{name: "active vector", symbol: active, callees: map[string]*ast.FunctionStatement{"double": vector}, want: true},
				{name: "opposite vector", symbol: opposite, callees: map[string]*ast.FunctionStatement{"double": vector}},
				{name: "alias", symbol: "alias", callees: map[string]*ast.FunctionStatement{"alias": vector}},
			} {
				t.Run(test.name, func(t *testing.T) {
					items, labels, exit := nativeCalleeLoop(arch, test.symbol)
					_, found := findLoopsIn("caller", arch, items, labels, test.callees)[exit]
					if found != test.want {
						t.Fatalf("loop call %q recognized = %v, want %v", test.symbol, found, test.want)
					}
				})
			}
		})
	}
}

func nativeCalleeLoop(arch, symbol string) ([]Item, map[string]int, int) {
	call := Instruction{Mnemonic: "bl", Operands: []Operand{Symbol{Name: symbol}}}
	exit := Instruction{Mnemonic: "b.", Cond: "hs", Operands: []Operand{Symbol{Name: "done"}}}
	back := Instruction{Mnemonic: "b", Operands: []Operand{Symbol{Name: "loop"}}}
	header := Instruction{Mnemonic: "cmp"}
	step := Instruction{Mnemonic: "add"}
	if arch == ArchRV64 {
		call.Mnemonic = "call"
		exit = Instruction{Mnemonic: "bgeu", Operands: []Operand{Symbol{Name: "done"}}}
		back.Mnemonic = "j"
		header.Mnemonic = "addi"
		step.Mnemonic = "addi"
	}
	items := []Item{
		Label{Name: "loop"},
		header,
		exit,
		call,
		step,
		back,
		Label{Name: "done"},
		Instruction{Mnemonic: "ret"},
	}
	return items, map[string]int{"loop": 0, "done": 6}, 2
}

func nativeCalleeDeclaration(t *testing.T, source string) *ast.FunctionStatement {
	t.Helper()
	declaration, err := parseSignatureWithBody(source)
	if err != nil {
		t.Fatal(err)
	}
	return declaration
}
