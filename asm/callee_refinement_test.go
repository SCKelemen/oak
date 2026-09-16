package asm

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
)

// Oak.AssemblerCalleeIdentity proves the finite identity model used by the
// native-callee resolver. These bounded pins require representative live Go
// decisions to remain stated as kernel-checked Lean examples; they do not
// claim a universal implementation refinement or prove either calling ABI.
func TestResolveNativeCalleeMatchesLeanPins(t *testing.T) {
	contents, err := os.ReadFile(filepath.Join("..", "spec", "lean", "Oak", "AssemblerCalleeIdentity.lean"))
	if err != nil {
		t.Fatal(err)
	}
	normalize := func(text string) string { return strings.Join(strings.Fields(text), " ") }
	lean := normalize(string(contents))

	scalar := nativeCalleeDeclaration(t, "inc: (x: u32) -> u32 = x + u32(1)")
	vector := nativeCalleeDeclaration(t, "dot: (v: simd.U8x16) -> simd.U8x16 = simd.add_u8x16(v, v)")
	dec := nativeCalleeDeclaration(t, "dec: (x: u32) -> u32 = x - u32(1)")
	otherVector := nativeCalleeDeclaration(t, "other: (v: simd.U8x16) -> simd.U8x16 = v")
	reserved := nativeCalleeDeclaration(t, "user_neon_abi: (x: u32) -> u32 = x")
	malformedShadow := nativeCalleeDeclaration(t, "wrong: (x: u32) -> u32 = x")
	emptyShadow := nativeCalleeDeclaration(t, "empty: (x: u32) -> u32 = x")
	emptyShadow.Name.Value = ""

	tests := []struct {
		name     string
		arch     string
		symbol   string
		callees  map[string]*ast.FunctionStatement
		want     *ast.FunctionStatement
		resolved bool
		leanPin  string
	}{
		{
			name: "arm64 scalar", arch: ArchArm64, symbol: "inc",
			callees: map[string]*ast.FunctionStatement{"inc": scalar}, want: scalar, resolved: true,
			leanPin: `example : resolve .arm64 (.exact "inc" (some scalarInc)) = some scalarInc := by native_decide`,
		},
		{
			name: "rv64 scalar", arch: ArchRV64, symbol: "inc",
			callees: map[string]*ast.FunctionStatement{"inc": scalar}, want: scalar, resolved: true,
			leanPin: `example : resolve .rv64 (.exact "inc" (some scalarInc)) = some scalarInc := by native_decide`,
		},
		{
			name: "arm64 vector", arch: ArchArm64, symbol: "dot_neon_abi",
			callees: map[string]*ast.FunctionStatement{"dot": vector}, want: vector, resolved: true,
			leanPin: `example : resolve .arm64 (.vector "dot_neon_abi" "dot" none (some armVectorDot)) = some armVectorDot := by native_decide`,
		},
		{
			name: "rv64 vector", arch: ArchRV64, symbol: "dot_rvv_abi",
			callees: map[string]*ast.FunctionStatement{"dot": vector}, want: vector, resolved: true,
			leanPin: `example : resolve .rv64 (.vector "dot_rvv_abi" "dot" none (some rvVectorDot)) = some rvVectorDot := by native_decide`,
		},
		{
			name: "arm64 wrong lane", arch: ArchArm64, symbol: "dot_rvv_abi",
			callees: map[string]*ast.FunctionStatement{"dot": vector},
			leanPin: `example : resolve .arm64 (.vector "dot_rvv_abi" "dot" none (some armVectorDot)) = none := by native_decide`,
		},
		{
			name: "rv64 wrong lane", arch: ArchRV64, symbol: "dot_neon_abi",
			callees: map[string]*ast.FunctionStatement{"dot": vector},
			leanPin: `example : resolve .rv64 (.vector "dot_neon_abi" "dot" none (some rvVectorDot)) = none := by native_decide`,
		},
		{
			name: "arm64 scalar alias", arch: ArchArm64, symbol: "inc",
			callees: map[string]*ast.FunctionStatement{"inc": dec},
			leanPin: `example : resolve .arm64 (.exact "inc" (some ⟨"inc", "dec", .scalar⟩)) = none := by native_decide`,
		},
		{
			name: "rv64 vector alias", arch: ArchRV64, symbol: "dot_rvv_abi",
			callees: map[string]*ast.FunctionStatement{"dot": otherVector},
			leanPin: `example : resolve .rv64 (.vector "dot_rvv_abi" "dot" none (some ⟨"dot", "other", .vector⟩)) = none := by native_decide`,
		},
		{
			name: "arm64 reserved name", arch: ArchArm64, symbol: "user_neon_abi",
			callees: map[string]*ast.FunctionStatement{"user_neon_abi": reserved},
			leanPin: `example : resolve .arm64 (.exact "user_neon_abi" (some ⟨"user_neon_abi", "user_neon_abi", .scalar⟩)) = none := by native_decide`,
		},
		{
			name: "rv64 reserved name", arch: ArchRV64, symbol: "user_neon_abi",
			callees: map[string]*ast.FunctionStatement{"user_neon_abi": reserved},
			leanPin: `example : resolve .rv64 (.exact "user_neon_abi" (some ⟨"user_neon_abi", "user_neon_abi", .scalar⟩)) = none := by native_decide`,
		},
		{
			name: "arm64 malformed exact shadow", arch: ArchArm64, symbol: "dot_neon_abi",
			callees: map[string]*ast.FunctionStatement{"dot": vector, "dot_neon_abi": malformedShadow},
			leanPin: `example : resolve .arm64 (.vector "dot_neon_abi" "dot" (some ⟨"dot_neon_abi", "wrong", .scalar⟩) (some armVectorDot)) = none := by native_decide`,
		},
		{
			name: "rv64 malformed exact shadow", arch: ArchRV64, symbol: "dot_rvv_abi",
			callees: map[string]*ast.FunctionStatement{"dot": vector, "dot_rvv_abi": emptyShadow},
			leanPin: `example : resolve .rv64 (.vector "dot_rvv_abi" "dot" (some ⟨"dot_rvv_abi", "", .scalar⟩) (some rvVectorDot)) = none := by native_decide`,
		},
		{
			name: "missing exact slot", arch: ArchArm64, symbol: "inc",
			callees: map[string]*ast.FunctionStatement{},
			leanPin: `example : resolve .arm64 (.exact "inc" none) = none := by native_decide`,
		},
	}

	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			got, resolved := ResolveNativeCallee(test.arch, test.symbol, test.callees)
			if resolved != test.resolved || got != test.want {
				t.Fatalf("ResolveNativeCallee(%q, %q) = (%p, %v), want (%p, %v)", test.arch, test.symbol, got, resolved, test.want, test.resolved)
			}
			if pin := normalize(test.leanPin); !strings.Contains(lean, pin) {
				t.Fatalf("Lean callee-identity model is missing decision pin:\n%s", test.leanPin)
			}
		})
	}
}
