package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
)

// A pure aggregate helper that returns a permutation of its array argument is
// expanded at the assignment. The native lowering rotates the two permutation
// cycles in the destination itself instead of building a second 64-byte array
// and copying it back. This is BLAKE3's message permutation verbatim.
const nativeArrayPermutationProgram = `
permute: (m: [16]u32): [16]u32 = [16]u32{
  m[2], m[6], m[3], m[10], m[7], m[0], m[4], m[13],
  m[1], m[11], m[12], m[5], m[9], m[14], m[15], m[8]
}

apply: (m: [16]u32): [16]u32 {
  m = permute(m)
  m
}

main: (): i32 {
  before: [16]u32 = [16]u32{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16 }
  after: [16]u32 = apply(before)
  weighted: u32 = after[0] + after[1] * u32(2) + after[2] * u32(3) + after[3] * u32(4) +
    after[4] * u32(5) + after[5] * u32(6) + after[6] * u32(7) + after[7] * u32(8) +
    after[8] * u32(9) + after[9] * u32(10) + after[10] * u32(11) + after[11] * u32(12) +
    after[12] * u32(13) + after[13] * u32(14) + after[14] * u32(15) + after[15] * u32(16)
  weighted == u32(1343) ? 42 | 1
}
`

func TestNativeArrayPermutationShape(t *testing.T) {
	model, err := nativeShapeModel("array_permutation.oak", nativeArrayPermutationProgram)
	if err != nil {
		t.Fatal(err)
	}
	var apply *asm.Function
	for _, function := range model.AsmFunctions {
		if function.Name == "apply" {
			apply = function
			break
		}
	}
	if apply == nil {
		t.Fatal("apply was not lowered natively")
	}
	if verdict := model.NativeVerdicts["apply"]; verdict.Kind != asm.VerdictProven {
		t.Fatalf("apply verdict = %s (%s), want proven", verdict.Kind, verdict.Message)
	}
	stackMemory := 0
	for _, item := range apply.Items {
		instruction, isInstruction := item.(asm.Instruction)
		if !isInstruction || !strings.HasPrefix(instruction.Mnemonic, "ld") && !strings.HasPrefix(instruction.Mnemonic, "st") {
			continue
		}
		for _, operand := range instruction.Operands {
			if memory, isMemory := operand.(asm.Memory); isMemory && memory.Base.Class == asm.ClassSP {
				stackMemory++
			}
		}
	}
	if apply.Frame != 144 || stackMemory != 40 {
		t.Fatalf("the permutation must use one 64-byte array and 40 stack-memory operations; frame=%d, stack memory=%d", apply.Frame, stackMemory)
	}
}

func TestE2ENativeArrayPermutation(t *testing.T) {
	requireArm64Host(t)
	if _, native, abnormal := buildAndRunFrom(t, "native_array_permutation", New().WithSource("array_permutation.oak", nativeArrayPermutationProgram).WithNativeBodies().WithNativeAsm()); abnormal || native != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42", native, abnormal)
	}
	if _, viaC, abnormal := buildAndRunFrom(t, "native_array_permutation_c", New().WithSource("array_permutation.oak", nativeArrayPermutationProgram)); abnormal || viaC != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", viaC, abnormal)
	}
}
