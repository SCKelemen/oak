package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/nativegen"
)

// BLAKE3's message permutation has two eight-element cycles. Repeated
// assignments must read each round's original words; an in-place store
// must not destroy a word another destination still needs.
const nativeArrayPermutationLoopProgram = `
permute: (m: [16]u32): [16]u32 = [16]u32{
  m[2], m[6], m[3], m[10], m[7], m[0], m[4], m[13],
  m[1], m[11], m[12], m[5], m[9], m[14], m[15], m[8]
}

shuffle: (input: [16]u32): [16]u32 {
  m: [16]u32 = input
  round: u32 = u32(0)
  while round < u32(7) {
    m = permute(m)
    round = round + u32(1)
  }
  m
}

main: (): i32 {
  input: [16]u32 = [16]u32{
    0xffffffff, 0x80000000, 2, 3, 4, 5, 6, 7,
    8, 9, 10, 11, 12, 13, 14, 15
  }
  result: [16]u32 = shuffle(input)
  back: [16]u32 = permute(result)
  i: u32 = u32(0)
  while i < u32(16) {
    assert(back[i] == input[i])
    i = i + u32(1)
  }
  42
}
`

func TestE2ENativeArrayPermutationLoop(t *testing.T) {
	requireArm64Host(t)
	comp := New().WithSource("permutation_loop.oak", nativeArrayPermutationLoopProgram).WithNativeBodies().WithNativeAsm()
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	if v := model.NativeVerdicts["shuffle"]; v.Kind != asm.VerdictProven {
		t.Fatalf("selected shuffle must be proven: %s: %s", v.Kind, v.Message)
	}
	functions := map[string]*ast.FunctionStatement{}
	symbols := map[string]bool{}
	for _, stmt := range model.Tree.Root.Statements {
		if fn, ok := stmt.(*ast.FunctionStatement); ok {
			functions[fn.Name.Value] = fn
			symbols[fn.Name.Value] = true
		}
	}
	fn := functions["shuffle"]
	body, err := nativegen.CompileFor(nativegen.Lane{Arch: asm.ArchArm64}, fn, functions, nil, nil, nil, model.TypeChecker)
	if err != nil {
		t.Fatal(err)
	}
	body.Callees = functions
	if findings := asm.Check(body, fn, symbols); len(findings) != 0 {
		t.Fatal(findings)
	}
	if v := asm.Verify(body, fn, fn.Body); v.Kind != asm.VerdictProven {
		t.Fatalf("direct shuffle must be proven: %s: %s", v.Kind, v.Message)
	}
	// The message array is the only thing shuffle owns on the frame, and
	// it need not be there at all: with its elements promoted to
	// registers the frame holds nothing of its own, and the eighty bytes
	// it reserves are spill space rather than an object. What must not
	// appear is a second object, or one of another size.
	objects := nativegen.FrameObjects(body)
	if len(objects) > 1 {
		t.Fatalf("shuffle should own only its message array, got %+v\n%s", objects, nativegen.Describe(body))
	}
	if len(objects) == 1 && objects[0].Size != 64 {
		t.Fatalf("shuffle's one frame object should be its 64-byte message array, got %+v\n%s", objects, nativegen.Describe(body))
	}
	for _, build := range []struct {
		name string
		comp Compilation
	}{
		{"native", comp},
		{"c", New().WithSource("permutation_loop.oak", nativeArrayPermutationLoopProgram)},
	} {
		t.Run(build.name, func(t *testing.T) {
			stdout, code, abnormal := buildAndRunFrom(t, "array_permutation_loop_"+build.name, build.comp)
			if abnormal || code != 42 {
				t.Fatalf("exit %d (abnormal %v): %s", code, abnormal, strings.TrimSpace(stdout))
			}
		})
	}
}
