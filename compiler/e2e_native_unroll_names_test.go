package compiler

import (
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/nativegen"
)

const nativeUnrollNamesProgram = `
nested_names: (seed: u32): u32 {
  total: u32 = seed
  outer: u32 = u32(0)
  while outer < u32(2) {
    inner: u32 = u32(0)
    while inner < u32(2) {
      g: u32 = total + inner
      total = g + outer
      inner = inner + u32(1)
    }
    outer = outer + u32(1)
  }
  total
}

sequential_names: (seed: u32): u32 {
  total: u32 = seed
  first: u32 = u32(0)
  while first < u32(2) {
    g: u32 = total + first
    total = g + u32(1)
    first = first + u32(1)
  }
  second: u32 = u32(0)
  while second < u32(2) {
    g: u32 = total + second
    total = g + u32(1)
    second = second + u32(1)
  }
  total
}

main: (): i32 {
  nested_names(u32(1)) == u32(5) ? {
    sequential_names(u32(1)) == u32(7) ? 42 | 2
  } | 1
}
`

func TestNativeUnrollGeneratedNamesProven(t *testing.T) {
	t.Setenv("OAK_VERIFY_CACHE", "0")
	t.Setenv("OAK_VERIFY_BUDGET", "")
	t.Setenv("OAK_NATIVE_ONLY", "nested_names,sequential_names")
	model, err := nativeShapeCompilation("unroll_names.oak", nativeUnrollNamesProgram).SemanticModel().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, name := range []string{"nested_names", "sequential_names"} {
		verdict, exists := model.NativeVerdicts[name]
		if !exists || verdict.Kind != asm.VerdictProven {
			t.Fatalf("%s must be proven with fresh default budgets: %s: %s", name, verdict.Kind, verdict.Message)
		}
		var selected *asm.Function
		for _, body := range model.AsmFunctions {
			if body.Name == name {
				selected = body
				break
			}
		}
		if selected == nil || nativegen.UnrolledConstant(selected) == 0 {
			t.Fatalf("%s did not exercise constant unrolling", name)
		}
	}
}

func TestE2ENativeUnrollGeneratedNames(t *testing.T) {
	requireArm64Host(t)
	t.Setenv("OAK_VERIFY_CACHE", "0")
	t.Setenv("OAK_VERIFY_BUDGET", "")
	t.Setenv("OAK_NATIVE_ONLY", "nested_names,sequential_names")
	for _, variant := range []struct {
		name string
		comp Compilation
	}{
		{"native", New().WithSource("unroll_names.oak", nativeUnrollNamesProgram).WithNativeBodies().WithNativeAsm()},
		{"c", New().WithSource("unroll_names.oak", nativeUnrollNamesProgram)},
	} {
		t.Run(variant.name, func(t *testing.T) {
			if _, code, abnormal := buildAndRunFrom(t, "unroll_names_"+variant.name, variant.comp); abnormal || code != 42 {
				t.Fatalf("%s: exit=%d abnormal=%v, want42 (nested=5, sequential=7)", variant.name, code, abnormal)
			}
		})
	}
}
