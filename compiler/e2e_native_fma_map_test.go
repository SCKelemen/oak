package compiler

import (
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/nativegen"
)

const nativeFMAMaps = `
map32: (dst: [*]f32, a: []f32, k: f32, c: f32): () {
  len(dst) == len(a) ? {
    i: u32 = u32(0)
    while i < len(a) {
      dst[i] = fma(a[i], k, c)
      i = i + u32(1)
    }
  } | { }
}
map64: (dst: [*]f64, a: []f64, k: f64, c: f64): () {
  len(dst) == len(a) ? {
    i: u32 = u32(0)
    while i < len(a) {
      dst[i] = fma(a[i], k, c)
      i = i + u32(1)
    }
  } | { }
}
nested: (dst: [*]f32, a: []f32, b: []f32, k: f32): () {
  len(dst) == len(a) && len(a) == len(b) ? {
    i: u32 = u32(0)
    while i < len(a) {
      dst[i] = fma(fma(a[i], k, 0.5), b[i], 1.0)
      i = i + u32(1)
    }
  } | { }
}
`

func TestE2ENativeFMAMaps(t *testing.T) {
	requireArm64Host(t)
	// Verify/time the kernels; the assertion-heavy oracle stays in C.
	t.Setenv("OAK_NATIVE_ONLY", "map32,map64,nested")
	for _, length := range []int{0, 1, 2, 3, 4, 5, 7, 8, 9, 17} {
		t.Run(fmt.Sprint(length), func(t *testing.T) {
			// Cancellation distinguishes one rounding from two; the list also
			// exercises signed zero, tiny normals, subnormals, overflow and NaN.
			values32 := []string{"f32_bits_u32(u32(1065353217))", "0.0", "f32_bits_u32(u32(2147483648))", "f32_bits_u32(u32(1))", "f32_bits_u32(u32(8388608))", "f32_bits_u32(u32(2139095039))", "f32_bits_u32(u32(2139095040))", "f32_bits_u32(u32(2143289344))"}
			values64 := []string{"f64_bits_u64(u64(4607182418800017409))", "0.0", "f64_bits_u64(u64(9223372036854775808))", "f64_bits_u64(u64(1))", "f64_bits_u64(u64(4503599627370496))", "f64_bits_u64(u64(9218868437227405311))", "f64_bits_u64(u64(9218868437227405312))", "f64_bits_u64(u64(9221120237041090560))"}
			var a32, a64, zeros []string
			for i := 0; i < length; i++ {
				a32 = append(a32, values32[i%len(values32)])
				a64 = append(a64, values64[i%len(values64)])
				zeros = append(zeros, "0.0")
			}
			source := nativeFMAMaps + fmt.Sprintf(`
main: (): i32 {
  a: [%d]f32 = [%d]f32{ %s }
  b: [%d]f64 = [%d]f64{ %s }
  dst: [%d]f32 = [%d]f32{ %s }
  wide: [%d]f64 = [%d]f64{ %s }
  nests: [%d]f32 = [%d]f32{ %s }
  k: f32 = f32_bits_u32(u32(1065353215))
  kw: f64 = f64_bits_u64(u64(4607182418800017407))
  map32(span(&dst), view(&a), k, -1.0)
  map64(span(&wide), view(&b), kw, -1.0)
  nested(span(&nests), view(&a), view(&a), k)
  i: u32 = u32(0)
  while i < len(a) {
    expected: f32 = fma(a[i], k, -1.0)
    assert(is_nan(expected) ? is_nan(dst[i]) | u32_bits_f32(dst[i]) == u32_bits_f32(expected))
    nw: f32 = fma(fma(a[i], k, 0.5), a[i], 1.0)
    assert(is_nan(nw) ? is_nan(nests[i]) | u32_bits_f32(nests[i]) == u32_bits_f32(nw))
    i = i + u32(1)
  }
  j: u32 = u32(0)
  while j < len(b) {
    expected: f64 = fma(b[j], kw, -1.0)
    assert(is_nan(expected) ? is_nan(wide[j]) | u64_bits_f64(wide[j]) == u64_bits_f64(expected))
    j = j + u32(1)
  }
  i32(42)
}
`, length, length, strings.Join(a32, ","), length, length, strings.Join(a64, ","), length, length, strings.Join(zeros, ","), length, length, strings.Join(zeros, ","), length, length, strings.Join(zeros, ","))
			comp := New().WithSource("fma_maps.oak", source).WithNativeBodies().WithNativeAsm()
			model, err := comp.Check().Get()
			if err != nil {
				t.Fatal(err)
			}
			for _, name := range []string{"map32", "map64", "nested"} {
				found := false
				for _, unit := range model.AsmFunctions {
					if unit.Name != name {
						continue
					}
					found = true
					if nativegen.VectorizedMaps(unit) != 1 || model.NativeVerdicts[name].Kind != asm.VerdictProven {
						t.Fatalf("%s not selected as proven vector map: %+v\n%s", name, model.NativeVerdicts[name], nativegen.Describe(unit))
					}
					if !strings.Contains(nativegen.Describe(unit), "fmla ") {
						t.Fatalf("%s missing vector FMA", name)
					}
				}
				if !found {
					t.Fatalf("missing %s", name)
				}
			}
			if _, code, abnormal := buildAndRunFrom(t, "native_fma_maps", comp); abnormal || code != 42 {
				t.Fatalf("native exit=%d abnormal=%v", code, abnormal)
			}
			if _, code, abnormal := buildAndRunFrom(t, "c_fma_maps", New().WithSource("fma_maps.oak", source)); abnormal || code != 42 {
				t.Fatalf("C exit=%d abnormal=%v", code, abnormal)
			}
		})
	}
}

func TestNativeFMAMapRefusesShadowedAndEffectfulCalls(t *testing.T) {
	for _, test := range []struct{ name, prefix, expression string }{
		{"shadowed", "fma: (a: f32, b: f32, c: f32): f32 = a - b - c\n", "fma(a[i], k, c)"},
		{"effectful argument", "state: f32 = 0.0\ntouch: (x: f32): f32 { state = x\n x }\n", "fma(touch(a[i]), k, c)"},
		{"other intrinsic", "", "copysign(a[i], k)"},
	} {
		t.Run(test.name, func(t *testing.T) {
			source := test.prefix + strings.Replace(nativeFMAMaps[:strings.Index(nativeFMAMaps, "map64:")], "fma(a[i], k, c)", test.expression, 1)
			model, err := New().WithSource("fma_refusal.oak", source).Check().Get()
			if err != nil {
				t.Fatal(err)
			}
			functions := map[string]*ast.FunctionStatement{}
			for _, statement := range model.Tree.Root.Statements {
				if function, ok := statement.(*ast.FunctionStatement); ok {
					functions[function.Name.Value] = function
				}
			}
			unit, err := nativegen.CompileFor(nativegen.Lane{VectorMaps: true}, functions["map32"], functions, nil, nil, nil, model.TypeChecker)
			// An ordinary unsupported effectful call may refuse native lowering;
			// it must never obtain a vector map by reinterpreting the call.
			if err == nil && nativegen.VectorizedMaps(unit) != 0 {
				t.Fatal("unlicensed call vectorized")
			}
		})
	}
}

func TestNativeFMAMapKeepsStrictArithmetic(t *testing.T) {
	t.Setenv("OAK_NATIVE_ONLY", "map32")
	source := strings.Replace(nativeFMAMaps, "fma(a[i], k, c)", "a[i] * k + c", 1)
	model, err := New().WithSource("strict_fma_map.oak", source).WithNativeBodies().WithNativeAsm().Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, unit := range model.AsmFunctions {
		if unit.Name != "map32" {
			continue
		}
		if nativegen.VectorizedMaps(unit) != 1 || model.NativeVerdicts[unit.Name].Kind != asm.VerdictProven {
			t.Fatal("strict map did not remain proven/vectorized")
		}
		mul, add := false, false
		for _, instruction := range mainLoopOf(unit) {
			switch instruction.Mnemonic {
			case "fmul":
				mul = true
			case "fadd":
				add = true
			case "fmla", "fmadd":
				t.Fatal("ordinary multiply/add was contracted")
			}
		}
		if !mul || !add {
			t.Fatal("strict map lost one of its roundings")
		}
		return
	}
	t.Fatal("strict map was not emitted")
}
