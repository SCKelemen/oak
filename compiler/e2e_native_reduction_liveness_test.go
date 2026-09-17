package compiler

import (
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
)

func TestE2ENativeReductionLivenessTails(t *testing.T) {
	requireArm64Host(t)
	t.Setenv("OAK_NATIVE_ONLY", "sum32,sum64")
	kernels := nativeVectorReductionProgram[:strings.Index(nativeVectorReductionProgram, "fsum:")]
	for _, n := range []int{0, 1, 3, 4, 7, 8, 9, 15, 16, 17, 31, 32, 33} {
		t.Run(fmt.Sprint(n), func(t *testing.T) {
			var values32, values64 []string
			var total32 uint32
			var total64 uint64
			for i := 0; i < n; i++ {
				v32 := ^uint32(0) - uint32(i)*2654435761
				v64 := ^uint64(0) - uint64(i)*6364136223846793005
				values32 = append(values32, fmt.Sprintf("u32(%d)", v32))
				values64 = append(values64, fmt.Sprintf("u64(%d)", v64))
				total32 += v32
				total64 += v64
			}
			source := kernels + fmt.Sprintf(`
main: (): i32 {
  a: [%d]u32 = [%d]u32{ %s }
  b: [%d]u64 = [%d]u64{ %s }
  assert(sum32(view(&a)) == u32(%d))
  assert(sum64(view(&b)) == u64(%d))
  i32(42)
}
`, n, n, strings.Join(values32, ","), n, n, strings.Join(values64, ","), total32, total64)
			comp := New().WithSource("sum_tails.oak", source).WithNativeBodies().WithNativeAsm()
			model, err := comp.Check().Get()
			if err != nil {
				t.Fatal(err)
			}
			for _, name := range []string{"sum32", "sum64"} {
				if verdict, ok := model.NativeVerdicts[name]; !ok || verdict.Kind != asm.VerdictProven {
					t.Fatalf("%s not proven: %+v", name, verdict)
				}
			}
			if _, code, abnormal := buildAndRunFrom(t, "sum_tails_native", comp); abnormal || code != 42 {
				t.Fatalf("native exit=%d abnormal=%v", code, abnormal)
			}
			if _, code, abnormal := buildAndRunFrom(t, "sum_tails_c", New().WithSource("sum_tails.oak", source)); abnormal || code != 42 {
				t.Fatalf("C exit=%d abnormal=%v", code, abnormal)
			}
		})
	}
}
