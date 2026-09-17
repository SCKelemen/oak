package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
)

const nativeExtentFoldProgram = `
TABLE: [12]u32
D: u32 = 3

groups: (): u32 {
  whole: []u32 = view(&TABLE)
  alias: []u32 = whole
  len(alias) / D
}

tail_groups: (n: u32): u32 {
  whole: []u32 = view(&TABLE)
  tail: []u32 = subslice(whole, u32(1), n)
  len(tail) / u32(3)
}

dynamic_divisor: (divisor: u32): u32 {
  whole: []u32 = view(&TABLE)
  len(whole) / divisor
}

remainder: (): u32 {
  a: [13]u32
  whole: []u32 = view(&a)
  len(whole) % u32(3)
}

main: (): i32 {
  assert(groups() == u32(4))
  assert(tail_groups(u32(0)) == u32(0))
  assert(tail_groups(u32(2)) == u32(0))
  assert(tail_groups(u32(5)) == u32(1))
  assert(dynamic_divisor(u32(7)) == u32(1))
  assert(remainder() == u32(1))
  42
}
`

func TestE2ENativeExtentFold(t *testing.T) {
	requireArm64Host(t)
	t.Setenv("OAK_NATIVE_ONLY", "groups,tail_groups,dynamic_divisor,remainder")
	for _, native := range []bool{false, true} {
		comp := New().WithSource("extent_fold.oak", nativeExtentFoldProgram)
		if native {
			comp = comp.WithNativeBodies().WithNativeAsm()
			model, err := comp.Check().Get()
			if err != nil {
				t.Fatal(err)
			}
			for _, name := range []string{"groups", "tail_groups", "dynamic_divisor", "remainder"} {
				if verdict := model.NativeVerdicts[name]; verdict.Kind != asm.VerdictProven {
					t.Fatalf("%s not proven: %+v", name, verdict)
				}
			}
		}
		if _, code, abnormal := buildAndRunFrom(t, "extent_fold", comp); abnormal || code != 42 {
			t.Fatalf("native=%v: exit=%d abnormal=%v", native, code, abnormal)
		}
	}
}

func TestE2ENativeExtentFoldRetainsTraps(t *testing.T) {
	requireArm64Host(t)
	t.Setenv("OAK_NATIVE_ONLY", "groups,tail_groups,dynamic_divisor,remainder")
	for _, call := range []string{"dynamic_divisor(u32(0))", "tail_groups(u32(12))"} {
		// Neither a dynamic zero divisor nor an invalid subslice can be
		// bypassed by treating the backing table's extent as a constant.
		source := nativeExtentFoldProgram[:strings.Index(nativeExtentFoldProgram, "main:")] +
			"main: (): i32 { n: u32 = " + call + "; i32_bits_u32(n) }\n"
		for _, native := range []bool{false, true} {
			comp := New().WithSource("extent_trap.oak", source)
			if native {
				comp = comp.WithNativeBodies().WithNativeAsm()
			}
			if _, code, abnormal := buildAndRunFrom(t, "extent_trap", comp); !abnormal {
				t.Fatalf("%s, native=%v: returned %d instead of trapping", call, native, code)
			}
		}
	}
}
