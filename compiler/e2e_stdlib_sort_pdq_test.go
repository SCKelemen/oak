package compiler

import (
	"fmt"
	"math/rand/v2"
	"slices"
	"strings"
	"testing"
)

// sortShapes are the input patterns a pattern-defeating quicksort treats
// differently: random, presorted, reversed, all equal, organ pipe, few
// distinct values, and a sawtooth. Each is generated at every length below,
// sorted by Go's slices.Sort, and the Oak result must be identical.
func sortShapes(rng *rand.Rand) []struct {
	name string
	gen  func(n int) []uint32
} {
	return []struct {
		name string
		gen  func(n int) []uint32
	}{
		{"random", func(n int) []uint32 {
			out := make([]uint32, n)
			for i := range out {
				out[i] = rng.Uint32()
			}
			return out
		}},
		{"sorted", func(n int) []uint32 {
			out := make([]uint32, n)
			for i := range out {
				out[i] = uint32(i * 3)
			}
			return out
		}},
		{"reversed", func(n int) []uint32 {
			out := make([]uint32, n)
			for i := range out {
				out[i] = uint32((n - i) * 5)
			}
			return out
		}},
		{"equal", func(n int) []uint32 {
			out := make([]uint32, n)
			for i := range out {
				out[i] = 42
			}
			return out
		}},
		{"organ_pipe", func(n int) []uint32 {
			out := make([]uint32, n)
			for i := range out {
				if i < n/2 {
					out[i] = uint32(i)
				} else {
					out[i] = uint32(n - i)
				}
			}
			return out
		}},
		{"few_distinct", func(n int) []uint32 {
			out := make([]uint32, n)
			for i := range out {
				out[i] = uint32(rng.IntN(3))
			}
			return out
		}},
		{"sawtooth", func(n int) []uint32 {
			out := make([]uint32, n)
			for i := range out {
				out[i] = uint32(i % 7)
			}
			return out
		}},
	}
}

func oakU32Literal(values []uint32) string {
	parts := make([]string, len(values))
	for i, v := range values {
		parts[i] = fmt.Sprintf("%d", v)
	}
	return fmt.Sprintf("[%d]u32{ %s }", len(values), strings.Join(parts, ", "))
}

// oakSortCheck emits one Oak function that sorts `data` with the given call
// and asserts element-wise equality with Go's sorted result.
func oakSortCheck(name string, data []uint32, call string) string {
	want := slices.Clone(data)
	slices.Sort(want)
	return fmt.Sprintf(`%s: (): () {
  data: [%d]u32 = %s
  expected: [%d]u32 = %s
  true ? {
    s: [*]u32 = span(&data)
    %s
  }
  i: u32 = u32(0)
  while i < u32(%d) {
    assert(data[i] == expected[i])
    i = i + u32(1)
  }
}
`, name, len(data), oakU32Literal(data), len(want), oakU32Literal(want), call, len(data))
}

// TestE2EStdlibSortMatchesGo sorts every shape at lengths around the
// insertion-sort threshold (12), the ninther threshold (50), and beyond,
// through sort_span, and compares with slices.Sort. The depth budget path
// is forced with sort_span_budget at budgets 0 (heapsort at once) and 1
// (one partition, then heapsort on the pieces).
func TestE2EStdlibSortMatchesGo(t *testing.T) {
	rng := rand.New(rand.NewPCG(11, 7))
	lengths := []int{1, 2, 3, 7, 12, 13, 24, 25, 49, 50, 51, 63, 100, 257}
	var src strings.Builder
	src.WriteString("import(std)\n")
	var calls []string
	index := 0
	for _, shape := range sortShapes(rng) {
		for _, n := range lengths {
			name := fmt.Sprintf("check_%s_%d", shape.name, index)
			index++
			src.WriteString(oakSortCheck(name, shape.gen(n), "sort_span[u32](s)"))
			calls = append(calls, name+"()")
		}
	}
	for _, budget := range []int{0, 1} {
		for _, n := range []int{13, 50, 257} {
			shape := sortShapes(rng)[0]
			name := fmt.Sprintf("check_budget%d_%d", budget, index)
			index++
			src.WriteString(oakSortCheck(name, shape.gen(n), fmt.Sprintf("sort_span_budget[u32](s, u32(%d))", budget)))
			calls = append(calls, name+"()")
		}
	}
	// An empty span and a second element type.
	src.WriteString(`check_empty: (): () {
  data: [1]u32 = [1]u32{ 9 }
  true ? {
    s: [*]u32 = span(&data)
    none: [*]u32 = s[u32(0):u32(0)]
    sort_span[u32](none)
  }
  assert(data[0] == u32(9))
}
check_signed: (): () {
  data: [60]i32
  true ? {
    s: [*]i32 = span(&data)
    i: u32 = u32(0)
    while i < u32(60) {
      s[i] = i32(29) - i32_bits_u32((i * u32(17)) % u32(59))
      i = i + u32(1)
    }
    sort_span[i32](s)
  }
  assert(sort_is_sorted[i32](view(&data)))
  assert(data[0] == i32(0) - i32(29) && data[59] == i32(29))
}
`)
	calls = append(calls, "check_empty()", "check_signed()")
	src.WriteString("main: (): i32 {\n")
	for _, call := range calls {
		src.WriteString("  " + call + "\n")
	}
	src.WriteString("  42\n}\n")
	code, abnormal := buildAndRun(t, "stdlib_sort_pdq", src.String())
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
