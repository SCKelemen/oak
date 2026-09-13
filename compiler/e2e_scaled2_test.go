package compiler

import (
	"strings"
	"testing"
)

// Two scaled indices (docs/spec/50-borrowing.md, scaled index;
// Oak.Extents.scaled2_under_bound): a loop inside a loop over a flat
// buffer, `grid[i * 4 + j]` under `i < 3` and `j < 4`, is proven against
// the twelve elements; the same shape in the association the binary codec
// emits, `i * 4 + (j * 1 + 0)`, too; an index the facts do not bound
// (`k = j % 2`, then `i * 4 + k * 3`) stays checked.
const scaled2Program = `
fill: (): u32 {
  grid: [12]u8
  i: u32 = u32(0)
  while i < u32(3) {
    j: u32 = u32(0)
    while j < u32(4) {
      grid[i * u32(4) + j] = u8_trunc_u32(i * u32(10) + j)
      j = j + u32(1)
    }
    i = i + u32(1)
  }
  total: u32 = u32(0)
  a: u32 = u32(0)
  while a < u32(3) {
    b: u32 = u32(0)
    while b < u32(4) {
      total = total + u32(grid[a * u32(4) + (b * u32(1) + u32(0))])
      b = b + u32(1)
    }
    a = a + u32(1)
  }
  total
}

near_miss: (): u32 {
  grid: [12]u8
  total: u32 = u32(0)
  i: u32 = u32(0)
  while i < u32(3) {
    j: u32 = u32(0)
    while j < u32(4) {
      k: u32 = j % u32(2)
      total = total + u32(grid[i * u32(4) + k * u32(3)])
      j = j + u32(1)
    }
    i = i + u32(1)
  }
  total
}

main: (): i32 {
  fill() == u32(0 + 1 + 2 + 3 + 10 + 11 + 12 + 13 + 20 + 21 + 22 + 23) && near_miss() == u32(0) ? 42 | 1
}
`

func TestE2ETwoScaledIndicesAreProven(t *testing.T) {
	code, err := New().WithSource("scaled2.oak", scaled2Program).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	fill := cFunctionBody(t, code, "oak_fill")
	for _, checked := range []string{"oak_index(", "oak_lv_idx(", "oak_store("} {
		if strings.Contains(fill, checked) {
			t.Errorf("fill keeps a check on grid: %q\n%s", checked, fill)
		}
	}
	if strings.Count(fill, "grid.v[") != 2 {
		t.Errorf("expected two direct accesses on grid:\n%s", fill)
	}
	miss := cFunctionBody(t, code, "oak_near_miss")
	if !strings.Contains(miss, "oak_index(") {
		t.Errorf("the overshooting stride must stay checked:\n%s", miss)
	}
	exit, abnormal := buildAndRun(t, "scaled2", scaled2Program)
	if abnormal || exit != 42 {
		t.Fatalf("exit=(%d,%v)", exit, abnormal)
	}
}
