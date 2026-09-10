package compiler

import (
	"strings"
	"testing"
)

// Nested owned arrays [N][M]T are arrays of array values (docs/spec/90-backend.md
// section 10): a row copied out of a grid is its own storage, a store through
// the grid path reaches the grid, and the typed literal spells the rows.
func TestE2ENestedArraysAreValues(t *testing.T) {
	src := `
Grid: type = struct { rows: [2][3]u8 }
row_sum: (row: [3]u8): u32 {
  u32(row[0]) + u32(row[1]) + u32(row[2])
}
main: (): i32 {
  grid: [2][2]u8 = [2][2]u8{ [2]u8{ 1, 2 }, [2]u8{ 3, 4 } }
  row: [2]u8 = grid[1]
  row[0] = 9
  grid[0][1] = 8
  assert(grid[1][0] == 3)
  assert(row[1] == 4)
  assert(grid[0][1] == 8)
  g: Grid = Grid { rows: [2][3]u8{ [3]u8{ 1, 2, 3 }, [3]u8{ 4, 5, 6 } } }
  g.rows[1][2] = 7
  assert(row_sum(g.rows[0]) == 6)
  assert(row_sum(g.rows[1]) == 16)
  u32(grid[0][0]) + u32(grid[0][1]) + u32(grid[1][0]) + u32(grid[1][1]) + u32(row[0]) + u32(row[1]) + row_sum(g.rows[1]) == 45 ? { 42 } | { 1 }
}
`
	output, err := New().WithSource("nestedarrays.oak", src).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"typedef struct oak_arr_u8_2 { u8 v[ 2 ]; } oak_arr_u8_2;",
		"typedef struct oak_arr_oak_arr_u8_2_2 { oak_arr_u8_2 v[ 2 ]; } oak_arr_oak_arr_u8_2_2;",
		"oak_arr_oak_arr_u8_3_2 rows;",
	} {
		if !strings.Contains(output, want) {
			t.Fatalf("generated C lacks %q:\n%s", want, output)
		}
	}
	if strings.Contains(output, "OAK_UNSUPPORTED") {
		t.Fatalf("generated C fails closed somewhere:\n%s", output)
	}
	code, abnormal := buildAndRun(t, "nestedarrays", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if interpreted := interpretChecked(t, src); interpreted != 42 {
		t.Fatalf("interpreter returned %d", interpreted)
	}
}
