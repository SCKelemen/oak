package compiler

import (
	"context"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

// F27: stores descend through record fields and array elements, then
// update the original owner. Loops, branches and span calls must carry
// the resulting owner, preserving every field outside the target path.
const leanNestedAssignmentProgram = `
Meta: type = struct { stamp: u32 }
View: type = struct { shape: [3]u32, meta: Meta, offset: u32 }
Box: type = struct { items: [2]View }
views: [3]View
calls: u32 = 0

chosen: (): u32 {
  calls = calls + 1
  1
}

write_shape: (dst: [*]View, id: u32, dim: u32, value: u32): () {
  dst[id].shape[dim] = value
}

window_write: (dst: [*]View): () {
  part: [*]View = dst[1:3]
  part[0].shape[1] = 13
}

fill: (id: u32): () {
  matches: u32 = 11
  dim: u32 = 0
  while dim < 3 {
    dim == 1 ? {
      views[id].shape[dim] = matches
    } | {
      views[id].shape[dim] = 10 + dim
    }
    dim = dim + 1
  }
  views[id].meta.stamp = 90
  views[id].offset = 101
}

scenario: (): u32 {
  fill(1)
  views[chosen()].shape[2] = 18
  write_shape(span(&views), 1, 2, 19)
  window_write(span(&views))
  box: Box
  box.items[1].shape[2] = 5
  box.items[1].meta.stamp = 17
  views[1].shape[0] + views[1].shape[1] + views[1].shape[2] +
    views[1].meta.stamp + views[1].offset +
    box.items[1].shape[2] + box.items[1].meta.stamp + calls
}

main: (): i32 = scenario() == 256 ? 42 | 1
`

func TestE2ELeanNestedAssignment(t *testing.T) {
	if code, abnormal := buildAndRun(t, "nested_assignment", leanNestedAssignmentProgram); abnormal || code != 42 {
		t.Fatalf("C exit=(%d,%v), want 42", code, abnormal)
	}
	if got := interpretChecked(t, leanNestedAssignmentProgram); got != 42 {
		t.Fatalf("interpreter result=%d, want 42", got)
	}
	extracted, err := New().WithSource("nested_assignment.oak", leanNestedAssignmentProgram).EmitLeanRoots("Oak.NestedAssignment", []string{"scenario"}).Get()
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(extracted, "sorry") {
		t.Fatal("extraction contains sorry")
	}
	t.Run("Lean", func(t *testing.T) {
		lake := findLake()
		if lake == "" {
			t.Skip("lake not found (PATH or ~/.elan/bin)")
		}
		// These assertions execute the extracted code, including its
		// loop/branch state tuples and returned span, in Lean's kernel.
		driver := extracted + `
open Oak.NestedAssignment
example : (scenario views_init calls_init 20).map (fun r => r.1) = some 256 := by decide
example : (scenario views_init calls_init 20).map (fun r => r.2.1[0]!) = some (default : View) := by decide
example : (scenario views_init calls_init 20).map (fun r => r.2.1[2]!) = some (default : View) := by decide
example : (scenario views_init calls_init 20).map (fun r => r.2.2) = some 1 := by decide
example : scenario views_init calls_init 0 = none := by decide
-- Out-of-range writes retain the extraction's documented totalization.
example : write_shape views_init 9 0 7 20 = some ((), views_init) := by decide
example : write_shape views_init 0 9 7 20 = some ((), views_init) := by decide
`
		path := filepath.Join(t.TempDir(), "NestedAssignment.lean")
		if err := os.WriteFile(path, []byte(driver), 0o644); err != nil {
			t.Fatal(err)
		}
		ctx, cancel := context.WithTimeout(context.Background(), time.Minute)
		defer cancel()
		cmd := exec.CommandContext(ctx, lake, "env", "lean", path)
		cmd.Dir = filepath.Join("..", "spec", "lean")
		if out, err := cmd.CombinedOutput(); err != nil {
			t.Fatalf("Lean: %v\n%s", err, out)
		}
	})
}
