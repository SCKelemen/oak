package compiler

import (
	"strings"
	"testing"
)

// The dbs pilot's segment recovery (docs/notes/dbs-feedback-2026-09.md,
// pilot pack item 2): a guard `count <= 8` around the loops that fill and
// read an `[8]Seg`, each loop `while i < count`. The guard is `count < 9`;
// `i < count` composes to `i < 8` (Oak.Extents.bound_through_literal), so
// every element access is proven against the array's extent and the
// emitted C carries no check on the array.
const recoveryBoundsProgram = `
Seg: type = struct { base: u64, len: u32, live: Bool }

recover: (count: u32, stride: u64): u64 {
  segs: [8]Seg
  total: u64 = u64(0)
  count <= u32(8) ? {
    i: u32 = u32(0)
    while i < count {
      segs[i].base = stride * u64(i)
      segs[i].len = u32(16) * (i + u32(1))
      segs[i].live = (i % u32(2)) == u32(0)
      i = i + u32(1)
    }
    j: u32 = u32(0)
    while j < count {
      segs[j].live ? { total = total + segs[j].base + u64(segs[j].len) } | { }
      j = j + u32(1)
    }
    k: u32 = u32(0)
    while k < count {
      total = total + u64(segs[k].len)
      k = k + u32(1)
    }
  } | { total = u64(1) }
  total
}

main: (): i32 {
  full: u64 = recover(u32(8), u64(100))
  part: u64 = recover(u32(3), u64(10))
  none: u64 = recover(u32(9), u64(1))
  full == u64(1200) + u64(256) + u64(576) && part == u64(0) + u64(20) + u64(16) + u64(48) + u64(96) && none == u64(1) ? 42 | 1
}
`

func TestE2ERecoveryLoopsAreCheckFree(t *testing.T) {
	code, err := New().WithSource("recover.oak", recoveryBoundsProgram).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	body := cFunctionBody(t, code, "oak_recover")
	for _, checked := range []string{"oak_index(", "oak_lv_idx(", "oak_store("} {
		if strings.Contains(body, checked) {
			t.Errorf("recover keeps a check on segs: %q\n%s", checked, body)
		}
	}
	if strings.Count(body, "segs.v[") < 6 {
		t.Errorf("expected direct element accesses on segs:\n%s", body)
	}
	exit, abnormal := buildAndRun(t, "recovery_bounds", recoveryBoundsProgram)
	if abnormal || exit != 42 {
		t.Fatalf("exit=(%d,%v)", exit, abnormal)
	}
}
