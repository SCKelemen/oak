package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// A loop that assigns one field of a record local carries only that field
// (docs/spec/94-assembler.md §9 "Loop invariants", the carried leaves):
// `acc.sum` is written each iteration while `acc.limit` is only read in
// the condition, so the coupling needs a machine image for `acc.sum` and
// none for `acc.limit`, which keeps its header value. Before, every leaf of
// the record was a loop variable and the unwritten one, held in no register
// the loop writes, left the unit witnessed (hash.sha256_update's whole-block
// loop reads next.filled the same way).
const nativeRecordFieldLoopProgram = `
Acc: type = struct {
  sum: u64
  limit: u32
  count: u32
}

total: (v: []u64, limit: u32): u64 {
  acc: Acc
  acc.sum = u64(0)
  acc.limit = limit
  acc.count = u32(0)
  i: u32 = 0
  while i < len(v) && i < acc.limit {
    acc.sum = acc.sum + v[i]
    i = i + u32(1)
  }
  acc.sum + u64(acc.limit) + u64(acc.count)
}

main: (): i32 {
  v: [8]u64 = [u64(1), u64(2), u64(3), u64(4), u64(5), u64(6), u64(7), u64(8)]
  assert(total(view(&v), u32(3)) == u64(9))
  assert(total(view(&v), u32(100)) == u64(136))
  42
}
`

func TestNativeShapesRecordFieldLoopCarriesAssignedLeaves(t *testing.T) {
	var infos []string
	comp := New().WithSource("acc.oak", nativeRecordFieldLoopProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	if _, err := comp.Check().Get(); err != nil {
		t.Fatalf("check: %v\n%s", err, strings.Join(infos, "\n"))
	}
	joined := strings.Join(infos, "\n")
	if !strings.Contains(joined, "asm unit total: proven equal") {
		t.Errorf("total must be proven with only acc.sum carried; diagnostics:\n%s", joined)
	}
	if strings.Contains(joined, "acc.limit") || strings.Contains(joined, "acc.count") {
		t.Errorf("the unwritten fields must not be loop variables; diagnostics:\n%s", joined)
	}
}

func TestE2ENativeRecordFieldLoop(t *testing.T) {
	requireArm64Host(t)
	comp := New().WithSource("acc.oak", nativeRecordFieldLoopProgram).WithNativeBodies().WithNativeAsm()
	if _, code, abnormal := buildAndRunFrom(t, "native_record_field_loop", comp); abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_record_field_loop_c", New().WithSource("acc.oak", nativeRecordFieldLoopProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
