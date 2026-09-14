package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Readers of spans of records are proven, not trusted (docs/spec/94-
// assembler.md §9, the OS pilot's V1): a field of an element, an element
// of an array field by a symbolic or constant index, and the N4 shape,
// through a view or a span, with a small element (the shifted add) and a
// 4 KiB one (the umaddl stride). The writer stays trusted. Native exit ==
// C exit.
const nativeRecordSpanProofProgram = `
Node: type = struct { value: u32, next: u32, weight: u64 }
Leaf: type = struct { entries: [512]u64, level: u32, flags: u32 }
Dom: type = struct { pending: [8]u32, count: u32 }

peek: (pool: []Node, i: u32): u32 {
  i < len(pool) ? { pool[i].value + pool[i].next } | { u32(0) }
}

heavy: (pool: [*]Node, i: u32): u64 {
  i < len(pool) ? { pool[i].weight } | { u64(0) }
}

walk: (leaves: [*]Leaf, t: u32, idx: u32): u64 {
  t < len(leaves) && idx < u32(512) ? { leaves[t].entries[idx] + u64(leaves[t].level) } | { u64(0) }
}

fixed: (leaves: []Leaf, t: u32): u64 {
  t < len(leaves) ? { leaves[t].entries[u32(7)] } | { u64(1) }
}

pend: (doms: [*]Dom, d: u32, i: u32): u32 {
  d < len(doms) && i < u32(8) ? { doms[d].pending[i] + doms[d].count } | { u32(0) }
}

set_level: (leaves: [*]Leaf, t: u32, v: u32): () {
  t < len(leaves) ? { leaves[t].level = v; leaves[t].entries[u32(9)] = u64(40); leaves[t].entries[u32(7)] = u64(5) } | { }
}

main: (): i32 {
  nodes: [3]Node
  nodes[u32(1)].value = u32(6)
  nodes[u32(1)].next = u32(4)
  nodes[u32(2)].weight = u64(11)
  leaves: [1]Leaf
  doms: [2]Dom
  doms[u32(1)].pending[u32(2)] = u32(8)
  doms[u32(1)].count = u32(1)
  set_level(span(&leaves), u32(0), u32(3))
  // 10 + 11 + (40 + 3) + 5 + 9 = 78
  i32_bits_u32(peek(view(&nodes), u32(1)) + u32_trunc_u64(heavy(span(&nodes), u32(2)) + walk(span(&leaves), u32(0), u32(9)) + fixed(view(&leaves), u32(0))) + pend(span(&doms), u32(1), u32(2)))
}
`

func TestE2ENativeRecordSpanReadersProven(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("record_span_proof.oak", nativeRecordSpanProofProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_record_span_proof", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 78 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 78\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"peek", "heavy", "walk", "fixed", "pend"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") {
			t.Errorf("%s reads a span of records and must be proven; diagnostics:\n%s", fn, joined)
		}
	}
	if !strings.Contains(joined, "asm unit set_level:") {
		t.Errorf("set_level must lower natively; diagnostics:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_record_span_proof_c", New().WithSource("record_span_proof.oak", nativeRecordSpanProofProgram)); abnormal || code != 78 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 78", code, abnormal)
	}
}
